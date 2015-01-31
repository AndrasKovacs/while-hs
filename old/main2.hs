
{-# LANGUAGE NoMonomorphismRestriction, LambdaCase, RecordWildCards #-}

import Control.Applicative 
import Control.Lens
import Control.Monad.State.Strict
import Control.Monad.Writer.Strict
import Control.Monad.Error.Class
import Text.Printf
import System.FilePath.Glob
import qualified Data.HashMap.Strict as HM

import Text.Parsec hiding ((<|>), many, label)
import Text.Parsec.Combinator
import Text.Parsec.Expr
import Text.Parsec.Pos
import qualified Text.Parsec.Token as Tok


-- Testing
-- ------------------------------------------------------------

testDir :: FilePath
testDir = "./while-tesztfajlok/"

parseTestPaths :: FilePath -> IO ()
parseTestPaths path = do
  paths <- glob path
  forM_ paths $ \p -> do
    printf "\ntesting file: %s\n" p
    parseTest pProgram =<< readFile p

-- checkTestPaths :: FilePath -> IO ()
-- checkTestPaths path = do
--   ps <- glob path
--   forM_ ps $ \p -> do
--     printf "\ntesting file: %s\n" p
--     either putStrLn (\_ -> putStrLn "OK") =<< checkFile p    


-- Parsing
-- ------------------------------------------------------------

binOps  = ["+", "-", "*", "<", ">", "="]
binFuns = ["and", "or", "not", "div", "mod"]

reservedNames = [
  "program", "begin", "end", "integer",
  "boolean", "true", "false", "div",
  "mod", "and", "or", "not", "skip", "if",
  "then", "else", "endif", "while", "do",
  "done", "read", "write" ]

Tok.TokenParser {..} =
  Tok.makeTokenParser $ Tok.LanguageDef {
    commentStart    = "",
    commentEnd      = "",
    commentLine     = "#",
    nestedComments  = False,
    identStart      = letter,
    identLetter     = char '_' <|> alphaNum,
    opStart         = oneOf (concat binOps),
    opLetter        = oneOf (concat binOps),
    reservedNames   = reservedNames,
    reservedOpNames = binOps ++ binFuns,
    caseSensitive   = True }

mkBinOp opType op = Infix (BinOp opType <$ reservedOp op) AssocLeft

binOpTable = [
    [Prefix (Not <$ reservedOp "not")],
    [mkBinOp Mod "mod", mkBinOp Div "div"],
    [mkBinOp Mul "*"],
    [mkBinOp Add "+", mkBinOp Sub "-"],
    [mkBinOp Less "<", mkBinOp Greater ">"],
    [mkBinOp Equal "="],
    [mkBinOp And "and"],
    [mkBinOp Or "or"]
 ]

pExp = buildExpressionParser binOpTable (
      parens pExp
  <|> (I <$> natural)
  <|> (B <$> ((True <$ reserved "true") <|> (False <$ reserved "false")))
  <|> (Var <$> identifier))      

pStmt = (,) <$> getPosition <*> (
  
      (Read <$ reserved "read" <*> parens identifier <* semi)      
  <|> (Write <$ reserved "write" <*> parens pExp <* semi)
  <|> try (If <$ reserved "if" <*>
      pExp <* reserved "then" <*>
      many1 pStmt <* reserved "endif")
  <|> (IfElse <$ reserved "if" <*>
      pExp <* reserved "then" <*>
      many1 pStmt <* reserved "else" <*>
      many1 pStmt <* reserved "endif")
  <|> (While <$ reserved "while" <*> 
      pExp <* reserved "do" <*> 
      many1 pStmt <* reserved "done")
  <|> (Skip <$ reserved "skip" <* semi)
  <|> (Assign <$> identifier <* symbol ":=" <*> pExp <* semi))
  
pDecl =
      (,) <$>
        getPosition <*>        
        ((,) <$>
         ((TInt <$ reserved "integer") <|> (TBool <$ reserved "boolean")) <*>
         identifier <* semi)

pProgram =
  (,) <$ whiteSpace <* reserved "program" <* identifier <*>
  many pDecl <* reserved "begin" <*>
  many1 pStmt <* reserved "end" <* eof

-- AST
-- ------------------------------------------------------------

type Posed   = (,) SourcePos
type Id      = String
type Decl    = Posed (Type, Id)
type Stmt    = Posed Stmt'
type Program = ([Decl], [Stmt])

data Type
  = TBool | TInt
  deriving (Eq, Show)
           
data BinOp
  = Add | Sub | Mul | Div | Mod
  | Less | Greater | Equal
  | And | Or
  deriving (Eq, Show)

data Exp
  = I Integer
  | B Bool
  | Var Id
  | BinOp BinOp Exp Exp
  | Not Exp
  deriving (Eq, Show)

data Stmt'
  = Assign Id Exp
  | Read Id
  | Write Exp
  | If Exp [Stmt]
  | IfElse Exp [Stmt] [Stmt]
  | While Exp [Stmt]
  | Skip
  deriving (Eq, Show)

-- Typecheck + Codegen
-- ------------------------------------------------------------

type Codegen = 
   StateT (SourcePos, Int, HM.HashMap Id (SourcePos, Type), String)
  (WriterT String
  (Either String))

currPos  = _1
label    = _2
symTable = _3
newLabel = printf "label%d:\n" <$> (label <<+= 1)

checkExp :: Type -> Exp -> Codegen ()
checkExp want exp = do
    ty <- inferExp exp 
    unless (ty == want) $ do
      p <- use currPos 
      throwError $
        printf
          "line %d: expected type %s, inferred %s for expression (%s)"
           (sourceLine p) (show want) (show ty) (show exp)

lookupVar :: Id -> Codegen Type
lookupVar name = 
  maybe
    (do
        p <- use currPos
        throwError $
          printf "line %d: undefined variable: %s" (sourceLine p) name)
    (pure . snd) =<< use (symTable . at name)

inferExp :: Exp -> Codegen Type
inferExp = \case  
  I i -> do
    tell $ printf "mov eax, %d\n" i
    pure TInt
    
  B b -> do
    tell $ printf "mov eax, %d\n" (fromEnum b)
    pure TBool
    
  Var id -> do
    tell $ printf "mov eax, [%s]\n" id
    lookupVar id        
    
  BinOp op l r -> do
    if elem op [Add, Sub, Mul, Div, Mod, Less, Greater, Equal] then do
      each (checkExp TInt) (l, r)
      pure $ if elem op [Less, Greater, Equal] then TBool else TInt
    else if elem op [And, Or] then
      TBool <$ each (checkExp TBool) (l, r)
    else 
      throwError "unknown binary operation"

  Not exp -> do
    checkExp TBool exp
    tell "not eax\n"
    pure TBool

checkStmt :: Stmt -> Codegen ()
checkStmt (pos, stmt) = (currPos .= pos) >> case stmt of
  Assign name exp -> do
    ty <- lookupVar name
    checkExp ty exp
  Read name -> lookupVar name & void
  Write exp -> inferExp exp & void
  If exp stmts -> checkStmt (pos, IfElse exp stmts [])
  IfElse exp t f -> do
    checkExp TBool exp
    (t, f) & each . each %%~ checkStmt & void
  While exp stmts -> do
    checkExp TBool exp
    stmts & each checkStmt & void
  Skip -> pure ()
    
checkDecls :: [Decl] -> Codegen ()
checkDecls =
  mapM_ $ \(pos, (ty, name)) -> 
     maybe
      (symTable . at name ?= (pos, ty))
      (\(pos', _) -> 
        throwError $
          printf
            "line %d: identifier \"%s\" already declared at line %d"
             (sourceLine pos) name (sourceLine pos'))
      =<< use (symTable . at name)      

checkProgram :: Program -> Codegen ()
checkProgram (decls, stmts) = do
  checkDecls decls
  mapM_ checkStmt stmts

-- checkFile :: FilePath -> IO (Either String ())
-- checkFile path = 
--   readFile path <&> \inp ->
--     either
--       (Left . show)
--       (\prog -> evalStateT (checkProgram prog) (initialPos path, 0, HM.empty, ""))
--       (parse pProgram path inp)

-- Codegen
-- ------------------------------------------------------------


stExp = undefined

stCode :: Stmt -> StateT Int (Writer String) ()
stCode (_, stmt) = case stmt of
  Assign id e -> do
    stExp e
    tell $ printf "mov [%s], eax\n" id
  Read id -> do
    tell "call read_unsigned\n"
    tell $ printf "mov [%s], eax\n" id
  Write e -> do
    stExp e
    tell "push eax\n"
  



-- data Stmt'
--   = Assign Id Exp
--   | Read Id
--   | Write Exp
--   | If Exp [Stmt]
--   | IfElse Exp [Stmt] [Stmt]
--   | While Exp [Stmt]
--   | Skip
--   deriving (Eq, Show)

           
-- genCode :: Program -> String
-- genCode (decls, stmts) = let
--   header = unlines [
--     "extern read_unsigned",
--     "extern write_unsigned",
--     "extren read_boolean",
--     "extern write_boolean",
--     "global main" ]

--   declCode = "section .bss\n" ++ [
--     printf "%s: res%s 1\n" id ty' | (_, (ty, id)) <- decls,
--     let ty' = case ty of TInt -> "d"; _ -> "b"]

--   stmtsCode = unlines [
--     "section .text\n" ++ "main:\n" ++ (genStmtsCode =<< stmts)

--   in _             

 
  
