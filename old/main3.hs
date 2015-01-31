
{-# LANGUAGE
  TupleSections,
  UndecidableInstances,
  NoMonomorphismRestriction,
  LambdaCase,
  RecordWildCards #-}

import Control.Applicative
import Control.Lens
import Control.Monad.State.Strict
import Control.Monad.Writer.Strict
import Control.Monad.Except
import Text.Printf
import qualified Data.HashMap.Strict as HM
import System.FilePath.Glob

import Text.Parsec hiding ((<|>), many, many1, label)
import qualified Text.Parsec.Token as Tok
import Text.Parsec.Combinator
import Text.Parsec.Expr
import Text.Parsec.Pos
import Text.Parsec.String (Parser)

import Data.List (sort)


data Tagged t f = Tag t (f (Tagged t f))
deriving instance (Eq t, Eq (f (Tagged t f))) => Eq (Tagged t f)
deriving instance (Show t, Show (f (Tagged t f))) => Show (Tagged t f)
deriving instance Show a => Show (Const a b) -- orphan instance...

type Id         = String
type RawExp     = Tagged SourcePos ExpF
type RawSt      = Tagged SourcePos (StF RawExp)
type Exp        = Tagged (SourcePos, Type) ExpF
type St         = Tagged SourcePos (StF Exp)
type Decl       = Tagged SourcePos (Const (Type, Id))
type RawProgram = ([Decl], [RawSt])
type Program    = ([Decl], [St])

data Type
  = TBool | TInt
  deriving (Eq, Show)
           
data BinOp
  = Add | Sub | Mul | Div | Mod
  | Less | Greater | Equal
  | And | Or
  deriving (Eq, Show)

data ExpF rec
  = I Integer
  | B Bool
  | Var Id
  | BinOp BinOp rec rec
  | Not rec
  deriving (Eq, Show)

data StF exp rec
  = Assign Id exp
  | Read Id
  | Write exp
  | If exp [rec]
  | IfElse exp [rec] [rec]
  | While exp [rec]
  | Skip
  deriving (Eq, Show)




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

(f .: g) x y = f (g x y)
pos ma = Tag <$> getPosition <*> ma  

mkBinOp :: Stream s m Char => BinOp -> String -> Operator s u m RawExp
mkBinOp opType op = Infix go AssocLeft where
  go = do
    pos <- getPosition    
    reservedOp op
    pure (Tag pos .: BinOp opType)

opTable :: Stream s m Char => OperatorTable s u m RawExp
opTable = [
    [Prefix (do {p <- getPosition; reservedOp "not"; pure (Tag p . Not)})],
    [mkBinOp Mod "mod", mkBinOp Div "div"],
    [mkBinOp Mul "*"],
    [mkBinOp Add "+", mkBinOp Sub "-"],
    [mkBinOp Less "<", mkBinOp Greater ">"],
    [mkBinOp Equal "="],
    [mkBinOp And "and"],
    [mkBinOp Or "or"]
 ]

pExp :: Parser RawExp
pExp = buildExpressionParser opTable (
      parens pExp
  <|> (pos $ I <$> natural)
  <|> (pos $ B <$> ((True <$ reserved "true") <|> (False <$ reserved "false")))
  <|> (pos $ Var <$> identifier))      

pStmt :: Parser RawSt
pStmt = pos (
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
  <|> (Assign <$> identifier <* symbol ":=" <*> pExp <* semi)
      )
        
pDecl :: Parser Decl
pDecl = 
  pos (Const .: (,) <$>
   ((TInt <$ reserved "integer") <|> (TBool <$ reserved "boolean")) <*>
   identifier <* semi)

pProgram :: Parser RawProgram
pProgram =
  (,) <$ whiteSpace <* reserved "program" <* identifier <*>
  many pDecl <* reserved "begin" <*>
  many1 pStmt <* reserved "end" <* eof


type Check = StateT (HM.HashMap Id (SourcePos, Type)) (Either String)

checkExp :: Type -> RawExp -> Check Exp 
checkExp want exp = do
    exp@(Tag (pos, ty) _) <- inferExp exp 
    unless (ty == want) $ 
      throwError $ printf
        "%s: expected type %s, inferred %s"
        (show pos) (show want) (show ty)
    pure exp

inferExp :: RawExp -> Check Exp
inferExp (Tag pos exp) = case exp of
  
  I i       -> pureTag TInt (I i)
  B b       -> pureTag TBool (B b)
  Var id    -> lookupId pos id
  
  BinOp op l r -> do
    
    if elem op [Add, Sub, Mul, Div, Mod, Less, Greater, Equal] then do
      (l, r) <- each (checkExp TInt) (l, r)
      let ty = if elem op [Less, Greater, Equal] then TBool else TInt 
      pureTag ty $ BinOp op l r
      
    else if elem op [And, Or] then do
      (l, r) <- each (checkExp TBool) (l, r)
      pureTag TBool $ BinOp op l r

    else 
      throwError $ printf 
        "%s: unknown binary operation: %s" (show pos) (show op)

  Not exp -> do
    exp <- checkExp TBool exp
    pureTag TBool (Not exp)
  
  where
    pureTag :: Type -> ExpF Exp -> Check Exp
    pureTag ty exp = pure $ Tag (pos, ty) exp

lookupId :: SourcePos -> Id -> Check Exp
lookupId pos id = 
  use (at id) >>= maybe
    (throwError $ printf
       "%s: undefined variable: %s" (show pos) id)
    (\tag -> pure $ Tag tag (Var id))

inferSt :: RawSt -> Check St
inferSt (Tag pos st) = case st of
  
  Assign id exp -> do
    Tag (_, ty) _ <- lookupId pos id
    pureTag . Assign id =<< checkExp ty exp
    
  Read id ->
    Tag pos (Read id) <$ lookupId pos id
  
  Write exp ->
    pureTag . Write =<< inferExp exp
    
  If exp sts -> do
    exp <- checkExp TBool exp
    sts <- mapM inferSt sts
    pureTag $ If exp sts
    
  IfElse exp t f -> do
    exp <- checkExp TBool exp
    (t, f) <- each (mapM inferSt) (t, f)
    pureTag $ IfElse exp t f

  While exp sts -> do
    exp <- checkExp TBool exp
    sts <- mapM inferSt sts
    pureTag $ While exp sts
    
  Skip ->
    pureTag Skip
    
  where
    pureTag :: StF Exp St -> Check St
    pureTag = pure . Tag pos

checkDecls :: [Decl] -> Check ()
checkDecls = 
  mapM_ $ \(Tag pos (Const (ty, id))) ->
    use (at id) >>= maybe
      (at id ?= (pos, ty))
      (\(pos', _) -> 
        throwError $
          printf "line %d: identifier \"%s\" already declared at line %d"
          (sourceLine pos) id (sourceLine pos'))

checkProgram :: RawProgram -> Check Program 
checkProgram (decls, sts) = do
  checkDecls decls
  (decls,) <$> each inferSt sts



testDir :: FilePath
testDir = "./while-tesztfajlok/"

testParser :: FilePath -> IO ()
testParser path = do
  paths <- sort <$> glob path
  forM_ paths $ \path -> do
    printf "\ntesting parsing on file: %s\n" path
    inp <- readFile path
    either print (\_ -> putStrLn "OK") $ parse pProgram path inp

testChecker :: FilePath -> IO ()
testChecker path = do
  paths <- sort <$> glob path
  forM_ paths $ \path -> do
    printf "\ntesting type checking on file: %s\n" path
    either putStrLn (\_ -> putStrLn "OK") =<< checkFile path

checkFile :: FilePath -> IO (Either String ())
checkFile path = do
  inp <- readFile path
  pure $ either
    (Left . show)
    (\prog -> void $ evalStateT (checkProgram prog) (HM.empty))
    (parse pProgram path inp)



type Codegen = StateT Int (Writer String)

newLabel :: Codegen String
newLabel = ("label"++) . show <$> (id <<+= 1)

genDecls :: [Decl] -> Codegen ()
genDecls = mapM_ $ \(Tag _ (Const (ty, id))) -> do
  let resTy = case ty of TInt -> "d"; TBool -> "b"
  tell $ printf "%s: res%s 1\n" id resTy

externs :: [Id]
externs = ["read_unsigned", "write_unsigned", "read_boolean", "write_boolean"]

header :: Codegen ()
header = do
  tell "global main\n"
  mapM_ (tell . ("extern "++)) externs

genExp :: Exp -> Codegen ()
genExp (Tag (pos, ty) exp) = case exp of
  
  I i    -> tell $ printf "mov eax, %d\n" i
  B b    -> tell $ printf "mov eax, %d\n" (fromEnum b)
  Var id -> tell $ printf "mov eax, [%s]\n" id
  
  BinOp op l r -> do    
    genExp r
    tell "push eax\n"
    genExp l
    tell "pop ebx\n"
    case op of
      Add  -> tell "add eax, ebx\n"
      Sub  -> tell "sub eax, ebx\n"
      Mul  -> tell "mul ebx\n"
      Div  -> tell "div ebx\n"
      Mod  -> tell "mod ebx\n" >> tell "mov eax, edx\n"
      And  -> tell "and eax, ebx\n"
      Or   -> tell "or eax, ebx\n"
      other -> do
        trueLabel <- newLabel
        endLabel  <- newLabel
        tell "cmp eax, ebx\n"
        tell $ case other of
          Greater -> printf "ja %s\n" trueLabel
          Less    -> printf "jb %s\n" trueLabel
          Equal   -> printf "je %s\n" trueLabel
        tell "xor eax, eax\n"
        tell $ printf "jmp %s\n" endLabel
        tell $ trueLabel ++ ":\n"
        tell "mov eax, 1\n"
        tell $ endLabel ++ ":\n"

  Not exp -> do
    genExp exp
    tell "not eax\n"
    
    
  


-- data BinOp
--   = Add | Sub | Mul | Div | Mod
--   | Less | Greater | Equal
--   | And | Or
--   deriving (Eq, Show)

-- data ExpF rec
--   = I Integer
--   | B Bool
--   | Var Id
--   | BinOp BinOp rec rec
--   | Not rec
--   deriving (Eq, Show)
