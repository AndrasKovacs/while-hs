
{-# LANGUAGE
  NoMonomorphismRestriction, LambdaCase, RecordWildCards,
  TupleSections, DeriveFunctor, DeriveFoldable, DeriveTraversable,
  FlexibleContexts #-}

import Control.Applicative
import Control.Comonad
import Control.Comonad.Cofree
import Control.Lens
import Control.Monad.Except
import Control.Monad.State.Strict
import Control.Monad.Writer.Strict
import Data.Bifoldable
import Data.Bitraversable
import Data.Foldable (Foldable)
import Data.List
import System.FilePath.Glob
import System.Environment
import Text.Printf
import qualified Data.HashMap.Strict as HM
import qualified Data.Traversable as T (mapM)

import Text.Parsec hiding ((<|>), many, many1, label)
import Text.Parsec.Combinator
import Text.Parsec.Expr
import Text.Parsec.Pos
import Text.Parsec.String (Parser)
import qualified Text.Parsec.Token as Tok


---- MAIN
----------------------------------------------------------------------

main :: IO ()
main = do
  getArgs >>= \case
    path:[] ->  do
      inp <- readFile path
      Main.compile path inp ^. chosen & putStrLn
    _ -> putStrLn "usage: ./while filename"

compile :: FilePath -> String -> Either String String
compile path inp = do
  ast <- parse pProgram path inp & _Left %~ show
  (ast, (_, symtable)) <- 
    runStateT (checkProgram ast) (initialPos path, HM.empty)
  pure $ execWriter $ evalStateT (genProgram ast) (0, snd <$> symtable)    


---- TESTING
----------------------------------------------------------------------

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
    (\prog -> void $ evalStateT (checkProgram prog) (initialPos path, HM.empty))
    (parse pProgram path inp)


---- TYPES
----------------------------------------------------------------------

type Id         = String
type RawExp     = Cofree ExpF SourcePos
type RawSt      = Cofree (StF RawExp) SourcePos
type Exp        = Cofree ExpF (SourcePos, Type)
type St         = Cofree (StF Exp) SourcePos
type Decl       = Cofree (Const (Type, Id)) SourcePos
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
  deriving (Eq, Show, Functor, Foldable, Traversable)

data StF exp rec
  = Assign Id exp
  | Read Id
  | Write exp
  | If exp [rec]
  | IfElse exp [rec] [rec]
  | While exp [rec]
  | Skip
  deriving (Eq, Show, Functor, Foldable, Traversable)

instance Bifunctor StF  where bimap = bimapDefault
instance Bifoldable StF where bifoldMap = bifoldMapDefault
                              
instance Bitraversable StF where
  bitraverse f g = \case
    Assign id exp    -> Assign id <$> f exp
    Read id          -> pure (Read id)
    Write exp        -> Write <$> f exp
    If exp sts       -> If <$> f exp <*> traverse g sts
    IfElse exp ts fs -> IfElse <$> f exp <*> traverse g ts <*> traverse g fs
    While exp sts    -> While <$> f exp <*> traverse g sts
    Skip             -> pure Skip
    

---- PARSER
----------------------------------------------------------------------
    
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
pos ma = (:<) <$> getPosition <*> ma  

mkBinOp :: Stream s m Char => BinOp -> String -> Operator s u m RawExp
mkBinOp opType op = Infix go AssocLeft where
  go = do
    pos <- getPosition    
    reservedOp op
    pure ((:<) pos .: BinOp opType)

opTable :: Stream s m Char => OperatorTable s u m RawExp
opTable = [
    [Prefix (do {p <- getPosition; reservedOp "not"; pure ((:<) p . Not)})],
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
      (Read <$ reserved "read" <*>
        parens identifier <* semi)      
  <|> (Write <$ reserved "write" <*>
        parens pExp <* semi)      
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
  <|> (Assign <$>
        identifier <* symbol ":=" <*>
        pExp <* semi))
        
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


---- TYPE CHECKER
----------------------------------------------------------------------

type Check = StateT (SourcePos, HM.HashMap Id (SourcePos, Type)) (Either String)

symTable = _2
currPos  = _1

-- Bottom-up synthesize a new tag data component
retagM :: (Traversable f, Monad m) =>
     (a -> b -> c)      -- combine old and new tags
  -> (c -> b)           -- extract tag
  -> (a -> m ())        -- initialization step using old tag
  -> (f b -> m b)       -- synthesize  
  -> Cofree f a
  -> m (Cofree f c)
retagM combine tagEx init f (a :< fca) = do
  fcc <- T.mapM (retagM combine tagEx init f) fca
  init a
  b <- f (tagEx . extract <$> fcc)
  return (combine a b :< fcc)

-- Same as retagM but also (bi)traverses the first type param
biRetagM ::
     (Bitraversable f, Monad m, Applicative m) =>
     (a -> b -> c)                 -- combine old and new tags
  -> (c -> b)                      -- extract tag
  -> (a -> m ())                   -- initialization step using old tag
  -> (dat' -> datSummary)          -- extract data summary
  -> (dat  -> m dat')              -- operation on data
  -> (f datSummary b -> m b)       -- synthesize  
  -> Cofree (f dat) a
  -> m (Cofree (f dat') c)
biRetagM combine tagEx init datSum datOp f = go where
  go (a :< x) = do
    x <- bitraverse datOp go x
    init a
    b <- f (bimap datSum (\(x:<_) -> tagEx x) x)
    return (combine a b :< x)

(=?) :: Type -> Type -> Check ()
(=?) has want =
  unless (has == want) $ do
    pos <- use currPos
    throwError $ printf
      "%s: expected type %s, inferred %s"
      (show pos) (show want) (show has)

lookupId :: Id -> Check Type
lookupId id = 
  use (symTable . at id) >>= maybe
    (do pos <- use currPos
        throwError $ printf
          "%s: undefined variable: %s" (show pos) id)
    (pure . snd)  

inferExp :: RawExp -> Check Exp
inferExp = retagM (,) snd (currPos .=) $ \case
  I{}     -> pure TInt
  B{}     -> pure TBool
  Var id  -> lookupId id
  Not exp -> TBool <$ exp =? TBool
  BinOp op l r ->       
    if elem op [Add, Sub, Mul, Div, Mod, Less, Greater, Equal] then do
      each (=? TInt) (l, r)
      pure $ if elem op [Less, Greater, Equal] then TBool else TInt 
    else
      TBool <$ each (=? TBool) (l, r)

inferSt :: RawSt -> Check St
inferSt = biRetagM const (const ()) (currPos .=) (snd . extract) inferExp $ \case
  Assign id exp  -> (exp =?) =<< lookupId id
  Read id        -> void $ lookupId id
  If exp _       -> exp =? TBool
  IfElse exp _ _ -> exp =? TBool
  While exp _    -> exp =? TBool
  _              -> pure ()
  
checkDecls :: [Decl] -> Check ()
checkDecls = 
  mapM_ $ \(pos :< Const (ty, id)) ->
    use (symTable . at id) >>= maybe
      (symTable . at id ?= (pos, ty))
      (\(pos', _) -> 
        throwError $
          printf "%s: identifier \"%s\" already declared at line %d"
          (show pos) id (sourceLine pos'))

checkProgram :: RawProgram -> Check Program 
checkProgram (decls, sts) = do
  checkDecls decls
  (decls,) <$> each inferSt sts


---- CODEGEN
----------------------------------------------------------------------

type Codegen = StateT (Int, HM.HashMap Id Type) (Writer String)

label = _1

newLabel :: Codegen String
newLabel = ("label"++) . show <$> (label <<+= 1)

genDecls :: [Decl] -> Codegen ()
genDecls decls = do
  tell "section .bss\n"
  forM_ decls $ \(_ :< (Const (ty, id))) -> do
    let resTy = case ty of TInt -> "d"; TBool -> "b"
    tell $ printf "%s: res%s 1\n" id resTy

externs :: [Id]
externs = ["read_unsigned", "write_unsigned", "read_boolean", "write_boolean"]

header :: Codegen ()
header = do
  tell "global main\n"
  mapM_ (\s -> tell $ "extern " ++ s ++ "\n") externs

genExp :: Exp -> Codegen ()
genExp (_ :< exp) = case exp of
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

genSt :: St -> Codegen ()
genSt (_ :< st) = case st of
  Assign id exp -> do
    genExp exp
    tell $ printf "mov [%s], eax\n" id
  Read id -> do
    Just ty <- use $ symTable . at id
    case ty of
      TInt  -> tell "call read_unsigned\n"
      TBool -> tell "call read_boolean\n"
    tell $ printf "mov [%s], eax\n" id
  Write exp -> do
    genExp exp
    tell "push eax\n"
    case snd $ extract exp of
      TInt  -> tell "call write_unsigned\n"
      TBool -> tell "call write_boolean\n"
    tell "pop eax\n"
  If exp sts -> do
    endLabel <- newLabel    
    genExp exp
    tell "cmp eax, 1\n"
    tell $ printf "jne %s\n" endLabel
    each genSt sts
    tell $ endLabel ++ ":\n"
  IfElse exp ts fs -> do
    trueLabel <- newLabel
    endLabel  <- newLabel    
    genExp exp
    tell "cmp eax, 1\n"
    tell $ printf "je %s\n" trueLabel
    each genSt fs
    tell $ printf "jmp %s\n" endLabel
    tell $ trueLabel ++ ":\n"
    each genSt ts
    tell $ endLabel ++ ":\n"
  While exp sts -> do
    beginLabel <- newLabel
    endLabel   <- newLabel
    tell $ beginLabel ++ ":\n"
    genExp exp
    tell "cmp eax, 1\n"
    tell $ printf "jne %s\n" endLabel
    each genSt sts
    tell $ printf "jmp %s\n" beginLabel
    tell $ endLabel ++ ":\n"
  Skip ->
    pure ()

genProgram :: Program -> Codegen ()
genProgram (decls, sts) = do
  tell "\n"
  header
  tell "\n"
  genDecls decls
  tell  "\n"
  tell "section .text\n"
  tell "main:\n"
  each genSt sts
  tell "ret\n"    
