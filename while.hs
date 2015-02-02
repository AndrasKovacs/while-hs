
{-# LANGUAGE
  NoMonomorphismRestriction, LambdaCase, RecordWildCards,
  TupleSections, DeriveFunctor, DeriveFoldable, DeriveTraversable,
  FlexibleContexts, OverloadedStrings, RecursiveDo #-}

import Prelude hiding (div, mod, and, or, not)
import Control.Applicative
import Control.Comonad 
import Control.Comonad.Cofree (Cofree(..))
import Control.Lens
import Control.Monad.Except
import Control.Monad.State.Strict
import Control.Monad.Writer.Strict

import Data.Bifoldable
import Data.Bitraversable
import Data.Foldable (Foldable)
import qualified Data.Traversable as T (mapM)

import System.FilePath.Glob
import System.Environment

import Data.DList (DList)
import qualified Data.DList as DL
import Data.List (sort)
import qualified Data.HashMap.Strict as HM

import Formatting (formatToString, (%))
import Formatting.ShortFormatters

import Text.Parsec hiding ((<|>), many, many1, label)
import Text.Parsec.Combinator
import Text.Parsec.Expr
import Text.Parsec.Pos
import Text.Parsec.String (Parser)
import qualified Text.Parsec.Token as Tok


---- UTIL
----------------------------------------------------------------------

format       = formatToString
(f .: g) x y = f (g x y)
pos ma       = (:<) <$> getPosition <*> ma  


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
  let writerRes = execWriter $ evalStateT (genProgram ast) (0, snd <$> symtable)    
  pure $ unlines $ DL.toList writerRes


---- TESTING
----------------------------------------------------------------------

testDir :: FilePath
testDir = "./while-test-files/"

testParser :: FilePath -> IO ()
testParser path = do
  paths <- sort <$> glob path
  forM_ paths $ \path -> do
    putStrLn $ format ("\ntesting parsing on file: "%s%"\n") path
    inp <- readFile path
    either print (\_ -> putStrLn "OK") $ parse pProgram path inp

testChecker :: FilePath -> IO ()
testChecker path = do
  paths <- sort <$> glob path
  forM_ paths $ \path -> do
    putStrLn $ format ("\ntesting type checking on file: "%s%"\n") path
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

data ExpF k
  = I Integer
  | B Bool
  | Var Id
  | BinOp BinOp k k
  | Not k
  deriving (Eq, Show, Functor, Foldable, Traversable)

data StF exp k
  = Assign Id exp
  | Read Id
  | Write exp
  | If exp [k]
  | IfElse exp [k] [k]
  | While exp [k]
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

binOps, binFuns :: [String]    
binOps  = ["+", "-", "*", "<", ">", "="]
binFuns = ["and", "or", "not", "div", "mod"]

reservedNames :: [String]
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
    throwError $ format 
      (s%": expected type "%s%", inferred "%s)
      (show pos) (show want) (show has)

lookupId :: Id -> Check Type
lookupId id = 
  use (symTable . at id) >>= maybe
    (do pos <- use currPos
        throwError $ format
          (s%": undefined variable: "%s) (show pos) id)
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
        throwError $ format
          (s%": identifier \""%s%"\" already declared at line "%d)
          (show pos) id (sourceLine pos'))

checkProgram :: RawProgram -> Check Program 
checkProgram (decls, sts) = do
  checkDecls decls
  (decls,) <$> each inferSt sts


---- CODEGEN MACROS
----------------------------------------------------------------------

type Codegen = StateT (Int, HM.HashMap Id Type) (Writer (DList String))

label :: String -> Codegen String
label lbl = do
  tell $ DL.singleton $ lbl ++ ":"
  return lbl

newLabel :: Codegen String
newLabel = do
  i <- _1 <<+= 1
  label $ "label" ++ show i

newLine  = tell $ DL.singleton ""
ret      = tell $ DL.singleton "ret"
res ty n = tell $ DL.singleton $ "res" ++ ty ++ " " ++ show n
resd     = res "d"
resb     = res "b"

binIns op a b = tell $ DL.singleton $ op ++ " " ++ a ++ ", " ++ b
unaryIns op a = tell $ DL.singleton $ op ++ " " ++ a
deref x       = "[" ++ x ++ "]"

[mov, add, sub, or, and, cmp, xor] = map binIns
  ["mov", "add", "sub", "or", "and", "cmp", "xor"]

[call, ja, jb, je, jmp, jne, not, div,
 mod, mul, push, pop, section, extern, global] = map unaryIns
  ["call", "ja", "jb", "je", "jmp", "jne", "not", "div",
   "mod", "mul", "push", "pop", "section", "global", "extern"]

[eax, ebx, edx, bss, text] =
  ["eax", "ebx", "edx", ".bss", ".text"]

externs = ["read_unsigned", "write_unsigned", "read_boolean", "write_boolean"]


---- CODEGEN 
----------------------------------------------------------------------

genExp :: Exp -> Codegen ()
genExp (_ :< exp) = case exp of
  I i    -> mov eax (show i)
  B b    -> mov eax (show $ fromEnum b)
  Var id -> mov eax (deref id)
  BinOp op l r -> do    
    genExp r
    push eax
    genExp l
    pop ebx
    case op of
      Add  -> add eax ebx
      Sub  -> sub eax ebx
      Mul  -> mul ebx
      Div  -> div ebx
      Mod  -> do {mod ebx; mov eax edx}
      And  -> and eax ebx
      Or   -> or eax ebx
      other -> mdo
        cmp eax ebx
        case other of
          Greater -> ja true
          Less    -> jb true
          Equal   -> je true
        mov eax "0"
        jmp end
        true <- newLabel
        mov eax "1"
        end <- newLabel
        pure ()
  Not exp -> do
    genExp exp
    not eax

genSt :: St -> Codegen ()
genSt (_ :< st) = case st of
  Assign id exp -> do
    genExp exp
    mov (deref id) eax
  Read id -> do
    Just ty <- use $ symTable . at id
    case ty of
      TInt  -> call "read_unsigned"
      TBool -> call "read_boolean"
    mov (deref id) eax
  Write exp -> do
    genExp exp
    push eax
    case snd $ extract exp of
      TInt  -> call "write_unsigned"
      TBool -> call "write_boolean"
    pop eax
  If exp sts -> mdo
    genExp exp
    cmp eax "1"
    jne end
    each genSt sts
    end <- newLabel
    pure ()
  IfElse exp ts fs -> mdo
    genExp exp
    cmp eax "1"
    je true
    each genSt fs
    jmp end
    true <- newLabel
    each genSt ts
    end <- newLabel
    pure ()
  While exp sts -> mdo
    begin <- newLabel
    genExp exp
    cmp eax "1"
    jne end
    each genSt sts
    jmp begin
    end <- newLabel
    pure ()
  Skip ->
    pure ()

genProgram :: Program -> Codegen ()
genProgram (decls, sts) = do
  newLine
  global "main"
  mapM_ extern externs
  
  newLine
  section bss
  forM_ decls $ \(_ :< (Const (ty, id))) -> do
    label id
    case ty of
      TInt -> resd 1
      TBool -> resb 1
  
  newLine
  section text
  label "main"
  each genSt sts
  ret

