module Parser where 

import Control.Applicative((<*))
import Text.Parsec
import Text.Parsec.String
import Text.Parsec.Expr
import Text.Parsec.Token
import Text.Parsec.Language
import CoreLang

-- import Text.Parsec.Combinator
import System.IO
import qualified Data.Map as M
import qualified Data.Set as S

data LParse =
    At String 
  | Neg LParse
  | And LParse LParse
  | B String LParse
  | Box String LParse
  | Or LParse LParse
  | Imp LParse LParse deriving Show

def :: LanguageDef st
def = emptyDef{ commentStart = "{*"
              , commentEnd = "*}"
              , identStart = letter
              , identLetter = alphaNum
              , opStart = oneOf "&-B["
              , opLetter = oneOf "-^|>B[]U"
              , reservedOpNames = ["^", "|", "-", ">", "B", "[", "U", "]"]
              , reservedNames = []
              }


TokenParser{ parens = m_parens
           , identifier = m_identifier
           , reservedOp = m_reservedOp
           , reserved = m_reserved
           , semiSep1 = m_semiSep1
           , whiteSpace = m_whiteSpace } = makeTokenParser def

lParseStatParser :: Parser LParse
lParseStatParser = buildExpressionParser lParseStatParser_table lParseStatParser_term <?> "formula"
lParseStatParser_table = [
    [Prefix (m_reservedOp "-" >> return Parser.Neg)] ,
    [Infix (m_reservedOp ">" >> return Imp) AssocRight] ,
    [Infix (m_reservedOp "^" >> return And) AssocRight] ,
    [Infix (m_reservedOp "|" >> return Or) AssocRight]
  ]

lParseStatParser_term = 
  try(m_parens lParseStatParser)
  <|> do 
      m_reservedOp "B"
      agt <- m_identifier
      form <- lParseStatParser
      return (Parser.B agt form)
  <|> do
      m_reservedOp "["
      m <- m_identifier
      m_reservedOp "]"
      form <- lParseStatParser
      return (Box m form)
  <|> fmap Parser.At m_identifier


parseLParse :: String -> Maybe LParse
parseLParse inp = case parse (m_whiteSpace >> lParseStatParser) "" inp of
  { Left err -> Nothing
   ; Right ans -> Just ans
  }


-- parseLStat :: String -> Maybe L
-- parseLStat inp = case parse (m_whiteSpace >> lParseStatParser) "" inp of
--   Left err -> print err
--     -- Nothing
--   Right ans -> case lParseToLStat ans of
--     Just f -> print f
--     Nothing -> print "formula cant be turned into LStat"

parseL :: (M.Map String Model') -> String -> Maybe L
parseL m inp = case parse (m_whiteSpace >> lParseStatParser) "" inp of
  Left err -> Nothing
  Right ans -> lParseToL m ans

parseLStat :: String -> Maybe L
parseLStat = parseL M.empty

data Model'Parse = W World | Pre World L | R Agt [(World , World)] deriving Show


tupleParser = do
  m_reservedOp "("
  a <- m_identifier
  m_reservedOp ","
  b <- m_identifier
  m_reservedOp ")"
  return (a , b)

setParser = do
  m_reservedOp "{"
  set <- sepBy tupleParser (m_reservedOp ",")
  m_reservedOp "}"
  return set

rParser = do
  m_reservedOp "R"
  m_reservedOp "("
  a <- m_identifier
  m_reservedOp ")"
  m_reservedOp "="
  set <- setParser
  return $ Parser.R a set


lParseToL :: (M.Map String Model') -> LParse -> Maybe L
lParseToL m (Parser.At p) = return $ CoreLang.At p
lParseToL m (Parser.Neg (Parser.Neg f)) = lParseToL m f
lParseToL m (Parser.Neg f) = (lParseToL m f) >>= (return . CoreLang.Neg) 
lParseToL m (Parser.And f1 f2) = do
  f1M <- lParseToL m f1
  f2M <- lParseToL m f2
  return $ f1M :^: f2M
lParseToL m (Parser.B agt f) = (lParseToL m f) >>= (return . (CoreLang.B agt)) 
lParseToL m (Parser.Box mlab f) = do
  model <- M.lookup mlab m
  fM <- lParseToL m f
  return $ (M model) :□: fM
lParseToL m (Parser.Or f1 f2) = lParseToL m (Parser.Neg (Parser.And (Parser.Neg f1) (Parser.Neg f2)))
lParseToL m (Parser.Imp f1 f2) = lParseToL m (Or (Parser.Neg f1) f2)

lParseToLStat :: LParse -> Maybe L
lParseToLStat = lParseToL (M.empty)

preParser = do
  m_reservedOp "Pre"
  m_reservedOp "("
  a <- m_identifier
  m_reservedOp ")"
  m_reservedOp "="
  form <- lParseStatParser
  case lParseToLStat form of 
    Just formL -> return $ Pre a formL
    Nothing -> fail "could not turn the formula into an LStat formula"

worldParser = do
  a <- m_identifier
  return $ W a

modelParser = do
  name <- m_identifier
  m_reservedOp "="
  m_reservedOp "{{"
  set <- many1 (preParser <|> rParser <|> worldParser)
  m_reservedOp "}}"
  return (name, set)

modelFileParser :: Parser (M.Map String Model')
modelFileParser = do
  set <- sepBy modelParser (m_reservedOp ";;")
  return $ M.fromList $ foldr 
    (\(name, mset) rest -> 
      case genModel' mset of {Just r -> ((name, r): rest) ; Nothing -> rest} ) 
    [] set


genModel' :: [Model'Parse] -> Maybe Model'
genModel' defs = do
  w <- getW defs
  let r = getR defs in 
    let pre = getPre defs in
      return $ Model w r pre
  where
    getW [] = Nothing
    getW ((W w):_) = Just w
    getW _ = Nothing

    getR [] = M.empty
    getR ((Parser.R agt set) : defs) = M.insert agt (S.fromList set) $ getR defs
    getR (_ : defs) = getR defs

    getPre [] = M.empty
    getPre ((Pre w form) : defs) = M.insert w form $ getPre defs
    getPre (_ : defs) = getPre defs


parseModel' :: String -> Maybe (M.Map String Model')
parseModel' inp = case parse (m_whiteSpace >> modelFileParser) "" inp of
  Left err -> Nothing
  Right ans -> return ans


readWorldFile fileName = do 
  contents <- readFile fileName

  -- contents <- hGetContents handle
  res <- case parse (m_whiteSpace >> modelFileParser) "" contents of
    Left err -> do
      print err
      return M.empty
    Right ans -> return ans

  print res