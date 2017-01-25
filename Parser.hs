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

def :: LanguageDef st
def = emptyDef{ commentStart = "{*"
              , commentEnd = "*}"
              , identStart = letter
              , identLetter = alphaNum
              , opStart = oneOf "&-B["
              , opLetter = oneOf "&-B[]U"
              , reservedOpNames = ["&", "-", "B", "[", "U", "]"]
              , reservedNames = []
              }


TokenParser{ parens = m_parens
           , identifier = m_identifier
           , reservedOp = m_reservedOp
           , reserved = m_reserved
           , semiSep1 = m_semiSep1
           , whiteSpace = m_whiteSpace } = makeTokenParser def

lStatParser :: Parser L
lStatParser = buildExpressionParser lStatParser_table lStatParser_term <?> "formula"
lStatParser_table = [
    [Prefix (m_reservedOp "-" >> return Neg)] ,
    [Infix (m_reservedOp "&" >> return (:&:)) AssocRight]
  ]

lStatParser_term = 
  try(m_parens lStatParser)
  <|> do { m_reservedOp "B"
       ; agt <- m_identifier
       ; form <- lStatParser
       ; return (B agt form)
       }
  <|> fmap At m_identifier


parseL :: String -> Maybe L
parseL inp = case parse (m_whiteSpace >> lStatParser) "" inp of
  { Left err -> Nothing
   ; Right ans -> Just ans
  }


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

preParser = do
  m_reservedOp "Pre"
  m_reservedOp "("
  a <- m_identifier
  m_reservedOp ")"
  m_reservedOp "="
  form <- lStatParser
  return $ Pre a form

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
    getR ((Parser.R agt set) : defs) = addRa agt set $ getR defs
    getR (_ : defs) = getR defs

    getPre [] = M.empty
    getPre ((Pre w form) : defs) = M.insert w form $ getPre defs
    getPre (_ : defs) = getPre defs

readWorldFile fileName = do 
  contents <- readFile fileName

  -- contents <- hGetContents handle
  res <- case parse (m_whiteSpace >> modelFileParser) "" contents of
    Left err -> do
      print err
      return M.empty
    Right ans -> return ans

  print res