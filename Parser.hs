{- HLINT ignore "Use lambda-case" -}
{- HLINT ignore "Use <$>" -}
module Parser where

import Control.Applicative
import Data.Char (isDigit, isLower, isUpper)

import Lambda
import Code

newtype Parser a = Parser { parse :: String -> Maybe (a, String) }

-- run the inner parser on the input
-- if Just transform the parsed value with f keeping the rest
-- if nothing propagate nothing
instance Functor Parser where
  fmap f (Parser p) = Parser $ \s -> case p s of
    Just (a, rest) -> Just (f a, rest)
    Nothing -> Nothing

-- pure x returns a parser that consumes nothing and yields x
-- <*> runs pf to get a function and remaining input
-- then runs pa on that remaining to get a value
-- both must succeed otherwise nothing
instance Applicative Parser where
  pure x = Parser $ \s -> Just (x, s)
  Parser pf <*> Parser pa = Parser $ \s -> case pf s of
    Nothing -> Nothing
    Just (f, r1) -> case pa r1 of
      Nothing -> Nothing
      Just (a, r2) -> Just (f a, r2)

-- bind runs p on input
-- if it succeeded feed the parsed value to f and run the resulting parser
-- on the leftover input
instance Monad Parser where
  Parser p >>= f = Parser $ \s -> case p s of
    Nothing -> Nothing
    Just (a, rest) -> parse (f a) rest

-- empty is the parser that always fails
-- <|> tries the first parser if it succeeds keep that result
-- otherwise try the second parser on the original input
instance Alternative Parser where
  empty = Parser $ const Nothing
  Parser p <|> Parser q = Parser $ \s -> case p s of
    Just result -> Just result
    Nothing -> q s

-- predp go
sat :: (Char -> Bool) -> Parser Char
sat pred = Parser go
  where
    go (c : rest) | pred c = Just (c, rest)
    go _ = Nothing

-- ch sat
ch :: Char -> Parser Char
ch c = sat (== c)

-- sat iL
varName :: Parser String
varName = some (sat isLower)

-- sat iMC w iU/iD
macroName :: Parser String
macroName = some (sat isMacroChar)
  where
    isMacroChar c = isUpper c || isDigit c

-- |$|$| (lambda) pure
atom :: Parser Lambda
atom = parens <|> (Var <$> varName) <|> (Macro <$> macroName)
  where
    parens = do
      _ <- ch '('
      e <- lambda
      _ <- ch ')'
      pure e

-- st f  foldl fr
app :: Parser Lambda
app = do
  first <- atom
  rest <- many (ch ' ' >> atom)
  pure (foldl App first rest)

-- \\ v . bl
abst :: Parser Lambda
abst = do
  _ <- ch '\\'
  v <- varName
  _ <- ch '.'
  body <- lambda
  pure (Abs v body)

-- abstr or app
lambda :: Parser Lambda
lambda = abst <|> app

-- 2.1. / 3.2.
-- ret parsed lambda or parse error
parseLambda :: String -> Lambda
parseLambda s = case parse lambda s of
  Just (e, "") -> e
  _ -> error "parse error"

-- 3.3.
-- case parse line s rlls 
parseLine :: String -> Either String Line
parseLine s = case parse line s of
  Just (l, "") -> Right l
  _ -> Left s
  where
    line = binding <|> (Eval <$> lambda)
    binding = do
      name <- macroName
      _ <- ch '='
      body <- lambda
      pure (Binding name body)
