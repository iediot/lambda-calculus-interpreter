{- HLINT ignore "Use lambda-case" -}
{- HLINT ignore "Use <$>" -}
module Parser where

import Control.Applicative
import Data.Char (isDigit, isLower, isUpper)

import Lambda
import Code

-- a Parser is a newtype wrapping a function from input string
-- to maybe a pair (parsed value, leftover string)
-- nothing means parse failure
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

-- look at the input
-- if it starts with a char satisfying pred consume it and return it with the rest
-- otherwise nothing
sat :: (Char -> Bool) -> Parser Char
sat pred = Parser go
  where
    go (c : rest) | pred c = Just (c, rest)
    go _ = Nothing

-- sat for equality with one specific char
ch :: Char -> Parser Char
ch c = sat (== c)

-- some sat islower gives one or more lowercase letters
varName :: Parser String
varName = some (sat isLower)

-- some sat of isupper or isdigit
macroName :: Parser String
macroName = some (sat isMacroChar)
  where
    isMacroChar c = isUpper c || isDigit c

-- try parens else Var of varname else macro of macroName
-- parens is a do block consume ( then parse a lambda then consume ) return the lambda
atom :: Parser Lambda
atom = parens <|> (Var <$> varName) <|> (Macro <$> macroName)
  where
    parens = do
      _ <- ch '('
      e <- lambda
      _ <- ch ')'
      pure e

-- do block parse one atom then many of (space then atom)
-- foldl app over them so x y z becomes app (app x y) z
app :: Parser Lambda
app = do
  first <- atom
  rest <- many (ch ' ' >> atom)
  pure (foldl App first rest)

-- do block consume \ then varname then . then parse a lambda body
-- return abs of the var name and body
abst :: Parser Lambda
abst = do
  _ <- ch '\\'
  v <- varName
  _ <- ch '.'
  body <- lambda
  pure (Abs v body)

-- a lambda is an abst or an app
lambda :: Parser Lambda
lambda = abst <|> app

-- 2.1. / 3.2.
-- run parse lambda on the input
-- if it consumed everything return the parsed lambda
-- otherwise error
parseLambda :: String -> Lambda
parseLambda s = case parse lambda s of
  Just (e, "") -> e
  _ -> error "parse error"

-- 3.3.
-- a line is a binding or an eval of a lambda
-- binding is a do block macroName then = then a lambda body return binding name body
-- if parse succeeds with no leftover return right of the line
-- otherwise left of the input string
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
