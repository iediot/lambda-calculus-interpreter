{- HLINT ignore "Use lambda-case" -}
{- HLINT ignore "Use <$>" -}
module Parser where

import Control.Applicative
import Data.Char (isDigit, isLower, isUpper)

import Lambda
import Code

-- a parser is a function from input to either failure
-- or a parsed value plus the leftover string
newtype Parser a = Parser { parse :: String -> Maybe (a, String) }

instance Functor Parser where
  fmap f (Parser p) = Parser $ \s -> case p s of
    Just (a, rest) -> Just (f a, rest)
    Nothing        -> Nothing

instance Applicative Parser where
  pure x = Parser $ \s -> Just (x, s)
  Parser pf <*> Parser pa = Parser $ \s -> case pf s of
    Nothing      -> Nothing
    Just (f, r1) -> case pa r1 of
      Nothing      -> Nothing
      Just (a, r2) -> Just (f a, r2)

instance Monad Parser where
  Parser p >>= f = Parser $ \s -> case p s of
    Nothing        -> Nothing
    Just (a, rest) -> parse (f a) rest

instance Alternative Parser where
  empty = Parser $ const Nothing
  Parser p <|> Parser q = Parser $ \s -> case p s of
    Just result -> Just result
    Nothing     -> q s

-- consume one char that matches the predicate
sat :: (Char -> Bool) -> Parser Char
sat pred = Parser $ \s -> case s of
  c : rest | pred c -> Just (c, rest)
  _                 -> Nothing

-- consume one specific char
ch :: Char -> Parser Char
ch c = sat (== c)

-- one or more lowercase letters
varName :: Parser String
varName = some (sat isLower)

-- one or more uppercase letters or digits
macroName :: Parser String
macroName = some (sat (\c -> isUpper c || isDigit c))

-- an atom is a parenthesized lambda a variable or a macro
atom :: Parser Lambda
atom = parens <|> (Var <$> varName) <|> (Macro <$> macroName)
  where
    parens = do
      _ <- ch '('
      e <- lambda
      _ <- ch ')'
      pure e

-- one or more atoms separated by single spaces
-- x y z is grouped left to right as App nested on the left
app :: Parser Lambda
app = do
  first <- atom
  rest  <- many (ch ' ' >> atom)
  pure (foldl App first rest)

-- an abstraction \x.body where the body extends to the end
abst :: Parser Lambda
abst = do
  _ <- ch '\\'
  v <- varName
  _ <- ch '.'
  body <- lambda
  pure (Abs v body)

lambda :: Parser Lambda
lambda = abst <|> app

-- 2.1. / 3.2.
parseLambda :: String -> Lambda
parseLambda s = case parse lambda s of
  Just (e, "") -> e
  _            -> error "parse error"

-- 3.3.
-- a line is either a binding NAME=expr
-- or a bare expression to evaluate
parseLine :: String -> Either String Line
parseLine s = case parse line s of
  Just (l, "") -> Right l
  _            -> Left s
  where
    line    = binding <|> (Eval <$> lambda)
    binding = do
      name <- macroName
      _ <- ch '='
      body <- lambda
      pure (Binding name body)
