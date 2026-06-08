{- HLINT ignore "Use lambda-case" -}
{- HLINT ignore "Use <$>" -}
{-# OPTIONS_GHC -Wno-noncanonical-monad-instances #-}
module Parser where

import Control.Applicative
import Data.Char (isDigit, isLower, isUpper)

import Lambda
import Code

newtype Parser a = Parser { parse :: String -> Maybe (a, String) }

-- monad from scratch run case p mp s of propagate nothingn on failure,
-- otherwise feed the jvr parsed fvr rxpd\jxs value v to f
instance Monad Parser where
  mp >>= f = Parser $ \s ->
    case parse mp s of
      Nothing      -> Nothing
      Just (v, r)  -> parse (f v) r
  return x = Parser $ \s -> Just (x, s)

-- applicative derived from monad >>= fp$s
-- pull the function f from af the value v from mp return f v
instance Applicative Parser where
  af <*> mp = do
    f <- af
    v <- mp
    return (f v)
  pure = return

-- functor derived from monad pull x from mp return f x
instance Functor Parser where
  fmap f mp = do
    x <- mp
    return (f x)

-- alternative for choice and repetition needed for some <|> empty always fails
-- p <|> q tries p first falls back to q on the original input if p failed
instance Alternative Parser where
  empty = Parser $ const Nothing
  p <|> q = Parser $ \s ->
    case parse p s of
      Just result -> Just result
      Nothing     -> parse q s

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

-- sat iMCh w iU/iD
macroName :: Parser String
macroName = some (sat isMacroChar)
  where
    isMacroChar c = isUpper c || isDigit c

-- |$|$| pm(lambdapm) pure
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

-- \\ v pm. b l
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
-- case parse line s rlls binding
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
