module Lambda where

import Data.List (nub, (\\))

data Lambda
  = Var String
  | App Lambda Lambda
  | Abs String Lambda
  | Macro String

instance Show Lambda where
  show (Var x)     = x
  show (App e1 e2) = "(" ++ show e1 ++ " " ++ show e2 ++ ")"
  show (Abs x e)   = "λ" ++ x ++ "." ++ show e
  show (Macro x)   = x

instance Eq Lambda where
  e1 == e2 = eq e1 e2 ([], [], [])
    where
      eq (Var x) (Var y) (env, xb, yb)     = elem (x, y) env || not (elem x xb || elem y yb)
      eq (App e1 e2) (App f1 f2) env       = eq e1 f1 env && eq e2 f2 env
      eq (Abs x e) (Abs y f) (env, xb, yb) = eq e f ((x, y) : env, x : xb, y : yb)
      eq (Macro x) (Macro y) _             = x == y
      eq _ _ _                             = False

-- 1.1.
-- all variable names that appear anywhere in the expression
vars :: Lambda -> [String]
vars (Var x)     = [x]
vars (App e1 e2) = nub (vars e1 ++ vars e2)
vars (Abs x e)   = nub (x : vars e)
vars (Macro _)   = []

-- 1.2.
-- variables not bound by any outer lambda
freeVars :: Lambda -> [String]
freeVars (Var x)     = [x]
freeVars (App e1 e2) = nub (freeVars e1 ++ freeVars e2)
freeVars (Abs x e)   = freeVars e \\ [x]
freeVars (Macro _)   = []

-- 1.3.
-- smallest name not in the list in order a b c through z
-- then aa ab through zz then aaa and so on
newVar :: [String] -> String
newVar taken = head [name | name <- allNames, name `notElem` taken]
  where
    letters                          = ['a' .. 'z']
    namesOfLength :: Int -> [String]
    namesOfLength 1                  = [[c] | c <- letters]
    namesOfLength n                  = [c : rest | c <- letters, rest <- namesOfLength (n - 1)]
    allNames                         = concat [namesOfLength n | n <- [1 ..]]

-- 1.4.
-- normal form means no redex anywhere
isNormalForm :: Lambda -> Bool
isNormalForm (Var _)             = True
isNormalForm (App (Abs _ _) _)   = False
isNormalForm (App e1 e2)         = isNormalForm e1 && isNormalForm e2
isNormalForm (Abs _ e)           = isNormalForm e
isNormalForm (Macro _)           = True

-- 1.5.
-- substitute e for every free x inside the body
-- when going under a lambday that would capture a free var of e
-- rename y to a fresh name first
reduce :: String -> Lambda -> Lambda -> Lambda
reduce x (Var y) e
  | x == y    = e
  | otherwise = Var y
reduce x (App e1 e2) e =
  App (reduce x e1 e) (reduce x e2 e)
reduce x (Abs y body) e
  | x == y               = Abs y body
  | y `notElem` freeInE  = Abs y (reduce x body e)
  | otherwise            = Abs fresh (reduce x renamedBody e)
  where
    freeInE     = freeVars e
    fresh       = newVar (freeInE ++ freeVars body ++ [x])
    renamedBody = reduce y body (Var fresh)
reduce _ (Macro m) _ = Macro m

-- 1.6.
-- one step of leftmost outermost reduction
-- fire the topmost redex first
normalStep :: Lambda -> Lambda
normalStep (App (Abs x body) arg) = reduce x body arg
normalStep (App e1 e2)
  | not (isNormalForm e1) = App (normalStep e1) e2
  | otherwise             = App e1 (normalStep e2)
normalStep (Abs x e) = Abs x (normalStep e)
normalStep e         = e

-- 1.7.
-- one step of leftmost innermost reduction
-- only fire a redex once both sides are already in normal form
applicativeStep :: Lambda -> Lambda
applicativeStep (App e1 e2)
  | not (isNormalForm e1) = App (applicativeStep e1) e2
  | not (isNormalForm e2) = App e1 (applicativeStep e2)
  | otherwise = case e1 of
      Abs x body -> reduce x body e2
      _          -> App e1 e2
applicativeStep (Abs x e) = Abs x (applicativeStep e)
applicativeStep e         = e

-- 1.8.
-- keep stepping until normal form and return every intermediate
simplify :: (Lambda -> Lambda) -> Lambda -> [Lambda]
simplify step e
  | isNormalForm e = [e]
  | otherwise      = e : simplify step (step e)

normal :: Lambda -> [Lambda]
normal = simplify normalStep

applicative :: Lambda -> [Lambda]
applicative = simplify applicativeStep
