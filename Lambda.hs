module Lambda where

import Data.List (nub, (\\))
import Distribution.TestSuite (Test(Test))
import GHC.Base (TrName(TrNameD))
import GHC.IO.Encoding.Failure (CodingFailureMode(TransliterateCodingFailure))
import GHC.Exts.Heap (GenClosure(var))

data Lambda
 = Var String
  | App Lambda Lambda
  | Abs String Lambda
  | Macro String

instance Show Lambda where
  show (Var x) = x
  show (App e1 e2) = "(" ++ show e1 ++ " " ++ show e2 ++ ")"
  show (Abs x e) = "λ" ++ x ++ "." ++ show e
  show (Macro x) = x

instance Eq Lambda where
  e1 == e2 = eq e1 e2 ([], [], [])
    where
      eq (Var x) (Var y) (env, xb, yb) = elem (x, y) env || not (elem x xb || elem y yb)
      eq (App e1 e2) (App f1 f2) env = eq e1 f1 env && eq e2 f2 env
      eq (Abs x e) (Abs y f) (env, xb, yb) = eq e f ((x, y) : env, x : xb, y : yb)
      eq (Macro x) (Macro y) _ = x == y
      eq _ _ _ = False

-- 1.1.
-- var x is singleton list of x
-- app nub of recursing on both sides concatenated
-- abs nub of binder name cons recurse on body
-- macro is empty list
vars :: Lambda -> [String]
vars (Var x) = [x]
vars (App e1 e2) = nub (vars e1 ++ vars e2)
vars (Abs x e) = nub (x : vars e)
vars (Macro _) = []

-- 1.2.
-- same shape as vars only abs differs
-- instead of including the binder remove it from the body result using \\ x
freeVars :: Lambda -> [String]
freeVars (Var x) = [x]
freeVars (App e1 e2) = nub (freeVars e1 ++ freeVars e2)
freeVars (Abs x e) = freeVars e \\ [x]
freeVars (Macro _) = []

-- 1.3.
-- generate every name ordered by length then alphabetical
-- take the first one not in the taken list
-- helper namesoflength 1 is each single letter wrapped as a string
-- helper namesoflength n is each letter prepended to each name of length n-1
-- allnames is the concat of namesoflength n for n from 1 upward
-- need a type sig on namesoflength so n is inferred as int not integer
newVar :: [String] -> String
newVar taken = head [name | name <- allNames, name `notElem` taken]
  where
    letters = ['a' .. 'z']
    namesOfLength :: Int -> [String]
    namesOfLength 1 = [[c] | c <- letters]
    namesOfLength n = [c : rest | c <- letters, rest <- namesOfLength (n - 1)]
    allNames = concat [namesOfLength n | n <- [1 ..]]

-- 1.4.
-- 5 cases
-- var and macro are true
-- abs recurses into its body
-- app with abs on the left is false because that is a redex
-- any other app requires both sides to be in normal form
isNormalForm :: Lambda -> Bool
isNormalForm (Var _) = True
isNormalForm (App (Abs _ _) _) = False
isNormalForm (App e1 e2) = isNormalForm e1 && isNormalForm e2
isNormalForm (Abs _ e) = isNormalForm e
isNormalForm (Macro _) = True

-- 1.5.
-- substitute e for every free x inside the second arg
-- var y returns e when x = y else var y
-- app recurses on both children
-- abs has three sub cases
--   if binder name equals x stop because x is shadowed
--   if binder y is not free in e just recurse safely
--   else pick a fresh name avoiding freeVars e ++ freeVars body ++ x
--     first rename y to fresh in body using reduce y body - var fresh
--     then recurse with the renamed body
-- macro stays as is
reduce :: String -> Lambda -> Lambda -> Lambda
reduce x (Var y) e
  | x == y = e
  | otherwise = Var y
reduce x (App e1 e2) e =
  App (reduce x e1 e) (reduce x e2 e)
reduce x (Abs y body) e
  | x == y = Abs y body
  | y `notElem` freeVars e = Abs y (reduce x body e)
  | otherwise =
      let fresh = newVar (freeVars e ++ freeVars body ++ [x])
          renamedBody = reduce y body (Var fresh)
      in Abs fresh (reduce x renamedBody e)
reduce _ (Macro m) _ = Macro m

-- 1.6.
-- leftmost outermost
-- first clause app of abs fires the redex directly with reduce
-- next clause any app if left not in nf recurse left else recurse right
-- abs recurses into its body
-- anything else returns itself
normalStep :: Lambda -> Lambda
normalStep (App (Abs x body) arg) = reduce x body arg
normalStep (App e1 e2)
  | not (isNormalForm e1) = App (normalStep e1) e2
  | otherwise = App e1 (normalStep e2)
normalStep (Abs x e) = Abs x (normalStep e)
normalStep e = e

-- 1.7.
-- leftmost innermost
-- on app e1 e2 three guards in order
--   if e1 not in nf recurse on e1
--   else if e2 not in nf recurse on e2
--   else case on e1 if it is abs fire the redex else rebuild app e1 e2
-- abs recurses into its body
-- anything else returns itself
applicativeStep :: Lambda -> Lambda
applicativeStep (App (Abs x body) arg)
  | isNormalForm body && isNormalForm arg = reduce x body arg
applicativeStep (App e1 e2)
  | not (isNormalForm e1) = App (applicativeStep e1) e2
  | otherwise = App e1 (applicativeStep e2)
applicativeStep (Abs x e) = Abs x (applicativeStep e)
applicativeStep e = e

-- 1.8.
-- if already in nf return e
-- else cons e onto simplify step - step e
simplify :: (Lambda -> Lambda) -> Lambda -> [Lambda]
simplify step e
  | isNormalForm e = [e]
  | otherwise = e : simplify step (step e)

normal :: Lambda -> [Lambda]
normal = simplify normalStep

applicative :: Lambda -> [Lambda]
applicative = simplify applicativeStep
