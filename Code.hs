module Code where

import Lambda

type Context = [(String, Lambda)]

data Line
 = Eval Lambda
  | Binding String Lambda
  deriving (Eq)

instance Show Line where
  show (Eval l) = show l
  show (Binding s l) = s ++ " = " ++ show l

-- var right, app expand both, abs ab the same
expand :: Context -> Lambda -> Either String Lambda
expand _ (Var x) = Right (Var x)
expand ctx (App e1 e2) = do
  e1' <- expand ctx e1
  e2' <- expand ctx e2
  pure (App e1' e2')
expand ctx (Abs x e) = do
  e' <- expand ctx e
  pure (Abs x e')
expand ctx (Macro name) = case lookup name ctx of
  Just e -> expand ctx e
  Nothing -> Left name

-- 3.1.
-- left same right simplified, macro name case lookup of
simplifyCtx :: Context -> (Lambda -> Lambda) -> Lambda -> Either String [Lambda]
simplifyCtx ctx step e = case expand ctx e of
  Left name -> Left name
  Right expanded -> Right (simplify step expanded)

normalCtx :: Context -> Lambda -> Either String [Lambda]
normalCtx ctx = simplifyCtx ctx normalStep

applicativeCtx :: Context -> Lambda -> Either String [Lambda]
applicativeCtx ctx = simplifyCtx ctx applicativeStep
