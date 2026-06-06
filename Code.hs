module Code where

import Lambda

type Context = [(String, Lambda)]

data Line
  = Eval Lambda
  | Binding String Lambda
  deriving (Eq)

instance Show Line where
  show (Eval l)      = show l
  show (Binding s l) = s ++ " = " ++ show l

-- replace every Macro node by its definition from the context
-- returns Left name if a macro is missing
expand :: Context -> Lambda -> Either String Lambda
expand ctx (Macro name) = case lookup name ctx of
  Just e  -> expand ctx e
  Nothing -> Left name
expand ctx (App e1 e2) = do
  e1' <- expand ctx e1
  e2' <- expand ctx e2
  pure (App e1' e2')
expand ctx (Abs x e) = do
  e' <- expand ctx e
  pure (Abs x e')
expand _ (Var x) = Right (Var x)

-- 3.1.
-- expand macros first then run simplify with the chosen step
simplifyCtx :: Context -> (Lambda -> Lambda) -> Lambda -> Either String [Lambda]
simplifyCtx ctx step e = case expand ctx e of
  Left name      -> Left name
  Right expanded -> Right (simplify step expanded)

normalCtx :: Context -> Lambda -> Either String [Lambda]
normalCtx ctx = simplifyCtx ctx normalStep

applicativeCtx :: Context -> Lambda -> Either String [Lambda]
applicativeCtx ctx = simplifyCtx ctx applicativeStep
