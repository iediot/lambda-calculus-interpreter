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

-- walk the tree and replace every macro by its definition
-- macro name lookup the name in ctx if found recurse on the definition else left name
-- app do block expand both children then rebuild with app
-- abs do block expand body then rebuild with abs x
-- var is unchanged returned as right
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
-- expand first then simplify
-- case on expand result
-- left passes the missing macro name through
-- right wraps simplify step expanded back in right
simplifyCtx :: Context -> (Lambda -> Lambda) -> Lambda -> Either String [Lambda]
simplifyCtx ctx step e = case expand ctx e of
  Left name      -> Left name
  Right expanded -> Right (simplify step expanded)

normalCtx :: Context -> Lambda -> Either String [Lambda]
normalCtx ctx = simplifyCtx ctx normalStep

applicativeCtx :: Context -> Lambda -> Either String [Lambda]
applicativeCtx ctx = simplifyCtx ctx applicativeStep
