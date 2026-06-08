module DeBruijn where

import Data.List (elemIndex)
import Lambda (Lambda(..))

type Context = [String]

data DeBruijn
 = DBVar Int
  | DBFree String
  | DBApp DeBruijn DeBruijn
  | DBAbs String DeBruijn

instance Show DeBruijn where
  show (DBVar n) = show n
  show (DBFree x) = x
  show (DBApp e1 e2) = "(" ++ show e1 ++ " " ++ show e2 ++ ")"
  show (DBAbs _ e) = "λ " ++ show e

instance Eq DeBruijn where
  DBVar n == DBVar m = n == m
  DBFree _ == DBFree _ = True
  DBApp e1 e2 == DBApp f1 f2 = e1 == f1 && e2 == f2
  DBAbs _ e == DBAbs _ f = e == f
  _ == _ = False

-- 4.1.
-- remember to use db not regular, var just and nothing, 
-- app usual abs kinda usual macro easy
toDB :: Context -> Lambda -> DeBruijn
toDB ctx (Var x) = case elemIndex x ctx of
  Just n -> DBVar n
  Nothing -> DBFree x
toDB ctx (App e1 e2) = DBApp (toDB ctx e1) (toDB ctx e2)
toDB ctx (Abs x e) = DBAbs x (toDB (x : ctx) e)
toDB _ (Macro m) = DBFree m

-- 4.2.
-- inverse of todb, again remember db
-- ctx !! n, free, app and abs
fromDB :: Context -> DeBruijn -> Lambda
fromDB ctx (DBVar n) = Var (ctx !! n)
fromDB _ (DBFree x) = Var x
fromDB ctx (DBApp e1 e2) = App (fromDB ctx e1) (fromDB ctx e2)
fromDB ctx (DBAbs x e) = Abs x (fromDB (x : ctx) e)

-- 4.3.
-- dbvft, appabs false, app usual abs kinda usual
isNormalForm :: DeBruijn -> Bool
isNormalForm (DBVar _) = True
isNormalForm (DBFree _) = True
isNormalForm (DBApp (DBAbs _ _) _) = False
isNormalForm (DBApp e1 e2) = isNormalForm e1 && isNormalForm e2
isNormalForm (DBAbs _ e) = isNormalForm e

-- if = if >, __, app usual abs diff but easy
subst :: Int -> DeBruijn -> DeBruijn -> DeBruijn
subst target val (DBVar n)
  | n == target = val
  | n > target = DBVar (n - 1)
  | otherwise = DBVar n
subst _ _ (DBFree x) = DBFree x
subst target val (DBApp e1 e2) = DBApp (subst target val e1) (subst target val e2)
subst target val (DBAbs x e) = DBAbs x (subst (target + 1) val e)

-- 4.4.
reduce :: DeBruijn -> DeBruijn -> DeBruijn
reduce = subst 0

-- 4.5.
-- _baab, app we check each, abse and ee
normalStep :: DeBruijn -> DeBruijn
normalStep (DBApp (DBAbs _ body) arg) = reduce arg body
normalStep (DBApp e1 e2)
  | not (isNormalForm e1) = DBApp (normalStep e1) e2
  | otherwise = DBApp e1 (normalStep e2)
normalStep (DBAbs x e) = DBAbs x (normalStep e)
normalStep e = e

-- 4.6.
-- app we check both and _bre2b
applicativeStep :: DeBruijn -> DeBruijn
applicativeStep (DBApp e1 e2)
  | not (isNormalForm e1) = DBApp (applicativeStep e1) e2
  | not (isNormalForm e2) = DBApp e1 (applicativeStep e2)
  | otherwise = case e1 of
      DBAbs _ body -> reduce e2 body
      _ -> DBApp e1 e2
applicativeStep (DBAbs x e) = DBAbs x (applicativeStep e)
applicativeStep e = e

-- 4.7.
-- infe simplify step
simplify :: (DeBruijn -> DeBruijn) -> DeBruijn -> [DeBruijn]
simplify step e
  | isNormalForm e = [e]
  | otherwise = e : simplify step (step e)

normal :: DeBruijn -> [DeBruijn]
normal = simplify normalStep

applicative :: DeBruijn -> [DeBruijn]
applicative = simplify applicativeStep
