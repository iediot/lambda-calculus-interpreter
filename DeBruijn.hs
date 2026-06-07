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
-- ctx is the binder names innermost first
-- var x case on elemindex x ctx just n means bound use dbvar n else dbfree x
-- app recurses on both with the same ctx
-- abs pushes binder name onto front of ctx then recurses
-- macro becomes dbfree of its name
toDB :: Context -> Lambda -> DeBruijn
toDB ctx (Var x) = case elemIndex x ctx of
  Just n -> DBVar n
  Nothing -> DBFree x
toDB ctx (App e1 e2) = DBApp (toDB ctx e1) (toDB ctx e2)
toDB ctx (Abs x e) = DBAbs x (toDB (x : ctx) e)
toDB _ (Macro m) = DBFree m

-- 4.2.
-- inverse of toDB
-- dbvar n is var of ctx !! n
-- dbfree x is var x
-- dbapp recurses on both
-- dbabs pushes name onto ctx then recurses building abs x of the result
fromDB :: Context -> DeBruijn -> Lambda
fromDB ctx (DBVar n) = Var (ctx !! n)
fromDB _ (DBFree x) = Var x
fromDB ctx (DBApp e1 e2) = App (fromDB ctx e1) (fromDB ctx e2)
fromDB ctx (DBAbs x e) = Abs x (fromDB (x : ctx) e)

-- 4.3.
-- dbvar and DBFree are True
-- dbapp with dbabs on the left is false that is a redex
-- any other dbapp needs both sides in NF
-- dbabs recurses into its body
isNormalForm :: DeBruijn -> Bool
isNormalForm (DBVar _) = True
isNormalForm (DBFree _) = True
isNormalForm (DBApp (DBAbs _ _) _) = False
isNormalForm (DBApp e1 e2) = isNormalForm e1 && isNormalForm e2
isNormalForm (DBAbs _ e) = isNormalForm e

-- add d to every free index inside e
-- d stays constant cutoff grows as we descend under binders
-- dbvar n if n >= cutoff bump by d else leave alone
-- dbfree unchanged
-- dbapp recurses on both with same d and cutoff
-- dbabs recurses on body with cutoff + 1 because we just passed a binder
shift :: Int -> Int -> DeBruijn -> DeBruijn
shift d cutoff (DBVar n)
  | n >= cutoff = DBVar (n + d)
  | otherwise = DBVar n
shift _ _ (DBFree x) = DBFree x
shift d cutoff (DBApp e1 e2) = DBApp (shift d cutoff e1) (shift d cutoff e2)
shift d cutoff (DBAbs x e) = DBAbs x (shift d (cutoff + 1) e)

-- replace index target with val inside e
-- dbvar n if n equals target return val
--        if n is bigger drop by 1 because a binder is being removed
--        otherwise leave it
-- dbfree unchanged
-- dbapp recurses on both with same target and val
-- dbabs under a new binder target grows by 1
--      and val must be shifted by 1 from cutoff 0
--      so its free indices still point to the same outer binders
subst :: Int -> DeBruijn -> DeBruijn -> DeBruijn
subst target val (DBVar n)
  | n == target = val
  | n > target = DBVar (n - 1)
  | otherwise = DBVar n
subst _ _ (DBFree x) = DBFree x
subst target val (DBApp e1 e2) = DBApp (subst target val e1) (subst target val e2)
subst target val (DBAbs x e) = DBAbs x (subst (target + 1) val e)

-- 4.4.
-- one beta step is substitute val for index 0
-- point free reduce = subst 0
reduce :: DeBruijn -> DeBruijn -> DeBruijn
reduce = subst 0

-- 4.5.
-- leftmost outermost
-- first clause dbapp of dbabs fires reduce arg body right away
-- next clause any dbapp if left not NF recurse left else recurse right
-- dbabs recurses into body
-- anything else returns itself
normalStep :: DeBruijn -> DeBruijn
normalStep (DBApp (DBAbs _ body) arg) = reduce arg body
normalStep (DBApp e1 e2)
  | not (isNormalForm e1) = DBApp (normalStep e1) e2
  | otherwise = DBApp e1 (normalStep e2)
normalStep (DBAbs x e) = DBAbs x (normalStep e)
normalStep e = e

-- 4.6.
-- leftmost innermost
-- on dbapp e1 e2 three guards
--   if e1 not nf recurse e1
--   else if e2 not nf recurse e2
--   else case on e1 if dbabs fire reduce e2 body else rebuild
-- dbabs recurses into body
-- anything else returns itself
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
-- if e is in nf return e
-- else cons e onto simplify step - step e
simplify :: (DeBruijn -> DeBruijn) -> DeBruijn -> [DeBruijn]
simplify step e
  | isNormalForm e = [e]
  | otherwise = e : simplify step (step e)

normal :: DeBruijn -> [DeBruijn]
normal = simplify normalStep

applicative :: DeBruijn -> [DeBruijn]
applicative = simplify applicativeStep
