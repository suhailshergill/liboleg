{-# LANGUAGE PatternGuards #-}
-- | Simply-typed Curry-style (nominal) lambda-calculus
-- with integers and zero-comparison
-- Type inference
--
-- <http://okmij.org/ftp/Computation/Computation.html#teval>
--

module Language.TEval.TInfT where

import qualified Data.IntMap as M

data Typ = TInt | !Typ :> !Typ | TV TVarName deriving (Show, Eq)
infixr 9 :>
type TVarName = Int

data Term = V VarName
          | L VarName Term
          | A Term Term
          | I Int
          | Term :+ Term                -- addition
          | IFZ Term Term Term          -- if zero
          | Fix Term                    -- fix f, where f :: (a->b)->(a->b)
            deriving (Show, Eq)

infixl 9 `A`
type VarName = String

-- | Type Environment: associating types with `free' term variables
type TEnv = [(VarName, Typ)]

env0 :: TEnv
env0 = []

lkup :: TEnv -> VarName -> Typ
lkup env x = maybe err id $ lookup x env 
 where err = error $ "Unbound variable " ++ x

ext :: TEnv -> (VarName,Typ) -> TEnv
ext env xt = xt : env

--  |Type Variable Environment: associating types with `free' type variables
data TVE = TVE Int (M.IntMap Typ) deriving Show

--  |Allocate a fresh type variable (see the first component of TVE)
newtv :: TVE -> (Typ,TVE)
newtv (TVE n s) = (TV n,TVE (succ n) s)

tve0 :: TVE
tve0 = TVE 0 M.empty

tvlkup :: TVE -> TVarName -> Maybe Typ
tvlkup (TVE _ s) v = M.lookup v s

tvext :: TVE -> (TVarName,Typ) -> TVE
tvext (TVE c s) (tv,t) = TVE c $ M.insert tv t s

-- | Type variables are logic variables: hypothetical reasoning
tvsub :: TVE -> Typ -> Typ
tvsub tve (t1 :> t2) = tvsub tve t1 :> tvsub tve t2
tvsub tve (TV v) | Just t <- tvlkup tve v = tvsub tve t
tvsub tve t = t

-- | `shallow' substitution; check if tv is bound to anything `substantial'
tvchase :: TVE -> Typ -> Typ
tvchase tve (TV v) | Just t <- tvlkup tve v = tvchase tve t
tvchase _ t = t

-- | The unification. If unification failed, return the reason
unify :: Typ -> Typ -> TVE -> Either String TVE
unify t1 t2 tve = unify' (tvchase tve t1) (tvchase tve t2) tve

-- | If either t1 or t2 are type variables, they are definitely unbound
unify' :: Typ -> Typ -> TVE -> Either String TVE
unify' TInt TInt = Right
unify' (t1a :> t1r) (t2a :> t2r) = either Left (unify t1r t2r) . unify t1a t2a
unify' (TV v1) t2 = unifyv v1 t2
unify' t1 (TV v2) = unifyv v2 t1
unify' t1 t2 = const (Left $ unwords ["constant mismatch:",show t1,"and",
                                      show t2])

-- | Unify a free variable v1 with t2
unifyv :: TVarName -> Typ -> TVE -> Either String TVE
unifyv v1 (TV v2) tve =
    if v1 == v2 then Right tve
       else Right (tvext tve (v1,TV v2)) -- record new constraint
unifyv v1 t2 tve = if occurs v1 t2 tve
                      then Left $ unwords ["occurs check:",show (TV v1),
                                           "in",show $ tvsub tve t2]
                      else Right (tvext tve (v1,t2))

-- | The occurs check: if v appears free in t
occurs :: TVarName -> Typ -> TVE -> Bool
occurs v TInt _ = False
occurs v (t1 :> t2) tve = occurs v t1 tve || occurs v t2 tve
occurs v (TV v2) tve =
    case tvlkup tve v2 of
         Nothing -> v == v2
         Just t  -> occurs v t tve


-- | Type reconstruction: abstract evaluation
teval' :: TEnv -> Term -> (TVE -> (Typ,TVE))
teval' env (V x)   = \tve0 -> (lkup env x,tve0)
teval' env (L x e) = \tve0 ->
    let (tv,tve1) = newtv tve0
        (te,tve2) = teval' (ext env (x,tv)) e tve1
    in (tv :> te,tve2)
teval' env (A e1 e2) = \tve0 ->
    let (t1,tve1) = teval' env e1 tve0
        (t2,tve2) = teval' env e2 tve1
        (t1r,tve3)= newtv tve2
    in case unify t1 (t2 :> t1r) tve3 of
       Right tve -> (t1r,tve)
       Left err  -> error $ err

teval' env (I n) = \tve0 -> (TInt,tve0)
teval' env (e1 :+ e2) = \tve0 ->
    let (t1,tve1) = teval' env e1 tve0
        (t2,tve2) = teval' env e2 tve1
    in case either Left (unify t2 TInt) . unify t1 TInt $ tve2 of
       Right tve -> (TInt,tve)
       Left err  -> error $ "Trying to add non-integers: " ++ err
teval' env (IFZ e1 e2 e3) = \tve0 ->
    let (t1,tve1) = teval' env e1 tve0
        (t2,tve2) = teval' env e2 tve1
        (t3,tve3) = teval' env e3 tve2
    in case unify t1 TInt tve3 of
       Right tve -> case unify t2 t3 tve of
        Right tve -> (t2,tve)    
        Left err  -> error $ unwords ["Branches of IFZ have",
                                      "different types.",
                                      "Unification failed:", err]
       Left err -> error $ "Trying to compare a non-integer to 0: " ++ err

teval' env (Fix e) = \tve0 ->
    let (t,tve1)  = teval' env e tve0
        (ta,tve2) = newtv tve1
        (tb,tve3) = newtv tve2
    in case unify t ((ta :> tb) :> (ta :> tb)) tve3 of
       Right tve -> (ta :> tb,tve)
       Left err  -> error $ "Inappropriate type in Fix: "++err

-- | Resolve all type variables, as far as possible
teval :: TEnv -> Term -> Typ
teval tenv e = let (t,tve) = teval' tenv e tve0 in tvsub tve t

-- Tests
(vx,vy) = (V "x",V "y")

test0 = teval' env0 ((L "x" (vx :+ (I 2))) `A` (I 1)) tve0
-- (TV 1,TVE 2 (fromList [(0,TInt),(1,TInt)]))

term1 = L "x" (IFZ vx (I 1) (vx :+ (I 2)))
test10 = teval' env0 term1 tve0
-- (TV 0 :> TInt,TVE 1 (fromList [(0,TInt)]))

-- need a better presentation of the final result: cf. teval' and teval

test1 = teval env0 term1 -- TInt :> TInt

termid = L "x" vx
testid = teval env0 termid -- TV 0 :> TV 0

term2a = L "x" (L "y" (vx `A` vy))
test2a = teval env0 term2a
-- (TV 1 :> TV 2) :> (TV 1 :> TV 2)

-- Used to be hidden problem. The main benefit of types: static approximation
-- of program behavior
term3 = L "x" (IFZ vx (I 1) vy)
test3 = teval env0 term3

term4 = L "x" (IFZ vx (I 1) (vx `A` (I 1)))
test4 = teval env0 term4
-- compare the error message with that of test4a and test4b in TEvalNC.hs

term6  = (L "x" (I 1)) `A` vy
test61 = teval env0 term6
test62 = teval env0 $ (I 1) :+ vx


tmul1 = L "x" (L "y"
          (IFZ vx (I 0)
            ((tmul1 `A` (vx :+ (I (-1))) `A` vy) :+ vy)))

testm1 = teval env0 tmul1 -- is typechecking really decidable?

-- Can termY be typechecked?
delta = L "y" (vy `A` vy)
testd = teval env0 delta 

tmul = Fix (L "self" (L "x" (L "y"
          (IFZ vx (I 0)
            (((V "self") `A` (vx :+ (I (-1))) `A` vy) :+ vy)))))

testm21' = teval' env0 tmul tve0
-- (TV 5 :> TV 6,TVE 7 (fromList 
--     [(0,TInt :> TV 3),(1,TInt),(2,TInt),(3,TV 2 :> TV 4),
--      (4,TInt),(5,TInt),(6,TV 2 :> TV 4)]))

testm21 = teval env0 tmul                       -- TInt :> (TInt :> TInt)
testm22 = teval env0 (tmul `A` (I 2))           -- TInt :> TInt
testm23 = teval env0 (tmul `A` (I 2) `A` (I 3)) -- TInt
testm24 = teval env0 (tmul `A` (I (-1)) `A` (I (-1))) -- TInt

-- using the metalanguage definition of termid: `top-level let'
term2id = L "f" (L "y" 
               ((I 2) :+
                ((termid `A` (V "f")) `A` ((termid `A` vy) :+ (I 1)))))
test2id = teval env0 term2id -- (TInt :> TInt) :> (TInt :> TInt)

-- using the metalanguage let
termlet = let c2  = L "f" (L "x" (V "f" `A` (V "f" `A` vx)))
              inc = L "x" (vx :+ (I 1))
              compose = L "f" (L "g" (L "x" (V "f" `A` (V "g" `A` vx))))
          in c2 `A` (compose `A` inc `A` inc) `A` (I 10) :+
             (c2 `A` (compose `A` inc) `A` termid `A` (I 100))
testlet = teval env0 termlet

