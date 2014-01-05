{-# LANGUAGE PatternGuards #-}
-- | Simply-typed Curry-style (nominal) lambda-calculus
-- with integers and zero-comparison
-- Let-polymorphism via type schemes
-- Type inference
--
-- <http://okmij.org/ftp/Computation/Computation.html#teval>
--

module Language.TEval.TInfLetP where

import Data.List (nub)
import qualified Data.IntMap as M
import Control.Monad.State.Strict               -- why needed strict?
-- import Control.Monad.State.Lazy              -- if enable this, run test62

data Typ = TInt | !Typ :> !Typ | TV TVarName deriving (Show, Eq)
infixr 9 :>
type TVarName = Int

data TypS = TypS [TVarName] Typ         -- A type scheme, with n quantified
   deriving Show                        -- type variables (n >= 0)

data Term = V VarName
          | L VarName Term
          | A Term Term
          | I Int
          | Term :+ Term                -- addition
          | IFZ Term Term Term          -- if zero
          | Fix Term                    -- fix f, where f :: (a->b)->(a->b)
          | Let (VarName,Term) Term
            deriving (Show, Eq)

infixl 9 `A`
type VarName = String

-- | Type Environment: associating *would-be* types with `free' term variables
type TEnv = [(VarName, TypS)]

env0 :: TEnv
env0 = []

lkup :: TEnv -> VarName -> TypS
lkup env x = maybe err id $ lookup x env 
 where err = error $ "Unbound variable " ++ x

ext :: TEnv -> (VarName,TypS) -> TEnv
ext env xt = xt : env

-- | Type Variable Environment: associating types with `free' type variables
data TVE = TVE Int (M.IntMap Typ) deriving Show

-- | TVE is the state of a monadic computation
type TVEM = State TVE

-- | Allocate a fresh type variable (see the first component of TVE)
newtv :: TVEM Typ
newtv = do
 TVE n s <- get
 put (TVE (succ n) s)
 return (TV n)

tve0 :: TVE
tve0 = TVE 0 M.empty

tvlkup :: TVE -> TVarName -> Maybe Typ
tvlkup (TVE _ s) v = M.lookup v s

tvext :: TVE -> (TVarName,Typ) -> TVE
tvext (TVE c s) (tv,t) = TVE c $ M.insert tv t s

-- | TVE domain predicate: check to see if a TVarName is in the domain of TVE
tvdomainp :: TVE -> TVarName -> Bool
tvdomainp (TVE _ s) v = M.member v s

-- | Give the list of all type variables that are allocated in TVE but
-- not bound there
tvfree :: TVE -> [TVarName]
tvfree (TVE c s) = filter (\v -> not (M.member v s)) [0..c-1]

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

-- | Compute (quite unoptimally) the characteristic function of the set 
--  forall tvb \in fv(tve_before). Union fv(tvsub(tve_after,tvb))
tvdependentset :: TVE -> TVE -> (TVarName -> Bool)
tvdependentset tve_before tve_after = 
    \tv -> any (\tvb -> occurs tv (TV tvb) tve_after) tvbs
 where
 tvbs = tvfree tve_before
 

-- | Monadic version of unify
unifyM :: Typ -> Typ -> (String -> String) -> TVEM ()
unifyM t1 t2 errf = do
  tve <- get
  case unify t1 t2 tve of 
       Right tve -> put tve
       Left  err -> fail (errf err)

-- | Given a type scheme, that is, the type t and the list of type variables tvs,
-- for every tvs, replace all of its occurrences in t with a fresh
-- type variable.
-- We do that by creating a substitution tve and applying it to t.
instantiate :: TypS -> TVEM Typ
instantiate (TypS tvs t) = do
  tve <- associate_with_freshvars tvs
  return $ tvsub tve t
 where
 associate_with_freshvars [] = return tve0
 associate_with_freshvars (tv:tvs) = do
   tve     <- associate_with_freshvars tvs
   tvfresh <- newtv
   return $ tvext tve (tv,tvfresh)

-- | Given a typechecking action ta yielding the type t, return the type
-- scheme quantifying over _truly free_ type variables in t
-- with respect to TVE that existed before the typechecking action began.
-- Let tve_before is TVE before the type checking action is executed, 
-- and tve_after is TVE after the action. A type variable tv
-- is truly free if it is free in tve_after and remains free if the 
-- typechecking action were executed in any tve extending tve_before
-- with arbitrary binding to type variables free in tve_before.
-- To be more precise, a type variable tv is truly free with respect
-- to tve_before if:
--    tv \not\in domain(tve_after)
--    forall tvb \in fv(tve_before). tv \not\in fv(tvsub(tve_after,tvb))
-- In other words, tv is truly free if it is free and `independent' of
-- tve_before.
--
-- Our goal is to reproduce the behavior in TInfLetI.hs:
-- generalize/instantiate should mimic multiple executions of
-- the typechecking action. That means we should quantify over all
-- type variables created by ta that are independent of the type environment
-- in which the action may be executed.

generalize :: TVEM Typ -> TVEM TypS
generalize ta = do
 tve_before <- get      -- type env before ta is executed
 t          <- ta
 tve_after  <- get      -- type env after ta is executed
 let t' = tvsub tve_after t
 let tvdep = tvdependentset tve_before tve_after
 let fv = filter (not . tvdep) (nub (freevars t'))
 return $ TypS fv t'

-- | Return the list of type variables in t (possibly with duplicates)
freevars :: Typ -> [TVarName]
freevars TInt       = []
freevars (t1 :> t2) = freevars t1 ++ freevars t2
freevars (TV v)     = [v]


-- | Type reconstruction: abstract evaluation
teval' :: TEnv -> Term -> TVEM Typ
teval' env (V x)   = instantiate (lkup env x)
teval' env (L x e) = do
    tv <- newtv
    te <- teval' (ext env (x,TypS [] tv)) e -- extend with the monomorphic type
    return $ tv :> te
teval' env (A e1 e2) = do
    t1  <- teval' env e1
    t2  <- teval' env e2
    t1r <- newtv
    unifyM t1 (t2 :> t1r) id
    return t1r

teval' env (I n) = return TInt
teval' env (e1 :+ e2) = do
    t1 <- teval' env e1
    t2 <- teval' env e2
    unifyM t1 TInt ("Trying to add non-integers: " ++)
    unifyM t2 TInt ("Trying to add non-integers: " ++)
    return TInt
teval' env (IFZ e1 e2 e3) = do
    t1 <- teval' env e1
    t2 <- teval' env e2
    t3 <- teval' env e3
    unifyM t1 TInt ("Trying to compare a non-integer to 0: " ++)
    unifyM t2 t3 (\err  -> unwords ["Branches of IFZ have different",
                                    "types. Unification failed:",err])
    return t2

teval' env (Fix e) = do
    t  <- teval' env e
    ta <- newtv
    tb <- newtv
    unifyM t ((ta :> tb) :> (ta :> tb))
           ("Inappropriate type in Fix: " ++)
    return $ ta :> tb

teval' env (Let (x,e) eb) = do
    t  <- generalize $ teval' env e     -- This is new, cf TInfLetI.hs
    teval' (ext env (x,t)) eb


-- | Resolve all type variables, as far as possible, and generalize
-- We assume teval will be used for top-level expressions where generalization
-- is appropriate.
teval :: TEnv -> Term -> TypS
teval tenv e = let (ts,tve) = runState (generalize $ teval' tenv e) tve0 in ts

-- | non-generalizing teval (as before)
tevalng :: TEnv -> Term -> Typ
tevalng tenv e = let (t,tve) = runState (teval' tenv e) tve0 in tvsub tve t

-- Tests
(vx,vy) = (V "x",V "y")

test0 = runState (teval' env0 ((L "x" (vx :+ (I 2))) `A` (I 1))) tve0
-- (TV 1,TVE 2 (fromList [(0,TInt),(1,TInt)]))

term1 = L "x" (IFZ vx (I 1) (vx :+ (I 2)))
test10 = runState (teval' env0 term1) tve0
-- (TV 0 :> TInt,TVE 1 (fromList [(0,TInt)]))

-- need a better presentation of the final result: cf. teval' and teval

test1 = teval env0 term1 -- TypS [] (TInt :> TInt)

termid = L "x" vx
testid = teval env0 termid -- TypS [0] (TV 0 :> TV 0), i.e., forall a. a->a

term2a = L "x" (L "y" (vx `A` vy))
test2a = teval env0 term2a
-- TypS [2,1] ((TV 1 :> TV 2) :> (TV 1 :> TV 2))

-- Used to be a hidden problem. The main benefit of types: static approximation
-- of program behavior
term3 = L "x" (IFZ vx (I 1) vy)
test3 = teval env0 term3

term4 = L "x" (IFZ vx (I 1) (vx `A` (I 1)))
test4 = teval env0 term4
-- compare the error message with that of test4a and test4b in TEvalNC.hs

term6  = (L "x" (I 1)) `A` vy
test61 = teval env0 term6

test62 = teval env0 $ (I 1) :+ vx       -- If the state is Lazy: problem


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

testm21' = runState (teval' env0 tmul) tve0
-- (TV 5 :> TV 6,TVE 7 (fromList 
--     [(0,TInt :> TV 3),(1,TInt),(2,TInt),(3,TV 2 :> TV 4),
--      (4,TInt),(5,TInt),(6,TV 2 :> TV 4)]))

testm21 = teval env0 tmul                  -- TypS [] (TInt :> (TInt :> TInt))
testm22 = teval env0 (tmul `A` (I 2))           -- TypS [] (TInt :> TInt)
testm23 = teval env0 (tmul `A` (I 2) `A` (I 3)) -- TypS [] TInt


-- Tests of let

testl1 = teval env0 $ Let ("x",vx) vx            -- error
testl2 = teval env0 $ Let ("x",vy) (I 1)         -- error
testl3 = teval env0 $ Let ("x",(I 1)) (vx :+ vx) -- TypS [] TInt

-- these are essentially tests of hygiene
testl40 = runState (teval' env0 (L "x" (Let ("x",vx `A` (I 1)) (vx :+ (I 2)))))
                   tve0
testl4  = teval env0 $ L "x" (Let ("x",vx `A` (I 1)) (vx :+ (I 2)))
-- TypS [] ((TInt :> TInt) :> TInt)
testl42 = teval env0 $ (L "x" (Let ("x",vx `A` (I 1)) (vx :+ (I 2))))
                      `A` termid
testl43 = teval env0 $ (L "x" (Let ("x",vx `A` (I 1)) (vx :+ (I 2))))
                      `A` term2a
-- type error

testl5  = teval env0 $ L "x" (Let ("y",vx `A` (I 1)) (L "x" (vy :+ vx)))
-- TypS [] ((TInt :> TInt) :> (TInt :> TInt))

terml51 = L "x" (Let ("y",L"f" ((V "f") `A` vx)) vy)
testl51  = teval env0 terml51 -- TypS [3,0] (TV 0 :> ((TV 0 :> TV 3) :> TV 3))
terml52 = terml51 `A` (I 10)
testl52  = teval env0 terml52 -- TypS [3] ((TInt :> TV 3) :> TV 3)

-- lambda vs. let-bound variables
testl61 = teval env0 $ L "x" (Let ("y",vx `A` (I 1))
                               (Let ("z",vy :+ (I 2)) vy))
-- TypS [] ((TInt :> TInt) :> TInt)
testl62 = teval env0 $ L "x" (Let ("y",vx `A` (I 1))
                               (Let ("z",vy :+ (I 2)) vx))
-- TypS [] ((TInt :> TInt) :> (TInt :> TInt))
testl63 = teval env0 $ L "x" (Let ("y",vx `A` (I 1))
                               (Let ("z",(I 2)) vx))
-- TypS [1] ((TInt :> TV 1) :> (TInt :> TV 1))

-- Tests from Cardelli, Basic Polymorphic Type Checking, Ex3
testl66 = teval env0 $ L "x" (Let ("y",vx) 
                              (Let ("z",(vy `A` (I 1) :+ (I 2))) vy))
-- TypS [] ((TInt :> TInt) :> (TInt :> TInt)), monomorphic
testl67 = teval env0 $ L "x" (Let ("y",vx) ((vy `A` (I 1)) :+
                                            (vy `A` (L "x" vx))))
-- *** Exception: constant mismatch: TInt and TV 2 :> TV 2


-- more intricate tests
testl69 = teval env0 (L "f" $
                           Let ("g", L "x" $ Let ("y", A (V "f") (V "x"))
                                                 (V "x"))
                               (V "g"))
-- TypS [1,2] ((TV 1 :> TV 2) :> (TV 1 :> TV 1))

testl6a = teval env0 (L "f" $
                           Let ("g", L "x" $ Let ("y", A (V "f") (V "x"))
                                                 (V "x"))
                               (A (V "g") (V "g")))
-- *** Exception: occurs check: TV 1 in TV 1 :> TV 1


testl71 = teval env0 $ Let ("x",term2a) vx
-- TypS [4,3] ((TV 3 :> TV 4) :> (TV 3 :> TV 4))

testl72 = teval env0 $ Let ("x",term2a) (Let ("y",vx `A` termid)
                               (Let ("z",vy `A` (I 2)) vx))
-- TypS [10,9] ((TV 9 :> TV 10) :> (TV 9 :> TV 10))

testl73 = teval env0 $ Let ("x",term2a) (Let ("y",vx `A` termid)
                               (Let ("z",vy `A` (I 2)) vy))
-- TypS [9] (TV 9 :> TV 9)
testl74 = teval env0 $ Let ("x",term2a) 
                        (Let ("y",(Let ("z",vx `A` tmul) (vx `A` termid)))
                         vy)
-- TypS [17] (TV 17 :> TV 17)
testl75 = teval env0 $ Let ("x",term2a) 
                        (Let ("y",(Let ("z",(vx `A` termid)) (V "z")))
                         vy)
-- TypS [8] (TV 8 :> TV 8)

testl76 = teval env0 $ Let ("x",(L "y" (I 10))) 
                           (Let ("y",vx)
                            (Let ("z",(vy `A` (I 1) :+ (I 2))) vy))
-- TypS [4] (TV 4 :> TInt), polymorhic
testl77 = teval env0 $ Let ("x",(L "y" (I 10)))
                           (Let ("y",vx) ((vy `A` (I 1)) :+
                                          (vy `A` (L "x" vx))))
-- TypS [] TInt, OK.

-- compared to the corresponding tests in TInfT.hs, we are using
-- the object-level Let
term2id = Let ("id",L "x" vx) (
          L "f" (L "y" 
               ((I 2) :+
                ((V "id" `A` (V "f")) `A` ((V "id" `A` vy) :+ (I 1))))))
test2id = teval env0 term2id
-- TypS [] ((TInt :> TInt) :> (TInt :> TInt))

termlet = Let ("c2", L "f" (L "x" (V "f" `A` (V "f" `A` vx)))) (
          Let ("inc", L "x" (vx :+ (I 1))) (
          Let ("compose", L "f" (L "g" (L "x" (V "f" `A` (V "g" `A` vx))))) (
          Let ("id",L "x" vx) (
          V "c2" `A` (V "compose" `A` V "inc" `A` V "inc") `A` (I 10) :+
          (V "c2" `A` (V "compose" `A` V "inc") `A` V "id" `A` (I 100))
          ))))
testlet = teval env0 termlet -- TypS [] TInt

