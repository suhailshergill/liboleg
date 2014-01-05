-- | Simply-typed Church-style (nominal) lambda-calculus
-- with integers and zero-comparison
-- Type reconstruction, for all subterms
--
-- <http://okmij.org/ftp/Computation/Computation.html#teval>
--

module Language.TEval.TEvalNR where

import qualified Data.Map as M

data Typ = TInt | !Typ :> !Typ deriving (Show, Eq)
infixr 9 :>

data Term = V VarName
          | L VarName Typ Term
          | A Term Term
          | I Int
          | Term :+ Term                -- addition
          | IFZ Term Term Term          -- if zero
          | Fix Term                    -- fix f, where f :: (a->b)->(a->b)
            deriving (Show, Eq)

infixl 9 `A`
type VarName = String

-- | Type Environment: associating types with `free' variables
type TEnv = [(VarName, Typ)]

env0 :: TEnv
env0 = []

lkup :: TEnv -> VarName -> Typ
lkup env x = maybe err id $ lookup x env 
 where err = error $ "Unbound variable " ++ x

ext :: TEnv -> (VarName,Typ) -> TEnv
ext env xt = xt : env

-- | A virtual typed AST: associating a type to each subterm
type TermIndex = [Int]                  -- an index of a subterm in a term
type Typs = M.Map TermIndex Typ
topterm :: Typ -> Typs
topterm = M.singleton []
toptyp :: Typs -> Typ
toptyp ts = (M.!) ts []
shift :: Int -> Typs -> Typs
shift n = M.mapKeys (n:) 

-- | Type reconstruction: abstract evaluation
teval :: TEnv -> Term -> Typs
teval env (V x) = topterm $ lkup env x
teval env (L x t e) = 
    let ts = teval (ext env (x,t)) e
    in topterm (t :> toptyp ts) `M.union` shift 0 ts
teval env (A e1 e2) = 
    let t1 = teval env e1
        t2 = teval env e2
    in case toptyp t1 of
       t1a :> t1r | t1a == toptyp t2 -> 
                   topterm t1r `M.union` shift 0 t1 `M.union` shift 1 t2
       t1a :> t1r -> error $ unwords ["Applying a function of arg type",
                                      show t1a, "to argument of type",
                                      show $ toptyp t2]
       t1 -> error $ "Trying to apply a non-function: " ++ show t1

teval env (I n) = topterm TInt
teval env (e1 :+ e2) =
    let t1 = teval env e1
        t2 = teval env e2
    in case (toptyp t1,toptyp t2) of
       (TInt, TInt) -> 
           topterm TInt `M.union` shift 0 t1 `M.union` shift 1 t2
       ts     -> error $ "Trying to add non-integers: " ++ show ts
teval env (IFZ e1 e2 e3) =
    let t1 = teval env e1
        t2 = teval env e2
        t3 = teval env e3
        tr  = shift 0 t1 `M.union` shift 1 t2 `M.union` shift 2 t3
    in case toptyp t1 of
       TInt | toptyp t2 == toptyp t3 -> topterm (toptyp t2) `M.union` tr
       TInt -> error $ unwords ["Branches of IFZ have different types:",
                                show (toptyp t2), "and", show (toptyp t3)]
       t    -> error $ "Trying to compare a non-integer to 0: " ++ show t

teval env (Fix e) =
    let t = teval env e
    in case toptyp t of
       ((ta1 :> tb1) :> (ta2 :> tb2)) | ta1 == ta2 && tb1 == tb2 
           -> topterm (ta1 :> tb1) `M.union` shift 0 t
       t -> error $ "Inappropriate type in Fix: " ++ show t

(vx,vy) = (V "x",V "y")

term1 = L "x" TInt (IFZ vx (I 1) (vx :+ (I 2)))

test1 = teval env0 term1 -- TInt :> TInt

term2a = L "x" TInt (L "y" TInt (vx `A` vy))
test2a = teval env0 term2a

term2b = L "x" (TInt :> TInt) (L "y" TInt (vx `A` vy))
test2b = teval env0 term2b -- (TInt :> TInt) :> (TInt :> TInt)

-- can we write term2c with a different assignment of types to x and y?

-- Used to be hidden problem. The main benefit of types: static approximation
-- of program behavior
term3 = L "x" TInt (IFZ vx (I 1) vy)
test3 = teval env0 term3

term4a = L "x" TInt (IFZ vx (I 1) (vx `A` (I 1)))
test4a = teval env0 term4a

term4b = L "x" (TInt :> TInt) (IFZ vx (I 1) (vx `A` (I 1)))
test4b = teval env0 term4b


tmul1 = L "x" TInt (L "y" TInt
          (IFZ vx (I 0)
            ((tmul1 `A` (vx :+ (I (-1))) `A` vy) :+ vy)))

testm1 = teval env0 tmul1 -- is typechecking really decidable?

-- Can termY be typechecked?
delta = L "y" (TInt :> TInt) (vy `A` vy)
testd = teval env0 delta 

tmul = Fix (L "self" (TInt :> TInt :> TInt) (L "x" TInt (L "y" TInt
          (IFZ vx (I 0)
            (((V "self") `A` (vx :+ (I (-1))) `A` vy) :+ vy)))))

testm21 = teval env0 tmul                       -- TInt :> (TInt :> TInt)
testm22 = teval env0 (tmul `A` (I 2))           -- TInt :> TInt
testm23 = teval env0 (tmul `A` (I 2) `A` (I 3)) -- TInt 
