-- |
-- Untyped (nominal) lambda-calculus with integers and the conditional
--
-- <http://okmij.org/ftp/Computation/Computation.html#teval>
--
--
--    [The Abstract of the lecture notes]
--    We expound a view of type checking as evaluation with `abstract values'. Whereas dynamic
--     semantics, evaluation, deals with (dynamic) values like 0, 1, etc., static semantics, type
--     checking, deals with approximations like int. A type system is sound if it correctly approximates
--     the dynamic behavior and predicts its outcome: if the static semantics predicts that a term has
--     the type int, the dynamic evaluation of the term, if it terminates, will yield an integer.
-- 
--     As object language, we use simply-typed and let-polymorphic lambda calculi with integers and
--     integer operations as constants. We use Haskell as a metalanguage in which to write evaluators,
--     type checkers, type reconstructors and inferencers for the object language.
-- 
--     We explore the deep relation between parametric polymorphism and `inlining'. Polymorphic type
--     checking then is an optimization allowing us to type check a polymorphic term at the place of its
--     definition rather than at the places of its use.
-- 
--     Joint work with Chung-chieh Shan.
-- 
-- Version
--     The current version is 1.1, July 2008.
-- References
--     lecture.pdf [199K]
-- 

module Language.TEval.EvalN where

data Term = V VarName
          | L VarName Term
          | A Term Term
          | I Int
          | Term :+ Term                -- addition
          | IFZ Term Term Term          -- if zero
            deriving (Show, Eq)

infixl 9 `A`
type VarName = String

-- | Environment: associating values with `free' variables
type Env = [(VarName, Value)]

env0 :: Env
env0 = []

lkup :: Env -> VarName -> Value
lkup env x = maybe err id $ lookup x env 
 where err = error $ "Unbound variable " ++ x

ext :: Env -> (VarName,Value) -> Env
ext env xt = xt : env

data Value = VI Int | VC (Value -> Value)
instance Show Value where
    show (VI n) = "VI " ++ show n
    show (VC _) = "<function>"

-- | Denotational semantics. Why? How to make it operational?
eval :: Env -> Term -> Value
eval env (V x)   = lkup env x
eval env (L x e) = VC (\v -> eval (ext env (x,v)) e)
eval env (A e1 e2) = 
    let v1 = eval env e1
        v2 = eval env e2
    in case v1 of
       VC f  -> f v2
       v     -> error $ "Trying to apply a non-function: " ++ show v

eval env (I n) = VI n                   -- already a value
eval env (e1 :+ e2) =
    let v1 = eval env e1
        v2 = eval env e2
    in case (v1,v2) of
       (VI n1, VI n2) -> VI (n1+n2)
       vs     -> error $ "Trying to add non-integers: " ++ show vs
eval env (IFZ e1 e2 e3) =
    let v1 = eval env e1
    in case v1 of
       VI 0 -> eval env e2
       VI _ -> eval env e3
       v    -> error $ "Trying to compare a non-integer to 0: " ++ show v

(vx,vy) = (V "x",V "y")

term1 = L "x" (IFZ vx (I 1) (vx :+ (I 2)))

test11 = eval env0 term1
test12 = eval env0 (term1 `A` (I 2))    -- VI 4
test13 = eval env0 (term1 `A` (I 0))    -- VI 1
test14 = eval env0 (term1 `A` vx)       -- Exception: Unbound variable x

term2 = L "x" (L "y" (vx :+ vy))

test21 = eval env0 term2
test22 = eval env0 (term2 `A` (I 1))
test23 = eval env0 (term2 `A` (I 1) `A` (I 2)) -- VI 3

-- | Hidden problems
term3 = L "x" (IFZ vx (I 1) vy)

test31 = eval env0 term3
test32 = eval env0 (term3 `A` (I 0))    -- VI 1
test33 = eval env0 (term3 `A` (I 1))    -- Exception: Unbound variable y

term4 = L "x" (IFZ vx (I 1) (vx `A` (I 1)))
test41 = eval env0 term4
test42 = eval env0 (term4 `A` (I 0))    -- VI 1
test43 = eval env0 (term4 `A` (I 1))    -- applying a non-function


term6  = (L "x" (I 1)) `A` vy
test61 = eval env0 term6                -- regarding CBN vs CBV...


-- (x+1)*y = x*y + y

-- | why is this cheating? Try showing the term
tmul1 = L "x" (L "y" 
          (IFZ vx (I 0)
            ((tmul1 `A` (vx :+ (I (-1))) `A` vy) :+ vy)))

testm1 = eval env0 (tmul1 `A` (I 2) `A` (I 3))

-- | termY f === f (termY f)
-- or: termY f x === f (termY f) x

termY = L "f" (delta `A` (L "y" (L "x" (vf `A` (delta `A` vy) `A` vx))))
 where delta = L "y" (vy `A` vy)
       vf = V "f"

tmul = termY `A` (L "self" (L "x" (L "y" 
          (IFZ vx (I 0)
            (((V "self") `A` (vx :+ (I (-1))) `A` vy) :+ vy)))))

testm2 = eval env0 (tmul `A` (I 2) `A` (I 3)) -- VI 6

-- | The following is the implementation of a few exercises. Don't show them

termfib = termY `A` (L "self" (L "n"
     (IFZ vn (I 1)
       (IFZ (pred vn) (I 1)
        ((self `A` (pred vn)) :+ (self `A` (pred (pred vn))))))))
 where (vn,self) = (V "n", V "self")
       pred x = x :+ (I (-1))           -- This is an _abbreviation_

testfib = map (\n -> eval env0 (termfib `A` (I n))) [0..7]
-- [VI 1,VI 1,VI 2,VI 3,VI 5,VI 8,VI 13,VI 21]
