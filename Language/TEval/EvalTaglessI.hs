{-# LANGUAGE GADTs #-}

-- | Tagless Typed lambda-calculus with integers and the conditional
-- in the higher-order abstract syntax.
-- Haskell itself ensures the object terms are well-typed.
-- Here we use GADT: This file is not in Haskell98
--
-- <http://okmij.org/ftp/Computation/Computation.html#teval>
--

module Language.TEval.EvalTaglessI where

data Term t where
  V    :: t -> Term t                   -- used only for denot semantics
  L    :: (Term t1 -> Term t2) -> Term (t1->t2)
  A    :: Term (t1->t2) -> Term t1 -> Term t2
  I    :: Int -> Term Int
  (:+) :: Term Int -> Term Int -> Term Int              -- addition
  IFZ  :: Term Int -> Term t -> Term t -> Term t        -- if zero
  Fix  :: Term ((a->b) -> (a->b)) -> Term (a->b)
  -- Let :: Term t1 -> (Term t1 -> Term t) -> Term t

-- | Since we rely on the metalanguage for typechecking and hence
-- type generalization, we have to use the metalanguage `let'
-- The (V n) term, aka the polymorphic lift, is not used in user terms.
-- This is the `internal' component for the sake of evald only (evalo doesn't
-- need it).
infixl 9 `A`


-- | It is quite challenging to show terms. In fact, we can't do it
-- for lambda-terms at all! The argument of the L constructor is a function.
-- We can't show functions; if we find a term to apply the function to,
-- we obtain a term, which we can show then. The only candidate for the
-- term to pass to the body of L is the V term; but to construct
-- (V x) we need x -- the value of some type (and we don't have an idea
-- of the type). So, the best we can do is (V undefined) -- which, alas,
-- we can't show. The only solution is to modify the definition of Term t, 
-- and make the V constructor thusly: V :: t -> String -> Term t.
-- In that case, we can show V-term values.

instance Show (Term t) where
    show (I n) = "I " ++ show n
    show (L f) = "<function>"
    -- The other terms are not values, so we won't show them at all.
    -- The above two clauses are enough to show the result of the evalo
    -- evaluator.


-- | We no longer need variables or the environment and we do
-- normalization by evaluation.

-- | Denotational semantics. Why?
evald :: Term t -> t
evald (V x) = x
evald (L f) = \x -> evald (f (V x))
evald (A e1 e2) = (evald e1) (evald e2)
evald (I n) = n
evald (e1 :+ e2) = evald e1 + evald e2
evald (IFZ e1 e2 e3) = if evald e1 == 0 then evald e2 else evald e3
evald (Fix e) = fix (evald e) where fix f = f (fix f)


-- | Operational semantics. Why?
-- GADT are still implemented imperfectly: we the default case in case 
-- statements (with cannot happen error), to avoid the warning about
-- inexhaustive pattern match -- although these case-brances can never
-- be executed. Why?

evalo :: Term t -> Term t
evalo e@(L _) = e                       -- already a value
evalo (A e1 e2) = 
    let v1 = evalo e1
        v2 = evalo e2
    in case v1 of
       L f -> evalo (f v2)              -- could just use e2?
       _     -> error "Cannot happen"
evalo e@(I _) = e                       -- already a value
evalo (e1 :+ e2) =
    let v1 = evalo e1
        v2 = evalo e2
    in case (v1,v2) of
       (I n1, I n2) -> I (n1+n2)
       _     -> error "Cannot happen"
evalo (IFZ e1 e2 e3) =
    let v1 = evalo e1
    in case v1 of
       I 0 -> evalo e2
       I _ -> evalo e3
       _    -> error "Cannot happen"
evalo (Fix e) = evalo (e `A` (Fix e))


-- Tests

test0d = evald $ L(\vx -> vx :+ (I 2)) `A` (I 1) -- 3
test0o = evalo $ L(\vx -> vx :+ (I 2)) `A` (I 1) -- I 3

term1 = L (\vx -> IFZ vx (I 1) (vx :+ (I 2)))

test11d = evald term1
test11o = evalo term1                   -- <function>
test12d = evald (term1 `A` (I 2))       -- 4, as Haskell Int
test12o = evalo (term1 `A` (I 2))       -- I 4, but as Term Int
-- test14 = evalo (term1 `A` vx)       -- Type error! Not in scope: `vx'

term2 = L (\vx -> L (\vy -> vx :+ vy))
-- *EvalTaglessI> :t term2
-- term2 :: Term (Int -> Int -> Int)


test21 = evalo term2
test22 = evalo (term2 `A` (I 1))            -- <function>
test23d = evald (term2 `A` (I 1) `A` (I 2)) -- 3
test23o = evalo (term2 `A` (I 1) `A` (I 2)) -- I 3

termid = L(\vx -> vx)
testid = evald termid -- testid :: t1 -> t1

term2a = L (\vx -> L(\vy -> vx `A` vy))
{- The meta-language figured the (polymorphic) type now
 *EvalTaglessI> :t term2a
 term2a :: Term ((t1 -> t2) -> t1 -> t2)
-}

-- No longer hidden problems
-- term3 = L (\vx -> IFZ vx (I 1) vy) -- Not in scope: `vy'

-- The following is a type error, we can't even enter the term
-- term4 = L (\vx -> IFZ vx (I 1) (vx `A` (I 1)))
{- Now we get good error messages!

    Couldn't match expected type `t1 -> Int'
           against inferred type `Int'
      Expected type: Term (t1 -> Int)
      Inferred type: Term Int
    In the first argument of `A', namely `vx'
    In the third argument of `IFZ', namely `(vx `A` (I 1))'
-}


-- term6  = (L "x" (I 1)) `A` vy  -- Not in scope: `vy'


-- (x+1)*y = x*y + y

-- why is this less of a cheating? Try showing the term
-- Now, both type-checking and evaluation of tmul1 works!
tmul1 = L (\vx -> L (\vy ->
          (IFZ vx (I 0)
            ((tmul1 `A` (vx :+ (I (-1))) `A` vy) :+ vy))))

-- tmul1 :: Term (Int -> Int -> Int)

testm1d = evald (tmul1 `A` (I 2) `A` (I 3))  -- 6
testm1o = evalo  (tmul1 `A` (I 2) `A` (I 3)) -- I 6

-- Can termY be typechecked?
-- delta = L (\vy -> vy `A` vy)
{-
    Occurs check: cannot construct the infinite type: t1 = t1 -> t2
      Expected type: Term t1
      Inferred type: Term (t1 -> t2)
    In the second argument of `A', namely `vy'
    In the expression: vy `A` vy
-}

tmul = Fix (L (\self -> L (\vx -> L (\vy ->
          (IFZ vx (I 0)
            ((self `A` (vx :+ (I (-1))) `A` vy) :+ vy))))))

testm21d = evald tmul
testm21o = evalo tmul
testm23d = evald (tmul `A` (I 2) `A` (I 3)) -- 6
testm23o = evalo (tmul `A` (I 2) `A` (I 3)) -- I 6

-- Tests of let (cf. the corresponding tests in TInfLetP.hs)

testl1 = let vx = vx in vx               -- why this works in Haskell?
-- testl2 = let vx = vy in (I 1)            -- type error
testl3 = evald $ let vx = I 1 in vx :+ vx -- 2

-- this is essentially the test of hygiene
testl5  = evald $ L(\vx -> let vy = vx `A` (I 1) in L(\vx -> vy :+ vx))
-- testl5 :: (Int -> Int) -> Int -> Int

-- lambda vs. let-bound variables
testl61 = evald $ L(\vx -> let vy = vx `A` (I 1) in
                           let vz = vy :+ (I 2) in vy)
-- testl61 :: (Int -> Int) -> Int
testl62 = evald $ L(\vx -> let vy = vx `A` (I 1) in
                           let vz = vy :+ (I 2) in vx)
-- testl62 :: (Int -> Int) -> Int -> Int
testl63 = evald $ L(\vx -> let vy = vx `A` (I 1) in
                           let vz = (I 2) in vx)
-- testl63 :: (Int -> t2) -> Int -> t2

-- Tests from Cardelli, Basic Polymorphic Type Checking, Ex3
testl66 = evald $ L(\vx -> let vy = vx in
                           let vz = vy `A` (I 1) :+ (I 2) in vy)
-- testl66 :: (Int -> Int) -> Int -> Int, monomorphic

{-
testl67 = evald $ L(\vx -> let vy = vx 
                           in ((vy `A` (I 1)) :+ (vy `A` L (\vx->vx))))
-}
-- Couldn't match expected type `Int' against inferred type `t1 -> t1'

-- more intricate tests
testl69 = evald $ L(\f -> let g = L(\x -> let vy = A f x in x)
                         in g)
-- testl69 :: (t1 -> t2) -> t1 -> t1

{-
testl6a = evald $ L(\f -> let g = L(\x -> let vy = A f x in x)
                         in A g g)
-- Occurs check: cannot construct the infinite type: t1 = t1 -> t1
-}


testl71 = evald $ let vx = term2a in vx
-- testl71 :: (t1 -> t2) -> t1 -> t2

testl72 = evald $ let vx = term2a in 
                  let vy = vx `A` termid in
                  let vz = vy `A` (I 2) in vx
-- testl72 :: (t1 -> t2) -> t1 -> t2

testl73 = evald $ let vx = term2a in 
                  let vy = vx `A` termid in
                  let vz = vy `A` (I 2) in vy
-- testl73 :: t2 -> t2
testl74 = evald $ let vx = term2a in 
                  let vy = let z = vx `A` tmul in vx `A` termid
                  in vy
-- testl74 :: t2 -> t2
testl75 = evald $ let vx = term2a in 
                  let vy = let z = vx `A` termid in z
                  in vy
-- testl75 :: t2 -> t2

testl76 = evald $ let vx = L(\y -> I 10) in
                  let vy = vx in
                  let z  = vy `A` (I 1) :+ (I 2) in vy
-- testl76 :: t1 -> Int, polymorhic
testl77 = evald $ let vx = L(\y -> I 10) in
                  let vy = vx
                  in (vy `A` (I 1)) :+ (vy `A` (L(\vx->vx)))
-- 20::Int, OK.


term2id = let id = L(\vx ->vx) in
          L(\f -> L(\vy -> 
               ((I 2) :+
                ((id `A` f) `A` ((id `A` vy) :+ (I 1))))))
test2id = evald term2id
-- test2id :: (Int -> Int) -> Int -> Int

termlet = let c2 = L(\f -> L(\vx -> f `A` (f `A` vx))) in
          let inc = L(\vx -> vx :+ (I 1)) in
          let compose = L(\f -> L(\g -> L(\vx -> f `A` (g `A` vx)))) in
          let id = L(\vx -> vx) in
          c2 `A` (compose `A` inc `A` inc) `A` (I 10) :+
          ((c2 `A` (compose `A` inc) `A` id) `A` (I 100))
testlet = evald termlet -- 116
