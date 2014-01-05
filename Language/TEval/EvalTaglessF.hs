{-# LANGUAGE NoMonomorphismRestriction #-}
  -- Haskell' Committee seems to have agreed to remove the restriction

-- | Tagless Typed lambda-calculus with integers and the conditional
-- in the higher-order abstract syntax.
-- Haskell itself ensures the object terms are well-typed.
-- Here we use the tagless final approach.
--
-- <http://okmij.org/ftp/Computation/Computation.html#teval>
--

module Language.TEval.EvalTaglessF where

class Symantics repr where
  l    :: (repr t1 -> repr t2) -> repr (t1->t2)
  a    :: repr (t1->t2) -> repr t1 -> repr t2
  i    :: Int -> repr Int
  (+:) :: repr Int -> repr Int -> repr Int              -- addition
  ifz  :: repr Int -> repr t -> repr t -> repr t        -- if zero
  fix  :: repr ((a->b) -> (a->b)) -> repr (a->b)
  -- Let :: repr t1 -> (repr t1 -> repr t) -> repr t

-- compared to EvalTaglessI, everything is in lower-case now

-- | Since we rely on the metalanguage for typechecking and hence
-- type generalization, we have to use `let' of the metalanguage.
infixl 9 `a`


-- | It is quite challenging to show terms. Yet, in contrast to the GADT-based
-- approach (EvalTaglessI.hs), we are able to do that, without
-- extending our language with auxiliary syntactic forms.
-- Incidentally, showing of terms is just another way of _evaluating_
-- them, to strings.
--
type VarCount = Int                     -- to build the names of variables
newtype S t = S (VarCount -> (String,VarCount))
evals (S t) = t

instance Symantics S where
    l f      = S $ \c0 ->
                   let vname = "v" ++ show c0
                       c1 = succ c0
                       (s,c2) = evals (f (S $ \c -> (vname,c))) c1
                   in ("(\\" ++ vname ++ "-> " ++ s ++ ")",c2)
    a e1 e2  = S $ \c0 ->
                   let (s1,c1) = evals e1 c0
                       (s2,c2) = evals e2 c1
                   in ("(" ++ s1 ++ " " ++ s2 ++ ")",c2)
    i n      = S $ \c -> (show n,c)
    e1 +:e2  = S $ \c0 ->
                   let (s1,c1) = evals e1 c0
                       (s2,c2) = evals e2 c1
                   in ("(" ++ s1 ++ " + " ++ s2 ++ ")",c2)
    ifz e1 e2 e3 = S $ \c0 ->
                   let (s1,c1) = evals e1 c0
                       (s2,c2) = evals e2 c1
                       (s3,c3) = evals e3 c2
                   in ("(ifz " ++ s1 ++ " " ++ s2 ++ " " ++ s3 ++")",c3)
    fix e = S $ \c0 ->
                   let (s1,c1) = evals e c0
                   in ("(fix " ++ s1 ++ ")",c1)

tshow t = fst $ evals t 0

-- | We no longer need variables or the environment and we do
-- normalization by evaluation.

-- | Denotational semantics. Why?
newtype D t = D t                       -- This is not a tag. Why?
evald:: D t -> t
evald (D t) = t

instance Symantics D where
    l f      = D $ \x -> evald (f (D x))
    a e1 e2  = D $ (evald e1) (evald e2)
    i n      = D $ n
    e1 +: e2 = D $ evald e1 + evald e2
    ifz e1 e2 e3 = D $ if evald e1 == 0 then evald e2 else evald e3
    fix e    = D $ hfix (evald e) where hfix f = f (hfix f)

{- |
We can also give operational semantics, by implementing the function of the
following signature:

evalo :: (forall repr. Symantics repr => repr t) ->
         (forall repr. Symantics repr => repr t)

The signature has rank-2 type and hence this file requires a PRAGMA
declaration {-# LANGUAGE Rank2Types #-}

The implementation of evalo is exactly the partial evaluator of the
tagless final paper. Please see the paper for details.

-}

-- Tests
-- Truly the tests differ from those in EvalTaglessI.hs only in the case
-- of `syntax`: (i 1) vs (I 1), etc.

test0d = evald $ l(\vx -> vx +: (i 2)) `a` (i 1) -- 3

term1 = l (\vx -> ifz vx (i 1) (vx +: (i 2)))
test11d = evald $ term1
test11s = tshow $ term1 -- "(\\v0-> (ifz v0 1 (v0 + 2)))"

test12d = evald (term1 `a` (i 2))       -- 4, as Haskell Int
-- test14  = evald (term1 `a` vx)       -- Type error! Not in scope: `vx'


term2 = l (\vx -> l (\vy -> vx +: vy))
-- *EvalTaglessF> :t term2
-- term2 :: (Symantics repr) => repr (Int -> Int -> Int)

test21  = evald term2
test23d = evald (term2 `a` (i 1) `a` (i 2)) -- 3

termid = l(\vx -> vx)
testid = evald termid -- testid :: t1 -> t1

term2a = l (\vx -> l(\vy -> vx `a` vy))
{- The meta-language figured the (polymorphic) type now
 *EvalTaglessF> :t term2a
 term2a :: (Symantics repr) => repr ((t1 -> t2) -> t1 -> t2)
-}


-- No longer hidden problems
-- term3 = l (\vx -> ifz vx (i 1) vy) -- Not in scope: `vy'

-- The following is a type error, we can't even enter the term
-- term4 = l (\vx -> ifz vx (i 1) (vx `a` (i 1)))
{- Now we get good error messages!

    Couldn't match expected type `t1 -> Int'
           against inferred type `Int'
      Expected type: repr (t1 -> Int)
      Inferred type: repr Int
    In the first argument of `a', namely `vx'
    In the third argument of `ifz', namely `(vx `a` (i 1))'
-}



-- (x+1)*y = x*y + y

-- why is this less of a cheating? Try showing the term
-- Now, both type-checking and evaluation of tmul1 works!
tmul1 = l (\vx -> l (\vy ->
          (ifz vx (i 0)
            ((tmul1 `a` (vx +: (i (-1))) `a` vy) +: vy))))

-- tmul1 :: (Symantics repr) => repr (Int -> Int -> Int)

testm1d = evald (tmul1 `a` (i 2) `a` (i 3))  -- 6


-- Can termY be typechecked?
-- delta = l (\vy -> vy `a` vy)
{-
    Occurs check: cannot construct the infinite type: t1 = t1 -> t2
      Expected type: repr t1
      Inferred type: repr (t1 -> t2)
    In the second argument of `a', namely `vy'
    In the expression: vy `a` vy
-}

tmul = fix (l (\self -> l (\vx -> l (\vy ->
          (ifz vx (i 0)
            ((self `a` (vx +: (i (-1))) `a` vy) +: vy))))))

testm21d = evald tmul
testm23d = evald (tmul `a` (i 2) `a` (i 3)) -- 6

-- Tests of let (cf. the corresponding tests in TInfLetP.hs)

testl1 = let vx = vx in vx               -- why this works in Haskell?
-- testl2 = let vx = vy in (i 1)            -- type error
testl3 = evald $ let vx = i 1 in vx +: vx -- 2

-- this is essentially the test of hygiene
testl5  = evald $ l(\vx -> let vy = vx `a` (i 1) in l(\vx -> vy +: vx))
-- testl5 :: (Int -> Int) -> Int -> Int

-- lambda vs. let-bound variables
testl61 = evald $ l(\vx -> let vy = vx `a` (i 1) in
                           let vz = vy +: (i 2) in vy)
-- testl61 :: (Int -> Int) -> Int
testl62 = evald $ l(\vx -> let vy = vx `a` (i 1) in
                           let vz = vy +: (i 2) in vx)
-- testl62 :: (Int -> Int) -> Int -> Int
testl63 = evald $ l(\vx -> let vy = vx `a` (i 1) in
                           let vz = (i 2) in vx)
-- testl63 :: (Int -> t2) -> Int -> t2

testl71 = evald $ let vx = term2a in vx
-- testl71 :: (t1 -> t2) -> t1 -> t2

testl72 = evald $ let vx = term2a in 
                  let vy = vx `a` termid in
                  let vz = vy `a` (i 2) in vx
-- testl72 :: (t1 -> t2) -> t1 -> t2

testl73 = evald $ let vx = term2a in 
                  let vy = vx `a` termid in
                  let vz = vy `a` (i 2) in vy
-- testl73 :: t2 -> t2
testl74 = evald $ let vx = term2a in 
                  let vy = let z = vx `a` tmul in vx `a` termid
                  in vy
-- testl74 :: t2 -> t2
testl75 = evald $ let vx = term2a in 
                  let vy = let z = vx `a` termid in z
                  in vy
-- testl75 :: t2 -> t2

term2id = let id = l(\vx ->vx) in
          l(\f -> l(\vy -> 
               ((i 2) +:
                ((id `a` f) `a` ((id `a` vy) +: (i 1))))))
test2id = evald term2id
-- test2id :: (Int -> Int) -> Int -> Int

termlet = let c2 = l(\f -> l(\vx -> f `a` (f `a` vx))) in
          let inc = l(\vx -> vx +: (i 1)) in
          let compose = l(\f -> l(\g -> l(\vx -> f `a` (g `a` vx)))) in
          let id = l(\vx -> vx) in
          c2 `a` (compose `a` inc `a` inc) `a` (i 10) +:
          ((c2 `a` (compose `a` inc) `a` id) `a` (i 100))
testlet = evald termlet -- 116
