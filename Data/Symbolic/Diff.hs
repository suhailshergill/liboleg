{-# OPTIONS -fglasgow-exts #-}
{-# LANGUAGE TemplateHaskell #-}

-- | Reify the (compiled) code to its typed TH representation 
-- (or, the dictionary *view*, to be precise) and reflect\/compile that code.
-- We must spread the code through several modules, due to the
-- particular requirement of the Template Haskell.
-- See DiffTest.hs for reflection of the differentiated TH code back
-- into (machine) code.

module Data.Symbolic.Diff where

import Data.Symbolic.TypedCode


-- | Lift Nums, Fractionals, and Floating to code expressions
--
instance Num a => Num (Code a) where
    x + y = op'add `appC` x `appC` y
    x - y = op'sub `appC` x `appC` y
    x * y = op'mul `appC` x `appC` y
    negate x = op'negate `appC` x
    fromInteger = integerC

instance Fractional a => Fractional (Code a) where
    x / y = op'div `appC` x `appC` y
    recip x = op'recip `appC` x
    fromRational = rationalC

instance Floating a => Floating (Code a) where
    pi = op'pi
    sin x = op'sin `appC` x
    cos x = op'cos `appC` x

testf1 :: Num a => a
testf1 = 1 + 2
testf1' = return (testf1 :: Code Int)
testf1'' = showQC testf1' -- (GHC.Num.+) 1 2


-- | We can define a function
--
test1f x = let y = x * x in y + 1
test1 = test1f (2.0::Float)

-- | we can even compile it. At any point, we can reify it, into
-- a `dictionary view'
-- The result is the TH code, which we can print, and compile back
-- to the code. We can also differentiate the TH code, simplify it,
-- partially evaluate it, etc.
--
test1c = new'diffVar >>= \ (v::Var Float) -> return $ (test1f (var'exp v),v)
test1r = test1c >>= \ (c,v) -> reflectDF v c
test1cp = showQC test1r

-- and reflect it back, see DiffTest.hs
{-
We must stress that there is no `reify' function. One may say it is
built into Haskell already.


    *Diff> test1
    5.0
    *DiffTest> test1'
    5.0
    *Diff> test1cp
    \dx_0 -> GHC.Num.+ (GHC.Num.* dx_0 dx_0) 1
-}


-- | Symbolic Differentiation of the reified, typed TH code expressions
-- The derivative over the code is a type preserving operation
--
diffC :: (Floating a, Floating b) => Var b -> Code a -> Code a

diffC v c | Just _  <- on'litC c = 0
diffC v c | Just ev <- on'varC v c = either (const 1) (const 0) ev

diffC v c | Just (x,y) <- on'2opC op'add c =
			  (diffC v x) + (diffC v y)

diffC v c | Just (x,y) <- on'2opC op'sub c =
			  (diffC v x) - (diffC v y)

diffC v c | Just (x,y) <- on'2opC op'mul c =
			    ((diffC v x) * y) + (x * (diffC v y))

diffC v c | Just (x,y) <- on'2opC op'div c =
			  ((diffC v x) * y - x * (diffC v y)) / (y*y)

diffC v c | Just x <- on'1opC op'negate c =
			  negate (diffC v x)

diffC v c | Just x <- on'1opC op'recip c =
			  negate (diffC v x) / (x*x)

diffC v c | Just x <- on'1opC op'sin c =
			  (diffC v x) * cos x

diffC v c | Just x <- on'1opC op'cos c =
			  negate ((diffC v x) * sin x)

diffC v c = error $ "Cannot handle code: " ++ show c


test1d = test1c >>= \ (c,v) -> reflectDF v $ diffC v c
test1dp = showQC test1d

{-
 *Diff> test1dp
 \dx_0 -> (GHC.Num.+) ((GHC.Num.+) ((GHC.Num.*) 1 dx_0) ((GHC.Num.*) dx_0 1)) 0
-}


-- | Simplification rules
-- simplification is type-preserving
-- obviously, simplification is an `open-ended' problem:
-- we could even recognize common sub-expressions and simplify them
-- by introducing let binding.
-- In the following however, we do trivial simplification only.
-- One can always add more simplification rules later.
--
simpleC :: Floating a => Var b -> Code a -> Code a

-- | repeat until no simplifications are made
simpleC v c | Just c' <- simpleCL v c = simpleC v c'
simpleC v c = c

simpleCL :: Floating a => Var b -> Code a -> Maybe (Code a)

simpleCL v c | Just _ <- on'litC c = Nothing
simpleCL v c | Just _ <- on'varC v c = Nothing

simpleCL v c | Just (x,y) <- on'2opC op'add c =
			     simple'recur op'add sadd v x y
  where
  sadd x y | Just 0 <- on'litRationalC x = Just y
  sadd x y | Just 0 <- on'litRationalC y = Just x
		       -- constant folding
  sadd x y | (Just x, Just y) <- (on'litRationalC x, on'litRationalC y)
			      = Just (fromRational $ x + y)
  sadd x y = Nothing

simpleCL v c | Just (x,y) <- on'2opC op'sub c =
			     simple'recur op'sub ssub v x y
  where
  ssub x y | Just 0 <- on'litRationalC y = Just x
		       -- constant folding
  ssub x y | (Just x, Just y) <- (on'litRationalC x, on'litRationalC y)
			      = Just (fromRational $ x - y)
  ssub x y = Nothing


simpleCL v c | Just (x,y) <- on'2opC op'mul c =
			     simple'recur op'mul smul v x y
  where
  smul x y | Just 0 <- on'litRationalC x = Just (fromRational 0)
  smul x y | Just 0 <- on'litRationalC y = Just (fromRational 0)
  smul x y | Just 1 <- on'litRationalC x = Just y
  smul x y | Just 1 <- on'litRationalC y = Just x
  smul x y | (Just x, Just y) <- (on'litRationalC x, on'litRationalC y)
			      = Just (fromRational $ x * y)
  smul x y = Nothing -- error $ unwords ["here",show x,show y] -- Nothing


simpleCL v c | Just (x,y) <- on'2opC op'div c =
			     simple'recur op'div sdiv v x y
  where
  sdiv x y | Just 0 <- on'litRationalC x = Just (fromRational 0)
  sdiv x y = Nothing -- error $ unwords ["here",show x,show y] -- Nothing

simpleCL v c | Just x <- on'1opC op'negate c =
			     simple'recur1 op'negate sneg v x
  where
  sneg x | Just 0 <- on'litRationalC x = Just (fromRational 0)
  sneg x = Nothing 


simpleCL v c = Nothing

simple'recur op fn v x y = 
    case (simpleCL v x, simpleCL v y) of
	     (Nothing,Nothing) -> fn x y
	     (Just x,Nothing)  -> Just (op `appC` x `appC` y)
	     (Nothing,Just y)  -> Just (op `appC` x `appC` y)
	     (Just x,Just y)   -> Just (op `appC` x `appC` y)

simple'recur1 op fn v x = 
    case simpleCL v x of
	     Nothing -> fn x
	     Just x  -> Just (op `appC` x)

test1ds = test1c >>= \ (c,v) -> reflectDF v $ simpleC v $ diffC v c
test1dsp = showQC test1ds

{-
   *Diff> test1dsp
   \dx_0 -> GHC.Num.+ dx_0 dx_0
-}

-- | And that's about it. Putting it all together gives us:
--
diff_fn :: Floating b => (forall a. Floating a => a -> a) -> QCode (b -> b)
diff_fn f = 
    do
    v <- new'diffVar
    let body = f (var'exp v)   -- reified body of the function
    reflectDF v . simpleC v . diffC v $ body -- differentiate and simplify

-- | This is a useful helper to show us the code of the function in question
show_fn :: (forall a. Floating a => a -> a) -> IO ()
show_fn f = showQC (
		    do
		    v <- new'diffVar
		    reflectDF v (f (var'exp v)))

-- We can either print the result of diff_fn, or compile it
-- (that is, splice it: see DiffTest.hs)


-- | More examples
--
test2f x = foldl (\z c -> x*z + c) 0 [1,2,3]
test2n = test2f (4::Float)  -- 27.0
test2s = show_fn test2f

{-
  *Diff> test2s
  \dx_0 -> GHC.Num.+ (GHC.Num.* dx_0 (GHC.Num.+ 
     (GHC.Num.* dx_0 (GHC.Num.+ (GHC.Num.* dx_0 0) 1)) 2)) 3
-}

test2ds = showQC (diff_fn test2f)

{- Not too bad: 2*x + 2
 *Diff> test2ds
 \dx_0 -> GHC.Num.+ (GHC.Num.+ dx_0 2) dx_0
-}

{- The differentiated code can be `compiled back', see DiffTest.hs
  test2dn = $(reflectQC (diff_fn test2f)) (4::Float)
  -- 10.0
-}

-- Check the constant folding
test11f x = 2*x + 3*x
test11ds = showQC (diff_fn test11f) -- \dx_0 -> 5%1


-- | Here's a slightly more complex example:
--
test5f x = sin (5*x + pi/2) + cos(1 / x)
test5n = test5f (pi::Float) -- cos(1/pi)-1 == -5.023426e-2
test5ds = showQC (diff_fn test5f)


{- which isn't too bad: quite optimal, actually
*Diff> test5ds
\dx_0 -> GHC.Num.+ (GHC.Num.* 5 (GHC.Float.cos 
    (GHC.Num.+ (GHC.Num.* 5 dx_0) (GHC.Real./ GHC.Float.pi 2))))
   (GHC.Num.negate (GHC.Num.* (GHC.Real./ ((-1)%1) (GHC.Num.* dx_0 dx_0)) 
        (GHC.Float.sin (GHC.Real./ 1 dx_0))))
-}

-- One may evaluate the function test5f numerically, differentiate it
-- symbolically, check the result of differentiation -- and evaluate it
-- numerically right away. See test5dn in DiffTest.hs for the latter.


-- | We can even do partial derivatives:
--
test3f x y = (x*y + (5*x*x)) / y

test4x y = diff_fn (\x -> test3f x (fromIntegral y))
test4y x = diff_fn (test3f (fromInteger x))

test4xds = showQC (test4x 1) -- 1 + 10*x
test4yds = showQC (test4y 5) 

{-
 *DiffTest> test4yds
 \dx_0 -> GHC.Real./ (GHC.Num.- (GHC.Num.* 5 dx_0) 
             (GHC.Num.+ (GHC.Num.* 5 dx_0) (125%1))) (GHC.Num.* dx_0 dx_0)

-}

{- In DiffTest.hs
-- partial derivative with respect to x
test4xdn = $(reflectQC (test4x 1)) (2::Float)
-- 21.0

-- | partial derivative with respect to y
test4ydn = $(reflectQC (test4y 5)) (5::Float)
-- -5.0
-}
