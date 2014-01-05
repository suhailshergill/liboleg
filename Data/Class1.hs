{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE EmptyDataDecls, ScopedTypeVariables, KindSignatures #-}

-- | Haskell with only one typeclass
--
-- <http://okmij.org/ftp/Haskell/Haskell1/Class1.hs>
--
-- <http://okmij.org/ftp/Haskell/types.html#Haskell1>
--
-- How to make ad hoc overloading less ad hoc while defining no
-- type classes.
--  For clarity, we call as Haskell1 the language Haskell98
--  with no typeclass declarations but with a single, pre-defined typeclass C
--  (which has two parameters related by a functional dependency).
--  The programmers may not declare any typeclasses; but they
--  may add instances to C and use them. We show on a series of examples that
--  despite the lack of typeclass declarations, Haskell1 can express all
--  the typeclass code of Haskell98 plus multi-parameter type classes
--  and even some (most useful?) functional dependencies.
--
--  Haskell1 is not a new language and requires no new compilers;
--  rather, it is a subset of the current Haskell. The `removal' of typeclass
--  declarations is merely the matter of discipline.  
--
--
--

module Data.Class1 where

-- | The one and only type class present in Haskell1
class C l t | l -> t where
    ac :: l -> t

__ = __					-- short synonym for undefined

-- ----------------------------------------------------------------------
-- | Example 1: Building overloaded numeric functions, the analogue of Num.
-- The following defines overloaded numeric functions `a la carte'. We
-- shall see how to bundle such methods into what Haskell98 calls `classes'
--
data Add a				-- auxiliary labels
data Mul a
data FromInteger a

instance C (Add Int) (Int->Int->Int) where
    ac _ x y = x + y

-- | We can now define the generic addition. We use the operation +$
-- to avoid the confusion with Prelude.(+)
infixl 6 +$

-- | In H98, the overloaded addition was a method. In Haskell1, it is an
-- ordinary (bounded polymorphic) function
-- The signature looks a bit ugly; we'll see how to simplify it a bit
(+$) :: forall a. C (Add a) (a->a->a) => a -> a -> a
(+$) = ac (__:: Add a)

ta1 = (1::Int) +$ 2 +$ 3
-- 6

-- | Let's define the addition for floats
instance C (Add Float) (Float->Float->Float) where
    ac _ x y = x + y

-- | We now illustrate overloading over datatypes other than basic ones.
-- We define dual numbers (see Wikipedia)
data Dual a = Dual a a deriving Show

-- | We define the addition of Duals inductively, with the addition over
-- base types as the base case.
-- We could have eliminated the mentioning (a->a->a)  and replaced with some
-- type t. But then we would need the undecidable instance extension...
--
instance C (Add a) (a->a->a) => C (Add (Dual a)) (Dual a->Dual a->Dual a) where
    ac _ (Dual x1 y1) (Dual x2 y2) = Dual (x1 +$ x2) (y1 +$ y2)

-- | The following test uses the previously defined +$ operation, which 
-- now accounts for duals automatically. 
-- As in Haskell98, our overloaded functions are extensible.
ta2 = let x = Dual (1::Int) 2 in x +$ x
-- Dual 2 4

-- | Likewise define the overloaded multiplication
infixl 7 *$

instance C (Mul Int) (Int->Int->Int) where
    ac _ x y = x * y
instance C (Mul Float) (Float->Float->Float) where
    ac _ x y = x * y
instance (C (Add a) (a->a->a), C (Mul a) (a->a->a))
    => C (Mul (Dual a)) (Dual a->Dual a->Dual a) where
    ac _ (Dual x1 y1) (Dual x2 y2) = Dual (x1 *$ x2) (x1 *$ y2 +$ y1 *$ x2)


-- | Here is a different, perhaps simpler, way of defining signatures of
-- overloaded functions. The constraint C is inferred and no longer has
-- to be mentioned explicitly
mul_sig :: a -> a -> a; mul_sig = undefined
mul_as  :: a -> Mul a;  mul_as = undefined

x *$ y | False = mul_sig x y
x *$ y = ac (mul_as x) x y

-- | fromInteger conversion
-- This numeric operation is different from the previous in that
-- the overloading is resolved on the result type only. The function
-- `read' is another example of such a `producer'

instance C (FromInteger Int) (Integer->Int) where
    ac _ = fromInteger
instance C (FromInteger Float) (Integer->Float) where
    ac _ = fromInteger
instance (C (FromInteger a) (Integer->a)) 
    => C (FromInteger (Dual a)) (Integer->Dual a) where
    ac _ x = Dual (frmInteger x) (frmInteger 0)

-- | and the corresponding overloaded function (which in Haskell98 was a method)
-- Again, we chose a slightly different name to avoid the confusion with
-- the Prelude
frmInteger :: forall a. C (FromInteger a) (Integer->a) => Integer -> a
frmInteger = ac (__::FromInteger a)

-- | We can define generic function at will, using already defined overloaded
-- functions. For example,
genf x = x *$ x *$ (frmInteger 2)

tm1 = genf (Dual (1::Float) 2) +$ (frmInteger 3)
-- Dual 5.0 8.0

-- For completeness, we implement the quintessential Haskell98 function, Show.

data SHOW a
instance C (SHOW Int) (Int->String) where
    ac _ = show
instance C (SHOW Float) (Float->String) where
    ac _ = show
instance (C (SHOW a) (a->String))
    => C (SHOW (Dual a)) (Dual a -> String) where
    ac _ (Dual x y) = "(|" ++ shw x ++ "," ++ shw y ++ "|)"

shw :: forall a. C (SHOW a) (a->String) => a->String
shw = ac (__::SHOW a)

ts1 = shw tm1
-- "(|5.0,8.0|)"


-- | Finally, we demonstrate overloading of non-functional values, such as
-- minBound and maxBound. These are not `methods' in the classical sense.
--
data MinBound a
instance C (MinBound Int) Int where
    ac _ = minBound
instance C (MinBound Bool) Bool where
    ac _ = False

mnBound :: forall a. C (MinBound a) a => a
mnBound = ac (__::MinBound a)

tmb = mnBound::Int
-- -2147483648


-- ----------------------------------------------------------------------
-- Constructor classes and Monads

-- | We are defining a super-set of monads, so called `restricted monads'.
-- Restricted monads include all ordinary monads; in addition, we can
-- define a SET monad. See 
--    <http://okmij.org/ftp/Haskell/types.html#restricted-datatypes>
--
data RET  (m :: * -> *) a
data BIND (m :: * -> *) a b

ret :: forall m a. C (RET m a) (a->m a) => a -> m a
ret = ac (__::RET m a)

bind :: forall m a b. C (BIND m a b) (m a->(a -> m b)->m b) => 
	(m a->(a -> m b)->m b)
bind = ac (__::BIND m a b)


--  | Define two sample monads
--
instance C (RET Maybe a) (a -> Maybe a) where
    ac _ = Just
instance C (BIND Maybe a b) (Maybe a -> (a->Maybe b) -> Maybe b) where
    ac _ Nothing f  = Nothing
    ac _ (Just x) f = f x

instance C (RET (Either e) a) (a -> Either e a) where
    ac _ = Right
instance C (BIND (Either e) a b)
           (Either e a -> (a->Either e b) -> Either e b) where
    ac _ (Right x) f  = f x
    ac _ (Left x) f   = Left x


-- | An example of using monads and other overloaded functions
tmo = (tmo' True, tmo' False)
 where
  tmo' x = let t = if x then Nothing else ret (1::Int) 
	       v = t `bind` (\x -> ret (x +$ (frmInteger 1)))
           in shw v
-- ("Nothing","Just 2")

instance C (SHOW a) (a->String) => C (SHOW (Maybe a)) (Maybe a->String) where
    ac _ Nothing = "Nothing"
    ac _ (Just x) = "Just " ++ shw x


