{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE EmptyDataDecls, ScopedTypeVariables, KindSignatures #-}
{-# LANGUAGE UndecidableInstances, ExistentialQuantification #-}

-- | Haskell with only one typeclass
--
-- <http://okmij.org/ftp/Haskell/Haskell1/Class2.hs>
--
-- <http://okmij.org/ftp/Haskell/types.html#Haskell1>
--
-- How to make ad hoc overloading less ad hoc while defining no
-- type classes.
-- Haskell1' -- the extension of Haskell1 with functional dependencies,
-- and bounded-polymorphic higher-rank types

module Data.Class2 where

import Data.Class1

-- ----------------------------------------------------------------------
-- | Some functional dependencies: implementing Monad Error
-- As it turns out, some functional dependencies are expressible already
-- in Haskell1. The example is MonadError, which in Haskell' has the form

-- class Error a where
--   strMsg :: String -> a
-- class Monad m => MonadError e m | m -> e where
--   throwError :: e -> m a
--   catchError :: m a -> (e -> m a) -> m a

-- In Haskell1, the above code becomes

data ERROR a
strMsg :: forall a. C (ERROR a) (String->a) => String -> a
strMsg = ac (__::ERROR a)

instance C (ERROR String) (String->String) where
    ac _ = id


data ThrowError (m :: * -> *) a

-- The C (RET m a) t1 and C (BIND m a b) t2 constraints are not 
-- called for, but we specified them anyway. That is, we require that
-- `m' be an instance of a Monad. This extra constraints are Haskell1
-- analogue of Haskell's `class constraints'
throwError :: forall e m a b t1 t2. 
	      (C (ThrowError m a) (e -> m a),
	       C (RET m a) t1,
	       C (BIND m a b) t2) =>
	      e -> m a
throwError = ac (__::ThrowError m a)

data CatchError (m :: * -> *) a
catchError :: forall e m a. C (CatchError m a) (m a -> (e -> m a) -> m a) =>
	      m a -> (e -> m a) -> m a
catchError = ac (__::CatchError m a)


-- define one particular Error Monad, Either e
instance C (ThrowError (Either e) a) (e -> Either e a) where
    ac _ = Left
instance C (CatchError (Either e) a)
           (Either e a -> (e -> Either e a) -> Either e a) where
    ac _ (Left x) f = f x
    ac _ x _ = x


-- so we can write a test

te1 x = runEither $ catchError ac (\e -> ret e)
 where
 ac = (if x then throwError "er" else ret (2::Int)) `bind`
      (\x -> ret (x *$ x)) `bind` (ret.shw)
 runEither :: Either a b -> Either a b
 runEither = id
te1r = (te1 True, te1 False)
-- (Right "er",Right "4")


-- ----------------------------------------------------------------------
-- Functional dependencies

-- The first example has no functional dependencies. In Haskell:
-- class FC1 a b c where fc1 :: a -> b -> c
-- instance FC1 Bool Char Int

-- In Haskell1:

data FC1 a b c
instance C (FC1 Bool Char Int) (Bool->Char->Int) where
    ac _ x y = 1

fc1 :: forall a b c. C (FC1 a b c) (a->b->c) => a->b->c
fc1 = ac (__::FC1 a b c)

-- The definition tfc1 below is rejected because of the unresolved
-- overloading on the return type of fc1. If we specify the return
-- type explicitly, the definition is accepted.
-- To eliminate such explicit type annotations, functional dependencies
-- are introduced.

-- tfc1 = fc1 True 'a'
tfc12 = (fc1 True 'a') :: Int -- OK
-- 1

-- If our function fc is such that the type of its two arguments determines
-- the result type, we can write, in Haskell
-- class FC2 a b c | a b -> c where fc2 :: a -> b -> c
-- instance FC2 Bool Char Int

-- In Haskell1'
data FC2 a b c
instance TypeCast c Int => C (FC2 Bool Char c) (Bool->Char->Int) where
    ac _ x y = 1

fc2 :: forall a b c. C (FC2 a b c) (a->b->c) => a->b->c
fc2 = ac (__::FC2 a b c)

-- Now, tfc2 is accepted without the additional annotations.
-- The argument types still have to be explicitly specified:
-- The definition tfc21 is rejected because of the unresolved overloading
-- over the second argument
tfc2  = fc2 True 'a' -- This is now OK with no type annotations
-- tfc21 = fc2 True undefined -- here, the second arg type is needed

-- If fc is overloaded over the type of the first argument only, we
-- can write
-- class FC3 a b c | a -> b c where fc3 :: a -> b -> c
-- instance FC3 Bool Char Int

-- Or, in Haskell1:
data FC3 a b c
instance TypeCast (FC3 Bool b c) (FC3 Bool Char Int) 
    => C (FC3 Bool b c) (Bool->Char->Int) where
    ac _ x y = 1

fc3 :: forall a b c. C (FC3 a b c) (a->b->c) => a->b->c
fc3 = ac (__::FC3 a b c)

-- In this case, no more type annotations are needed. Both
-- of the following definitions are accepted as they are.
tfc3  = fc3 True 'a'
tfc31 = fc3 True undefined 


-- We do not distinguish between a b -> c and a->b, a->c 
-- The argument has been made for the distinction (Stuckey, Sulzmann: 
-- A theory of overloading)
-- Hereby we make an argument for not having this distinction. We offer
-- a different model: when an instance is selected, its dependent
-- argument are improved (`typecast'). If an instance is not selected,
-- no type improvement is applied.


-- Associated Datatypes
-- The implementation of arrays, whose concrete representation depends on the
-- data type of their elements. This is the first example from
-- the paper Manuel M. T. Chakravarty, Gabriele Keller, Simon Peyton Jones
-- and Simon Marlow, `Associated Types with Class', POPL2005.
-- For simplicity, we limit ourselves to two methods: fromList
-- (which creates an array) and index. Again for simplicity, our
-- arrays are one-dimensional and indexed from 0.
-- As in the paper, the overloading is over the element type only.
-- Although for the function indexA, it would make more sense to overload
-- over the array type (and so the type of the result, that is, of the
-- extracted element, will be inferred).

data FromList e
fromList :: forall e array. C (FromList e) (Int -> [e] -> array) => 
	    Int -> [e] -> array
fromList = ac (__::FromList e)

data Index e
indexA :: forall e array. C (Index e) (array -> Int -> e) => 
	    (array -> Int -> e)
indexA = ac (__::Index e)

instance C (FromList Bool) (Int -> [Bool] -> (Int,Integer)) where
    ac _ dim lst = (dim,foldr (\e a -> 2*a + fromIntegral (fromEnum e)) 0
		              (take dim lst))
instance C (FromList Char) (Int -> [Char] -> String) where
    ac _ dim lst = take dim lst

-- Represent the array of pairs as a pair of arrays (example from the paper)
instance (C (FromList a) (Int -> [a] -> ara),
	  C (FromList b) (Int -> [b] -> arb))
	  => C (FromList (a,b)) (Int -> [(a,b)] -> (ara,arb)) where
    ac _ dim lst = (fromList dim (map fst lst),
		    fromList dim (map snd lst))

instance C (Index Bool) ((Int,Integer) -> Int -> Bool) where
    ac _ (dim,num) i = if i >= dim then error "range check"
		          else (num `div` (2^i)) `mod` 2 == 1

instance C (Index Char) (String -> Int -> Char) where
    ac _ s i = s !! i

instance (C (Index a) (ara -> Int -> a),
	  C (Index b) (arb -> Int -> b))
    => C (Index (a,b)) ((ara,arb) -> Int -> (a,b)) where
    ac _ (ara,arb) i = (indexA ara i, indexA arb i)

-- The `asTypeOf` annotation below could be avoided if we overloaded
-- indexA differently, as mentioned above. We preferred to literally follow
-- the paper though...
testar lst = let arr = fromList (length lst) lst
	     in  [(indexA arr 0) `asTypeOf` (head lst), 
		  indexA arr (pred (length lst))]

testarr = (testar [True,True,False], testar "abc",
	   testar [('x',True),('y',True),('z',False)])
-- ([True,False],"ac",[('x',True),('z',False)])


-- ----------------------------------------------------------------------
-- Haskell98 classes (method bundles) and bounded existentials

-- But what if we really need classes, as bundles of methods?
-- The compelling application is higher-ranked types: bounded existentials.
-- Let's define the Num bundle and numeric functions that are truly
-- NUM-overloaded
data NUM a = NUM{nm_add,nm_mul  :: a->a->a,
		 nm_fromInteger :: Integer->a,
		 nm_show        :: a->String}

data CLS a

instance (C (Add a) (a->a->a), C (Mul a) (a->a->a),
	  C (FromInteger a) (Integer->a),
	  C (SHOW a) (a->String))
    => C (CLS (NUM a)) (NUM a) where
    ac _ = NUM (+$) (*$) frmInteger shw

-- We re-visit the overloaded addition, multiplication, show and
-- fromInteger functions, defining them now in terms of the just
-- introduced `class' NUM.
-- We should point out the uniformity of the declarations below, ripe
-- for syntactic sugar. For example, one may introduce NUM a => ...
-- to mean C (CLS (NUM a)) (NUM a) => ...

infixl 6 +$$
infixl 7 *$$

(+$$) :: forall a. C (CLS (NUM a)) (NUM a) => a -> a -> a
(+$$) x y = nm_add (ac (__:: CLS (NUM a))) x y

(*$$) :: forall a. C (CLS (NUM a)) (NUM a) => a -> a -> a
(*$$) x y = nm_mul (ac (__:: CLS (NUM a))) x y

nshw :: forall a. C (CLS (NUM a)) (NUM a) => a -> String
nshw x = nm_show (ac (__:: CLS (NUM a))) x

nfromI :: forall a. C (CLS (NUM a)) (NUM a) => Integer -> a
nfromI x = nm_fromInteger (ac (__:: CLS (NUM a))) x

-- We are in a position to define a bounded existential, whose quantified
-- type variable 'a' is restricted to members of NUM. The latter lets us
-- use the overloaded numerical functions after opening the existential
-- envelope.

data PACK = forall a. C (CLS (NUM a)) (NUM a) => PACK a

t1d = let x = PACK (Dual (1.0::Float) 2) in
      case x of PACK y -> nshw (y *$$ y +$$ y +$$ (nfromI 2))
--"(|4.0,6.0|)"


-- This typeclass assumed pre-defined; it is not user-extensible.
-- It is best viewed as a ``built-in constraint''
class TypeCast   a b   | a -> b, b->a   where typeCast   :: a -> b
class TypeCast'  t a b | t a -> b, t b -> a where typeCast'  :: t->a->b
class TypeCast'' t a b | t a -> b, t b -> a where typeCast'' :: t->a->b
instance TypeCast'  () a b => TypeCast a b where typeCast x = typeCast' () x
instance TypeCast'' t a b => TypeCast' t a b where typeCast' = typeCast''
instance TypeCast'' () a a where typeCast'' _ x  = x
