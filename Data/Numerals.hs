{-# OPTIONS -fglasgow-exts #-}

-- | Illustration of the 2-order lambda-calculus, 
-- using Church numerals as an example.
-- The example shows limited impredicativity
--
-- <http://okmij.org/ftp/Haskell/types.html#some-impredicativity>
--

module Data.Numerals where

import Prelude hiding (succ, exp)

newtype N = N (forall a . (a -> a) -> a -> a)
un (N x) = x

zero :: N
zero = N ( \f a ->  a )

succ :: N -> N
succ n = N ( \f a -> f (un n f a) )

one:: N
one = succ zero

add, mul :: N -> N -> N
add m n = N( \f a -> un m f (un n f a)  )
mul m n = N( \f a -> un m (un n f) a )

exp :: N -> N -> N
exp m n = un n (mul m) one

exp2 :: N -> N -> N
exp2 m n = N (\f a -> un n (un m) f a)

test1 = un (exp two three) (+1) 0
    where two = succ one
	  three = succ two

test2 = un (exp2 two three) (+1) 0
    where two = succ one
	  three = succ two


-- | Simpler illustrations of impredicativity
--
f1:: (forall a. a->a) -> b -> b
f1 g x = g x

testf1 = f1 id True
-- True

foo:: forall c notimportant. (c->c) -> notimportant
foo = undefined

{- the following gives an error
testf1' = foo f1

    Inferred type is less polymorphic than expected
      Quantified type variable `a' escapes
      Expected type: (a -> a) -> a -> a
      Inferred type: (forall a1. a1 -> a1) -> b -> b
    In the first argument of `foo', namely `f1'
    In the definition of `testf1'': testf1' = foo f1
-}


newtype W = W{unW :: forall a. a -> a}

f2:: W -> b -> b
f2 g x = unW g x

testf2 = f2 (W id) True

testf2' = foo (\x -> W(f2 x))
-- testf2'' = foo (W . f2) -- can't use the composition

