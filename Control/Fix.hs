{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -O0 #-}

-- | Several ways of expressing the polymorphic fix-point combinator in Haskell
-- without resorting to value recursion or unsafe operations.
-- This present code attempts to translate the OCaml version
--
-- <http://okmij.org/ftp/Computation/fixed-point-combinators.html#Self->
--
-- to Haskell.
--
module Control.Fix where

import Control.Monad.ST.Lazy
import Data.STRef.Lazy
import Data.Dynamic

-- | Factorial written in the `open recursion style', without the use
-- of recursion.
fact self 0 = 1
fact self n = n * self (pred n)

-- The first approach: using the iso-recursive algebraic data type
-- The functions Wrap and unwrap witness the isomorphism
--
-- > r == r -> a
--
newtype Wrap a = Wrap{unwrap :: Wrap a -> a}
fix1 f = let aux g = g (Wrap g) in
         aux (\x -> f (unwrap x x))

test1 = fix1 fact 5
-- 120

-- | The 2. approach: using Dynamics for type abstraction.
-- This is the only example where constraints, Typeable in this case,
-- are imposed.
-- The other fixes in this file are fully polymorphic.
fix2 f =
    let wrap = toDyn
        unwrap x = fromDyn x undefined
        aux g = g (wrap g) in
        aux (\x -> f (unwrap x x))

test2 = fix2 fact (5::Int)
-- 120

-- | The third approach: type abstraction, impredicativity
-- and implicit type-level recursion:
-- the data type declaration can refer to a class that refers
-- to the type being declared
-- No spurious constraints are introduced
data W3 a = forall d. C d => W3 (d a -> a)

class C d where
    unwrap3 :: (d a -> a) -> W3 a -> a

instance C W3 where
    unwrap3 = ($)

fix3 f = let aux g = g (W3 g) in
         aux (\x -> f (case x of W3 h -> unwrap3 h x))

test3 = fix3 fact 5
-- 120


-- | Even better example, exploiting the fact that type classes and
-- type families are open. Hence we can define instances afterwards,
-- referring to already defined types.
-- Haskell is inconsistent in yet another way.
--
type family D a :: *

newtype W31 a = W31 (D a -> a)

type instance D a = W31 a

fix31 f = let aux g = g (W31 g) in
          aux (\x -> f (case x of W31 h -> h x))


test31 = fix31 fact 5
-- 120

-- | The fourth approach: using references and laziness
-- Any sort of partiality (partial pattern-match) would work instead
-- of the error call. 
-- The example might seem paradoxical: the effect of reading the wrap
-- cell seems to be occurring in the pure code. 
-- Lazy ST is indeed quite interesting (for more discussion, see
-- Moggi and Sabry, 2001).
--
fix4 f = runST (do
         wrap <- newSTRef (error "black hole")
         let aux = readSTRef wrap >>= (\x -> x >>= return . f)
         writeSTRef wrap aux
         aux)

test4 = fix4 fact 5
-- 120

