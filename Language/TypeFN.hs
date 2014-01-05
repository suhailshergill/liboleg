-- 
-- |
-- 
-- <http://okmij.org/ftp/Haskell/types.html#computable-types>
-- 
-- Part I of the series introduced the type-level functional language
-- with the notation that resembles lambda-calculus with case
-- distinction, fixpoint recursion, etc. Modulo a bit of syntactic tart,
-- the language of the type functions even looks almost like the pure
-- Haskell.  In this message, we show the applications of computable
-- types, to ascribe signatures to terms and to drive the selection of
-- overloaded functions.  We can compute the type of a tree of the depth
-- fib(N) or a complex XML type, and instantiate the read function to
-- read the trees of only that shape.
-- 
-- A telling example of the power of the approach is the ability to use
-- not only (a->) but also (->a) as an unary type function. The former is
-- just (->) a. The latter is considered impossible.  In our approach,
-- (->a) is written almost literally as (flip (->) a)
-- 
-- 
-- This series of messages has been inspired by Luca Cardelli's 1988
-- manuscript ``Phase Distinctions in Type Theory''
--        <http://lucacardelli.name/Papers/PhaseDistinctions.pdf>
-- and by Simon Peyton Jones and Erik Meijer's ``Henk: A Typed
-- Intermediate Language''
--        <http://www.research.microsoft.com/~simonpj/Papers/henk.ps.gz>
-- which expounds many of the same notions in an excellent tutorial style
-- and in modern terminology.
-- 
-- I'm very grateful to Chung-chieh Shan for pointing out these papers to
-- me and for thought-provoking discussions.
-- 

{-# LANGUAGE KindSignatures, TypeOperators, EmptyDataDecls, Rank2Types #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances, TypeSynonymInstances  #-}
{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies #-}
{-# LANGUAGE UndecidableInstances #-}
module Language.TypeFN where

import Language.TypeLC                 -- Load part I of this series (prev message)


-- | Our first example comes from Cardelli's paper: defining the type
-- Prop(n), of n-ary propositions. That is, 
--
-- >   Prop(2) should be the type       Bool -> Bool -> Bool
-- >   Prop(3) is the type of functions Bool -> Bool -> Bool -> Bool
--
-- etc. 
--
-- Cardelli's paper (p. 10) writes this type as
--
-- >let Prop:: AllKK(N:: NatK) Type =
-- >     recK(F:: AllKK(N:: NatK) Type)
-- >         funKK(N:: NatK) caseK N of 0K => Bool; succK(M) => Bool -> F(M);
--
-- >let and2: Prop(2K) =
-- >     fun(a: Bool) fun(b: Bool) a & b;
--
-- Here 0K and 2K are type-level numerals of the kind NatK; recK is the
-- type-level fix-point combinator. The computed type Prop(2) then gives
-- the type to the term and2.
--
--In our system, this example looks as follows:
--
data Prop'
instance A (F Prop') f (F (Prop',f))
instance A (F (Prop',f)) Zero Bool
instance E (f :< m) r => A (F (Prop',f)) (Su m) (Bool -> r)
type Prop  = Rec (F Prop')

type Prop2 = E (F Prop :< N2) r => r
and2 = (\x y -> x && y) `asTypeOf` (undefined:: Prop2)


-- | We can compute types by applying type functions, just as we can
-- compute values by applying regular functions. Indeed, let us define a
-- StrangeProp of the kind NAT -> Type. StrangeProp(n) is the type of
-- propositions of arity m, where m is fib(n). We compose together the
-- already defined type function Prop2 and the type function Fib in the
-- previous message.
--
data StrangeProp
instance E (F Prop :< (F Fib :< n)) r => A (F StrangeProp) n r

oddand4t :: E (F StrangeProp :< (F FSum :< N2 :< N2)) r => r
oddand4t = undefined

oddand5 = (\x1 x2 x3 x4 -> ((x1 && x2 && x3) &&) . and2 x4)
    `asTypeOf` oddand4t

-- > *DepType> :t oddand4t
-- > oddand4t :: Bool -> Bool -> Bool -> Bool -> Bool -> Bool

-- | We can do better, with the help of higher-order type functions.  First
-- we declare a few standard Haskell type constants as constants in our
-- calculus, with trivial evaluation rules
--
instance E Bool Bool 
instance E Int Int
instance E String String
instance E (a->b) (a->b)              -- We could just as well evaluate under
instance E (a,b) (a,b)                -- these

-- | We introduce the combinator Ntimes: |NTimes f x n| applies f to x n times.
-- This is a sort of fold over numerals.
--
data Ntimes
instance A (F Ntimes) f (F (Ntimes,f)) 
instance A (F (Ntimes,f)) x (F (Ntimes,f,x))
instance A (F (Ntimes,f,x)) Zero x 
instance E (F Ntimes :< f :< (f :< x) :< n) r => A (F (Ntimes,f,x)) (Su n) r

data ATC1 c
instance A (F (ATC1 c)) x (c x)

-- | We can then write the type of n-ary propositions Prop(N) in a different way,
-- as an N-times application of the type constructor (Bool->) to Bool.
--
type PropN' n = E(F Ntimes :< (F (ATC1 ((->) Bool))) :< Bool :< n) r => r
and2' = (\x y -> x && y) `asTypeOf` (undefined:: PropN' N2)


-- | To generalize,
--
data ATC2 (c :: * -> * -> *)
instance A (F (ATC2 c)) x (F (ATC1 (c x))) -- currying of type constructors

type SPropN' n = E(F Ntimes :< (F (ATC2 (->)) :< Bool) :< Bool
                            :< (F Fib :< n)) r => r
test_spn4 = undefined::SPropN' (Su N3)

-- > *TypeFN> :t test_spn4
-- > test_spn4 :: Bool -> Bool -> Bool -> Bool -> Bool -> Bool

-- | The comparison of ATC1 with ATC2 shows two different ways of defining
-- abstractions: as (F x) terms (`lambda-terms' in our calculus) and as
-- polymorphic types (Haskell type abstractions). The two ways are
-- profoundly related. The more verbose type application notation, via
-- (:<), has its benefits. After we introduce another higher-order
-- function
--
data Flip
instance A (F Flip) f (F (Flip,f))
instance A (F (Flip,f)) x (F (Flip,f,x))
instance E (f :< y :< x) r => A (F (Flip,f,x)) y r

-- | we make a very little change
--
type SSPropN' n = E(F Ntimes :< (F Flip :< (F (ATC2 (->))) :< Bool) :< Bool
                             :< (F Fib :< n)) r => r
test_sspn4 = undefined::SSPropN' (Su N3)

-- | and obtain quite a different result:
--
-- > *TypeFN> :t test_sspn4
-- > test_sspn4 :: ((((Bool -> Bool) -> Bool) -> Bool) -> Bool) -> Bool
--
-- In effect, we were able to use not only (a->) but also (->a) as an
-- unary type function. Moreover, we achieved the latter by almost
-- literally applying the flip function to the arrow type constructor
-- (->).
-- 
-- Using the type inspection tools (typecast), we can replace the family
-- of functions ATC1, ATC2 with one, kind-polymorphic, polyvariadic
-- function ATC. This approach will be explained in further messages.
-- 
-- We can use the computed types to drive overloaded functions such as
-- read and show. The specifically instantiated read functions, in
-- particular, will check that a (remotely) received serialized value
-- matches our expectation. Let's consider the type of trees of the depth
-- of at most N.
--
data Node v els = Node v [els] deriving (Read, Show)
type TreeDN v l n = E(F Ntimes :< (F (ATC1 (Node v))) :< l :< n) r => r
instance E (Node v els) (Node v els)

read_tree3 s = (read s) `asTypeOf` (undefined:: TreeDN Int String N3)

-- > *TypeFN> :t read_tree3
-- > read_tree3 :: String -> Node Int (Node Int (Node Int String))


-- | The ability of computed types to drive the selection of overloaded
-- functions has wider implications. We can remove the need for
-- functional dependencies, or simulate functional dependencies when they
-- cannot apply. For example, one may define a multi-parameter typeclass
-- but cannot assert functional dependencies, because not all instances
-- satisfy them.  Therefore, using the methods of the class may require
-- complex and annoying type annotations. Computed types remove the need
-- to manually write these annotations; the typechecker can compute them
-- itself.  This subject is to be explored further.
-- 
-- The last example showed computations of polymorphic types, which,
-- unsurprisingly, have the form of type abstractions. Our calculus is
-- built around the deep connection between type
-- abstraction/instantiation and functional abstraction/application.
ttree3_1 = read_tree3 "Node 1 [Node 2 []]"
ttree3_2 = read_tree3 "Node 1 [Node 2 [Node 3 [\"ok\"]]]"
ttree3_3 = read_tree3 "Node 0 [Node 1 [Node 2 [Node 3 [\"ok\"]]]]"

-- > *TypeFN> ttree3_2
-- > Node 1 [Node 2 [Node 3 ["ok"]]]
-- > *TypeFN> ttree3_3
-- > *** Exception: Prelude.read: no parse


