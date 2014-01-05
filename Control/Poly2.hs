{-# OPTIONS -fglasgow-exts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE OverlappingInstances #-}

-- | Type-class overloaded functions: second-order typeclass programming
-- with backtracking
--
-- <http://okmij.org/ftp/Haskell/types.html#poly2>
--
module Control.Poly2 where

-- | The classes of types used in the examples below
--
type Fractionals = Float :*: Double :*: HNil
type Nums = Int :*: Integer :*: AllOf Fractionals :*: HNil
type Ords = Bool :*: Char :*: AllOf Nums :*: HNil
type Eqs  = AllOf (TypeCl OpenEqs) :*: AllOfBut Ords Fractionals :*: HNil


-- | The Fractionals, Nums and Ords above are closed. But Eqs is open
-- (i.e., extensible), due to the following:
data OpenEqs
instance TypeCls OpenEqs () HTrue -- others can be added in the future

-- | Why we call Nums etc. a type class rather than a type set?
-- The following does not work: type synonyms can't be recursive.
--
-- > type Russel = AllOfBut () Russel :*: HNil
--
-- But the more elaborate version does, with the expected result:
--
data RusselC
instance Apply (Member Russel) x r => TypeCls RusselC x r
type Russel = AllOfBut () (TypeCl RusselC) :*: HNil

-- The following leads to predictable context stack overflow
-- testr = apply (undefined::Member Russel) True

-- Type class membership testing
--
data AllOf x
data AllOfBut x y
data TypeCl x

-- | Classifies if the type x belongs to the open class labeled l
-- The result r is either HTrue or HFalse
class TypeCls l x r | l x -> r

-- | the default instance: x does not belong
instance TypeCast r HFalse => TypeCls l x r

-- | Deciding the membership in a closed class, specified
-- by enumeration, union and difference
--
data Member tl
instance Apply (Member HNil) x HFalse

instance TypeCls l x r => Apply (Member (TypeCl l)) x r

instance (TypeEq h x bf, MemApp bf t x r) 
    => Apply (Member (h :*: t)) x r

instance (Apply (Member h) x bf, MemApp bf t x r)
    => Apply (Member ((AllOf h) :*: t)) x r

instance (Apply (Member exc) x bf, Apply (MemCase2 h t x) bf r)
    => Apply (Member ((AllOfBut h exc) :*: t)) x r

class MemApp bf t x r | bf t x -> r
instance MemApp HTrue t x HTrue
instance Apply (Member t) x r => MemApp HFalse t x r

-- | we avoid defining a new class like MemApp above.
-- I guess, after Apply, we don't need a single class ever?
data MemCase2 h t x
instance Apply (Member t) x r => Apply (MemCase2 h t x) HTrue r
instance Apply (Member ((AllOf h) :*: t)) x r 
    => Apply (MemCase2 h t x) HFalse r

testm1 = apply (undefined::Member Fractionals) (1::Float)
testm2 = apply (undefined::Member Fractionals) (1::Int)
testm3 = apply (undefined::Member Fractionals) ()


-- The implementation of the second-order polymorphic functions

-- | A type class for instance guards and back-tracking
-- Here, pred and f are labels and n is of a kind numeral.
--
class GFN n f a pred | n f a -> pred

-- | The guard that always succeeds (cf. `otherwise' in Haskell)
data Otherwise
instance Apply Otherwise a HTrue

newtype GFn f    = GFn f
newtype GFnA n f = GFnA f

newtype GFnTest n f flag = GFnTest f

instance (GFN Z f a pred, Apply pred a flag,
	  Apply (GFnTest Z f flag) a b)
    => Apply (GFn f) a b where
    apply (GFn f) a = apply ((GFnTest f)::GFnTest Z f flag) a

instance Apply (GFnA n f) a b		-- guard succeeded
    => Apply (GFnTest n f HTrue) a b where
    apply (GFnTest f) a = apply ((GFnA f) :: GFnA n f) a

instance (GFN (S n) f a pred, Apply pred a flag, -- else chose the next inst
	  Apply (GFnTest (S n) f flag) a b)
    => Apply (GFnTest n f HFalse) a b where
    apply (GFnTest f) a = apply ((GFnTest f)::GFnTest (S n) f flag) a



-- It's time for tests
-- | A generic function that tests if its argument is a member of Eqs
--
data IsAnEq = IsAnEq			-- define the label for our function

-- | Each case of a 2-poly function is defined by two instances,
-- of GFN and or Apply classes.
instance GFN Z IsAnEq a (Member Eqs)
instance Apply (GFnA Z IsAnEq) a Bool where
    apply _ _ = True

-- | the default instance
instance TypeCast pred Otherwise => GFN n IsAnEq a pred
instance Apply (GFnA n IsAnEq) a Bool where
    apply _ _ = False

test1 = [apply (GFn IsAnEq) (), apply (GFn IsAnEq) (1.0::Double),
	 apply (GFn IsAnEq) 'a']
-- [True,False,True]

-- | Augment the above function, to test for pairs of Eqs
-- We could have added an instance to TypeCls OpenEqs above. But we wish
-- to show off the recursive invocation of a second-order polymorphic 
-- function
--
instance GFN (S Z) IsAnEq (x,y) Otherwise

instance (Apply (GFn IsAnEq) x Bool,
	  Apply (GFn IsAnEq) y Bool)
    => Apply (GFnA (S Z) IsAnEq) (x,y) Bool where
    apply (GFnA f) (x,y) = apply (GFn f) x && apply (GFn f) y


test2 = [apply (GFn IsAnEq) (True,'a'),
	 apply (GFn IsAnEq) (1.0::Double,True)]
-- [True, False]


-- | The main test: approximate equality. See the article for
-- the description.
--
data PairOf t
instance Apply t x r => Apply (PairOf t) (x,x) r
instance TypeCast r HFalse => Apply (PairOf t) x r

testmp1 = apply (undefined::PairOf (Member Fractionals)) 
	  ((1::Float),(1::Float))
testmp2 = apply (undefined::PairOf (Member Fractionals)) 
	  ((1::Integer),(1::Integer))
testmp3 = apply (undefined::PairOf (Member Nums)) 
	  ((1::Integer),(1::Integer))


data ApproxEq = ApproxEq		-- define the label

-- GFN instance has no constraints!
instance GFN Z ApproxEq (x,x) (PairOf (Member Fractionals))
instance (Fractional x, Ord x) =>
    Apply (GFnA Z ApproxEq) (x,x) Bool where
    apply _ (x,y) = abs (x - y) < 0.5

instance GFN (S Z) ApproxEq (x,x) (PairOf (Member Nums))
instance (Num x, Ord x) =>
    Apply (GFnA (S Z) ApproxEq) (x,x) Bool where
    apply _ (x,y) = abs (x - y) < 2

instance GFN (S (S Z)) ApproxEq (x,x) (PairOf (Member Eqs))
instance (Eq x) =>
    Apply (GFnA (S (S Z)) ApproxEq) (x,x) Bool where
    apply _ (x,y) = x == y

-- Show off the recursive invocation
instance GFN (S (S (S Z))) ApproxEq ((x,x),(x,x))
             (PairOf (PairOf (Member Nums)))
instance (Apply (GFn ApproxEq) (x,x) Bool, Eq x) =>
    Apply (GFnA (S (S (S Z))) ApproxEq) ((x,x),(x,x)) Bool where
    apply _ ((x1,x2),(y1,y2)) = apply (GFn ApproxEq) (x1,y1) &&
				x2 == y2

-- The default instance
instance TypeCast pred Otherwise => GFN n ApproxEq a pred
instance Apply (GFnA n ApproxEq) a Bool where
    apply _ _ = False

-- A convenient abbreviation
approx_eq x y = apply (GFn ApproxEq) (x,y)

test3 = [approx_eq (1.0::Double) (1.5::Double),
	 approx_eq (1.0::Float) (1.1::Float),
	 approx_eq (1::Integer) (2::Integer),
	 approx_eq (1::Int) True,
	 approx_eq (Just ()) [],
	 approx_eq ((2::Integer),(2::Integer)) ((1::Integer),(2::Integer)),
	 approx_eq ((1::Integer),(2::Integer)) ((1::Integer),(2::Integer)) ]
-- [False,True,True,False,False,True,True]


-- The order matters	 
data ApproxEq' = ApproxEq'		-- define the label

instance GFN (S Z) ApproxEq' (x,x) (PairOf (Member Fractionals))
instance (Fractional x, Ord x) =>
    Apply (GFnA (S Z) ApproxEq') (x,x) Bool where
    apply _ (x,y) = abs (x - y) < 0.5

instance GFN Z ApproxEq' (x,x) (PairOf (Member Nums))
instance (Num x, Ord x) =>
    Apply (GFnA Z ApproxEq') (x,x) Bool where
    apply _ (x,y) = abs (x - y) < 2

-- The default instance
instance TypeCast pred Otherwise => GFN n ApproxEq' a pred
instance Apply (GFnA n ApproxEq') a Bool where
    apply _ _ = False

test4 = apply (GFn ApproxEq') ((1.0::Double),(1.5::Double))
-- True


-- The standard HList stuff, extracted from HList library


data HNil = HNil
data a :*: b = a :*: b
infixr 5 :*:
data HTrue
data HFalse

data Z = Z
newtype S n = S n


class TypeCast   a b   | a -> b, b->a   where typeCast   :: a -> b
class TypeCast'  t a b | t a -> b, t b -> a where typeCast'  :: t->a->b
class TypeCast'' t a b | t a -> b, t b -> a where typeCast'' :: t->a->b
instance TypeCast'  () a b => TypeCast a b where typeCast x = typeCast' () x
instance TypeCast'' t a b => TypeCast' t a b where typeCast' = typeCast''
instance TypeCast'' () a a where typeCast'' _ x  = x

class  TypeEq x y b | x y -> b
instance TypeEq x x HTrue
instance TypeCast HFalse b => TypeEq x y b


-- A heterogeneous apply operator

class Apply f a r | f a -> r where
  apply :: f -> a -> r
  apply = undefined

-- Normal function application
instance Apply (x -> y) x y where
  apply f x = f x
