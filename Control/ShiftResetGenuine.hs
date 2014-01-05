-- Haskell98!

-- | Implementation of the calculus lambda-sr-let
--
-- > Polymorphic delimited continuations
-- > Asai and Kameyama, APLAS 2007
-- > http://logic.cs.tsukuba.ac.jp/~kam/paper/aplas07.pdf
-- > hereafter, AK07
--
-- This embedding of the AK07 calculus into Haskell is another
-- proof that AK07 admit type inference algorithm.
-- In all the tests below, all the types are inferred.

module Control.ShiftResetGenuine where

import Prelude hiding ((^))

-- | Parameterized monad. This is almost the same monad used in 
-- the Region-IO and TFP07 paper
-- See also
--
-- >  Robert Atkey, Parameterised Notions of Computation, Msfp2006
-- >  http://homepages.inf.ed.ac.uk/ratkey/param-notions.pdf
--
-- and
--
-- >  http://www.haskell.org/pipermail/haskell/2006-December/018917.html

class Monadish m where
    ret :: tau -> m a a tau
    bind :: m b g sigma -> (sigma -> m a b tau) -> m a g tau

-- | Inject regular monads to be monadish things too
newtype MW m p q a = MW{ unMW:: m a }

instance Monad m => Monadish (MW m) where
    ret = MW . return
    bind (MW m) f = MW (m >>= unMW . f)

-- | some syntactic sugar
--
infixl 1 +>>
vm1 +>> vm2 = bind vm1 (const vm2)

infixl 1 >==
m >== f = bind m f

-- | The continuation monad parameterized by two answer types
-- We represent the the effectful expression e, whose type is
-- characterized by the judgement
--
-- >	Gamma; a |- e:tau; b
--
-- as a parameterized monad C a b tau. We represent an effectful function
-- type sigma/a -> tau/b of the calculus as an arrow type 
-- sigma -> C a b tau.
-- Incidentally, this notational `convention' expresses the rule `fun' in AK07
newtype C a b tau = C{unC:: (tau -> a) -> b}

-- | Fortunately, the rule app in AK07 (Fig 3) is expressible as 
-- the composition of two binds
instance Monadish C where
    ret x = C (\k -> k x)
    bind (C f) h = C (\k -> f (\s -> unC (h s) k))

-- | The rules from AK07 as they are (see Fig 3)
reset :: C sigma tau sigma -> C a a tau
reset (C f) = C(\k -> k (f id))

-- | shift.
shift :: ((tau-> C t t a) -> C s b s) -> C a b tau
shift f = C(\k -> unC (f (\tau -> ret (k tau))) id)

run :: C tau tau tau -> tau
run (C f) = f id

-- | The append example from AK07, section 2.1
--
appnd [] = shift (\k -> ret k)
appnd (a:rest) = appnd rest >== (\r' -> ret (a:r'))
-- inferred type
-- appnd :: [t] -> C a ([t] -> C t1 t1 a) [t]
-- It is the same type as described in the paper, after Fig 3.

appnd123 = reset (appnd [1,2,3])
-- :t appnd123
-- appnd123 :: C a a ([Integer] -> C t t [Integer])

test1 = run (appnd123 >== (\f -> f [4,5,6]))
-- [1,2,3,4,5,6]


-- | The sprintf test: Sec 2.3 of AK07
-- The paper argues this test requires both the changing of the answer type
-- and polymorphism (fmt is used polymorphically in stest3)
--
int:: Int -> String
int x = show x
str :: String -> String
str x = x

-- | The do-syntactic sugar would have been nice...
e1 ^ e2 = e1 >== (\x -> e2 >== (\y -> ret (x++y)))

infixl 1 $$
e1 $$ x =  e1 >== (\f -> f x)


fmt to_str = shift(\k -> ret (k . to_str))
sprintf p = reset p

stest1 = run $ sprintf (ret "Hello world")
-- "Hello world"

stest2 = run $
	  sprintf (ret "Hello " ^ fmt str ^ ret "!") $$ "world"
-- "Hello world!"

stest3 = run $
	  sprintf (ret "The value of " ^ fmt str ^ ret " is " ^ fmt int) 
	    $$ "x" $$ 3
-- "The value of x is 3"

-- The following is the same as stest3, only split into several parts.
-- The aim is to demonstrate that sprintf and the format specification
-- are first-class functions. This is not the case with Haskell's Printf
-- (which isn't even type safe) or OCaml's printf (where the 
-- format specification has a weird typing and is not first class).
stest3' = run $ formatter $$ "x" $$ 3
 where
  -- demonstrate sprintf and format_specification can be passed as arguments
  formatter = applyit sprintf format_specification
  applyit f x = f x
  format_specification = ret "The value of " ^ fmt str ^ ret " is " ^ fmt int
-- "The value of x is 3"

