{-# LANGUAGE TemplateHaskell, NoMonomorphismRestriction #-}
-- The rest is Haskell98

-- | Type-safe printf and scanf with C-like formatting string
-- We also permit a generic format specifier %a to format or parse
-- any showable and readable value.
-- Our format descriptors are first-class and can be built incrementally.
-- We can use the same format descriptor to format to a string,
-- to the standard output or any other data sink. Furthermore,
-- we can use the same format descriptor to parse from a string
-- or any data source.
-- What we print we can parse, using the same descriptor.

module Text.TFTest where

import Text.TotalPrintF
import Prelude hiding ((^))

-- The following import is needed only for the extensibility test
-- at the end of the file
import Text.PrintScanF (FormattingSpec(..), PrinterParser(..)) 

t1 = sprintf $(spec "Hello, there!")
-- "Hello, there!"

t1s = sscanf "Hello, there!" $(spec "Hello, there!") ()
-- Just ()

t2 = sprintf $(spec "Hello, %s!") "there"
-- "Hello, there!"

t3 = sprintf $(spec "The value of %s is %d") "x" 3
-- "The value of x is 3"

-- What we print we can parse, using the same descriptor
t31 = let printed = sprintf desc "x" 3
          parsed  = sscanf printed desc (\s i -> (s,i))
      in (printed, parsed)
  where desc = $(spec "The value of %s is %d")
-- ("The value of x is 3",Just ("x",3))

-- Mismatch between the formatting string and the printf arguments
-- is a type error.

-- t32 = sprintf $(spec "The value of %s is %d") "x" True
--     Couldn't match expected type `Bool' against inferred type `Int'

{-
t33 = sprintf $(spec "The value of %s is %d") "x" 3 10
    Couldn't match expected type `t1 -> t'
           against inferred type `String'
    Probable cause: `printf' is applied to too many arguments
-}

t4 = let x = [9,16,25] 
	 i = 2 
     in sprintf $(spec "The element number %d of %a is %a") i x (x !! i)
-- "The element number 2 of [9,16,25] is 25"

t4s = sscanf "The element number 2 of [9,16,25] is 25"
        $(spec "The element number %d of %a is %a")
        (\i a e -> (i,a::[Int],e::Int))
-- Just (2,[9,16,25],25)



-- Demonstrating that printf is first-class
t5 = map (uncurry printer) [("x",3), ("y",5), ("z",7)]
 where
 printer = sprintf $(spec "The value of %s is %d")

-- ["The value of x is 3","The value of y is 5","The value of z is 7"]

{- An inconsistent format descriptor generates a type error

t6 = map (uncurry printer) [("x",3), ("y",5), ("z",7)]
 where
 printer = sprintf $(spec "The value of %d is %d")
    Couldn't match expected type `Int' against inferred type `[Char]'
    In the expression: "x"
    In the expression: ("x", 3)
    In the second argument of `map', namely
        `[("x", 3), ("y", 5), ("z", 7)]'

-}

-- Demonstrating that format descriptors are first-class and can be built 
-- incrementally

spec71 = $(spec "The value of %s")
spec72 = $(spec " is %d")
t7 = sprintf (spec71 ^ spec72) "x" 3
-- "The value of x is 3"


-- Extensibility test

-- Furthermore, the user can always extend printf, for example, to
-- send the formatted data to the standard output, without first building
-- the formatted output as a string.


newtype FPrIO a b = FPrIO ((IO () -> a) -> b)

instance FormattingSpec FPrIO where
    lit str = FPrIO $ \k -> k $ putStr str
    int     = FPrIO $ \k -> \x -> k $ putStr (show x)
    char    = FPrIO $ \k -> \x -> k $ putStr [x]
    fpp (PrinterParser pr _) = FPrIO $ \k -> \x -> k $ putStr (pr x)
    (FPrIO a) ^ (FPrIO b)  = FPrIO $ \k -> a (\sa -> b (\sb -> k (sa >> sb)))

printf (FPrIO fmt) = fmt (\m -> m >> putStrLn "\n-end-of-output-")

t3io = printf $(spec "The value of %s is %d") "x" 3
{- printed on the standard output:

The value of x is 3
-end-of-output-
-}
