{-# LANGUAGE GADTs #-}

-- |
--
-- <http://okmij.org/ftp/typed-formatting/FPrintScan.html>
--
-- The initial view to the typed sprintf and sscanf
-- This code defines a simple domain-specific language of string
-- patterns and demonstrates two interpreters of the language:
-- for building strings (sprintf) and parsing strings (sscanf).
-- This code thus solves the problem of typed printf/scanf sharing the
-- same format string posed by Chung-chieh Shan.
--
-- Version: The current version is 1.1, Aug 31, 2008.
--
-- References
--
-- * The complete code with many examples.
--   <http://okmij.org/ftp/typed-formatting/PrintScan.hs>
--
-- * The initial view on typed sprintf and sscanf
--   <http://okmij.org/ftp/typed-formatting/PrintScanI.txt>
--
-- * The message with more explanations, posted on the Haskell mailing list
--   on Sun, 31 Aug 2008 19:40:41 -0700 (PDT)

module Text.PrintScan where

import Prelude hiding ((^))

data F a b where
    FLit :: String -> F a a
    FInt :: F a (Int -> a)
    FChr :: F a (Char -> a)
    FPP  :: PrinterParser b -> F a (b -> a)
    (:^) :: F b c -> F a b -> F a c

-- | Printer/parsers (injection/projection pairs)
data PrinterParser a = PrinterParser (a -> String) (String -> Maybe (a,String))

-- | a bit of syntactic sugar to avoid hitting the Shift key too many a time
infixl 5 ^
(^)  = (:^)
lit  = FLit
int  = FInt
char = FChr

fmt :: (Show b, Read b) => b -> F a (b -> a)
fmt x = FPP showread


-- | The interpreter for printf 
-- It implements Asai's accumulator-less alternative to
-- Danvy's functional unparsing

intp :: F a b -> (String -> a) -> b
intp (FLit str) k = k str
intp FInt       k = \x -> k (show x)
intp FChr       k = \x -> k [x]
intp (FPP (PrinterParser pr _))  k = \x -> k (pr x)
intp (a :^ b)   k = intp a (\sa -> intp b (\sb -> k (sa ++ sb)))


-- | The interpreter for scanf
ints :: F a b -> String -> b -> Maybe (a,String)
ints (FLit str) inp x = maybe Nothing (\inp' -> Just (x,inp')) $ prefix str inp
ints FChr (c:inp) f = Just (f c,inp)
ints FChr "" f      = Nothing
ints (FPP (PrinterParser _ pa)) inp f = 
    maybe Nothing (\(v,s) -> Just (f v,s)) $ pa inp 
ints FInt inp f = ints (FPP showread) inp f
ints (a :^ b) inp f = maybe Nothing (\(vb,inp') -> ints b inp' vb) $ 
                       ints a inp f


sprintf :: F String b -> b
sprintf fmt = intp fmt id

sscanf :: String -> F a b -> b -> Maybe a
sscanf inp fmt f = maybe Nothing (Just . fst) $ ints fmt inp f


-- Tests

tp1 = sprintf $ lit "Hello world"
-- "Hello world"
ts1 = sscanf "Hello world" (lit "Hello world")  ()
-- Just ()

tp2 = sprintf (lit "Hello " ^ lit "world" ^ char) '!'
-- "Hello world!"
ts2 = sscanf "Hello world!" (lit "Hello " ^ lit "world" ^ char) id
-- Just '!'

fmt3 = lit "The value of " ^ char ^ lit " is " ^ int
tp3 = sprintf fmt3 'x' 3
-- "The value of x is 3"
ts3 = sscanf "The value of x is 3" fmt3 (\c i -> (c,i))
-- Just ('x',3)

tp4 = sprintf (lit "abc" ^ int ^ lit "cde") 5
-- "abc5cde"
ts4 = sscanf "abc5cde" (lit "abc" ^ int ^ lit "cde") id
-- Just 5

-- | The format specification is first-class. One can build format specification
-- incrementally
-- This is not the case with OCaml's printf/scanf (where the 
-- format specification has a weird typing and is not first class).
fmt50 = lit "abc" ^ int ^ lit "cde" 
fmt5 = fmt50 ^ fmt (undefined::Float) ^ char
tp5 = sprintf fmt5 5 15 'c'
-- "abc5cde15.0c"
ts5 = sscanf "abc5cde15.0c" fmt5 (\i f c -> (i,f,c))
-- Just (5,15.0,'c')


-- Utility functions

-- | Primitive Printer/parsers
showread :: (Show a, Read a) => PrinterParser a
showread = PrinterParser show parse
 where
 parse s = case reads s of
             [(v,s')] -> Just (v,s')
             _        -> Nothing

-- | A better prefixOf function
-- prefix patt str --> Just str'
--    if the String patt is the prefix of String str. The result str'
--    is str with patt removed
-- Otherwise, the result is Nothing

prefix :: String -> String -> Maybe String
prefix "" str = Just str
prefix (pc:pr) (sc:sr) | pc == sc = prefix pr sr
prefix _  _  = Nothing
