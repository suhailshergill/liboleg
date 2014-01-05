-- Haskell98!

-- | The final view to the typed sprintf and sscanf
--
-- <http://okmij.org/ftp/typed-formatting/FPrintScan.html>
--
-- This code defines a simple domain-specific language of string
-- patterns and demonstrates two interpreters of the language:
-- for building strings (sprintf) and parsing strings (sscanf).
-- This code thus solves the problem of typed printf/scanf sharing the
-- same format string posed by Chung-chieh Shan.
-- This code presents scanf/printf interpreters in the final style;
-- it is thus the dual of the code in PrintScan.hs
--
-- Version: The current version is 1.1, Sep 2, 2008.
--
-- References
--
-- * The complete Haskell98 code with many examples.
--  <http://okmij.org/ftp/typed-formatting/PrintScanF.hs>
--
-- * The final view on typed sprintf and sscanf
--  <http://okmij.org/ftp/typed-formatting/PrintScanF.txt>
--
-- * The message posted on the Haskell mailing list on Tue, 2 Sep 2008 00:57:18 -0700 (PDT)
--

module Text.PrintScanF where

import Prelude hiding ((^))

class FormattingSpec repr where
    lit  :: String -> repr a a
    int  :: repr a (Int -> a)
    char :: repr a (Char -> a)
    fpp  :: PrinterParser b -> repr a (b -> a)
    (^)  :: repr b c -> repr a b -> repr a c
infixl 5 ^

-- Printer/parsers (injection/projection pairs)
data PrinterParser a = PrinterParser (a -> String) (String -> Maybe (a,String))

fmt :: (FormattingSpec repr, Show b, Read b) => b -> repr a (b -> a)
fmt x = fpp showread


-- The interpreter for printf 
-- It implements Asai's accumulator-less alternative to
-- Danvy's functional unparsing

newtype FPr a b = FPr ((String -> a) -> b)

instance FormattingSpec FPr where
    lit str = FPr $ \k -> k str
    int     = FPr $ \k -> \x -> k (show x)
    char    = FPr $ \k -> \x -> k [x]
    fpp (PrinterParser pr _) = FPr $ \k -> \x -> k (pr x)
    (FPr a) ^ (FPr b)  = FPr $ \k -> a (\sa -> b (\sb -> k (sa ++ sb)))


-- The interpreter for scanf
newtype FSc a b = FSc (String -> b -> Maybe (a,String))

instance FormattingSpec FSc where
    lit str = FSc $ \inp x -> 
		    maybe Nothing (\inp' -> Just (x,inp')) $ prefix str inp
    char    = FSc $ \inp f -> case inp of
		               (c:inp)  -> Just (f c,inp)
		               ""       -> Nothing
    fpp (PrinterParser _ pa) = FSc $ \inp f ->
	maybe Nothing (\(v,s) -> Just (f v,s)) $ pa inp
    int     = fpp showread
    (FSc a) ^ (FSc b) = FSc $ \inp f ->
	maybe Nothing (\(vb,inp') -> b inp' vb) $ a inp f

sprintf :: FPr String b -> b
sprintf (FPr fmt) = fmt id

sscanf :: String -> FSc a b -> b -> Maybe a
sscanf inp (FSc fmt) f = maybe Nothing (Just . fst) $ fmt inp f


-- One can easily build another interpreter, to convert a formatting
-- specification to a C-style formatting string


-- Tests

tp1 = sprintf $ lit "Hello world"
-- "Hello world"
ts1 = sscanf "Hello world" (lit "Hello world")  ()
-- Just ()

tp2 = sprintf (lit "Hello " ^ lit "world" ^ char) '!'
-- "Hello world!"
ts2 = sscanf "Hello world!" (lit "Hello " ^ lit "world" ^ char) id
-- Just '!'

-- Unit is to keep the type of fmt3 polymorphic and away from the
-- monomorphism restriction
fmt3 () = lit "The value of " ^ char ^ lit " is " ^ int
tp3 = sprintf (fmt3 ()) 'x' 3
-- "The value of x is 3"
ts3 = sscanf "The value of x is 3" (fmt3 ()) (\c i -> (c,i))
-- Just ('x',3)

tp4 = sprintf (lit "abc" ^ int ^ lit "cde") 5
-- "abc5cde"
ts4 = sscanf "abc5cde" (lit "abc" ^ int ^ lit "cde") id
-- Just 5

-- The format specification is first-class. One can build format specification
-- incrementally
-- This is not the case with OCaml's printf/scanf (where the 
-- format specification has a weird typing and is not first class).
-- Unit is to keep the type of fmt3 polymorphic and away from the
-- monomorphism restriction
fmt50 () = lit "abc" ^ int ^ lit "cde" 
fmt5 () = fmt50 () ^ fmt (undefined::Float) ^ char
tp5 = sprintf (fmt5 ()) 5 15 'c'
-- "abc5cde15.0c"
ts5 = sscanf "abc5cde15.0c" (fmt5 ()) (\i f c -> (i,f,c))
-- Just (5,15.0,'c')


-- Utility functions

-- Primitive Printer/parsers
showread :: (Show a, Read a) => PrinterParser a
showread = PrinterParser show parse
 where
 parse s = case reads s of
	     [(v,s')] -> Just (v,s')
	     _        -> Nothing

-- A better prefixOf function
-- prefix patt str --> Just str'
--    if the String patt is the prefix of String str. The result str'
--    is str with patt removed
-- Otherwise, the result is Nothing

prefix :: String -> String -> Maybe String
prefix "" str = Just str
prefix (pc:pr) (sc:sr) | pc == sc = prefix pr sr
prefix _  _  = Nothing
