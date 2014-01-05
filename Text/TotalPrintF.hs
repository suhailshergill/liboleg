{-# LANGUAGE TemplateHaskell #-}
-- The rest is Haskell98

-- |
--
-- <http://okmij.org/ftp/typed-formatting/FPrintScan.html#C-like>
--
-- Safe and generic printf/scanf with C-like format string
-- 
-- We implement printf that takes a C-like format string and the variable number
-- of other arguments.  Unlike C of Haskell's printf, ours is total: if the types
-- or the number of the other arguments, the values to format, does not match the
-- format string, a type error is reported at compile time.  To the familiar
-- format descriptors %s and %d we add %a to format any showable value. The latter
-- is like the format descriptor ~a of Common Lisp. Likewise, we build scanf that
-- takes a C-like format string and the consumer function with the variable number
-- of arguments. The types and the number of the arguments must match the format
-- string; a type error is reported otherwise.
-- 
-- Our approach is a variation of the safe printf and scanf described
-- elsewhere on this page. We use Template Haskell to translate the format string
-- to a phrase in the DSL of format descriptors. We use the final approach to
-- embed that DSL into Haskell.
-- 
-- Unlike the safe printf explained in the Template Haskell documentation, in
-- our implementation, format descriptors are first class. They can be built
-- incrementally. The same descriptor can be used both for printing and for
-- parsing. Our printf and scanf are user-extensible: library users can write
-- functions to direct format output to any suitable data sink, or to read parsed
-- data from any suitable data source such as string or a file. Finally, what is
-- formatted can be parsed back using the same format descriptor.
-- 
-- Here are some of the tests from the test collection referenced below. The
-- evaluation result is given in the comments below each binding. Example t31
-- shows that format descriptors are indeed first-class. The definition t32, when
-- uncommented, raises the shown type error because the format descriptor does not
-- match the type of the corresponding argument.
--

-- Type-safe printf and scanf with C-like formatting string
-- We also permit a generic format specifier %a to format or parse
-- any showable and readable value.
--
-- Our format descriptors are first-class and can be built incrementally.
-- We can use the same format descriptor to format to a string,
-- to the standard output or to any other data sink. Furthermore,
-- we can use the same format descriptor to parse from a string
-- or any data source.
-- What we print we can parse, using the same descriptor.
--
-- We rely on Template Haskell to convert the format string into
-- the phrase of the DSL for format descriptors.
-- We use the Final approach to embed that DSL into Haskell, see
-- PrintScanF.hs
--
-- Unlike the safe printf described in the Template Haskell
-- documentation, our format descriptors are first class.
-- They can be built incrementally. They can be used both
-- for printing and for parsing. Our printf and scanf are user-extensible:
-- library users can write functions to direct format output to any
-- suitable data sink, or to read parsed data from any suitable
-- data source.
-- Please see the examples in the file TFTest.hs.

module Text.TotalPrintF (spec, sprintf, sscanf, (^)) where

import Language.Haskell.TH
import Language.Haskell.TH.Syntax
import Language.Haskell.TH.Ppr
import Prelude hiding ((^))

import Text.PrintScanF			-- EDSL of format descriptors

-- | Primitive format descriptors used here
str :: (FormattingSpec repr) => repr w (String -> w)
str  = fpp (PrinterParser id parse)
 where
 parse s = Just $ break (== ' ') s	-- the behavior of %s in C

anys :: (FormattingSpec repr, Show a, Read a) => repr w (a -> w)
anys = fpp showread

-- | Converting from formatting strings to format descriptors
fdesc_to_code :: [FDesc] -> ExpQ
fdesc_to_code [d] = cnv1 d
fdesc_to_code (d:desc) = [e| $(cnv1 d) ^ $(fdesc_to_code desc)|]

cnv1 (FD_lit str) = [e| lit str|]
cnv1 FD_int       = [e| int  |]
cnv1 FD_str       = [e| str  |]
cnv1 FD_any       = [e| anys |]

spec :: String -> ExpQ
spec = fdesc_to_code . convert_to_fdesc

show_code cde = runQ cde >>= putStrLn . pprint

tc1 = show_code . spec $ "abc"
-- PrintScanF.lit ['a', 'b', 'c']

tc2 = show_code . spec $ "Hello %s!"
-- PrintScanF.lit "Hello " PrintScanF.^ 
--       (TotalPrintF.str PrintScanF.^ PrintScanF.lit ['!'])


-- A very simple language of format descriptors

data FDesc = FD_lit String | FD_str | FD_int | FD_any deriving (Eq, Show)

-- Convert "insert %s here" into 
-- [FD_lit "insert ", FD_str, FD_lit " here"]
convert_to_fdesc :: String -> [FDesc]
convert_to_fdesc str = 
    case break (=='%') str of
      (s1,"") -> make_lit s1
      (s1,'%':'s':rest) -> make_lit s1 ++ FD_str : convert_to_fdesc rest
      (s1,'%':'a':rest) -> make_lit s1 ++ FD_any : convert_to_fdesc rest
      (s1,'%':'d':rest) -> make_lit s1 ++ FD_int : convert_to_fdesc rest
      (_,s2) -> error $ "bad descriptor: " ++ take 5 s2
 where
 make_lit "" = []
 make_lit str = [FD_lit str]

test_cvf = and [
    convert_to_fdesc "Simple lit" ==
       [FD_lit "Simple lit"],
    convert_to_fdesc "%s insert" ==
       [FD_str,FD_lit " insert"],
    convert_to_fdesc "insert %s here" ==
    [FD_lit "insert ",FD_str,FD_lit " here"],
    convert_to_fdesc "The value of %s is %d" ==
    [FD_lit "The value of ",FD_str,FD_lit " is ",FD_int]
    ]
