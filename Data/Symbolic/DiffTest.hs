{-# OPTIONS -fglasgow-exts #-}
{-# LANGUAGE TemplateHaskell #-} 

-- | Running the splicing tests from Diff.hs.
-- Due to the TH requirement, this code must be in a separate module.
--
module Data.Symbolic.DiffTest where

import Data.Symbolic.Diff
import Data.Symbolic.TypedCode

testrf1 = $(reflectQC testf1')

test1' = $(reflectQC test1r) 2.0
test1ds' = $(reflectQC test1ds) 2.0

test2dn = $(reflectQC (diff_fn test2f)) (4::Float)
-- 10.0

test11dn = $(reflectQC (diff_fn test11f)) (4::Float)
-- 5.0

test5dn = $(reflectQC (diff_fn test5f)) (pi::Float)
-- 3.171623e-2, approx sin(1/pi)/pi/pi
-- approx, because: cos(5*(pi::Float) + pi/2) isn't exactly 0

-- | partial derivative with respect to x
test4xdn = $(reflectQC (test4x 1)) (2::Float)
-- 21.0

-- | partial derivative with respect to y
test4ydn = $(reflectQC (test4y 5)) (5::Float)
-- -5.0
