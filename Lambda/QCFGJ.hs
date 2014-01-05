{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE TypeFamilies, FlexibleInstances #-}

-- | Interpreting a CFG derivation with quantifiers
-- as a string in Japanese.
-- That is, we generate a yield of a CFG derivation,
-- this time in Japanese.
--
module Lambda.QCFGJ where

import Lambda.QCFG                             -- we shall re-use our earlier work
import Lambda.CFGJ
import Lambda.CFG

-- | We extend our JA interpreter (interpreter of
-- derivations as Japanese phrases) to deal
-- with QNP.
--
type instance TJ CN = String

-- | Quantifiers get the high type
-- In fact, the same type as TJ NP
--
type instance TJ QNP = Case -> SK

-- | The expression for quantifiers ensures that no
-- inverse reading is possible. Only linear reading.
instance Quantifier JA where
  farmer            = JA "農家"
  donkey            = JA "ロバ"

--  every (JA n)      = JA (\cas k -> k ("どの" ++ n ++ "も"))
  every (JA n)      = JA (\cas k -> k (n ++ case_particle cas ++ "みな"))
  a     (JA n)      = JA (\cas k -> k ("ある" ++ n ++ case_particle cas))
  who (JA vp) (JA n) = JA (vp (\cas k -> k "") ++ n)

  everyone = JA (\cas k -> "みんな" ++ case_particle cas ++ k "")
  someone  = JA (\cas k -> "ある人" ++ case_particle cas ++ k "")
  r5 (JA f) (JA x) = JA (f x) -- the same as r2
  r4 (JA x) (JA f) = JA (f x) -- the same as r1

-- | We can now see the English sentences that
-- correspond to the derivations sen2-sen5 in
-- QCFG.hs
sen2_ja = sen2 :: JA S
sen3_ja = sen3 :: JA S
sen4_ja = sen4 :: JA S
sen5_ja = sen5 :: JA S

