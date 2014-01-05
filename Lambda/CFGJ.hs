{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE TypeFamilies, FlexibleInstances #-}

-- | Interpreting a CFG derivation as a string in Japanese.
-- That is, we generate a yield of a CFG derivation,
-- this time in Japanese.
--
-- <http://okmij.org/ftp/gengo/NASSLLI10/>
--
module Lambda.CFGJ where

import Lambda.CFG				-- we shall re-use our earlier work

-- | We represent each node in the derivation tree
-- by a Japanese phrase or a Japanese "sentential form"
-- (that is, a phrase with holes). Contrast with the EN
-- interpreter in CFG.hs
--
data JA a = JA { unJA :: TJ a }

-- | A verb or a verb-like word (e.g., an i-adjective) require
-- arguments of particular cases. We need a way for a verb
-- to specify the desired case of its arguments.
--
data Case = Nom | NomStrong | Acc
case_particle :: Case -> String
case_particle Nom       = "は"
case_particle NomStrong = "のことが"
case_particle Acc       = "を"


-- | The type family TJ defines the types of
-- sentential forms corresponding to syntactic categories.
--
-- As we shall see in QCFGJ.hs, we are going to need
-- high (raised) types of our NP. 
-- A verb will ask its argument to turn itself to the
-- desired case.
type SK = (String -> String) -> String

type family TJ (a :: *) :: *
type instance TJ S = String
type instance TJ NP = Case -> SK
type instance TJ VP = (Case -> SK) -> String
type instance TJ TV = (Case -> SK) -> (Case -> SK) -> String

-- | Auxiliary functions for the code below
make_np :: String -> (Case -> SK)
make_np str cas k = k (str ++ case_particle cas)

make_tv :: String -> Case -> Case -> (Case -> SK) -> (Case -> SK) -> String
make_tv str co cs o s =
    s cs (\sv -> o co (\ov -> sv ++ ov ++ str))

instance Symantics JA where
  john             = JA (make_np "ジョンさん")
  mary             = JA (make_np "メリさん")
  like             = JA (make_tv "好きだ" NomStrong Nom)
  own              = JA (make_tv "飼っている" Acc Nom)
  r2 (JA f) (JA x) = JA (f x)
  r1 (JA x) (JA f) = JA (f x)

instance Show (JA S) where
  show = unJA

-- | The translation is certainly different: "like" corresponds
-- to an adjective in Japanese.
sen1_ja = sen1 :: JA S
