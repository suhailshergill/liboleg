{-# LANGUAGE TypeOperators, EmptyDataDecls, NoMonomorphismRestriction #-}
{-# LANGUAGE TypeFamilies, FlexibleInstances #-}

-- | Combinatorial Categorical Grammar (CCG)
--
-- <http://okmij.org/ftp/gengo/NASSLLI10>
--

module Lambda.CCG where

import Prelude hiding ((/))

import Lambda.Semantics

-- Abstract and concrete syntax

-- | Syntactic categories: non-terminals of CCG
--
data S                                  -- clause
data NP                                 -- noun phrase
data b :/ a
data b :\\ a

-- | This class defines the syntax of our fragment (the grammar,
-- essentially). Its instances will show interpretations
-- of the grammar, or `semantics'
--
class Symantics repr where
    john :: repr NP
    mary :: repr NP
    like :: repr ((NP :\\ S) :/ NP)
    (/)   :: repr (b :/ a) -> repr a -> repr b
    (\\)  :: repr a -> repr (a :\\ b) -> repr b

-- | show the inferred types, as well as the inferred types for
-- phrases like
phrase1 = like / mary
-- phrase1 :: (Symantics repr) => repr (S :\\ NP)

-- show the type errors from like \\ mary
{-
err1 = like \\ mary

    Couldn't match expected type `b :\\ (NP :/ (S :\\ NP))'
           against inferred type `NP'
      Expected type: repr (b :\\ (NP :/ (S :\\ NP)))
      Inferred type: repr NP
    In the second argument of `(\\)', namely `mary'
    In the expression: like \\ mary
-}



-- | The first sample sentence, or CCG derivation
-- The inferred type is S. So, sen1 is a derivations of
-- a complete sentence.
sen1 = john \\ (like / mary)

-- | We now define the first interpretation of a CCG derivations:
-- We interpret the derivation to give the parsed string.
-- That is, we generate a yield of a CCG derivation,
-- in English.
--
-- We represent each node in the derivation tree
-- by an English phrase
data EN a = EN{unEN:: String}

instance Symantics EN where
    john             = EN "John"
    mary             = EN "Mary"
    like             = EN "likes"
    (EN f) /  (EN x) = EN (f ++ " " ++ x)
    (EN x) \\ (EN f) = EN (x ++ " " ++ f)

instance Show (EN a) where
  show = unEN

-- | Show the English form of sen1
sen1_en = sen1 :: EN S

-- Try phonetic (using IPA)

-- | We now define semantics of a phrase represented
-- by a derivation. It is a different interpretation
-- of the phrase and its types.
--
-- We first interpret syntactic types (NP, slashes, etc)
-- in terms of the types of the language of
-- logic formulas. 
-- The type class Lambda defines the language
-- of logic formulas (STT, or higher-order logic)
-- with types Entity, Bool, and the arrows.
--
type family Tr (synt :: *) :: *
type instance Tr S  = Bool
type instance Tr NP = Entity
type instance Tr (b :/ a)  = Tr a -> Tr b
type instance Tr (a :\\ b) = Tr a -> Tr b

data Sem lrepr a = Sem { unSem :: lrepr (Tr a) }

instance (Lambda lrepr) => Symantics (Sem lrepr) where
  john               = Sem john'
  mary               = Sem mary'
  like               = Sem like'
  (Sem f) /  (Sem x) = Sem (app f x)
  (Sem x) \\ (Sem f) = Sem (app f x)

instance Show (Sem C a) where
  show (Sem x) = show x

instance Show (Sem (P C) a) where
  show (Sem x) = show x

-- | We can now see the semantics of sen1
sen1_sem = sen1 :: Sem C S

-- | Computing the yield in Japanese
--
-- The type family TJ defines the types of
-- sentential forms corresponding to syntactic categories.
--
-- We represent each node in the derivation tree
-- by a Japanese phrase or a Japanese "sentential form"
-- (that is, a phrase with holes). Contrast with the EN
-- interpreter above.
--
data JA a = JA { unJA :: TJ a }

type family TJ (a :: *) :: *
type instance TJ S  = String
type instance TJ NP = String
type instance TJ (b :/ a)  = TJ a -> TJ b
type instance TJ (a :\\ b) = TJ a -> TJ b

-- | The following works but is unsatisfactory: we wish
-- slashes to be interpreted only as concatenation!
instance Symantics JA where
    john = JA "ジョンさん"
    mary = JA "メリさん"
    like = JA (\o s -> s ++ "は" ++ o ++ "のことが" ++ "好きだ")
    (JA f) /  (JA x) = JA (f x)
    (JA x) \\ (JA f) = JA (f x)

instance Show (JA S) where
  show = unJA

-- | The translation is certainly different: "like" corresponds
-- to an adjective in Japanese.
sen1_ja = sen1 :: JA S


-- | Adding quantification; one way
--
type QNP = (S :/ (NP :\\ S))            -- Quantified noun phrase

-- | We extend our earlier fragment with quantifiers everyone, someone
-- We also add a combinator for raising the first argument of a TV
--
class (Symantics repr) => Quantifier repr where
    everyone :: repr QNP
    someone  :: repr QNP
    lift_vt  :: repr ((NP :\\ S) :/ NP) -> repr ((NP :\\ S) :/ QNP)

sen2 = everyone / (like / mary)
-- sen2 :: (Quantifier repr) => repr S

-- | But how to put a quantifier in an object position?
sen3 = john \\ ((lift_vt like) / someone)

sen4 = everyone / ((lift_vt like) / someone)

instance Quantifier EN where
    everyone        = EN "everyone"
    someone         = EN "someone"
    lift_vt  (EN f) = EN f


sen2_en = sen2 :: EN S

sen3_en = sen3 :: EN S

sen4_en = sen4 :: EN S

instance (Lambda lrepr) => Quantifier (Sem lrepr) where
    everyone           = Sem forall
    someone            = Sem exists
    lift_vt (Sem verb) = Sem (lam (\q -> lam (\s -> 
                              app q (lam $ \obj -> app (app verb obj) s))))

sen2_sem = sen2 :: Sem C S              -- The result is not normalized
sen3_sem = sen3 :: Sem C S
sen4_sem = sen4 :: Sem C S

sen2_semp = sen2 :: Sem (P C) S         -- We need normalization
sen3_semp = sen3 :: Sem (P C) S
sen4_semp = sen4 :: Sem (P C) S


-- | Japanese is challenging: like semantics
--
-- The expression for quantifiers ensures that no
-- inverse reading is possible. Only linear reading.
instance Quantifier JA where
    everyone          = JA (\k -> k "みんな")
    someone           = JA (\k -> k "ある人")
    lift_vt (JA verb) = JA (\q s -> q (\obj -> verb obj s))

sen2_ja = sen2 :: JA S
sen3_ja = sen3 :: JA S
sen4_ja = sen4 :: JA S
