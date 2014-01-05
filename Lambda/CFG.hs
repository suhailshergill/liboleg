{-# LANGUAGE EmptyDataDecls, NoMonomorphismRestriction #-}
{-# LANGUAGE TypeFamilies, FlexibleInstances #-}

-- | Context-free grammars, in the tagless-final style
--
-- <http://okmij.org/ftp/gengo/NASSLLI10/>
--
module Lambda.CFG where

import Lambda.Semantics

-- | Syntactic categories: non-terminals of CFG
--
data S                                  -- clause
data NP                                 -- noun phrase
data VP                                 -- verb phrase
data TV                                 -- transitive verb

-- | This class defines the syntax of our fragment (the grammar,
-- essentially). Its instances will show interpretations
-- of the grammar, or `semantics'
--
-- The names r1, r2, etc. are the labels of CFG rules.
-- These names are evocative of Montague
--
class Symantics repr where
  john :: repr NP
  mary :: repr NP
  like :: repr TV
  own  :: repr TV
  r2   :: repr TV -> repr NP -> repr VP
  r1   :: repr NP -> repr VP -> repr S

-- | show the inferred types, as well as the inferred types for
-- the phrases like
phrase1 = r2 like mary
{-
*CFG> :t phrase1
phrase1 :: (Symantics repr) => repr VP
-}

-- show the type errors from 
{-
err1 = r1 like mary
    Couldn't match expected type `NP' against inferred type `TV'
      Expected type: repr NP
      Inferred type: repr TV
    In the first argument of `r1', namely `like'
    In the expression: r1 like mary
-}

-- | The first sample sentence, or CFG derivation
-- The inferred type is S. So, sen1 is a derivations of
-- a complete sentence.
--
sen1 = r1 john (r2 like mary)

-- | We now define the first interpretation of a CFG derivations:
-- We interpret the derivation to give the parsed string.
-- That is, we generate a yield of a CFG derivation,
-- in English.
--
-- We represent each node in the derivation tree
-- by an English phrase
data EN a = EN { unEN :: String }

instance Symantics EN where
  john             = EN "John"
  mary             = EN "Mary"
  like             = EN "likes"
  own              = EN "owns"
  r2 (EN f) (EN x) = EN (f ++ " " ++ x)
  r1 (EN x) (EN f) = EN (x ++ " " ++ f)

instance Show (EN a) where
  show = unEN

-- | Show the English form of sen1
sen1_en = sen1 :: EN S

-- | We now define semantics of a phrase represented
-- by a derivation. It is a different interpretation
-- of the phrase and its types.
--
-- We first interpret syntactic types (NP, VP, etc)
-- in terms of the types of the language of
-- logic formulas. 
-- The type class Lambda defines the language
-- of logic formulas (STT, or higher-order logic)
-- with types Entity, Bool, and the arrows.
--
type family Tr (a :: *) :: *
type instance Tr S  = Bool
type instance Tr NP = Entity
type instance Tr VP = Entity -> Bool
type instance Tr TV = Entity -> Entity -> Bool

data Sem lrepr a = Sem { unSem :: lrepr (Tr a) }

instance (Lambda lrepr) => Symantics (Sem lrepr) where
  john               = Sem john'
  mary               = Sem mary'
  like               = Sem like'
  own                = Sem own'
  r2 (Sem f) (Sem x) = Sem (app f x)
  r1 (Sem x) (Sem f) = Sem (app f x)

instance Show (Sem C a) where
  show (Sem x) = show x

instance Show (Sem (P C) a) where
  show (Sem x) = show x

-- | We can now see the semantics of sen1
sen1_sem = sen1 :: Sem C S

