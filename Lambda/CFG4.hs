{-# LANGUAGE EmptyDataDecls, NoMonomorphismRestriction #-}
{-# LANGUAGE TypeFamilies, FlexibleInstances #-}

-- | Unifying syntax with semantics
--
module Lambda.CFG4 where

data S                                  -- clause
data NP                                 -- noun phrase
data VP                                 -- verb phrase
data TV                                 -- transitive verb

class Symantics repr where
  john, mary :: repr NP
  like       :: repr TV
  r2         :: repr TV -> repr NP -> repr VP
  r1         :: repr NP -> repr VP -> repr S

sentence = r1 john (r2 like mary)

data EN a = EN { unEN :: String }

instance Symantics EN where
  john             = EN "John"
  mary             = EN "Mary"
  like             = EN "likes"
  r2 (EN f) (EN x) = EN (f ++ " " ++ x)
  r1 (EN x) (EN f) = EN (x ++ " " ++ f)

instance Show (EN a) where
  show = unEN

sentence_en = sentence :: EN S

type family Tr (a :: *) :: *
type instance Tr S  = Bool
type instance Tr NP = Entity
type instance Tr VP = Entity -> Bool
type instance Tr TV = Entity -> Entity -> Bool

data Sem a = Sem { unSem :: Tr a }

data Entity = John | Mary
  deriving (Eq, Show)

instance Symantics Sem where
  john               = Sem John
  mary               = Sem Mary
  like               = Sem (\o s -> elem (s,o) [(John,Mary), (Mary,John)])
  r2 (Sem f) (Sem x) = Sem (f x)
  r1 (Sem x) (Sem f) = Sem (f x)

instance Show (Sem S) where
  show (Sem x) = show x

sentence_sem = sentence :: Sem S
