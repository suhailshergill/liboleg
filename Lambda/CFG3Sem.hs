{-# LANGUAGE EmptyDataDecls, FlexibleInstances, TypeFamilies #-}

-- | Type functions: interpretations of the type constants
--
-- <http://okmij.org/ftp/gengo/NASSLLI10/>
--

module Lambda.CFG3Sem where

data S                                  -- clause
data NP                                 -- noun phrase
data VP                                 -- verb phrase
data TV                                 -- transitive verb

type family Tr (a :: *) :: *
type instance Tr S  = Bool
type instance Tr NP = Entity
type instance Tr VP = Entity -> Bool
type instance Tr TV = Entity -> Entity -> Bool

data Sem a = Sem { unSem :: Tr a }

data Entity = John | Mary
  deriving (Eq, Show)

john, mary :: Sem NP
like       :: Sem TV
r2         :: Sem TV -> Sem NP -> Sem VP
r1         :: Sem NP -> Sem VP -> Sem S

john               = Sem John
mary               = Sem Mary
like               = Sem (\o s -> elem (s,o) [(John,Mary), (Mary,John)])
r2 (Sem f) (Sem x) = Sem (f x)
r1 (Sem x) (Sem f) = Sem (f x)

instance Show (Sem S) where
  show (Sem x) = show x

sentence :: Sem S
sentence = r1 john (r2 like mary)

-- How to tell if the result of evaluating the sentence 
-- shows that John likes Mary or that Mary likes John?
-- We could trace the evaluation.
-- A better idea is to display the denotation as a formula
-- rather than as its value in one particular world.
