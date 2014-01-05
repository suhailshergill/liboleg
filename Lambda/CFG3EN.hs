{-# LANGUAGE EmptyDataDecls #-}

-- | Introducing type constants
--
-- We wish to outlaw terms such as bad_sentence in CFG2EN.hs,
-- even though there may be an interpretation that accepts
-- these bad terms.
-- We really wish our terms represent all and only
-- valid CFG derivations. We accomplish this goal here.
-- Our approach is reminiscent of LCF.

module Lambda.CFG3EN where

data S                                  -- clause
data NP                                 -- noun phrase
data VP                                 -- verb phrase
data TV                                 -- transitive verb

-- | Parameterized types: cf notation:
--
-- > <string,features> in
--
-- the Minimalist Grammar
--
data EN a = EN { unEN :: String }

-- | One may think of the above data declaration as defining an
-- isomorphism between EN values and Strings. The functions
-- EN and unEN (what is their type?) witness the isomorphism.
-- It helps to look at their composition.
--
--
john, mary :: EN NP
like       :: EN TV
r2         :: EN TV -> EN NP -> EN VP
r1         :: EN NP -> EN VP -> EN S

john             = EN "John"
mary             = EN "Mary"
like             = EN "likes"
r2 (EN f) (EN x) = EN (f ++ " " ++ x)
r1 (EN x) (EN f) = EN (x ++ " " ++ f)

instance Show (EN a) where
  show = unEN

sentence :: EN S
sentence = r1 john (r2 like mary)

-- Now the bad_sentence is rejected already in
-- the EN interpretation, in contrast to CFG2EN.hs.
-- The type error message clearly describes the error,
-- in the CFG terms.
-- bad_sentence = r2 (r2 like mary) john
