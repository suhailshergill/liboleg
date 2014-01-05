{-# LANGUAGE EmptyDataDecls, NoMonomorphismRestriction #-}
{-# LANGUAGE TypeFamilies #-}

-- | Context-free grammar with quantifiers
--
-- We extend CFG.hs to add quantified noun phrases
-- in the tradition of Montague
--
module Lambda.QCFG where

import Lambda.Semantics
import Lambda.CFG                              -- we shall re-use our earlier work

-- | Additional syntactic categories
--
data CN                                 -- Common noun
data QNP                                -- Quantified noun phrase

-- | We extend our earlier fragment with common nouns farmer and donkey,
-- and quantifiers everyone, someone, every farmer, a donkey, etc.
-- Since we added two new categories (CN and QNP), we need to add rules
-- to our CFG to be able to use the categories in derivations.
--
-- The numbers 4 and 5 are due to Montague
class (Symantics repr) => Quantifier repr where
  farmer   :: repr CN
  donkey   :: repr CN
  everyone :: repr QNP
  someone  :: repr QNP
  every    :: repr CN -> repr QNP
  a        :: repr CN -> repr QNP
  who      :: repr VP -> repr CN -> repr CN
  r5       :: repr TV -> repr QNP -> repr VP
  r4       :: repr QNP -> repr VP -> repr S

-- | Sample sentences (or, CFG derivations)
-- We stress that the inferred type of sen2-sen4
-- is S. So, these are the derivations of
-- complete sentences.
sen2 = r4 everyone (r2 like mary)

sen3 = r1 john (r5 like someone)

sen4 = r4 everyone (r5 like someone)

sen5 = r4 (every (who (r5 own (a donkey)) farmer)) (r5 like (a donkey))

-- | We extend our EN interpreter (interpreter of
-- derivations as English phrases) to deal
-- with QNP.
instance Quantifier EN where
  farmer            = EN "farmer"
  donkey            = EN "donkey"
  everyone          = EN "everyone"
  someone           = EN "someone"
  every (EN n)      = EN ("every " ++ n)
  a     (EN n)      = EN ("a " ++ n)
  who (EN r) (EN q) = EN (q ++ " who " ++ r)
  r5 (EN f) (EN x)  = EN (f ++ " " ++ x)
  r4 (EN x) (EN f)  = EN (x ++ " " ++ f)

-- | We can now see the English sentences that
-- correspond to the derivations sen2-sen4.
sen2_en = sen2 :: EN S
sen3_en = sen3 :: EN S
sen4_en = sen4 :: EN S
sen5_en = sen5 :: EN S

-- | We also extend the semantics interpreter:
-- the interpreter of a derivation into a
-- formula of STT, or Lambda-calculus.
--
-- We add the interpretation of the categories CN and QNP,
-- following Montague
type instance Tr CN  = Entity -> Bool
type instance Tr QNP = (Entity -> Bool) -> Bool

instance (Lambda lrepr) => Quantifier (Sem lrepr) where
  farmer                = Sem farmer'
  donkey                = Sem donkey'
  everyone              = Sem forall
  someone               = Sem exists
  every (Sem cn)        = Sem (forall_ cn)
  a     (Sem cn)        = Sem (exists_ cn)
  who (Sem r) (Sem q)   = Sem (lam (\x -> conj (app q x) (app r x)))
  r5 (Sem tv) (Sem qnp) = Sem (lam (\s -> app qnp
                              (lam (\o -> app (app tv o) s))))
  r4 (Sem qnp) (Sem vp) = Sem (app qnp vp)

-- | We can see the semantic yield of our derivations,
-- but the formulas are not reduced!
--
sen2_sem = sen2 :: Sem C S
sen3_sem = sen3 :: Sem C S
sen4_sem = sen4 :: Sem C S
sen5_sem = sen5 :: Sem C S

-- | the shown result of sen3_sem is a formula with 
-- an apparent beta-redex. The formula can be simplified
-- (reduced) so it reads better. That's why we need the
-- partial evaluator.
sen3_semp = sen3 :: Sem (P C) S
sen5_semp = sen5 :: Sem (P C) S

-- The shown result of sen4_sem shows the linear reading
-- (linear reading) of the quantifiers?
-- How to get an inverse reading? Montague shown
-- a general approach: see QHCFG.hs
