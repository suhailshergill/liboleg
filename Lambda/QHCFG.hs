{-# LANGUAGE EmptyDataDecls, NoMonomorphismRestriction #-}
{-# LANGUAGE TypeFamilies #-}

-- | Context-free grammar with quantifiers
-- A different ways to add quantification, via 
-- Higher-Order abstract syntax (HOAS).
-- This is a "rational reconstruction" of Montague's
-- general approach of `administrative pronouns', which
-- later gave rise to the Quantifier Raising (QR)
--
module Lambda.QHCFG where

import Lambda.Semantics
import Lambda.CFG                               -- we shall re-use our earlier work

-- | No longer any need in a new syntactic category QNP
-- We leave out CN as an exercise
--
-- > data CN                                      -- Common noun
--
-- We extend our earlier fragment with quantifiers everyone, someone.
-- In contrast to QCFG.hs, we do not add any new syntactic category,
-- so we don't need to add any rules to our CFG.
--
class (Symantics repr) => Quantifier repr where
  everyone :: (repr NP -> repr S) -> repr S
  someone  :: (repr NP -> repr S) -> repr S

-- | Sample sentences (or, CFG derivations):
-- compare with those in QCFG.hs
-- We stress that the inferred type of sen2-sen4
-- is S. So, these are the derivations of
-- complete sentences.
--
sen2 = everyone (\he -> r1 he (r2 like mary))

sen3 = someone (\she -> r1 john (r2 like she))

sen4 = everyone (\he -> someone (\she -> r1 he (r2 like she)))

-- | We extend our EN interpreter (interpreter of
-- derivations as English phrases) to deal
-- with quantifiers.
--
instance Quantifier EN where
  everyone     f = f (EN "everyone")
  someone      f = f (EN "someone")

-- | We can now see the English sentences that
-- correspond to the derivations sen2-sen4.
sen2_en = sen2 :: EN S
sen3_en = sen3 :: EN S
sen4_en = sen4 :: EN S

-- | We also extend the semantics interpreter:
-- the interpreter of a derivation into a
-- formula of STT, or Lambda-calculus.
-- We reconstruct Montague's ``pronoun trick''
instance (Lambda lrepr) => Quantifier (Sem lrepr) where
  everyone       f = Sem (app forall       (lam (\he  -> unSem (f (Sem he)))))
  someone        f = Sem (app exists       (lam (\she -> unSem (f (Sem she)))))

-- | We can see the semantic yield of our derivations
sen2_sem = sen2 :: Sem (P C) S  -- We encode universal via existential
sen3_sem = sen3 :: Sem C S -- now reduced!
sen4_sem = sen4 :: Sem (P C) S

-- | As in QCFG.hs, sen4_sem demonstrates the linear reading.
-- Now however we can get the inverse reading of the phrase.
--
-- We build the following derivation
sen4' = someone (\she -> everyone (\he -> r1 he (r2 like she)))

-- | which corresponds to the same English phrase
sen4'_en = sen4' :: EN S
-- everyone likes someone

-- | The semantics shows the inverse reading
sen4'_sem = sen4' :: Sem (P C) S

