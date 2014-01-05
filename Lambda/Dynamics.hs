{-# OPTIONS -W #-}
{-# LANGUAGE TypeFamilies, FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE NoMonomorphismRestriction #-}

-- | Philippe de Groote. 2010.  Dynamic logic: a type-theoretic view.
-- Talk slides at `Le modèle et l'algorithme', Rocquencourt.
-- <http://www.inria.fr/rocquencourt/rendez-vous/modele-et-algo/dynamic-logic-a-type-theoretic-view>
--

module Lambda.Dynamics where

import Lambda.Semantics
import Lambda.CFG
import Lambda.QCFG

-- | We extend the Lambda language with state (of the type State)
type State = [Entity]
class (Lambda lrepr) => States lrepr where
  update :: lrepr Entity -> lrepr State -> lrepr State
  select :: lrepr State -> lrepr Entity

-- | We correspondingly extend our R, C, P intrepreters of Lambda
instance States R where
  update (R x) (R e) = R (x:e)
  select (R (x:_))   = R x
  select (R [])      = error "who?"

instance States C where
  update (C x) (C e) = C (\i p -> paren (p > 5) (x i 6 ++ "::" ++ e i 5))
  select (C e)       = C (\i p -> paren (p > 10) ("sel " ++ e i 11))

instance (States lrepr) => States (P lrepr) where
  update (P x _) (P e _) = unknown (update x e)
  select (P e _)         = unknown (select e)

type family Dynamic (a :: *)
type instance Dynamic (a -> b) = Dynamic a -> Dynamic b
type instance Dynamic Entity   = Entity
type instance Dynamic Bool     = State -> (State -> Bool) -> Bool
data D c a = D { unD :: c (Dynamic a) }
instance (States c) => Lambda (D c) where
  app (D f) (D x)  = D (app f x)
  lam f            = D (lam (\x -> unD (f (D x))))
  john'            = D john'
  mary'            = D mary'
  like'            = D (dynamic (\_ -> like'))
  own'             = D (dynamic (\_ -> own'))
  farmer'          = D (dynamic (\_ -> farmer'))
  donkey'          = D (dynamic (\_ -> donkey'))
  true             = D (dynamic (\_ -> true))
  neg (D x)        = D (dynamic (\e -> neg (static x e)))
  conj (D x) (D y) = D (lam (\e -> lam (\phi -> app (app x e)
                       (lam (\e -> app (app y e) phi)))))
  exists           = D (lam (\p -> lam (\e -> lam (\phi -> app exists
                       (lam (\x -> app (app (app p x) (update x e)) phi))))))
instance Show (Sem (D C) S) where
  show = show . unSem
instance Show (Sem (D (P C)) S) where
  show = show . unSem
instance Show (D C Bool) where
  show (D x) = show x
instance Show (D (P C) Bool) where
  show (D x) = show x
class Predicate a where
  dynamic :: (Lambda lrepr) => (lrepr State -> lrepr a) -> lrepr (Dynamic a)
  static  :: (Lambda lrepr) => lrepr (Dynamic a) -> lrepr State -> lrepr a
instance Predicate Bool where
  dynamic f  = lam (\e -> lam (\phi -> conj (f e) (app phi e)))
  static x e = app (app x e) (lam (\_ -> true))
instance (Predicate a) => Predicate (Entity -> a) where
  dynamic f  = lam (\o -> dynamic (\e -> app (f e) o))
  static x e = lam (\o -> static (app x o) e)

class (Lambda lrepr) => Dynamics lrepr where
  it' :: lrepr ((Entity -> Bool) -> Bool)

instance (States lrepr) => Dynamics (D lrepr) where
  it' = D (lam (\p -> lam (\e -> lam (\phi ->
           app (app (app p (select e)) e) phi))))

instance Dynamics C where
  it' = C (\_ _ -> "it")

instance (Dynamics lrepr) => Dynamics (P lrepr) where
  it' = unknown it'

class (Quantifier repr) => Pronoun repr where
  it_ :: repr QNP

instance Pronoun EN where
  it_ = EN "it"

instance (Dynamics lrepr) => Pronoun (Sem lrepr) where
  it_ = Sem it'

sentence = r4 (every (who (r5 own (a donkey)) farmer)) (r5 like it_)
sentence_en   = sentence :: EN S
sentence_sem  = sentence :: Sem (D C) S
sentence_semp = sentence :: Sem (D (P C)) S
