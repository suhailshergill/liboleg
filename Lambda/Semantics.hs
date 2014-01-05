{-# OPTIONS -W #-}
{-# LANGUAGE TypeFamilies, FlexibleContexts, NoMonomorphismRestriction #-}

module Lambda.Semantics where

-- | Here we encode the "target language", the language
-- to express denotations (or, meanings)
-- Following Montague, our language for denotations
-- is essentially Church's "Simple Theory of Types"
-- also known as simply-typed lambda-calculus
-- It is a form of a higher-order predicate logic.
--
data Entity = John | Mary
  deriving (Eq, Show)

-- | We define the grammar of the target language the same way
-- we have defined the grammar for (source) fragment
--
class Lambda lrepr where
  john'  :: lrepr Entity
  mary'  :: lrepr Entity
  like'  :: lrepr (Entity -> Entity -> Bool)
  own'   :: lrepr (Entity -> Entity -> Bool)
  farmer':: lrepr (Entity -> Bool)
  donkey':: lrepr (Entity -> Bool)

  true   :: lrepr Bool
  neg    :: lrepr Bool -> lrepr Bool
  conj   :: lrepr Bool -> lrepr Bool -> lrepr Bool
  exists :: lrepr ((Entity -> Bool) -> Bool)

  app    :: lrepr (a -> b) -> lrepr a -> lrepr b
  lam    :: (lrepr a -> lrepr b) -> lrepr (a -> b)

-- Examples
lsen1 = neg (conj (neg (neg true)) (neg true))
lsen2 = lam (\x -> neg x) 
lsen3 = app (lam (\x -> neg x)) true

disj x y = neg (conj (neg x) (neg y))
-- disj true (neg true)
ldisj = lam (\x -> lam (\y -> disj x y))
lsen4  = disj true (neg true)
lsen4' = app (app ldisj true) (neg true)

lsen5 = app exists (lam (\x -> app (app like' mary') x))


-- | Syntactic sugar
exists_ r = lam (\p ->      app exists
                            (lam (\x -> conj (app r x)      (app p x) )) )
forall_ r = lam (\p -> neg (app exists
                            (lam (\x -> conj (app r x) (neg (app p x))))))
forall = forall_ (lam (\_ -> true))


-- | The first interpretation: evaluating in the world with John, Mary,
-- and Bool as truth values.
-- Lambda functions are interpreted as Haskell functions and Lambda
-- applications are interpreted as Haskell applications.
-- The interpreter R is metacircular (and so, efficient).
--
data R a = R { unR :: a }
instance Lambda R where
  john'                  = R John
  mary'                  = R Mary
  like'                  = R (\o s -> elem (s,o) [(John,Mary), (Mary,John)])
  own'                   = R (\o s -> elem (s,o) [(Mary,John)])
  farmer'                = R (\s -> s == Mary)
  donkey'                = R (\s -> s == John)

  true                   = R True
  neg (R True)           = R False
  neg (R False)          = R True
  conj (R True) (R True) = R True
  conj _        _        = R False
  exists                 = R (\f -> any f domain)

  app (R f) (R x)        = R (f x)
  lam f                  = R (\x -> unR (f (R x)))


domain = [John, Mary]

instance (Show a) => Show (R a) where
  show (R x) = show x


-- | "Running" the examples
lsen1_r = lsen1 :: R Bool
lsen2_r = lsen2 :: R (Bool -> Bool)
lsen3_r = lsen3 :: R Bool

ldisj_r  = ldisj  :: R (Bool -> Bool -> Bool)

lsen4_r  = lsen4  :: R Bool
lsen4'_r = lsen4' :: R Bool

lsen5_r = lsen5   :: R Bool

-- | We now interpret Lambda terms as Strings, so we can show
-- our formulas.
-- Actually, not quite strings: we need a bit of _context_:
-- the precedence and the number of variables already bound in the context.
-- The latter number lets us generate unique variable names.
--
data C a = C { unC :: Int -> Int -> String }
instance Lambda C where
  john'            = C (\_ _ -> "john'")
  mary'            = C (\_ _ -> "mary'")
  like'            = C (\_ _ -> "like'")
  own'             = C (\_ _ -> "own'")
  farmer'          = C (\_ _ -> "farmer'")
  donkey'          = C (\_ _ -> "donkey'")

  true             = C (\_ _ -> "T")
  neg (C x)        = C (\i p -> paren (p > 10) ("-" ++ x i 11))
  conj (C x) (C y) = C (\i p -> paren (p > 3) (x i 4 ++ " & " ++ y i 3))
  exists           = C (\_ _ -> "E")

  app (C f) (C x)  = C (\i p -> paren (p > 10) (f i 10 ++ " " ++ x i 11))
  lam f            = C (\i p -> let x    = "x" ++ show i
                                    body = unC (f (C (\_ _ -> x))) (i + 1) 0
                                in paren (p > 0) ("L" ++ x ++ ". " ++ body))

instance Show (C a) where
  show (C x) = x 1 0
paren True  text = "(" ++ text ++ ")"
paren False text = text

-- | We can now see the examples
--
lsen1_c = lsen1 :: C Bool
lsen2_c = lsen2 :: C (Bool -> Bool)
lsen3_c = lsen3 :: C Bool

ldisj_c  = ldisj  :: C (Bool -> Bool -> Bool)

-- | The displayed difference between lsen4 and lsen4'
-- shows that beta-redices have been reduced. NBE.
lsen4_c  = lsen4  :: C Bool
lsen4'_c = lsen4' :: C Bool

lsen5_c = lsen5   :: C Bool


-- | Normalizing the terms: performing the apparent redices
--
type family Known (lrepr :: * -> *) (a :: *)
type instance Known lrepr (a -> b) = P lrepr a -> P lrepr b
type instance Known lrepr Bool     = [lrepr Bool]
data P lrepr a = P { unP :: lrepr a, known :: Maybe (Known lrepr a) }

instance (Lambda lrepr) => Lambda (P lrepr) where
  john'                      = unknown john'
  mary'                      = unknown mary'
  like'                      = unknown like'
  own'                       = unknown own'
  farmer'                    = unknown farmer'
  donkey'                    = unknown donkey'

  true                       = P true (Just [])
  neg (P x _)                = unknown (neg x)
  conj x (P _ (Just []))     = x
  conj x y                   = let conjuncts (P _ (Just zs)) = zs
                                   conjuncts (P z Nothing) = [z]
                               in P (foldr conj (unP y) (conjuncts x))
                                    (Just (conjuncts x ++ conjuncts y))
  exists                     = unknown exists

  app (P _ (Just f)) x       = f x
  app (P f Nothing ) (P x _) = unknown (app f x)
  lam f                      = P (lam (\x -> unP (f (unknown x)))) (Just f)


instance (Show (lrepr a)) => Show (P lrepr a) where
  show (P x _) = show x
unknown x = P x Nothing

-- | Now we can see beautified terms
--
lsen1_pc = lsen1 :: (P C) Bool
lsen2_pc = lsen2 :: (P C) (Bool -> Bool)
lsen3_pc = lsen3 :: (P C) Bool

ldisj_pc  = ldisj  :: (P C) (Bool -> Bool -> Bool)

-- | There is no longer difference between lsen4 and lsen4'
lsen4_pc  = lsen4  :: (P C) Bool
lsen4'_pc = lsen4' :: (P C) Bool

lsen5_pc = lsen5   :: (P C) Bool
