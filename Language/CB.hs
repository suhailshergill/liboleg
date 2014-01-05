{-# LANGUAGE TypeFamilies, EmptyDataDecls, TypeOperators #-}
{-# LANGUAGE FlexibleInstances #-}

-- | Embedding a higher-order domain-specific language (simply-typed
-- lambda-calculus with constants) with a selectable evaluation order:
-- Call-by-value, call-by-name, call-by-need in the same Final Tagless framework
--
-- <http://okmij.org/ftp/tagless-final/tagless-typed.html#call-by-any>
--

module Language.CB where

import Data.IORef
import Control.Monad
import Control.Monad.Trans

-- | Our EDSL is typed. EDSL types are built from the following two
-- type constructors:
data IntT
data a :-> b
infixr 5 :->

-- | We could have used Haskell's type Int and the arrow -> constructor.
-- We would like to emphasize however that EDSL types need not be identical
-- to the host language types. To give the type system to EDSL, we merely
-- need `labels' -- which is what IntT and :-> are
--
-- The (higher-order abstract) syntax of our DSL
class EDSL exp where
     lam :: (exp a -> exp b) -> exp (a :-> b)
     app :: exp (a :-> b) -> exp a -> exp b

     int :: Int -> exp IntT		-- Integer literal
     add :: exp IntT -> exp IntT -> exp IntT
     sub :: exp IntT -> exp IntT -> exp IntT

-- | A convenient abbreviation
let_ :: EDSL exp => exp a -> (exp a -> exp b) -> exp b
let_ x y = (lam y) `app` x

-- | A sample EDSL term
t :: EDSL exp => exp IntT
t = (lam $ \x -> let_ (x `add` x)
                      $ \y -> y `add` y) `app` int 10


-- | Interpretation of EDSL types as host language types
-- The type interpretation function Sem is parameterized by 'm',
-- which is assumed to be a Monad.
type family Sem (m :: * -> *) a :: *
type instance Sem m IntT      = Int
type instance Sem m (a :-> b) = m (Sem m a) -> m (Sem m b)

-- | Interpretation of EDSL expressions as values of the host language (Haskell)
-- An EDSL expression of the type a is interpreted as a Haskell value
-- of the type S l m a, where m is a Monad (the parameter of the interpretation)
-- and l is the label for the evaluation order (one of Name, Value, or Lazy).
-- (S l m) is not quite a monad -- only up to the Sem interpretation
newtype S l m a = S { unS :: m (Sem m a) }




-- | Call-by-name
--
data Name
instance MonadIO m => EDSL (S Name m) where
  int = S . return
  add x y = S $ do a <- unS x
                   b <- unS y
                   liftIO $ putStrLn "Adding"
                   return (a + b)
  sub x y = S $ do a <- unS x
                   b <- unS y
                   liftIO $ putStrLn "Subtracting"
                   return (a - b)
  lam f   = S . return $ (unS . f . S)
  app x y = S $ unS x >>= ($ (unS y))


-- Tests
runName :: S Name m a -> m (Sem m a)
runName x = unS x

-- | Evaluating:
--
-- > t = (lam $ \x -> let_ (x `add` x)
-- >                      $ \y -> y `add` y) `app` int 10
--
-- The addition (x `add` x) is performed twice because y is bound
-- to a computation, and y is evaluated twice
t0SN = runName t >>= print
{-
Adding
Adding
Adding
40
-}

-- A more elaborate example
t1 :: EDSL exp => exp IntT
t1 = (lam $ \x -> let_ (x `add` x) 
                  $ \y -> lam $ \z -> 
                  z `add` (z `add` (y `add` y))) `app` (int 10 `sub` int 5) 
                                                 `app` (int 20 `sub` int 10)

t1SN = runName t1 >>= print
{-
*CB> t1SN
Subtracting
Subtracting
Subtracting
Subtracting
Adding
Subtracting
Subtracting

Adding
Adding
Adding
Adding
40
-}

-- | A better example
t2 :: EDSL exp => exp IntT
t2 = (lam $ \z -> lam $ \x -> let_ (x `add` x)
                              $ \y -> y `add` y) 
     `app` (int 100 `sub` int 10)
     `app` (int 5 `add` int 5)

-- | The result of subtraction was not needed, and so it was not performed
-- | OTH, (int 5 `add` int 5) was computed four times
t2SN = runName t2 >>= print
{-
*CB> t2SN
Adding
Adding
Adding
Adding
Adding
Adding
Adding
40
-}

-- Call-by-value

data Value

-- | We reuse most of EDSL (S Name) except for lam
vn :: S Value m x -> S Name m x
vn = S . unS
nv :: S Name m x -> S Value m x
nv = S . unS

instance MonadIO m => EDSL (S Value m) where
    int = nv . int
    add x y = nv $ add (vn x) (vn y)
    sub x y = nv $ sub (vn x) (vn y)
    app x y = nv $ app (vn x) (vn y)
    -- This is the only difference between CBN and CBV:
    -- lam first evaluates its argument, no matter what
    -- This is the definition of CBV after all
    lam f   = S . return $ (\x -> x >>= unS . f . S . return)

runValue :: S Value m a -> m (Sem m a)
runValue x = unS x

-- We now evaluate the previously written tests t, t1, t2
-- under the new interpretation

t0SV = runValue t >>= print
{-
*CB> t0SV
Adding
Adding
40
-}

t1SV = runValue t1 >>= print
{-
*CB> t1SV
Subtracting
Adding
Subtracting
Adding
Adding
Adding
40
-}

-- Although the result of subs-traction was not needed, it was still performed
-- OTH, (int 5 `add` int 5) was computed only once
t2SV = runValue t2 >>= print
{-
*CB> t2SV
Subtracting
Adding
Adding
Adding
40
-}

-- Call-by-need

share :: MonadIO m => m a -> m (m a)
share m = do
	  r <- liftIO $ newIORef (False,m)
	  let ac = do
		   (f,m) <- liftIO $ readIORef r
		   if f then m
		      else do
			   v <- m
			   liftIO $ writeIORef r (True,return v)
			   return v
	  return ac

data Lazy

-- | We reuse most of EDSL (S Name) except for lam
ln :: S Lazy m x -> S Name m x
ln = S . unS
nl :: S Name m x -> S Lazy m x
nl = S . unS

instance MonadIO m => EDSL (S Lazy m) where
    int = nl . int
    add x y = nl $ add (ln x) (ln y)
    sub x y = nl $ sub (ln x) (ln y)
    app x y = nl $ app (ln x) (ln y)
    -- This is the only difference between CBN and CBNeed
    -- lam shares its argument, no matter what
    -- This is the definition of CBNeed after all
    lam f           = S . return $ (\x -> share x >>= unS . f . S)


runLazy :: S Lazy m a -> m (Sem m a)
runLazy x = unS x

-- We now evaluate the previously written tests t, t1, t2
-- under the new interpretation

-- | Here, Lazy is just as efficient as CBV
t0SL = runLazy t  >>= print
{-
*CB> t0SL
Adding
Adding
40
-}

-- | Ditto
t1SL = runLazy t1 >>= print
{-
*CB> t1SL
Subtracting
Subtracting
Adding
Adding
Adding
Adding
40
-}

-- | Now, Lazy is better than both CBN and CBV: subtraction was not needed,
-- and it was not performed.
-- All other expressions were needed, and evaluated once.
t2SL = runLazy t2 >>= print
{-
*CB> t2SL
Adding
Adding
Adding
40
-}
