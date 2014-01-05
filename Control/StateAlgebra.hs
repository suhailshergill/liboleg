{-# OPTIONS -fglasgow-exts #-}
{-# LANGUAGE UndecidableInstances #-}

-- | Implementing the State Monad as a term algebra
--
-- <http://okmij.org/ftp/Haskell/types.html#state-algebra>
--
module Control.StateAlgebra where

import Control.Monad
import Control.Monad.State hiding (runState)

-- | Monadic actions are terms composed from the following constructors
--
data Bind t f   = Bind t f
data Return v   = Return v
data Get        = Get
data Put v      = Put v

-- | examples of terms
term1 = (Return True) `Bind` Put
term2 = Get `Bind` (\v -> Put (not v) `Bind` (\() -> Return v))

-- | An example of an ill-formed term
term_ill1 = Get `Bind` Get
-- | An example of an ill-typed term
-- The following term is ill-typed because it attempts to store both
-- a boolean and a character in the state. Our state can have only one type.
term_ill2 = Put True `Bind` (\() -> Put 'a')


-- | The interpreter of monadic actions
-- It takes the term 't' and the initial state of the type 's'
-- and returns the final state and the resulting value. The type
-- of the result, 'a', is uniquely determined by the term and the state
--
class RunBind t s a => RunState t s a | t s -> a where
    runst :: t -> s -> (s,a)


instance RunState (Return a) s a where
    runst (Return a) s = (s,a)
instance RunState Get s s where
    runst _ s = (s,s)
instance RunState (Put s) s () where
    runst (Put s) _ = (s,())
instance (RunState m s a, RunState t s b)
    => RunState (Bind m (a->t)) s b where
    runst (Bind m k) s = runbind m k s

-- | Interpretation of the Bind action requires an auxiliary class
-- This is due to the polymorphism of the monadic bind, which has the 
-- type  
--
-- > m a -> (a -> m b) -> m b
--
-- Note the polymorphism both in 'a' (value type of the input monadic
-- action) and 'b' (value type of the resulting action)
--
class RunBind m s a where
    runbind :: RunState t s b => m -> (a->t) -> s -> (s,b)

instance RunBind (Return a) s a where
    runbind (Return a) k s = runst (k a) s

instance RunBind (Get) s s where
    runbind Get k s = runst (k s) s

instance RunBind (Put s) s () where
    runbind (Put s) k _ = runst (k ()) s

instance (RunBind m s x, RunState y s w)
    => RunBind (Bind m (x->y)) s w where
    runbind (Bind m f) k s
        = runbind m (\x -> Bind (f x) k) s

-- | We can now run (interpret) our sample terms
--
eterm1 = runst term1 False
-- (True,())

-- | term2 denoted the action of negating the current state and returning
-- the original state
eterm2 = runst term2 False
-- (True,False)

-- eterm_ill1 = runst term_ill1 True
-- The above gives an error message saying there is no rule
-- to interpret (Bind Get Get)
-- Indeed, this term is ill-formed.

-- eterm_ill2 = runst term_ill2 True
-- The error message says there is no rule (RunState (Put Char) Bool a)
-- That is, one can't store a Char in the state of the type Bool.
-- The above term is ill-typed indeed.


-- | Now, we show that our term representation of the state monad 
-- is an instance of MonadState
data Statte s a = forall t. RunState t s a => Statte t

instance RunState (Statte s a) s a where
    runst (Statte t) s = runst t s

instance RunBind (Statte s a) s a where
    runbind (Statte m) k s = runbind m k s

instance Monad (Statte s) where
    (Statte m) >>= f = Statte (Bind m (\x -> f x))
    return = Statte . Return

instance MonadState s (Statte s) where
    get = Statte Get
    put = Statte . Put

-- | We can write computations expressed by term1 and term2 using
-- the normal monadic syntax
--
-- The following identity function is to resolve polymorphism, to tell
-- that monadic terms below should use our representation of MonadState
as_statte :: Statte s a -> Statte s a
as_statte = id

-- term1 = (Return True) `Bind` Put
mterm1 = as_statte (return True >>= put)
emterm1 = runst mterm1 False
-- (True,())


-- term2 = Get `Bind` (\v -> Put (not v) `Bind` (\() -> Return v))
mterm2 = as_statte $
	 do
	 v <- get
	 put (not v)
	 return v
emterm2 = runst mterm2 False
-- (True,False)
