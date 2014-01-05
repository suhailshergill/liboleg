-- Haskell98!

-- | Variable state monad
--
-- <http://okmij.org/ftp/Computation/monads.html#param-monad>
--
--
--  The familiar State monad lets us represent computations with a state that can be queried and
--  updated. The state must have the same type during the entire computation however. One sometimes
--  wants to express a computation where not only the value but also the type of the state can be
--  updated -- while maintaining static typing. We wish for a parameterized `monad' that indexes each
--  monadic type by an initial (type)state and a final (type)state. The effect of an effectful
--  computation thus becomes apparent in the type of the computation, and so can be statically
--  reasoned about.
--
module Control.VarStateM where

import Control.Monad.State

-- | A parameterized `monad'
class Monadish m where
    gret :: a -> m p p a
    gbind :: m p q a -> (a -> m q r b) -> m p r b

-- | Inject regular monads to be monadish things too
newtype MW m p q a = MW{ unMW:: m a }

instance Monad m => Monadish (MW m) where
    gret = MW . return
    gbind (MW m) f = MW (m >>= unMW . f)

-- As a warm-up, we write the regular State computation, with the same 
-- type of state throughout

-- | First, use the regular Monad.State
test1 = runState c (0::Int) where
         c = do
             v <- get
             put (succ v)
             return v
-- (0,1)

-- | Now, wrap in MW
test2 = runState (unMW c) (0::Int) where
         c = gget `gbind` (
               \v -> gput (succ v) `gbind` (
                 \_ -> gret v))
         gget :: (MonadState s m) => MW m s s s
         gget = MW get
         gput :: (MonadState s m) => s -> MW m s s ()
         gput = MW . put
-- (0,1)


-- | Introduce the variable-type state
--
newtype VST m si so v = VST{runVST:: si -> m (so,v)}


instance Monad m => Monadish (VST m) where
  gret x = VST (\si -> return (si,x))
  gbind (VST m) f = VST (\si -> m si >>= (\ (sm,x) -> runVST (f x) sm))

vsget :: Monad m => VST m si si si
vsget = VST (\si -> return (si,si))
vsput :: Monad m => so -> VST m si so ()
vsput x = VST (\si -> return (x,()))


-- Repeat test2 via VST: the type of the state is the same
test3 = runVST c (0::Int) >>= print where
         c = vsget `gbind` (
               \v -> vsput (succ v) `gbind` (
                 \_ -> gret v))
-- (1,0)

-- Now, we vary the type of the state, from Int to a Char
test4 = runVST c (0::Int) >>= print where
         c = vsget `gbind` (
               \v -> vsput ((toEnum (65+v))::Char) `gbind` (
                 \_ -> vsget `gbind` (
                   \v' -> gret (v,v'))))
-- ('A',(0,'A'))

{-
-- The following is an error: 
    Couldn't match `Char' against `Int'
      Expected type: VST m Char r b
      Inferred type: VST m Int Int Bool

test4' = runVST c (0::Int) >>= print where
         c = vsget `gbind` (
               \v -> vsput ((toEnum (65+v))::Char) `gbind` (
                 \_ -> vsget `gbind` (
                   \v' -> gret (v==v'))))
-}


-- | Try polymorphic recursion, over the state.
-- crec1 invokes itself, and changes the type of the state from
-- some si to Bool.
crec1 :: (Enum si, Monad m) => VST m si si Int
crec1 = vsget `gbind` (\s1 -> case fromEnum s1 of
                      0 -> gret 0
                      1 -> vsput (pred s1) `gbind` (\_ -> gret 1)
                      _ -> vsput True `gbind` (\_ -> 
                             crec1 `gbind` (\v ->
                             (vsput s1 `gbind` -- restore state type to si
                             (\_ -> gret (v + 10))))))

test5 = runVST crec1 'a' >>= print
-- ('a',11)

-- | Another example, to illustrate locking and static reasoning about
-- the locking state
--
data Locked = Locked; data Unlocked = Unlocked
data LIO p q a = LIO{unLIO::IO a}

instance Monadish LIO where
  gret = LIO . return
  gbind m f = LIO (unLIO m >>= unLIO . f)

lput :: String -> LIO p p ()
lput = LIO . putStrLn
lget :: LIO p p String
lget = LIO getLine

-- In the real program, the following will execute actions to acquire
-- or release the lock. Here, we just print out our intentions.
lock :: LIO Unlocked Locked ()
lock = LIO (putStrLn "Lock")

unlock :: LIO Locked Unlocked ()
unlock = LIO (putStrLn "UnLock")

-- User code

tlock1 = lget `gbind` (\l -> 
	 gret (read l) `gbind` (\x ->
	 lput (show (x+1))))
{-
  *VarStateM> :t tlock1
  tlock1 :: LIO p p ()
 Inferred type has the same input and output states and is polymorphic:
 tlock1 does not affect the state of the lock.
-}

tlock2 = lget `gbind` (\l -> 
	 lock `gbind` (\_ ->
	 gret (read l) `gbind` (\x ->
	 lput (show (x+1)))))

{-
  *VarStateM> :t tlock2
  tlock2 :: LIO Unlocked Locked ()

The inferred type says that the computation does the locking.
-}

tlock3 = tlock2 `gbind` (\_ -> unlock)
{-
  *VarStateM> :t tlock3
  tlock3 :: LIO Unlocked Unlocked ()
-}

-- An attempt to execute the following
-- tlock4 = tlock2 `gbind` (\_ -> tlock2)

{-
 gives a type error:
    Couldn't match expected type `Locked'
	   against inferred type `Unlocked'
      Expected type: LIO Locked r b
      Inferred type: LIO Unlocked Locked ()
    In the expression: tlock2
    In a lambda abstraction: \ _ -> tlock2

The error message correctly points out an error of acquiring an already
held lock.
-}

-- Similarly, the following gives a type error because of an attempt
-- to release a lock twice
-- tlock4' = tlock2 `gbind` (\_ -> unlock `gbind` (\_ -> unlock))

