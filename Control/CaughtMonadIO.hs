-- 
-- |
-- <http://okmij.org/ftp/Haskell/misc.html#catch-MonadIO>
--
-- The ability to use functions 'catch', 'bracket', 'catchDyn', etc. in
-- MonadIO other than IO itself has been a fairly frequently requested
-- feature:
-- 
-- <http://www.haskell.org/pipermail/glasgow-haskell-users/2003-September/005660.html>
--
-- < http://haskell.org/pipermail/libraries/2003-February/000774.html>
-- 
-- The reason it is not implemented is because these functions cannot be
-- defined for a general MonadIO. However, these functions can be easily
-- defined for a large and interesting subset of MonadIO. The following
-- code demonstrates that. It uses no extensions (other than those needed
-- for the Monad Transformer Library itself), patches no compilers, and
-- proposes no extensions. The generic catch has been useful in a
-- database library (Takusen), where many operations work in a monad
-- (ReaderT Session IO): IO with the environment containing the database
-- session data. Many other foreign libraries have a pattern of passing
-- around various handles, which are better hidden in a monad. Still, we
-- should be able to handle IO errors and user exceptions that arise in
-- these computations.
-- 

{-# OPTIONS -fglasgow-exts #-}

module Control.CaughtMonadIO where

import Data.Typeable
import Data.Dynamic
import Control.Monad.Trans
import Control.OldException hiding (catch, catchDyn)
import qualified Control.OldException (catch)
import Control.Monad.Reader
import Control.Monad.Writer
import Control.Monad.State
import Control.Monad.RWS
import Control.Monad.Error

---------------------  Tests

data MyException = MyException String deriving (Show, Typeable)

testfn True = throwDyn (MyException "thrown")
testfn False = return True

testc m = catchDyn (m >>= return . show) (\ (MyException s) -> return s)

test1 = do tf True >>= print; tf False >>= print
  where
   tf x = runReaderT (runWriterT (testc (do
                                          tell "begin"
                                          r <- ask
                                          testfn r))) x

{-
*CaughtMonadIO> test1
("thrown","")
("True","begin")
-}


test2 = do tf True >>= print; tf False >>= print;
  where
   tf x = runReaderT (runErrorT (do
                                  r <- ask
                                  testfn r `catchDyn` 
                                   (\ (MyException s) -> throwError s))) x

{-
*CaughtMonadIO> test2
Left "thrown"
Right True
-}


-- | The implementation is quite trivial.
class MonadIO m => CaughtMonadIO m where
     gcatch :: m a -> (Exception -> m a) -> m a

instance CaughtMonadIO IO where
     gcatch = Control.OldException.catch

instance (CaughtMonadIO m, Error e) => CaughtMonadIO (ErrorT e m) where
     gcatch m f = mapErrorT (\m -> gcatch m (\e -> runErrorT $ f e)) m

-- | The following is almost verbatim from `Control.Monad.Error'
-- Section "MonadError instances for other monad transformers"
--
instance CaughtMonadIO m => CaughtMonadIO (ReaderT r m) where
     gcatch m f = ReaderT $ 
                  \r -> gcatch (runReaderT m r) (\e -> runReaderT (f e) r)

-- | The following instances presume that an exception that occurs in
-- 'm' discard the state accumulated since the beginning of 'm's execution.
-- If that is not desired -- don't use StateT. Rather, allocate
-- IORef and carry that _immutable_ value in a ReaderT. The accumulated
-- state will thus persist. One can always use IORefs within
-- any MonadIO.
instance (Monoid w, CaughtMonadIO m) => CaughtMonadIO (WriterT w m) where
         m `gcatch` h = WriterT $ runWriterT m
                 `gcatch` \e -> runWriterT (h e)

instance CaughtMonadIO m => CaughtMonadIO (StateT s m) where
         m `gcatch` h = StateT $ \s -> runStateT m s
                 `gcatch` \e -> runStateT (h e) s

instance (Monoid w, CaughtMonadIO m) => CaughtMonadIO (RWST r w s m) where
         m `gcatch` h = RWST $ \r s -> runRWST m r s
                 `gcatch` \e -> runRWST (h e) r s


catchDyn :: (Typeable e, CaughtMonadIO m) => m a -> (e -> m a) -> m a
catchDyn m f = gcatch m (\e -> maybe (throw e) f ((dynExceptions e) 
                                                   >>= fromDynamic))

