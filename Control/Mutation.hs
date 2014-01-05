{-# LANGUAGE TypeFamilies, FlexibleInstances, FlexibleContexts #-}

-- | This file is part of the code accompanying the paper
-- `Fun with type functions'
-- Joint work with Simon Peyton Jones and Chung-chieh Shan
-- See the paper for explanations.
--
module Control.Mutation where

import Data.IORef
import Data.STRef
import Control.Monad.ST
import Control.Monad.Trans

-- | Start basic
class Mutation m where
  type Ref m :: * -> *
  newRef   :: a -> m (Ref m a)
  readRef  :: Ref m a -> m a
  writeRef :: Ref m a -> a -> m ()

instance Mutation IO where
  type Ref IO = IORef
  newRef   = newIORef
  readRef  = readIORef
  writeRef = writeIORef

instance Mutation (ST s) where
  type Ref (ST s) = STRef s
  newRef   = newSTRef
  readRef  = readSTRef
  writeRef = writeSTRef
-- End basic

-- | Start transformer
instance (Monad m, Mutation m, MonadTrans t)
      => Mutation (t m) where
  type Ref (t m) = Ref m
  newRef   = lift . newRef
  readRef  = lift . readRef
  writeRef = (lift .) . writeRef
