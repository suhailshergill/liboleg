{-# LANGUAGE DeriveDataTypeable, ScopedTypeVariables #-}

-- |    Generators in Haskell
--
-- We translate the in-order tree traversal example from an old article
--   Generators in Icon, Python, and Scheme, 2004.
--
-- > http://okmij.org/ftp/Scheme/enumerators-callcc.html#Generators
--
-- using Haskell and delimited continuations rather than call/cc + mutation.
-- The code is shorter, and it even types.
-- To be honest, we actually translate the OCaml code generator.ml
--
-- This code is the extension of Generator1.hs; we use delimited
-- control not only to implement the generator. We also use delimited
-- control to accumulate the results in a list. We need two different
-- prompts then (with two different answer-types, as it happens).
-- This file illustrates the prompt flavors PP and PM, using newtypes
-- to define private global prompts (global prompts that are private to
-- the current module).
--
--
module Control.Generator2 where

import Control.CCExc
import Control.Monad.Trans (liftIO, lift)
import Data.Typeable

{-
A sample program Python programmers seem to be proud of: an in-order
traversal of a tree:

     >>>> # A recursive generator that generates Tree leaves in in-order.
     >>> def inorder(t):
     ...     if t:
     ...         for x in inorder(t.left):
     ...             yield x
     ...         yield t.label
     ...         for x in inorder(t.right):
     ...             yield x

Given below is the complete implementation in Haskell.
-}


-- | A few preliminaries: define the tree and build a sample tree
--
type Label = Int
data Tree = Leaf | Node Label Tree Tree deriving Show

make_full_tree :: Int -> Tree
make_full_tree depth = loop 1 depth
 where 
 loop label 0 = Leaf
 loop label n = Node label (loop (2*label) (pred n)) (loop (2*label+1) (pred n))

tree1 = make_full_tree 3

-- | In Python, `yield' is a keyword. In Haskell, it is a regular function.
-- Furthermore, it is a user-defined function, in one line of code.
-- To get generators there is no need to extend a language.
--
-- First, we try the prompt flavor PP
--
-- The answer-type for one of the prompts
newtype ResP m a = ResP ( (a -> CC PP m ()) -> CC PP m () )

instance Typeable1 m => Typeable1 (ResP m) where
  typeOf1 x = mkTyConApp (mkTyCon "ResP") [m]
    where m = typeOf1 (undefined:: m ())

outResP body (ResP f) = f body

-- | One prompt, used by the generator (the yield/enumerate pair)
-- We instantiate the global pp to the desired answer-type.
ppy :: (Typeable1 m, Typeable a) => Prompt PP m (ResP m a)
ppy = pp

-- | The rest of the code, up to test_io, is the same as that in Generator1.hs
yieldP :: (Typeable1 m, Typeable a) => Monad m => a -> CC PP m ()
yieldP v = shift0P ppy (\k -> return . ResP $ \b -> b v >> k () >>= outResP b)

-- | The enumerator: the for-loop essentially
enumerateP :: (Typeable1 m, Typeable a, Monad m) =>
     CC PP m () -> (a -> CC PP m ()) -> CC PP m ()
enumerateP iterator body = 
    pushPrompt ppy (iterator >> (return . ResP . const $ return ())) >>=
               outResP body

-- | The in_order function itself: compare with the Python version
in_orderP :: (Typeable1 m, Monad m) => Tree -> CC PP m ()
in_orderP Leaf = return ()
in_orderP (Node label left right) = do
    in_orderP left
    yieldP label
    in_orderP right

-- | Print out the result of the in-order traversal
test_ioP :: IO ()
test_ioP = runCC $ 
            enumerateP (in_orderP tree1) (liftIO .(print :: (Int -> IO ())))

-- 4 2 5 1 6 3 7

-- | Using the prompt flavor PM
--
-- The above code works. We can define the second pair of operators
-- to accummulate the result into a list. Yet, the solution is
-- not very satisfactory. We notice that the prompt type ppy is
-- polymorphic over a, the elements we yield. What ensures that
-- `yieldP' yields elements of the same type that enumerateP can pass to the
-- body of the loop? Nothing, actually, at compile time. If yieldP and
-- enumerateP do not agree on the type of the elements, a run-time
-- error will occur.
-- This is where the PM prompt type comes in handy. It has a phantom
-- type parameter c, which can be used to communicate between
-- producers and consumers of the effect. We use the type parameter c
-- to communicate the type of elements, between yield and enumerate.
-- Since the parameter is phantom, it costs us nothing at run-time.
--
-- The answer-type for one of the prompts
newtype Res m a = Res ( (a -> CC (PM a) m ()) -> CC (PM a) m () )

instance Typeable1 m => Typeable1 (Res m) where
  typeOf1 x = mkTyConApp (mkTyCon "Res") [m]
    where m = typeOf1 (undefined:: m ())

outRes body (Res f) = f body

-- | One prompt, used by the generator (the yield/enumerate pair)
py :: (Typeable1 m, Typeable a) => Prompt (PM a) m (Res m a)
py = pm

-- | The rest of the code, up to test_io, is the same as that in Generator1.hs
yield :: (Typeable1 m, Typeable a) => Monad m => a -> CC (PM a) m ()
yield v = shift0P py (\k -> return . Res $ \b -> b v >> k () >>= outRes b)

-- | The enumerator: the for-loop essentially
enumerate :: (Typeable1 m, Typeable a, Monad m) =>
     CC (PM a) m () -> (a -> CC (PM a) m ()) -> CC (PM a) m ()
enumerate iterator body = 
    pushPrompt py (iterator >> (return . Res . const $ return ())) >>=
               outRes body

-- | The in_order function itself: compare with the Python version
in_order :: (Typeable1 m, Monad m) => Tree -> CC (PM Label) m ()
in_order Leaf = return ()
in_order (Node label left right) = do
    in_order left
    yield label
    in_order right

-- | Print out the result of the in-order traversal
test_io :: IO ()
test_io = runCC $ enumerate (in_order tree1) (liftIO .(print :: (Int -> IO ())))

-- 4 2 5 1 6 3 7


-- | The second application of control: accumulating the results in a list
--
-- The answer-type for the second prompt. We use newtype for identification
newtype Acc a = Acc [a] deriving Typeable
toAcc v (Acc l) = return . Acc $ v:l

-- | The second prompt, used by the acc/accumulated pair
-- Again we use the mark of PM to communicate the type of the elements
-- between `acc' and `accumulated'. It happens to be the same type used
-- by yield/enumetrate.
-- If that was not the case, we could have easily arranged for a type-level
-- record (see HList or the TFP paper).
pa :: (Typeable a) => Prompt (PM a) m (Acc a)
pa = pm

acc :: (Typeable a, Monad m) => a -> CC (PM a) m ()
acc v = shift0P pa (\k -> k () >>= toAcc v)

accumulated :: (Typeable a, Monad m) => CC (PM a) m () -> CC (PM a) m [a]
accumulated body = 
    pushPrompt pa (body >> return (Acc [])) >>= \ (Acc l) -> return l

test_acc :: [Label]
test_acc = runIdentity . runCC . accumulated $
             (enumerate (in_order tree1) acc)

-- [4,2,5,1,6,3,7]


-- | To avoid importing mtl, we define Identity on our own
newtype Identity a = Identity{runIdentity :: a} deriving (Typeable)

instance Monad Identity where
    return = Identity
    m >>= f = f $ runIdentity m
