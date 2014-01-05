-- |	Generators in Haskell
--
-- We translate the in-order tree traversal example from an old article
--   Generators in Icon, Python, and Scheme, 2004.
--
-- <http://okmij.org/ftp/Scheme/enumerators-callcc.html#Generators>
--
-- using Haskell and delimited continuations rather than call/cc + mutation.
-- The code is shorter, and it even types.
-- To be honest, we actually translate the OCaml code generator.ml
--
-- In this code, we use a single global prompt (that is, ordinary shift0)
-- Generator2.hs shows the need for several prompts.
--
module Control.Generator1 where

import Control.CCExc
import Control.Monad.Trans (liftIO, lift)

import Control.Monad.ST			-- for pure tests
import Data.STRef

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
type P m a = PS (Res m a)	-- the type of the single prompt (recursive)
newtype Res m a = Res ( (a -> CC (P m a) m ()) -> CC (P m a) m () )
outRes body (Res f) = f body

yield :: Monad m => a -> CC (P m a) m ()
yield v = shift0P ps (\k -> return . Res $ \b -> b v >> k () >>= outRes b)

-- | The enumerator: the for-loop essentially
enumerate iterator body = 
    pushPrompt ps (iterator >> (return . Res . const $ return ())) >>=
	       outRes body

-- | The in_order function itself: compare with the Python version
in_order :: (Monad m) => Tree -> CC (P m Label) m ()
in_order Leaf = return ()
in_order (Node label left right) = do
    in_order left
    yield label
    in_order right

-- | Print out the result of the in-order traversal
test_io :: IO ()
test_io = runCC $ enumerate (in_order tree1) (liftIO . print)

-- 4 2 5 1 6 3 7

-- | Or return it as a pure list; the effects are encapsulated
test_st :: [Label]
test_st = runST (do
		 res <- newSTRef []
		 let body v = modifySTRef res (v:)
		 runCC $ enumerate (in_order tree1) (lift . body)
		 readSTRef res >>= return . reverse)

-- [4,2,5,1,6,3,7]
