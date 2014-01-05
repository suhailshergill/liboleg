{-# LANGUAGE PatternGuards, KindSignatures #-}
{-# LANGUAGE ExistentialQuantification, Rank2Types, ImpredicativeTypes #-}

-- | Monad transformer for multi-prompt delimited control
-- It implements the superset of the interface described in
--
-- <http://okmij.org/ftp/continuations/implementations.html#CC-monads>
--
-- > A Monadic Framework for Delimited Continuations
-- > R. Kent Dybvig, Simon Peyton Jones, and Amr Sabry
-- > JFP, v17, N6, pp. 687--730, 2007.
-- > http://www.cs.indiana.edu/cgi-bin/techreports/TRNNN.cgi?trnum=TR615
--
-- The first main difference is the use of generalized prompts, which
-- do not have to be created with new_prompt and therefore can be defined
-- at top level. That removes one of the main practical drawbacks of
-- Dybvig et al implementations: the necessity to carry around the prompts
-- throughout all the code.
--
-- The delimited continuation monad is parameterized by the flavor
-- of generalized prompts. The end of this code defines several flavors;
-- the library users may define their own. User-defined flavors are 
-- especially useful when user's code uses a small closed set of answer-types. 
-- Flavors PP and PD below are more general, assuming the set of possible
-- answer-types is open and Typeable. If the user wishes to create several
-- distinct prompts with the same answer-types, the user should use
-- the flavor of prompts accepting an integral prompt identifier, such as PD.
-- Prompts of the flavor PD correspond to the prompts in Dybvig, Peyton Jones,
-- Sabry framework. If the user wishes to generate unique prompts, the user
-- should arrange himself for the generation of unique integers
-- (using a state monad, for example). On the other hand, the user
-- can differentiate answer-types using `newtype.' The latter can
-- only produce the set of distinct prompts that is fixed at run-time.
-- Sometimes that is sufficient. There is not need to create a gensym
-- monad then.
--
-- The second feature of our implementation is the use of the 
-- bubble-up semantics:
-- See page 57 of <http://okmij.org/ftp/gengo/CAG-talk.pdf>
-- This present code implements, for the first time, the delimited 
-- continuation monad CC *without* the use of the continuation monad. 
-- This code implements CC in direct-style, so to speak.
-- Instead of continuations, we rely on exceptions. Our code has a lot
-- in common with the Error monad. In fact, our code implements
-- an Error monad for resumable exceptions.

module Control.CCExc (
	      CC,			-- Types
	      SubCont,
	      CCT,
	      Prompt,

	      -- Basic delimited control operations
	      pushPrompt,
              takeSubCont,
              pushSubCont,
              runCC,

              -- Useful derived operations
	      abortP,
              shiftP,
              shift0P,
              controlP,

              -- Pre-defined prompt flavors
	      PS, ps,
              P2, p2L, p2R,
              PP, pp,
              PM, pm,
              PD, newPrompt,
              as_prompt_type
	      ) where

import Control.Monad.Trans
import Data.Typeable			-- for prompts of the flavor PP, PD

-- | Delimited-continuation monad transformer
-- It is parameterized by the prompt flavor p
newtype CC p m a = CC{unCC:: m (CCV p m a)}

-- | The captured sub-continuation
type SubCont p m a b = CC p m a -> CC p m b

-- | Produced result: a value or a resumable exception
data CCV p m a = Iru a
	       | forall x. Deru (SubCont p m x a) (p m x) -- The bubble

-- | The type of control operator's body
type CCT p m a w = SubCont p m a w -> CC p m w

-- | Generalized prompts for the answer-type w: an injection-projection pair
type Prompt p m w = 
    (forall x. CCT p m x w -> p m x,
     forall x. p m x -> Maybe (CCT p m x w))


--
-- |CC monad: general monadic operations
--
instance Monad m => Monad (CC p m) where
    return = CC . return . Iru

    m >>= f = CC $ unCC m >>= check
	where check (Iru a)         = unCC $ f a
	      check (Deru ctx body) = return $ Deru (\x -> ctx x >>= f) body


instance MonadTrans (CC p) where
    lift m = CC (m >>= return . Iru)

instance MonadIO m => MonadIO (CC p m) where
    liftIO = lift . liftIO

--
-- | Basic Operations of the delimited control interface
--
pushPrompt :: Monad m =>
	      Prompt p m w -> CC p m w -> CC p m w
pushPrompt p@(_,proj) body = CC $ unCC body >>= check
 where
 check e@Iru{} = return e
 check (Deru ctx body) | Just b <- proj body  = unCC $ b ctx
 check (Deru ctx body) = return $ Deru (\x -> pushPrompt p (ctx x)) body


-- | Create the initial bubble
takeSubCont :: Monad m =>
	       Prompt p m w -> CCT p m x w -> CC p m x
takeSubCont p@(inj,_) body = CC . return $ Deru id (inj body)

-- Apply the captured continuation
pushSubCont :: Monad m => SubCont p m a b -> CC p m a -> CC p m b
pushSubCont = ($)

runCC :: Monad m => CC (p :: (* -> *) -> * -> *) m a -> m a
runCC m = unCC m >>= check
 where
 check (Iru x) = return x
 check _       = error "Escaping bubble: you have forgotten pushPrompt"


-- --------------------------------------------------------------------
-- | Useful derived operations
--
abortP :: Monad m => 
	  Prompt p m w -> CC p m w -> CC p m any
abortP p e = takeSubCont p (\_ -> e)

shiftP :: Monad m => 
	  Prompt p m w -> ((a -> CC p m w) -> CC p m w) -> CC p m a
shiftP p f = takeSubCont p $ \sk -> 
	       pushPrompt p (f (\c -> 
		  pushPrompt p (pushSubCont sk (return c))))

shift0P :: Monad m => 
	  Prompt p m w -> ((a -> CC p m w) -> CC p m w) -> CC p m a
shift0P p f = takeSubCont p $ \sk -> 
	       f (\c -> 
		  pushPrompt p (pushSubCont sk (return c)))

controlP :: Monad m => 
	  Prompt p m w -> ((a -> CC p m w) -> CC p m w) -> CC p m a
controlP p f = takeSubCont p $ \sk -> 
	       pushPrompt p (f (\c -> 
		  pushSubCont sk (return c)))

-- --------------------------------------------------------------------
-- Prompt flavors

-- | The extreme case: prompts for the single answer-type w.
-- The monad (CC PS) then is the monad for regular (single-prompt) 
-- delimited continuations
newtype PS w m x = PS (CCT (PS  w) m x w)

-- | There is only one generalized prompt of the flavor PS for a
-- given answer-type w. It is defined below
ps :: Prompt (PS w) m w
ps = (inj, prj)
 where
 inj = PS
 prj (PS x) = Just x

-- | Prompts for the closed set of answer-types
-- The following prompt flavor P2, for two answer-types w1 and w2,
-- is given as an example. Typically, a programmer would define their
-- own variant data type with variants for the answer-types that occur
-- in their program.
--
newtype P2 w1 w2 m x = 
  P2 (Either (CCT (P2 w1 w2) m x w1) (CCT (P2 w1 w2) m x w2))


-- | There are two generalized prompts of the flavor P2
p2L :: Prompt (P2 w1 w2) m w1
p2L = (inj, prj)
 where
 inj = P2 . Left
 prj (P2 (Left x)) = Just x
 prj _ = Nothing

p2R :: Prompt (P2 w1 w2) m w2
p2R = (inj, prj)
 where
 inj = P2 . Right
 prj (P2 (Right x)) = Just x
 prj _ = Nothing


-- | Prompts for the open set of answer-types
--
data PP m x = forall w. Typeable w => PP (CCT PP m x w)

-- | We need to wrap the type alias CCT into a newtype. Otherwise, gcast
-- doesn't work. We can't treat (CCT p m a w) as a an application of
-- the `type constructor' (CCT p m a) to the type w: type aliases can't 
-- be partially applied. But we can treat the type (NCCT p m a w) that way.
newtype NCCT p m a w = NCCT{unNCCT :: CCT p m a w}

pp :: Typeable w => Prompt PP m w
pp = (inj, prj)
 where
 inj = PP
 prj (PP c) = maybe Nothing (Just . unNCCT) (gcast (NCCT c))

-- | The same as PP but with the phantom parameter c
-- The parameter is useful to statically enforce various constrains
-- (statically pass some information between shift and reset)
-- The prompt PP is too `dynamic': all errors are detected dynamically
-- See Generator2.hs for an example
data PM c m x = forall w. Typeable w => PM (CCT (PM c) m x w)

pm :: Typeable w => Prompt (PM c) m w
pm = (inj, prj)
 where
 inj = PM
 prj (PM c) = maybe Nothing (Just . unNCCT) (gcast (NCCT c))

-- | Open set of answer types, with an additional distinction (given by
-- integer identifiers)
-- This prompt flavor corresponds to the prompts in the Dybvig, Peyton-Jones,
-- Sabry framework (modulo the Typeable constraint).
--
data PD m x = forall w. Typeable w => PD Int (CCT PD m x w)

newPrompt :: Typeable w => Int -> Prompt PD m w
newPrompt mark = (inj, prj)
 where
 inj = PD mark
 prj (PD mark' c) | mark' == mark, 
		    Just (NCCT x) <- gcast (NCCT c) = Just x
 prj _ = Nothing

-- | It is often helpful, for clarity of error messages, to specify the 
-- answer-type associated with the prompt explicitly (rather than relying 
-- on the type inference to figure that out). The following function
-- is useful for that purpose.
as_prompt_type :: Prompt p m w -> w -> Prompt p m w
as_prompt_type = const
