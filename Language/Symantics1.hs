{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE Rank2Types, GeneralizedNewtypeDeriving #-}
{-# LANGUAGE NoMonomorphismRestriction, EmptyDataDecls  #-}

-- | This is the Haskell version of symantics1.ml, for comparison
-- ACG with a more expressive semantic lexicon that includes
-- multi-prompt delimited continuations and the notion of evaluation.
-- Types are considered as a mere approximation rather than
-- the complete specification of grammatical composition.
--
-- * <http://okmij.org/ftp/gengo/index.html#CAG>
--
module Language.Symantics1 where

-- Part of the Dybvig, Sabry, Peyton-Jones' library
-- for multi-prompt delimited control
-- import CC_Frame -- ed. Oleg uses CC_Frame, available in the CC-delcont package now
--
import Control.Monad.CC
import Control.Monad.Reader

-- The abstract form, to be interpreted in several ways.

-- | Abstract signature, which defines base types, constants and their types
--
data N                                  -- Base types
data NP
data S
data SM

-- | An interpretation of the base type btyp in the signature
-- labeled by lab
type family I lab btyp 

class Abstract c where
  john :: c (I c NP)                    -- constants
  bill :: c (I c NP)

  man   :: c (I c N)
  woman :: c (I c N)
  see   :: c (I c NP) -> c (I c NP) -> c (I c S)
  love  :: c (I c NP) -> c (I c NP) -> c (I c S)

  every :: c (I c N) -> c (I c NP)
  some  :: c (I c N) -> c (I c NP)

  dot   :: c (I c S) -> c (I c SM)      -- Terminating dot

{-
  everyone :: c (I c NP)
  someone  :: c (I c NP)

-}


-- Sample phrases in the abstract language

-- term1 = see someone everyone

-- | Example from Sec 4.3 of the ESSLLI Advanced ACG course.
term43 = dot (love (some woman) (every man))


-- | An interpretation of the abstract signature as the surface form: strings
--
newtype LString a = LString a deriving Show

-- All base type are interpreted as strings
type instance I LString N  = String
type instance I LString NP = String
type instance I LString S  = String
type instance I LString SM = String

ccat :: LString String -> LString String -> LString String
ccat (LString a) (LString b) = LString (a ++ b)

instance Abstract LString where
  john  = LString "John"
  bill  = LString "Bill"
  man   = LString "man"
  woman = LString "woman"

  every = \x -> LString "every " `ccat` x
  some  = \x -> LString "some " `ccat` x
  see   = \o s -> s `ccat` LString " saw " `ccat` o
  love  = \o s -> s `ccat` LString " loves " `ccat` o

  dot   = \s -> s `ccat` LString "."


-- Surface forms of sample terms
term43S = case term43 of LString x -> x

-- ------------------------------------------------------------------------
-- | Semantic forms
--
data E = Ind String deriving Show
data T = Man E
       | Woman E
       | See E E
       | Love E E
       | And T T
       | Imply T T
       | Exists Varname T
       | Forall Varname T
         deriving Show
type Varname = String


-- We now build the semantic signature and the lexicon -- stepwise

-- | The order of quantification
data QuantOrder = Uni_over_Exi | Exi_over_Uni

data SemEnv r = 
    SemEnv{puni :: Prompt r T,
           pexi :: Prompt r T,
           quant_order :: QuantOrder,
           pcnt :: Prompt r (Int -> CC r T)     -- to generate variable names
          }

-- | The Semantic monad
newtype SemM r a = SemM (ReaderT (SemEnv r) (CC r) a)
  deriving Monad

unSem :: SemM r a -> SemEnv r -> CC r a
unSem (SemM m) env = runReaderT m env

-- | Interpretation of Basic types
type instance I (SemM r) NP = E
type instance I (SemM r) N  = E -> T
type instance I (SemM r) S  = T
type instance I (SemM r) SM = T

instance Abstract (SemM r) where
    john = return $ Ind "John'"
    bill = return $ Ind "Bill'"
    man  = return Man
    woman= return Woman
    love  = \o s -> (return Love) `ap` o `ap` s
    see   = \o s -> (return See)  `ap` o `ap` s

    every pred = pred >>= \pr -> 
     make_ind_quant puni (\vn x -> 
          return $ Forall vn $ Imply (pr (Ind vn)) x)
    some pred = pred >>= \pr -> 
     make_ind_quant pexi (\vn x -> 
          return $ Exists vn $ And (pr (Ind vn)) x)

    dot m = SemM $ do
            env <- ask
            lift $ do
             case quant_order env of
              Uni_over_Exi -> 
                 pushPrompt (puni env) $
                   pushPrompt (pexi env) (unSem m env)
              Exi_over_Uni -> 
                 pushPrompt (pexi env) $
                   pushPrompt (puni env) (unSem m env)

runSem :: QuantOrder -> (forall r. SemM r T) -> T
runSem qorder m = runCC init
 where
 init =  do
   uni <- newPrompt
   exi <- newPrompt
   cnt <- newPrompt
   -- initialize to 0 the counter to create variable names
   pushPrompt cnt (do
    v <- unSem m (SemEnv{puni=uni, pexi=exi, quant_order=qorder, pcnt=cnt})
    return $ const (return v)) `app` (return 0)

-- | /Movement/ into the position of the prompt selected by psel
make_ind_quant psel body = do
  vn <- genvar
  let v = Ind vn
  SemM $ do
   env <- ask
   lift $ shiftP (psel env) $ \sk -> 
      body vn =<< sk (Ind vn)

-- | Logical forms of sample terms in different semantic environment
term43L1 = runSem Uni_over_Exi term43
{-
  Forall "v1" (Imply (Man (Ind "v1")) 
     (Exists "v0" (And (Woman (Ind "v0")) 
        (Love (Ind "v0") (Ind "v1")))))
-}

term43L2 = runSem Exi_over_Uni term43
{-
  Exists "v0" (And (Woman (Ind "v0")) 
    (Forall "v1" (Imply (Man (Ind "v1")) 
       (Love (Ind "v0") (Ind "v1")))))
-}


-- | Auxiliary functions
--
app :: Monad m => m (a -> m b) -> m a -> m b
app m1 m2 = (m1 `ap` m2) >>= id

-- | Generate a new variable name
genvar :: SemM r Varname
genvar = SemM $ do
  env <- ask
  cnt <- lift $ shiftP (pcnt env) $ \sk ->
           return $ \cnt -> sk cnt `app` (return (succ cnt))
  return $ "v" ++ show cnt


shiftP :: Prompt r b -> ((a -> CC r b) -> CC r b) -> CC r a
shiftP p f = withSubCont p $ \sk -> 
               pushPrompt p (f (\v -> 
                 pushPrompt p (pushSubCont sk (return v))))


