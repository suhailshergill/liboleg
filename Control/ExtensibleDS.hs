{-# LANGUAGE PatternGuards #-}
-- |
--  Extensible Denotational Semantics
--
--
-- This work is a generalization of 
--   /Extensible Denotational Language Specifications
--    Robert Cartwright, Matthias Felleisen
--    Theor. Aspects of Computer Software, 1994/
--    <http://citeseer.ist.psu.edu/69837.html>
--
-- to be referred to as EDLS.
--
-- We implement the enhanced EDLS in Haskell and add delimited control.
-- To be precise, we implement the Base interpreter (whose sole
-- operations are Loop and Error) and the following extensions: CBV
-- lambda-calculus, Arithmetic, Storage, Control. The extensions can be
-- added to the Base interpreter in any order and in any combination.
-- 
-- Our implementation has the following advantages over EDLS:
--
-- * support for delimited control
-- * support for a local storage (including `thread-local' storage and
--   general delimited dynamic binding)
-- * extensions do not have to be composed explicitly, and so the
--   composition order truly does not matter.  In the
--   original EDLS, one
--   had to write interpreter composition explicitly. In our approach, an
--   extension is pulled in automatically if the program includes the
--   corresponding syntactic forms. For example, if a program contains
--   storage cell creation and dereference operations, the Storage extension
--   will automatically be used to interpret the program.
--
-- Our main departure from EDLS is is the removal of the `central
-- authority'. There is no semantic `admin' function. Rather, admin is
-- part of the source language and can be used at any place in the
-- code. The `central authority' of EDLS must be an extensible function,
-- requiring meta-language facilities to implement (such as quite
-- non-standard Scheme modules). We do not have central
-- authority. Rather, we have bureaucracy: each specific effect handler
-- interprets its own effects as it can, throwing the rest `upstairs' for
-- higher-level bureaucrats to deal with. Extensibility arises
-- automatically.
-- 
-- We take the meaning of a program to be the union of Values and
-- (unfulfilled) Actions. If the meaning of the program is a (non-bottom)
-- value, the program is terminating. If the meaning of the program is an
-- Action -- the program finished with an error, such as an action to
-- access a non-existing storage cell, or shift without reset, or a
-- user-raised error.
-- 
-- Incidentally, EDLS stresses on p. 2 (the last full paragraph) that
-- their schema critically relies on the distinction between a complete
-- program and a nested program phrase. Our contribution (which is the
-- consequence of removing the central admin, making it first-class) is
-- eliminating such a distinction! EDLS says, at the very top of p. 3,
-- that the handle in the effect message ``is roughly a conventional
-- continuation.'' Because the admin of EDLS is `outside' of the program
-- (at the point of infinity, so to speak), its continuation indeed
-- appears undelimited. By making our `admin' a part of the source
-- language, we recognize the handle in the effect message for what it
-- is: a _delimited_ continuation.
-- 
-- As we see below, the Control aspect is orthogonal to the CBV
-- aspect. So, we can just as easily replace the CBV extension with the
-- CBN extension, which will give us the denotation of delimited control
-- in CBN.
-- 
-- 
-- We shall be using Haskell to express denotations, taking advantage of
-- the fact that Haskell values are `lifted'. See also the remark on p21
-- of EDLS: someone (ref. [4]) showed that sets and partial functions can
-- suffice...
-- 
-- 
-- Our program denotations are stable: they have the same form regardless
-- of a particular composition of modular interpreters.  See Section 3.5
-- of EDLS for precise formulation (and the last paragraph of Section 3.4
-- for concise informal statement of stability). Also see the comparison
-- with the monads on p. 20: different monads assign numeral radically
-- different meanings, depending on the monad. But in EDLS, a numeral has
-- exactly the same denotation.
-- 
-- The meaning of an expression is also the same and stable, no matter
-- what the interpreter is: it is a function from Env to Computations
-- (the latter being the union of values and unfulfilled effects -- the
-- same union mentioned above).
-- 
-- However, by using handlers, some effect messages can be subtracted:
-- so, strictly speaking, the denotation of a fragment is V +
-- effect-message-issued - effect-messages handled.  There seem to be a
-- connection with effect systems.
-- 
-- 
-- Additional notes on EDLS:
-- 
-- The abstract and p. 2 (especially the last full paragraph) are
-- so well-written!
-- 
-- p. 5, bottom: ``It [ref \x.x, where ref means what it does in ML] 
-- is a closed expression that does not diverge, is not a value, and
-- cannot be reduced to a value without affecting the context. We refer
-- to such results as _effects_.''
-- 
-- Beginning of Section 3 and App A give a very good introduction
-- to the denotational semantics.
-- 
-- p. 6: ``Algebraically speaking, the interpreter is (roughly) a
-- homomorphism from syntax to semantics''
-- 
-- ``A straightforward representation of an evaluation context is a
-- function from values to computations, which directly corresponds to
-- its operational usage as a function from syntactic values to
-- expressions.'' (p. 8). EDLS then notices that the `handle' has
-- the same type as the denotation of a context. Footnote 6 notes that
-- handler is roughly the composition combinator for functions from values
-- to computations [contexts!] and it superficially relates to [bind]
-- but does not satisfy all monad laws.
-- 
-- The last of EDLS Sec 3.5, p. 15: ``Informally speaking, this property
-- [stable denotations] asserts that in the framework of extensible
-- semantics, the addition of a programming construct corresponds to the
-- addition of a new ``dimension'' to the space of meaning. [The
-- equations, featuring injection and projection functions, make that
-- precise and clear.] The reader may want to contrast this general
-- statement with the numerous papers on the relationship between direct
-- and continuation semantics.''
-- 
-- The practical consequence of the lack of stability of denotations for
-- monads is that monadic transformers put layers upon layers of thunks,
-- which have to be carried over _in full_ from one sub-expression into
-- the other, even if no single subexpression uses all of the features.
-- 
-- The present code is not written in idiomatic Haskell and does not take
-- advantage of types at all. The ubiquitous projections from the
-- universal domain tantamount to ``dynamic typing.''  The code is
-- intentionally written to be close to the EDLS paper, emphasizing
-- denotational semantics (whose domains are untyped). One can certainly
-- do better, for example, employ user-defined datatypes for tagged
-- values, avoiding the ugly string-tagged VT.
--

module Control.ExtensibleDS where

import Data.Maybe

------------------------------------------------------------------------
-- The base interpreter


-- | The universal domain
-- Yes, it is untyped... But Denot semantics is like this anyway...
-- Bottom is the implicit member of this domain.
data Value = VI Int                     -- integers
           | VS String                  -- strings
           | VP Value Value             -- pairs
           | VF (Value -> Value)        -- functions
           | VT Tag Value               -- tagged value

type Tag = String

type Action = Value                     -- only differently tagged

instance Show Value where
    show (VI x) = show x
    show (VS x) = show x
    show (VT tag v) = "{"++show tag++" "++show v++"}"
    show (VP x1 x2) = show (x1,x2)
    show (VF _)  = "<procedure>"



-- | Computations: just like in EDLS
-- The strictness of inV guarantees that inV bottom = bottom, as
-- on Fig. 3 of EDLS
-- Error is always a part of the computation
--
data Comp = InV !Value | InFX (Value -> Comp) Action

instance Show Comp where
    show (InV v) = show v
    show (InFX _ a) = "Effect: " ++ show a


-- | Auxiliary functions
newtype V = V String deriving (Eq, Show) -- Variables
type Env v = V -> v
empty_env x = error $ "impossible: an open program? var " ++ show x
ext_env env x v y | x == y = v
ext_env env x v y = env y


-- | Note that inV is essentially the identity `partial' continuation
inAC action = InFX InV action

-- | The error `raise' action and its tag
tagErr = "Err"
raise err = inAC $ VT tagErr (VS err)

-- | The universal handler of actions
-- It propagates the action request InFX up.
-- Since we do case-analysis on the first argument, v, the handler
-- is strict in that argument. That is, handler bottom ==> bottom,
-- as required by Fig. 3 of EDLS.
-- The last clause is essentially the denotation of a `control channel'
handler (InV v) k = k v
handler (InFX ka a) k = InFX (\v -> handler (ka v) k) a


-- | Expressions and their interpretations
-- This is an open data type and an open function. Haskell typeclasses
-- are ideal for that.
--
-- This is the function \curlyM of EDLS
class Interpretor exp where
    interpret ::  exp -> Env Value -> Comp

-- | The base language has only two expressions: omega and error
-- See Fig. 3 (p. 7) of EDLS
--
data BE_err   = BE_err
data BE_omega = BE_omega

instance Interpretor BE_omega where
    interpret _ _ = InV undefined

instance Interpretor BE_err where
    interpret _ _  = raise "error action"

-- | The meaning of a program
prog p = interpret p empty_env


-- ----------------------------------------------------------------------
-- | Extension: Call-by-Value: see a part Fig. 4 of EDLS (or, Fig. 8)
--
-- We add closures (procedures) to the Base
type Proc = Value -> Comp

class PV u where                        -- and the corresponding injection/
  inP :: Proc -> u                      -- projection functions
  prP :: u -> Maybe (Proc)


type Var = V
data Lam e = Lam V e
data App e1 e2 = e1 :@ e2
infixl 1 :@

instance Interpretor V where
    interpret v env = InV (env v)

instance Interpretor e => Interpretor (Lam e) where
    interpret (Lam x e) env = InV (inP (\d -> interpret e (ext_env env x d)))

instance (Interpretor e1, Interpretor e2) => Interpretor (App e1 e2) where
    interpret (e1 :@ e2) env =
        handler (interpret e1 env) $
                \f -> handler (interpret e2 env) $
                      \a -> maybe (raise "InP expected") (\g -> g a)
                                  (prP f)


-- | Create a few variables for use in examples
vx, vy, vr, vf :: Var
(vx,vy,vr,vf) = (V "x", V "y", V "r", V "f")

-- Test of the extension
-- Instantiate this extension on the top of the base language
--
-- | Denotations of the new actions (inj/proj to/from the Universal Domain)
tagProc  = "Proc"
tagCompV = "CompV"
tagCompE = "CompE"

-- | inject and project computations
inComp :: Comp -> Value
inComp (InV v) = VT tagCompV v
inComp (InFX k a) = VT tagCompE (VP (VF (inComp . k)) a)

prComp :: Value -> Maybe Comp
prComp (VT tag v) | tag == tagCompV = Just (InV v)
prComp (VT tag v) | tag == tagCompE = pr v
   where pr (VP (VF k) a) = Just $ InFX (fromJust . prComp . k) a
         pr _ = Nothing
prComp _ = Nothing


instance PV Value where
    inP f = VT tagProc (VF (inComp . f))
    prP (VT tag (VF k)) | tag == tagProc = Just $ fromJust . prComp . k
    prP _ = Nothing

test1 = Lam vx (vx :@ BE_err)

test1e = prog test1
-- {"Proc" <procedure>}


------------------------------------------------------------------------
-- | Extension: Arithmetic: see a part Fig. 4 of EDLS 
--
class PN u where                        -- inj/proj for numbers
  inN :: Int -> u
  prN :: u -> Maybe Int

data IntC = IntC Int                    -- an integer constant
data Add1 = Add1

instance Interpretor IntC where
    interpret (IntC v) _ = InV (inN v)

instance Interpretor Add1 where
    interpret Add1 _ = InV (inP $
                               \v -> maybe (raise "InN expected")
                                     (InV . inN . succ)
                                     (prN v))


add1 x = Add1 :@ x

-- | Test of the extension
-- Instantiate this extension on the top of the CBV evaluator
--
instance PN Value where
    inN n = VI n
    prN (VI n) = Just n
    prN _ = Nothing


test2 = (Lam vx $ add1 vx) :@ (IntC 1)
test2e = prog test2
-- 2

------------------------------------------------------------------------
-- | Extension: State: see Fig. 5 of EDLS 
--
newtype Loc = Loc Int deriving (Eq, Show) -- locations

class PL u where
  inL :: Loc -> u
  prL :: u -> Maybe Loc

-- | a better idea is Loc -> Maybe Value, so that when lookup fails,
-- we can re-throw that Deref or Set message. That would make the
-- storage extensible...
-- The first component of the pair is the allocation counter
type Sto = (Int, Loc -> Value) 

tagSto = "Storage"

inSto :: Sto -> Value
inSto (cnt, st) = VT tagSto (VP (VI cnt) (VF (st . fromJust . prL)))
prSto :: Value -> Maybe Sto
prSto (VT tag (VP (VI cnt) (VF k))) | tag == tagSto = Just (cnt, k . inL)
prSto _ = Nothing

init_sto :: Sto
init_sto  = (0,\l->undefined)


-- data StoAct v = InRef v | InDer Loc | InSet Loc v

-- | new expressions
data Ref e = Ref e
data Deref e = Deref e
data Set e1 e2 = Set e1 e2

-- | Denotations of the new actions (inj/proj to/from the Universal Domain)
tagInRef = "Ref"
tagInDer = "Deref"
tagInSet = "Set"

inRef v = VT tagInRef v
prRef (VT tag v) | tag == tagInRef = Just v
prRef _ = Nothing

inDer v = VT tagInDer (inL v)
prDer (VT tag v) | tag == tagInDer = prL v
prDer _ = Nothing

inSet l v = VT tagInSet (VP (inL l) v)
prSet (VT tag (VP l v)) | tag == tagInSet = fmap (\l -> (l,v)) (prL l)
prSet _ = Nothing



instance Interpretor e => Interpretor (Ref e) where
    interpret (Ref e) env = handler (interpret e env) $
                              \v -> inAC(inRef v)


instance Interpretor e => Interpretor (Deref e) where
    interpret (Deref e) env = handler (interpret e env) $
                              \v -> maybe (raise "InL expected")
                                    (inAC . inDer)
                                    (prL v)

instance (Interpretor e1, Interpretor e2) => Interpretor (Set e1 e2) where
    interpret (Set e1 e2) env = handler (interpret e1 env) $
                              \l -> handler (interpret e2 env) $
                                 \v -> maybe (raise "InL expected")
                                             (\l -> inAC (inSet l v))
                                             (prL l)


-- | Now we need a storage admin
-- It is treated as an expression in the source language!
--
data StoAdmin e = StoAdmin Sto e

instance Interpretor e => Interpretor (StoAdmin e) where
    interpret (StoAdmin sto e) env = sto_handler sto (interpret e env) InV


sto_handler (cnt,st) (InFX k a) f | Just v <- prRef a = 
   let l = Loc cnt
       sto = (cnt+1, \l' -> if l' == l then v else st l')
   in sto_handler sto (k (inL l)) f
sto_handler sto@(cnt,st) (InFX k a) f | Just l <- prDer a = 
   sto_handler sto (k (st l)) f
sto_handler (cnt,st) (InFX k a) f | Just (l,v) <- prSet a = 
   sto_handler (cnt, \l' -> if l' == l then v else st l') (k (inL l)) f

sto_handler sto (InV v) f = f (VP v (inSto sto)) -- normal return
-- Propagate everything else
sto_handler sto (InFX k a) f = InFX (\v -> sto_handler sto (k v) f) a

                                       
tagLoc = "Loc"

instance PL Value where
    inL (Loc l) = VT tagLoc (VI l)
    prL (VT tag (VI l)) | tag == tagLoc = Just (Loc l)
    prL _ = Nothing


-- Test of the extension
-- Note that we can use several local storages!


test3 = (Lam vr $ Lam vf $ vf :@ (Deref vr)) :@
          (Ref (IntC 1)) :@ (Lam vx $ add1 vx)

-- we forgot the Admin..., so the program terminates with an effect
test31 = prog test3 
-- Effect: {"Ref" 1}

test32 = prog (StoAdmin init_sto test3)
-- (2,{"Storage" (1,<procedure>)})

test33 = prog (StoAdmin init_sto 
               ((Lam vr $ (Lam (V "_") (Deref vr)) :@ (Deref (Set vr (IntC 2))))
                :@ (Ref (IntC 1))))
-- (2,{"Storage" (1,<procedure>)})

------------------------------------------------------------------------
-- Extension: Delimited continuation
-- That is new compared to EDLS

-- new effect message: Control ((Value->Comp)->Comp)
tagControl = "Control"

inControl :: (Value->Comp) -> Value
inControl f = VT tagControl (VF (inComp . f))
prControl :: Value -> Maybe (Value->Comp)
prControl (VT tag (VF f)) | tag == tagControl = Just (fromJust . prComp . f)
prControl _ = Nothing


data Control e = Control e

instance Interpretor e => Interpretor (Control e) where
    interpret (Control e) env = handler (interpret e env) $
                      \a -> maybe (raise "InP expected")
                                  (\f -> inAC(inControl f))
                                  (prP a)

-- The administrator here is prompt, quite unsurprisingly

data ControlAdmin e = ControlAdmin e

instance Interpretor e => Interpretor (ControlAdmin e) where
    interpret (ControlAdmin e) env = ctl_handler (interpret e env) InV


ctl_handler (InFX k a) f | Just e <- prControl a = 
   ctl_handler (e (inP k)) f

ctl_handler (InV v) f = f v -- normal return
-- Propagate everything else
ctl_handler (InFX k a) f = InFX (\v -> ctl_handler (k v) f) a

-- Ken's tests

control v e = Control (Lam (V v) e)
prompt e = ControlAdmin e
succ0 = (add1 (IntC 0))

-- if we forget Reset...
test41 = prog $ add1 (Control (Lam vf succ0))
-- Effect: {"Control" <procedure>}

test42 = prog $ prompt (add1 (control "f" succ0))
-- 1

test43 = prog $ prompt (add1 (control "f" (vf :@ succ0)))
--2

test44 = prog $ prompt (add1 (add1 (control "f" (vf :@ succ0))))
-- 3

test45 = prog $ prompt (add1 (add1 (control "f" 
                                    (vf :@ (vf :@ succ0)))))
-- 5

test46 = prog $ prompt (add1 ((Lam vx (add1 vx)) :@
                              (control "f" (vf :@ (vf :@ succ0)))))

-- 5
test47 = prog $ prompt (add1 ((Lam vx (control "f" (IntC 0))) :@
                              (control "f" (vf :@ (vf :@ succ0)))))
-- 0

test48 = prog $ add1 (prompt ((Lam vx (control "f" (IntC 0))) :@
                              (control "f" (vf :@ (vf :@ succ0)))))
-- 1
