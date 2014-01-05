{-# OPTIONS -fglasgow-exts #-}
{-# LANGUAGE TemplateHaskell #-}

-- | Template Haskell code is untyped, which is a bummer and leads to late
-- error reporting. We make code expressions typed, at least for our particular
-- domain.
--
module Data.Symbolic.TypedCode (
                  Code, -- only the type is exported,
                        -- data constructor is private
                  Var,  -- ditto
                  QCode,
                  reflectQC, showQC,

                  -- typed primitive operations
                  op'add, op'sub, op'mul, op'div, op'negate, op'recip,
                  op'sin, op'cos, op'pi,

                  -- Code combinators
                  appC,

                  -- Lifting from primitive datatypes to Code
                  integerC, rationalC,

                  -- create a variable to differentiate over
                  new'diffVar, var'exp, reflectDF,

                  -- combinators for the intensional code analysis
                  on'varC, on'litC, on'litRationalC, on'1opC, on'2opC
                 ) where

import Data.Symbolic.TypedCodeAux
import Language.Haskell.TH
import Language.Haskell.TH.Ppr

-- | The data type of a typed TH code experssion. The phantom parameter 'a'
-- is the type.
--
newtype Code a = Code {unC :: Exp} deriving (Eq, Show)
type QCode a = Q (Code a)
newtype Var a = Var Name

show_code cde = runQ cde >>= putStrLn . pprint

showQC :: Q (Code a) -> IO ()
showQC qc = runQ qc >>= putStrLn . pprint . unC

-- | This function is useful when splicing code expressions
-- See DiffTest.hs for the examples of its use.
reflectQC :: Q (Code a) -> Q Exp
reflectQC qc = qc >>= return . unC


-- | Typed primitive operations
--
op'add :: Num a => Code (a->a->a)
op'add = Code . VarE $ $(reifyName [e| (+) |])
op'sub :: Num a => Code (a->a->a)
op'sub = Code . VarE $ $(reifyName [e| (-) |])
op'mul :: Num a => Code (a->a->a)
op'mul = Code . VarE $ $(reifyName [e| (*) |])
op'div :: Fractional a => Code (a->a->a)
op'div = Code . VarE $ $(reifyName [e| (/) |])
op'negate :: Num a => Code (a->a)
op'negate = Code . VarE $ $(reifyName [e| negate |])
op'recip :: Fractional a => Code (a->a)
op'recip = Code . VarE $ $(reifyName [e| recip |])

op'sin :: Floating a => Code (a->a)
op'sin = Code . VarE $ $(reifyName [e| sin |])
op'cos :: Floating a => Code (a->a)
op'cos = Code . VarE $ $(reifyName [e| cos |])
op'pi :: Floating a => Code a
op'pi = Code . VarE $ $(reifyName [e| pi |])

-- | Code expression combinators 
--
appC :: Code (a->b) -> Code a -> Code b
appC (Code f) (Code x) = Code $ AppE f x

-- | Lifting from primitive datatypes to Code
--
integerC :: Num a => Integer -> Code a 
integerC x = Code . LitE . integerL $ x
rationalC :: Fractional a => Rational -> Code a 
rationalC x = Code . LitE . rationalL $ x

-- | A distinguished variable (over which we differentiate)
new'diffVar :: Q (Var a)
new'diffVar = newName "dx" >>= return . Var

-- | Lift this variable to Code
var'exp :: Var a -> Code a
var'exp (Var name) = Code . VarE $ name

-- abstract over the differentiation variable
-- That is, convert from
--
-- > diffVar |- body 
--
-- to
--
-- > |- diffVar -> body
--
-- In this formulation, this looks exactly like the Deduction theorem!
-- We take advantage of the fact that TH is non-hygienic.
-- That is, instead of binding a fresh variable and traversing
-- the body replacing diffVar with that variable (as we should do
-- in MetaOCaml), we simply non-hygienically bind the diffVar.
-- We save ourselves the term traversal: normalization by evaluation.
--
reflectDF:: Var a -> Code a -> QCode (a->a)
reflectDF (Var name) (Code body) = 
    lam1E (varP name) (return body) >>= return . Code

e1 = [e| 1 + 2 |]
t1 = show_code e1
t2 (InfixE me1 (VarE name) me3) = reify name
t2' = show_code (e1 >>= t2)


-- | Intensional code analysis
-- Alas, TH.Exp is not a GADT. So, we have to do their emulation...
--
on'litC :: Code a -> Maybe (Code a)
on'litC c@(Code (LitE _)) = Just c
on'litC _ = Nothing

on'litRationalC :: Code a -> Maybe Rational
on'litRationalC (Code (LitE lit)) = 
    case lit of
         IntegerL x    -> Just $ toRational x
         IntPrimL x    -> Just $ toRational x
         RationalL x   -> Just x
         FloatPrimL x  -> Just x
         DoublePrimL x -> Just x
         _ -> Nothing
on'litRationalC _ = Nothing


on'varC :: Var a -> Code b -> Maybe (Either (Var a) (Var b))
on'varC v@(Var name) (Code c) | c == VarE name = Just (Left v)
on'varC _ (Code (VarE n)) = Just . Right . Var $ n
on'varC _ _ = Nothing

on'2opC :: Code (a->b->c) -> Code d -> Maybe (Code a, Code b)
on'2opC (Code op) (Code (AppE (AppE f x) y)) | op == f
    = Just (Code x,Code y)
on'2opC _ _ = Nothing

on'1opC :: Code (a->b) -> Code d -> Maybe (Code a)
on'1opC (Code op) (Code (AppE f x)) | op == f
    = Just (Code x)
on'1opC _ _ = Nothing
