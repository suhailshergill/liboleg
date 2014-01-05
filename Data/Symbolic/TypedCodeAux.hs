{-# OPTIONS -fglasgow-exts #-}
{-# LANGUAGE TemplateHaskell #-}

-- | Obtain the Name that corresponds to a top-level (Prelude-level)
-- Haskell identifier.
-- Given an expression such as [e| (+) |] we return the expression
-- that is the application of mkNameG_v to the correct strings.
-- That expression, when spliced in, will compute exactly the same
-- name that corresponds to the one we started with, that is, (+).
-- Note that (+) was the identifier, not the name.
-- The result of splicing reifyName can be used in splices
-- (see the Diff.hs for examples).
-- We essentially apply the TH to itself and emulate more than one stage
-- of computation.
--
module Data.Symbolic.TypedCodeAux where

import Language.Haskell.TH
import Language.Haskell.TH.Syntax
import Language.Haskell.TH.Ppr

reifyName :: Q Exp -> Q Exp

{- For GHC prior to 6.6, use the following code. TH has changed in
   GHC 6.6
reifyName nameE = nameE >>= 
		    \ (VarE (Name occname (NameG VarName mn))) -> 
			[e| mkNameG_v $(litE . stringL . modString $ mn)
			 $(litE . stringL . occString $ occname)|]

-}

reifyName nameE = nameE >>= 
		    \ (VarE (Name occname (NameG VarName pn mn))) -> 
			[e| mkNameG_v
			 $(litE . stringL . pkgString $ pn)
			 $(litE . stringL . modString $ mn)
			 $(litE . stringL . occString $ occname)|]



{-
  Remnants of early experiments

foo = $([e| (+) |] >>= \ (VarE name) -> global name)
-- foo1 = $([e| (+) |] >>= \ (VarE name) -> global $ mkName "GHC.Num.+")
foo1 = $([e| (+) |] >>= \ (VarE (Name occname (NameG VarName mn))) -> 
	 [e| mkNameG_v $(litE . stringL . modString $ mn)
	               $(litE . stringL . occString $ occname)|])
-}
