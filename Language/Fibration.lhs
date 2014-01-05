 [Haskell] Applicative translucent functors in Haskell
 Chung-chieh Shan
 Mon Sep 13 15:20:33 EDT 2004
 http://www.haskell.org/pipermail/haskell/2004-September/014515.html
 Comment: added LANGUAGE pragmas.


On 2004-09-08T19:46:55+0200, Tomasz Zielonka wrote:
 ] On Wed, Sep 08, 2004 at 04:27:23PM +0100, Simon Peyton-Jones wrote:
 ]] The ML orthodoxy says that it's essential to give sharing constraints by
 ]] name, not by position.  If every module must be parameterised by every
 ]] type it may wish to share, modules might get a tremendous number of type
 ]] parameters, and matching them by position isn't robust. I think that
 ]] would be the primary criticism from a programming point of view.  I have
 ]] no experience of how difficult this would turn out to be in practice.
] How about named fields in type constructors? Something like Haskell's
] records but at type level. Seems like a fun extension ;)

Proponents of ML-style module systems emphasize the advantage
of `sharing by specification' (or `fibration') over `sharing by
construction' (or `parameterization') (MacQueen 1986; Pierce 2000;
Harper and Pierce 2003).  As Simon Peyton-Jones noted, in the context
of our translations of ML-style modules into System F-omega and
Haskell, sharing by specification gives type-equality constraints by
name, whereas sharing by construction gives type-equality constraints
by position.  Harper and Pierce (2003; Pierce 2000) give examples of
modular programming where the latter approach can lead to an exponential
number of parameters, which are clumsy to deal with at best.  It has
been often suggested that records at the type level be introduced to
address this issue (Jones 1995, 1996; Shao 1999a,b; Shan 2004; Tomasz
Zielonka in this discussion thread).

In this message, we (Oleg Kiselyov and Chung-chieh Shan) translate
Harper and Pierce's example into Haskell, using only the most common
Haskell extensions to give type-equality constraints by name and avoid
an exponential blowup.  This exercise suggests that, while type-level
records may be convenient to have in Haskell, they may not be strictly
necessary to express sharing by specification.  As shown below, we
can indeed refer to type parameters `by name', taking advantage of
the ability of a Haskell compiler to unify type expressions and bind
type variables.  Our technique may be generalizable to encode all
sharing by specification.  We hope this message helps clarify the
difference between the two sharing styles, and relate the ML and Haskell
orthodoxies.


First, let us demonstrate the exponential explosion of type variables.
We again will be using OCaml and Haskell in parallel, to make our
Haskell translation of module expression clearer.  Later we shall
show how we prevent the exponential explosion in Ocaml -- and how
to translate that solution to Haskell.  Again this message is a
doubly-literal code: both in OCaml and Haskell.  It can be loaded in
GHCi or Hugs -98 as it is.  To get the OCaml code, please filter the
text of the message with "sed -n -e '/^}/ s/^} //p'"

> {-# LANGUAGE MultiParamTypeClasses, FlexibleInstances #-}
> {-# LANGUAGE ScopedTypeVariables #-}
> {-# LANGUAGE FunctionalDependencies #-}
> {-# LANGUAGE UndecidableInstances #-}
> module Language.Fibration where

(The final solution arrived at by the end of this message does not
require -fallow-undecidable-instances above.)

Let us consider a module of the following interface (a signature, in
ML speak):

} module type FN = sig
}   type a
}   type b
}   val app  : a -> b
} end


This is the interface of a regular function.  It can be thought of
as a compiler stage or network protocol stack that translates one
intermediate language or representation (type a) into another (type b).
Here are two sample modules of that signature:

} module TIF = struct
}   type a = int
}   type b = float
}   let  app x = float_of_int x
} end
} 
} module TFI = struct
}   type a = float
}   type b = int
}   let  app x = truncate x + 1
} end


In our Haskell translation, a signature corresponds to a type class,
and an implementation (a structure, aka module) to an instance:

> class NFN a b where
>     napp:: a -> b
>
> instance NFN Integer Float where
>     napp x = fromInteger x
>
> instance NFN Float Integer where
>     napp x = truncate x + 1

Let us write a module that represents a composition appr . appl of
two FN-functions: appl: al->bl and appr: ar->br.  In order for the
composition to be well-formed, the result type of appl must be the
argument type of appr: bl = ar (which we will call the intermediate
type t).  Let us further suppose that we wish to make this intermediate
type explicit (e.g., for inspection, to resolve overloading, to invoke
the two intermediate functions separately, etc).  Thus we arrive at the
following interface:

} module type NFN1 = sig
}   type a1
}   type t
}   type b1
}   val  app1 : a1 -> b1
} end

Or, in Haskell

> class NFN1 a t b where
>     napp1:: t -> a -> b

Note that the type of the intermediate result is really needed in
Haskell, to resolve the overloading and properly select the instance.


The composition of two modules of the signature FN is computed by the
following transparent functor:

} module NFn1(L: FN)(R: (FN with type a = L.b)) = struct
}   type a1 = L.a
}   type t  = L.b
}   type b1 = R.b
}   let  app1 x = R.app (L.app x)
} end

It takes two modules of the signature FN, labeled L and R. We should
note a _sharing constraint_: the type a of module R must be the same
as the type b of module L. The result of the NFn1 is a module of the
signature NFN1.

Here is an example of using the module

} module TIFI = NFn1(TIF)(TFI)
} let test_tifi = TIFI.app1 7;; (* 8 *)


In Haskell, the functor corresponds to an instance with constraints
that correspond to the argument signatures. The sharing is expressed
by sharing of the names of type variables:

> instance (NFN a t, NFN t b) => NFN1 a t b where
>     napp1 t x = napp (napp x `asTypeOf` t)
>
> test_nfn1::Integer
> test_nfn1 = napp1 (undefined::Float) (7::Integer) -- 8

Suppose we wish to compose two modules NFN1 again. Again, we wish to
expose all intermediate types

} module type NFN2 = sig
}   type a2
}   type tl type t type tr
}   type b2
}   val  app2 : a2 -> b2
} end
} 
} module NFn2(L: NFN1)(R: (NFN1 with type a1 = L.b1)) = struct
}   type a2 = L.a1
}   type tl = L.t
}   type t  = L.b1
}   type tr = R.t
}   type b2 = R.b1
}   let  app2 x = R.app1 (L.app1 x)
} end


We should note again that the functor NFn2 imports two modules of the
signature NFN1 and re-exports their types, after relabeling them to avoid
ambiguity and applying the sharing constraint R.a1 = L.b1.

In Haskell:

> class NFN2 a tl t tr b where
>     napp2:: (tl,t,tr) -> a -> b
>
> instance (NFN1 a tl t, NFN1 t tr b) => NFN2 a tl t tr b where
>     napp2 (tl,t,tr) x = napp1 tr $ ((napp1 tl x) `asTypeOf` t)

We can do that again:

} module type NFN3 = sig
}   type a3
}   type tl type t type tr
}   type b3
}   val  app3 : a3 -> b3
} end
} 
} module NFn3(L: NFN2)(R: (NFN2 with type a2 = L.b2)) = struct
}   type a3  = L.a2
}   type tll = L.tl
}   type tl  = L.t
}   type trl = L.tr
}   type t   = L.b2
}   type tlr = R.tl
}   type tr  = R.t
}   type trr = R.tr
}   type b3  = R.b2
}   let  app3 x = R.app2 (L.app2 x)
} end


In Haskell:

> class NFN3 a tll tl tlr t trl tr trr b where
>     napp3:: ((tll,tl,tlr),t,(trl,tr,trr)) -> a -> b
>
> instance (NFN2 a tll tl tlr t, NFN2 t trl tr trr b)
>     => NFN3 a tll tl tlr t trl tr trr b where
>     napp3 (tl,t,tr) x = napp2 tr $ ((napp2 tl x) `asTypeOf` t)

Here is a usage example

} module TII = struct
}   type a = int
}   type b = int
}   let  app x = x + 2
} end
} 
} module NM1 = NFn1(TII)(TII)
} module NM2 = NFn2(NM1)(NM1)
} module NM3 = NFn3(NM2)(NM2)
} let test_nm3 = NM3.app3 5;;  (* 21 *)


> instance NFN Integer Integer where
>     napp x = x + 2
>
> test_nfn3:: Integer
> test_nfn3 = let i = undefined::Integer
> 		  i3 = (i,i,i)
> 	      in  napp3 (i3,i,i3) (5::Integer) -- 21

The exponential explosion of the type variables is apparent.  The term
expressions, the module expressions, and the sharing constraints are all
`linear'.  That is, if we wish to define another level of composition,
NFN4, we write an expression similar to NFn3, which, if we disregard the
type variables, has roughly the same size, in characters.  It's only
when we look at the type variables we see the explosion.  The explosion
can be overcome if could magically say: import module NFNn as L; import
module NFNn as R; make sure that L.bn = R.an; and re-export the rest.
Alas, we can't deal with the type variables of a structure 'in bulk'.
If we wish to re-export them, we have to enumerate them all.

The explosion is particularly apparent in Haskell, where we refer to
type parameters of a class by their position rather than by their name.
If we wish to write another level of composition, say, NFN4, we merely
need the first type variable NFN3 and the last type variable of NFN3.
Alas, we have to enumerate all the type variables in-between.


It turns out that we _can_ refer to type variables of a module `in bulk',
both in OCaml and in Haskell.  To do that, we introduce a more
structural representation:

} module type FN1 = sig
}   type a  type b  type t
}   module ML : (FN with type a = a and type b = t)
}   module MR : (FN with type b = b and type a = t)
}   val  app : a -> b
} end
} 
} module Fn1(L: FN)(R: (FN with type a = L.b)) = struct
}   type a = L.a   type b = R.b   type t = L.b
}   module ML = L  module MR = R
}   let  app x = R.app (L.app x)
} end
} 
} module type FN2 = sig
}   type a  type b  type t
}   module ML : (FN1 with type a = a and type b = t)
}   module MR : (FN1 with type b = b and type a = t)
}   val  app : a -> b
} end
} 
} module Fn2(L: FN1)(R: (FN1 with type a = L.b)) = struct
}   type a = L.a   type b = R.b   type t = L.b
}   module ML = L  module MR = R
}   let  app x = R.app (L.app x)
} end


The details of the two halves of the composition are stowed away in the
submodules ML and MR.  We avoid the explosion in Ocaml because we can
mention, for example, the type tl in NFN2 above as ML.t in FN2 instead.
We can build a chain of functions using source code of size logarithmic
in the length of the chain.

Let us extend the chain one more time for illustration, and show an
example:

} module type FN3 = sig
}   type a  type b  type t
}   module ML : (FN2 with type a = a and type b = t)
}   module MR : (FN2 with type b = b and type a = t)
}   val  app : a -> b
} end
} 
} module Fn3(L: FN2)(R: (FN2 with type a = L.b)) = struct
}   type a = L.a   type b = R.b   type t = L.b
}   module ML = L  module MR = R
}   let  app x = R.app (L.app x)
} end
} 
} module M1 = Fn1(TIF)(TFI)
} module M2 = Fn2(M1)(M1)
} module M3 = Fn3(M2)(M2)
} let test_m3 = M3.app 5;; (* 9 *)


With the help of Haskell type classes, we can also stow away the
detailed type information of a module.

First, we re-define our class representing the signature FN to take an
extra type parameter:

> class FN s a b | s -> a, s -> b where
>     app::  s -> a -> b

The parameter 's' is a `label' that uniquely identifies an instance of
the class FN: in other words, the label 's' represents a module of a
signature FN. The label is a `proxy' for the module. Here are a few
examples of such modules:

> instance FN (Integer->Float) Integer Float  where
>      app _ x = fromInteger x
>
> instance FN (Float->Integer) Float Integer  where
>      app _ x = truncate x + 1
>
> instance FN (Integer->Integer) Integer Integer where
>     app _ x = x + 2
>
> data L = L
> instance FN L Integer Integer where
>     app _ x = x + 2

In the last example, we used an `artificial' label `L'.  Now we can
write the signature and the functor FN1 that `composes' FN once, the
signature FN2 and the corresponding functor that compose FN twice,
etc.  However, because in Haskell an instance can refer to itself, we
can create a recursive functor and a signature:

> instance (FN u a t, FN v t b) => FN (u,v) a b where
>     app s = app (snd s) . app (fst s)

The FN instance above subsumes the old classes NFN1, NFN2, NFN3, etc.,
all under the same FN class:

> fn'1 = undefined :: (Integer->Float, Float->Integer)
> fn'2 = (fn'1, fn'1)
> fn'3 = (fn'2, fn'2)
> test_fn' = app fn'3 5 -- 9


If fn'1 is a 2-stage compiler, then fn'2 is a 4-stage compiler and
fn'3 is an 8-stage one.  The types of fn'1, fn'2, fn'3 above grow
exponentially, just as the Ocaml signature FN2 above is twice the size
of FN1 when expanded out.  But signature definitions in Ocaml and type
synonyms in Haskell allow us to avoid the explosion in the source code.

Even though the details of these composed modules are stowed away,
they are not hidden. Indeed, the label uniquely determines the the
module.  We can inspect the label or its type to find sub-labels,
which uniquely describe the intermediate modules and their internal
types.  For example, here is a Haskell function that runs the first 3
stages of an 8-stage compiler like fn'3:

> stages123of8 ~((s12,(s3,s4)),s5678)
>     = app s3 . app s12

The type of stages123of8 is inferred to be
  *Fibration> :t stages123of8
  stages123of8 :: forall b a s5678 s4 s3 s12 b1.
		  (FN s12 a b1, FN s3 b1 b) =>
		  ((s12, (s3, s4)), s5678) -> a -> b

Here ((s12,(s3,s4)),s5678) is a dummy type argument that identifies the
module (in other words, resolves the overloading).  Note that the term
and type above only mentions the parts of the module that are actually
used, not the exponentially-sized details of say s5678.  We thus avoid
exponential blowup and achieve sharing by specification.

> test_stagem3 = stages123of8 fn'3 5

  *Fibration> :t test_stagem3
  test_stagem3 :: Float
  *Fibration> test_stagem3
  6.0

We should point out that we have indeed accessed an intermediate type in
fn'3: although the whole compiler "app fn'3" maps Integer to Integer,
the first three stages map Integer to an intermediate type Float.  We
have taken a great advantage of the pattern-matching ability of the
Haskell compiler: the ability to unify one type expression with the
other and bind type variables.


REFERENCES

Robert Harper, and Benjamin C. Pierce. 2003.  Design issues in advanced
module systems.  In Advanced topics in types and programming languages,
ed. Benjamin C. Pierce. Cambridge: MIT Press.  Draft manuscript.

Mark P. Jones. 1995.  From Hindley-Milner types to first-class structures.
In Proceedings of the Haskell workshop, ed. Paul Hudak. Tech. Rep. YALEU/
DCS/RR-1075, New Haven: Department of Computer Science, Yale University.
http://www.cse.ogi.edu/~mpj/pubs/haskwork95.pdf

Mark P. Jones. 1996.  Using parameterized signatures to express modular
structure.  In POPL '96: Conference record of the annual ACM symposium
on principles of programming languages, 68-78. New York: ACM Press.
http://www.cse.ogi.edu/~mpj/pubs/paramsig.html
http://www.cse.ogi.edu/~mpj/pubs/paramsig.pdf

David B. MacQueen. 1986.  Using dependent types to express modular
structure.  In POPL '86: Conference record of the annual ACM symposium
on principles of programming languages, 277-286. New York: ACM Press.
http://www.cs.bell-labs.com/who/dbm/papers/popl86/paper.ps

Benjamin C. Pierce. 2000.  Advanced module systems: A guide for the
perplexed.  ICFP invited talk.
http://www.cis.upenn.edu/~bcpierce/papers/modules-icfp.ps

Chung-chieh Shan. 2004.  Higher-order modules in System F-omega and
Haskell.  Draft manuscript.
http://www.cs.rutgers.edu/~ccshan/xlate/xlate.pdf

Zhong Shao. 1999a.  Transparent modules with fully syntactic signatures.
In ICFP '99: Proceedings of the ACM international conference on functional
programming, vol. 34(9) of ACM SIGPLAN Notices, 220-232. New York:
ACM Press.
http://flint.cs.yale.edu/flint/publications/fullsig.pdf

Zhong Shao. 1999b.  Transparent modules with fully syntactic signatures.
Tech. Rep. YALEU/ DCS/ TR-1181, Department of Computer Science, Yale
University, New Haven.
http://flint.cs.yale.edu/flint/publications/fullsig-tr.pdf

