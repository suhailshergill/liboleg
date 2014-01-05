{-# LANGUAGE PatternGuards #-}
-- | A model of the evaluation of logic programs (i.e., resolving Horn clauses)
--
-- The point is not to re-implement Prolog with all the conveniences
-- but to formalize evaluation strategies such as SLD, SLD-interleaving, 
-- and others.
-- The formalization is aimed at reasoning about termination and
-- solution sequences. See App A and B of the full FLOPS 2008 paper 
-- (the file arithm.pdf in this directory).
--
module Language.DefinitionTree where

import Data.Map
import Prelude hiding (lookup)

-- | A logic var is represented by a pair of an integer
-- and a list of `predicate marks' (which are themselves
-- integers). Such an odd representation is needed to
-- ensure the standardization apart: different instances
-- of a clause must have distinctly renamed variables.
-- Unlike Claessen, we get by without the state monad
-- to generate unique variable names (labels). See the
-- discussion and examples in the `tests' section below.
-- Our main advantage is that we separate the naming of
-- variables from the evaluation strategy. Evaluation
-- no longer cares about generating fresh names, which
-- notably simplifies the analysis of the strategies.
-- Logic vars are typed, albeit phantomly.
type VStack = [Int]
type LogicVar term = (Int,VStack)

-- | A finite map from vars to terms (parameterized over the domain of terms)
type Subst term = Map (LogicVar term) term


-- | Formulas 
--
-- A formula describes a finite or _infinite_ AND-OR tree
-- that encodes the logic-program clauses that may be needed to
-- evaluate a particular goal.
-- We represent a goal g(t1,...,tn) by a combination of the goal
-- g(X1,...,Xn), whose arguments are distinct fresh logic
-- variables, and a substitution {Xi=ti}. For a goal
-- g(X1,...,Xn), a |Formula| encodes all the clauses of the
-- logic program that could possibly prove g, in their order. Each
-- clause 
--
-- > g(t1,...,tn) :- b1(t11,...,t1m), ...
--
-- is represented by the (guarding) substitution {Xi=ti, Ykj=tkj}
-- and the sequence of the goals bk(Yk1,...,Ykm) in the body. 
-- Each of these goals is again encoded as a |Formula|. 
-- All variables in the clauses are renamed to ensure the standardization apart.
--
-- Our trees are similar to Antoy's definitional trees, used to encode
-- rewriting rules and represent control strategies in
-- term-rewriting systems and _functional logic_ programming.
-- However, in definitional trees, function calls can be nested, 
-- and patterns are linear.
--
-- The translation from Prolog is straightforward; the first step
-- is to re-write clauses so that the arguments of each goal are 
-- logic variables:
-- A fact 
--
-- >    g(term).
--
-- is converted to
--
-- >    g(X) :- X = term.
--
-- A clause
--
-- >    g(term) :- g1(term1), g2(term2).
--
-- is converted to
--
-- >    g(X) :- X = term, _V1 = term1, g1(_V1), _V2=term2, g2(_V2).
--
-- See the real examples at the end
--
-- A formula (parameterized by the domain of terms) is an OR-sequence
-- of clauses
data Formula term = Fail | (Clause term) :+: (Formula term)

-- | A clause is a guarded body; the latter is an AND-sequence of formulas
data Clause term = G (Subst term) (Body term)

data Body term   = Fact  | (Formula term) :*: (Body term)

infixr 6 :+:
infix  7 `G`
infixr 8 :*:

--             Evaluation of formulas

-- | The evaluation process starts with a formula and the initial
-- substitution, which together represent a goal.  The
-- guarding substitution of the clause conjoins with the current
-- substitution to yield the substitution for the evaluation of the body. 
-- The conjunction of substitutions may lead to a contradiction, 
-- in which case the clause is skipped (`pruned').
--
-- Evaluation as pruning: we traverse a tree and prune away failed branches
prune :: Unifiable term => Formula term -> Subst term -> Formula term
prune Fail _ = Fail
prune (cl :+: f2) s = case prunec cl s of
                       Nothing -> prune f2 s
                       Just cl -> cl :+: prune f2 s

prunec :: Unifiable term => Clause term -> Subst term -> Maybe (Clause term)
prunec (G s' b) s  = case unify s s' of
                      Nothing -> Nothing
                      Just s  -> case pruneb b s of
                                  Nothing -> Nothing
                                  Just b -> Just $ G s b
pruneb Fact s = Just Fact
pruneb (f :*: b) s  = case prune f s of
                       Fail -> Nothing
                       f    -> case pruneb b s of
                               Nothing -> Nothing
                               Just b  -> Just $ f :*: b

-- one may also try to push disjunctions up using distributivity...


-- | A different evaluator: Evaluate a tree to a stream (lazy list)
-- given the initial substitution s.
-- Here we use the SLD strategy.
eval :: Unifiable term => Formula term -> Subst term -> [Subst term]
eval Fail _ = []
eval  (cl :+: f2) s = evalc cl s ++ eval f2 s
evalc (G s' b) s    = maybe [] (evalb b) $ unify s s'
evalb Fact s        = [s]
evalb (f :*: b) s   = concatMap (evalb b) (eval f s) 

-- | Same as above, using the SLD-interleaving strategy.
-- See Definition 3.1 of the LogicT paper (ICFP05)
evali :: Unifiable term => Formula term -> Subst term -> [Subst term]
evali Fail _        = []
evali (cl :+: f2) s = evalic cl s `interleave` evali f2 s
evalic (G s' b) s   = maybe [] (evalib b) $ unify s s'
evalib Fact s       = [s]
evalib (f :*: b) s  = fairConcatMap (evalib b) (evali f s)
  where fairConcatMap k [] = []
        fairConcatMap k (a:m) = interleave (k a) (fairConcatMap k m)

interleave [] m = m
interleave (a:m1) m2 = a : (interleave m2 m1)

--              Terms and substitutions

-- | Evaluation, substitutions and unification are parametric over terms
-- (term algebra), provided the following two operations are defined.
-- We should be able to examine a term and determine if it is a variable
-- or a constructor (represented by an integer) applied to a sequence of
-- zero or more terms. Conversely, given a constructor (represented by an
-- integer) and a list of terms-children we should be able to build a term.
-- The two operations must satisfy the laws:
--
-- > either id build . classify === id
-- > classify . build === Right
--
class Unifiable term where
    classify :: term -> Either (LogicVar term) (Int,[term])
    build    :: (Int,[term]) -> term

-- | building substitutions
bv :: LogicVar term -> term -> Subst term
bv x = singleton x

ins :: Subst term -> (LogicVar term, term) -> Subst term
ins m (v,t) = insert v t m

-- | Apply a substitution to a term
sapp :: Unifiable term => Subst term -> term -> term
sapp s t = either dov donv $ classify t
 where dov v          = maybe t id $ lookup v s -- term is a variable
       donv (ctr, ts) = build (ctr, Prelude.map (sapp s) ts) -- non-var term


-- | Conjoin two substitutions (see Defn 1 of the FLOPS 2008 paper).
-- We merge two substitutions and solve the resulting set of equations, 
-- returning Nothing if the two original substitutions are contradictory.
unify :: Unifiable term => Subst term -> Subst term -> Maybe (Subst term)
unify s1 s2 = solve empty $ foldWithKey fld (foldWithKey fld [] s1) s2 
  where
  fld v t l = (Left v,t) : l

-- | Solve the equations using the naive realization of the 
-- Martelli and Montanari process
solve :: Unifiable term => Subst term -> 
         [(Either (LogicVar term) term,term)] -> 
         Maybe (Subst term)
solve s [] = Just s
solve s ((Left v,t):r) = either dov donv $ classify t
  where dov v' = if v == v' then solve s r else add'cont
        donv _ = add'cont -- skip the occurs check
        s' = insert v t s
        add'cont = solve s' (Prelude.map (sapp'eq s') r)
        sapp'eq s (Left v,t) = (maybe (Left v) Right $ lookup v s, sapp s t)
        sapp'eq s (Right t1,t2) = (Right $ sapp s t1, sapp s t2)
solve s ((Right t1,t2):r) = 
  case (classify t1, classify t2) of
    (Left v,_) -> solve s $ (Left v,t2):r
    (_,Left v) -> solve s $ (Left v,t1):r
    (Right (ctr1,ts1),Right (ctr2,ts2)) 
        | ctr1 == ctr2, length ts1 == length ts2 ->
            solve s $ (zipWith (\x y -> (Right x,y)) ts1 ts2) ++ r
    _ -> Nothing



--              Tests and examples

-- | Unary numerals
--
data UN = UNv (LogicVar UN)
        | UZ
        | US UN 
          deriving (Eq, Show)

-- | Constructor UZ is represented by 0, and US is represented by 1
instance Unifiable UN where
    classify (UNv v) = Left v
    classify UZ      = Right (0,[])
    classify (US n)  = Right (1,[n])

    build (0,[])  = UZ
    build (1,[n]) = US n


-- | Encoding of variable names to ensure standardization apart.
-- A clause such as genu(X) or add(X,Y,Z) may appear in the tree
-- (infinitely) many times. We must ensure that each instance uses distinct
-- logic variables. To this end, we name variables by a pair (Int, VStack)
-- whose first component is the local label of a variable within a clause.
-- VStack is a path from the root of the tree to the current occurrence
-- of the clause in the tree. Each predicate along the path is represented
-- by an integer label (0 for genu, 1 for add, 2 for mul, etc). 
-- To `pass' arguments to a clause, we add to the current substitution
-- the bindings for the variables of that clause. See the genu' example
-- below: whereas (0,h) is the label of the variable X in the current
-- instance of genu, (0,genu_mark:h) is X in the callee.
--
-- A logic program
--
-- > genu([]).
-- > genu([u|X]) :- genu(X).
--
-- and the goal genu(X) are encoded as follows. The argument of genu' is
-- the path of the current instance of genu' from the top of the AND-OR
-- tree.
--
genu :: Formula UN
genu = genu' []
 where
 genu' h = (bv x UZ) `G` Fact :+: 
           (bv x (US (UNv x'))) `G` (genu' h') :*: Fact :+:
           Fail
   where x = (0,h)
         h' = genu_mark:h
         x' = (0,h')
         genu_mark = 0

test1 = take 5 (eval genu empty)
{-
*SLD> test1
  [fromList [((0,[]),UZ)],
   fromList [((0,[]),US UZ),((0,[0]),UZ)],
   fromList [((0,[]),US (US UZ)),((0,[0]),US UZ),((0,[0,0]),UZ)],
   fromList [((0,[]),US (US (US UZ))),((0,[0]),US (US UZ)),
             ((0,[0,0]),US UZ),((0,[0,0,0]),UZ)],
   fromList [((0,[]),US (US (US (US UZ)))),((0,[0]),US (US (US UZ))),
             ((0,[0,0]),US (US UZ)),((0,[0,0,0]),US UZ),((0,[0,0,0,0]),UZ)]]
-}


-- A logic program with the goal add(X,Y,Z)
--  add([],X,X).
--  add([u|X],Y,[u|Z]) :- add(X,Y,Z).
-- is encoded as follows. The labels of local variables are:
-- X is 0, Y is 1, Z is 2. 

add :: VStack -> Formula UN
add h = (bv x UZ) `ins` (y,(UNv z)) `G` Fact :+:
        (bv x (US (UNv x'))) `ins` (y,UNv y') `ins` (z,US (UNv z'))
            `G` add h' :*: Fact :+:
        Fail
  where
   [x,y,z]    = Prelude.map (\n->(n,h)) [0..2]  -- vars in the current call
   h' = add_mark:h
   [x',y',z'] = Prelude.map (\n->(n,h')) [0..2] -- vars in the recursive call
add_mark = 1

test2 = take 3 (eval (add []) empty)

{-
*SLD> test2
  [fromList [((0,[]),UZ),((1,[]),UNv (2,[]))],
   fromList [((0,[]),US UZ),((0,[1]),UZ),((1,[]),UNv (2,[1])),
             ((1,[1]),UNv (2,[1])),((2,[]),US (UNv (2,[1])))],
   fromList [((0,[]),US (US UZ)),((0,[1]),US UZ),((0,[1,1]),UZ),
             ((1,[]),UNv (2,[1,1])),((1,[1]),UNv (2,[1,1])),
             ((1,[1,1]),UNv (2,[1,1])),((2,[]),US (US (UNv (2,[1,1])))),
             ((2,[1]),US (UNv (2,[1,1])))]]

Note that (0,[]) is the top-level X, (1,[]) is teh top-level Y,
(2,[]) is the top-level Z. In the more concise notation, the above
list of substitution reads:
  [(X,0), (Y,Z)]
  [(X,1), (Y,Z'), (Z, succ(Z'))]
  [(X,2), (Y,Z''), (Z,succ (succ (Z'')))]
-}

test3 = take 3 (evali (add []) empty)
-- the same as test2

-- A logic program with the goal mul(X,Y,Z) (Sec 2.3 of the FLOPS paper)
--  mul([],_,[]).
--  mul([u|_],[],[]).
--  mul([u|X],[u|Y],Z) :- add([u|Y],Z1,Z), mul(X,[u|Y],Z1).
-- is converted into
--  mul(X,Y,Z) :- X=[], Z=[].
--  mul(X,Y,Z) :- X=[u|X1], Y=[], Z=[].
--  mul(X,Y,Z) :- X=[u|X1], Y=[u|Y1], 
--                AddX=Y,  AddY=Z1, AddZ=Z,
--                MulX=X1, MulY=Y,  MulZ=Z1, 
--                add(AddX,AddY,AddZ), mul(MulX,MulY,MulZ).

-- is encoded as follows. The labels of local variables are:
-- X is 0, Y is 1, Z is 2.

mul :: VStack -> Formula UN
mul h = (bv x UZ) `ins` (z,UZ) `G` Fact :+:

        (bv x (US (UNv x1))) `ins` (y,UZ) `ins` (z,UZ) `G` Fact :+:

        (bv x (US (UNv x1))) `ins` (y,US (UNv y1)) `ins`
        (addx,(UNv y)) `ins` (addy,(UNv z1)) `ins` (addz,(UNv z)) `ins`
        (mulx,(UNv x1)) `ins` (muly,(UNv y)) `ins` (mulz,(UNv z1))
        `G` add h'add :*: mul h'mul :*: Fact :+:
      Fail
  where
   [x,y,z,x1,y1,z1] = Prelude.map (\n->(n,h)) [0..5]
   h'add = add_mark:h -- frame for the call to add
   h'mul = mul_mark:h -- frame for the recursive call to mul
   [addx,addy,addz] = Prelude.map (\n->(n,h'add)) [0..2]
   [mulx,muly,mulz] = Prelude.map (\n->(n,h'mul)) [0..2]
mul_mark = 2

test4 = take 6 . Prelude.map proj_xyz $ (eval (mul []) empty)
test5 = take 8 . Prelude.map proj_xyz $ (evali (mul []) empty)

proj_xyz s = (pv 0, pv 1, pv 2)
 where
 pv n = maybe (UNv (n,[])) chase $ lookup (n,[]) s
 chase t = let t' = sapp s t in if t == t' then t else chase t'

{-
*SLD> test4
  [(UZ,UNv (1,[]),UZ),
   (US (UNv (3,[])),UZ,UZ),
   (US UZ,US UZ,US UZ),
   (US (US UZ),US UZ,US (US UZ)),
   (US (US (US UZ)),US UZ,US (US (US UZ))),
   (US (US (US (US UZ))),US UZ,US (US (US (US UZ))))]

This result matches the one mentioned on p10 of the paper (mul for SLD
without interleaving). In each solution except the first two, Y is 1.

For interleaving, the picture is different:

*SLD> test5
  [(UZ,UNv (1,[]),UZ),
   (US (UNv (3,[])),UZ,UZ),
   (US UZ,US UZ,US UZ),                     -- (1,1,1)
   (US UZ,US (US UZ),US (US UZ)),           -- (1,2,2)
   (US (US UZ),US UZ,US (US UZ)),           -- (2,1,1)
   (US UZ,US (US (US UZ)),US (US (US UZ))), -- (1,3,3)
   (US (US (US UZ)),US UZ,US (US (US UZ))), -- (3,1,3)
   (US (US UZ),US (US UZ),US (US (US (US UZ))))] -- (2,2,4)
-}
