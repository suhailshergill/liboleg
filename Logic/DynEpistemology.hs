-- | Dynamic Epistemic Logic: solving the puzzles from
-- Hans van Ditmarsch's tutorial course on Dynamic Epistemic Logic,
-- NASSLLI 2010, June 20, 2010.
-- See also
--
-- Dynamic Epistemic Logic and Knowledge Puzzles
-- H.P. van Ditmarsch, W. van der Hoek, and B.P. Kooi
-- <http://www.csc.liv.ac.uk/~wiebe/pubs/Documents/iccs.pdf>
--
-- Epistemic Puzzles
-- Hans van Ditmarsch
-- <http://www.cs.otago.ac.nz/staffpriv/hans/cosc462/logicpuzzlesB.pdf>
--
--
-- We encode the statement of the problem as a filter on
-- possible worlds.
-- The possible worlds consistent with the statement of
-- the problem are the solutions.
--
-- > "Agent A does not know proposition phi" is interpreted
--
-- as the statement that for all worlds consistent with the propositions
-- A currently knows, phi is true in some but false in the others.
--
-- <http://okmij.org/ftp/Algorithms.html#dyn-epistemology>
--
module Logic.DynEpistemology where

import qualified Data.Map as M
import Control.Monad
import Data.List (sortBy, groupBy)

-- ------------------------------------------------------------------------
-- | Problem 1
-- Anne and Bill each privately receive a natural number.
-- Their numbers are consecutive.
-- The following truthful conversation takes place:
--
-- > Anne: I don't know your number
-- > Bill: I don't know your number either
-- > Anne: I know your number.
-- > Bill: I know your number too.
--
-- If Anne has received the number 2, what was the number
-- received by Bill?
-- This puzzle is also known as `Conway paradox': it appears
-- that Anne and Bill have truthfully made contradictory statements.
--
-- A possible world for a problem 1:
-- numbers received by Anne and Bill
--
type P1World = (Int,Int)

-- | The number Anne received in the world w
p1_anne :: P1World -> Int
p1_anne = fst

-- | The number Bill received in the world w
p1_bill :: P1World -> Int
p1_bill = snd

-- | An initial stream of possible worlds for problem 1
p1worlds :: MonadPlus m => m P1World
p1worlds = do
  anne_number <- nat
  bill_number <- choose [anne_number + 1, anne_number - 1]
  guard (bill_number >= 0)
  return (anne_number,bill_number)

-- | Encoding the statement of the problem: the conversation steps.
-- The remaining possible world gives us the solution.
prob1 :: [P1World]
prob1 = take 1 $ 
        p1worlds 
        `andthen`
          nonunique (\w -> [p1_anne w]) -- Anne's statement 1
        `andthen`
          nonunique (\w -> [p1_bill w]) -- Bill's statement
        `andthen`
          filter (\w -> p1_anne w == 2) -- Anne's statement 2
-- Answer:
-- [(2,3)]
-- That is, Bill's number is 3.


-- | A variation of the problem:
-- Assuming the numbers don't exceed 100, what
-- are the numbers received by Anne and Bill?
-- Again, the possible worlds consistent with the statement of
-- the problem are the solutions.
prob1a :: [P1World]
prob1a = p1worlds 
         `andthen`
           nonunique (\w -> [p1_anne w]) -- Anne's statement 1
         `andthen`
           nonunique (\w -> [p1_bill w]) -- Bill's statement
         `andthen`
           unique (\w -> [p1_anne w]) (>100) -- Anne's statement 2
-- Answer
-- [(1,2),(2,3),(100,99)]

-- | Spelling out the `unique' condition, to demonstrate what it means
prob1a' :: [[P1World]]
prob1a' = p1worlds 
         `andthen`
           nonunique (\w -> [p1_anne w]) -- Anne's statement 1
         `andthen`
           nonunique (\w -> [p1_bill w]) -- Bill's statement
         `andthen`
           takeWhile (\w -> p1_anne w <= 100)
         `andthen`
           sortBy (\w1 w2 -> compare (p1_anne w1) (p1_anne w2)) 
         `andthen`
           groupBy (\w1 w2 -> p1_anne w1 == p1_anne w2) 
         `andthen` 
           filter (\l -> length l == 1)
-- [[(1,2)],[(2,3)],[(100,99)]]

-- ------------------------------------------------------------------------
-- | Problem 2
--
-- Anne, Bill and Cath each have a positive natural number written on
-- their foreheads. They can only see the foreheads of others.
-- One of the numbers is the sum of the other two. All the previous
-- is common knowledge. The following truthful conversation takes place:
--
-- > Anne: I don't know my number.
-- > Bill: I don't know my number.
-- > Cath: I don't know my number.
-- > Anne: I now know my number, and it is 50.
--
-- What are the numbers of Bill and Cath?
-- Math Horizons, November 2004. Problem 182.
--
-- A possible world for a problem 1:
-- numbers received by Anne, Bill, and Cath
type P2World = (Int,Int,Int)

-- | The number on Anne's forehead in the world w
p2_anne :: P2World -> Int
p2_anne (x,_,_) = x

-- | If Anne sees the number x on Bill's forehead and the
-- number y on Cath's forehead, what numbers could be
-- on Anne's forehead?
-- In other words, compute the set of possible worlds
-- that are indistinguishable from the world w as far as
-- Anne is concerned.
p2_anne_keys :: P2World -> [P2World]
p2_anne_keys (_,x,y) = [(abs (x-y),x,y),(x+y,x,y)]

-- | The number on Bill's forehead in the world w
p2_bill :: P2World -> Int
p2_bill (_,x,_) = x

-- | Which worlds Bill can't distinguish
p2_bill_keys :: P2World -> [P2World]
p2_bill_keys (x,_,y) = [(x,abs (x-y),y),(x,x+y,y)]

-- | The number on Cath's forehead in the world w
p2_cath :: P2World -> Int
p2_cath (_,_,x) = x

-- | Ditto for Cath
p2_cath_keys :: P2World -> [P2World]
p2_cath_keys (x,y,_) = [(x,y,abs (x-y)),(x,y,x+y)]

-- | An initial stream of possible worlds for problem 2.
-- The code is naive but hopefully obviously correct
-- as it clearly corresponds to the statement of the problem.
p2worlds :: MonadPlus m => m P2World
p2worlds = do
  sum <- iota 1
  summand1 <- choose [1..sum]
  let summand2 = sum - summand1
  guard $ summand1 >= 1 && summand2 >= 1
  choose [(summand1,summand2,sum),
          (sum,summand1,summand2),
          (summand2,sum,summand1)]


-- | Encoding the statement of the problem: the conversation steps.
-- The remaining possible world gives us the solution.
prob2 :: [P2World]
prob2 = take 1 $ 
        p2worlds
        `andthen`
          nonunique p2_anne_keys -- Anne does not know her number
        `andthen`
          nonunique p2_bill_keys -- Neither does Bill his
        `andthen`
          nonunique p2_cath_keys -- or Cath her
        `andthen`
          unique p2_anne_keys (\(x,_,_) -> x > 200) -- Anne now knows her number
        `andthen`
          filter (\w -> p2_anne w == 50)
-- answer
-- [(50,20,30)]


-- ------------------------------------------------------------------------
-- Utility functions

-- | Reverse application
infixl 1 `andthen`
andthen = flip ($)


choose :: MonadPlus m => [a] -> m a
choose = foldr (mplus . return) mzero 

-- | A stream of naturals
nat :: MonadPlus m => m Int
nat = iota 0

-- | A stream of integers starting with n
iota :: MonadPlus m => Int -> m Int
iota n = return n `mplus` iota (succ n)



-- | Filter a set of possible worlds
-- Given a proj function (yielding a set of keys for a world w),
-- return a stream of worlds that are not unique with
-- respect to their keys. That is, there are several
-- worlds with the same key.
-- Our state is a set of quarantined worlds.
-- When we receive a world whose key we have not seen,
-- we quarantine it. We release from the quarantine
-- when we encounter the same key again.
-- Our function is specialized to the List monad. In general,
-- we need MonadMinus (see the LogicT paper), of which List is an instance.
--
nonunique :: Ord key => (w -> [key]) -> [w] -> [w]
nonunique proj worlds = loop M.empty worlds
 where
 loop quarantine [] = []
 loop quarantine (w:ws) = 
     decide quarantine w ws . 
     map (\key -> (key,M.lookup key quarantine)) $ 
     proj w

     -- we have not seen that key yet, quarantine
 decide q w ws res@((k,_):rest) | all (\ (_,v)-> isNothing v) res =
     let q'  = M.insert k (Just w) q
         q'' = foldr (\ (k,_) -> M.insert k Nothing) q' rest in
     loop q'' ws

     -- we have seen a key, one or more times.
     -- If a world has been quarantined, release it
 decide q w ws res =
      let released = foldr (\ (_,v) -> maybe id (maybe id (:)) v) [] res
          q' = foldr (\ (k,v) -> maybe id (\_ -> M.insert k Nothing) v) q res
      in released ++ w:(loop q' ws)

isNothing Nothing = True
isNothing _       = False

-- | Given a proj function (yielding a set of keys for a world w),
-- return a stream of worlds that are unique with
-- respect to their keys. That is, there is only one
-- world for the key.
-- We accept a termination criterion.
-- We terminate the stream once we have received the key
-- for which the criterion returns true.
-- When we receive a world whose key we have not seen,
-- we quarantine it. We release from the quarantine
-- when the stream is terminated.
--
unique :: Ord key => (w -> [key]) -> (key -> Bool) -> [w] -> [w]
unique proj maxkey worlds = loop M.empty worlds
 where
 loop quarantine [] = M.fold (\x a -> maybe a (:a) x) [] quarantine
 loop quarantine (w:ws) = 
     let keys = proj w in
     if any maxkey keys then loop quarantine []
        else 
        decide quarantine w ws . 
        map (\key -> (key,M.lookup key quarantine)) $ keys

     -- we have not seen that key yet, quarantine
 decide q w ws res@((k,_):rest) | all (\ (_,v)-> isNothing v) res =
     let q'  = M.insert k (Just w) q
         q'' = foldr (\ (k,_) -> M.insert k Nothing) q' rest in
     loop q'' ws

     -- we have seen a key, one or more times. Skip w
 decide q w ws res =
      let q' = foldr (\ (k,v) -> maybe id (\_ -> M.insert k Nothing) v) q res
      in loop q' ws
