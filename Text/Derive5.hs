{-# LANGUAGE NoMonomorphismRestriction #-}

-- | Deriving type-safe printf in direct-style, using
-- shift/reset with effectful typing (supporting the answer-type
-- modification and polymorphism)
--
module Text.Derive5 where

import Control.Monad

import Control.ShiftResetGenuine

-- | Constructors and deconstructors of a particular sequence
-- See the end of derive5.ml
--
nilA :: Monadish m => a -> m s s a
nilA = ret

{-
consA :: (Monadish m) =>
         h -> (sigma -> m a b tau) -> (h -> m b g sigma) -> m a g tau
-}
consA h t = \f -> f h >== \x -> t x

un_consA x = reset (x (\h -> shift (\t -> ret (h,t))))


-- | The example of the de-construction:
--
l0 = consA 'a' nilA
l0r = fst $ run $ un_consA l0
-- 'a'

l1 = consA 5 (consA 'a' (consA 'f' nilA))
(h1,l11) = run $ un_consA l1
-- h1 is 5
(h2,l12) = run $ un_consA l11
-- h2 is 'a'

nilS :: String
nilS = ""
consS :: String -> String -> String
consS = (++)

-- litP4 :: (Monadish m) => String -> (t -> m a g String) -> t -> m a g String
litP4 str = \tD arg -> tD arg >== ret . consS str 

intP4 = \tD arg ->
  un_consA arg >== \(n,l2) ->
  tD l2 >== ret . consS (show (n::Int)) 

charP4 = \tD arg ->
  un_consA arg >== \(c,l2) ->
  tD l2 >== ret . consS (show (c::Char)) 

nilDP        = \x -> x nilS
consDP d acc = \x -> d acc x

desc0 = consDP (litP4 "lit") $ consDP intP4 nilDP
desc0r = run $ desc0 (consA 1 nilA)
-- "lit1"

desc4P = consDP intP4
    (consDP (litP4 "-th character after ")
       (consDP charP4
          (consDP (litP4 " is ")
             (consDP charP4
                nilDP))))

desc4r = run $ desc4P (consA 5 (consA 'a' (consA 'f' nilA)))
-- "5-th character after 'a' is 'f'"

t0 = \h -> reset (shift (\k -> desc0 k) >== \f -> f h)

{-
 We would like the argument sequence to be just the application of the
 arguments. We would like to transform
  (xxx x1 x2 x3)
to (fun f -> f x1 x2 x3), which is needed as an argument to desc4P.
We can do that if we enclose the whole printf expression in reset.
-}

-- Apply a monadish f to the pure argument x
app fm x = fm >== \f -> f x

t1 = (shift desc4P) `app` 5 `app` 'a' `app` 'f'
-- t1 :: C String String String

t1r = run $ reset t1
-- "5-th character after 'a' is 'f'"

-- A different take, viewing un_consA as `reading' from a sequence

is_nilA1 _ = ()

un_consA1 x = shift (\k -> ret $ \y -> k (y,()))

litP5 = litP4

intP5 = \tD arg ->
  un_consA1 arg >== \(n,l2) ->
  tD l2 >== ret . consS (show (n::Int)) 

charP5 = \tD arg ->
  un_consA1 arg >== \(c,l2) ->
  tD l2 >== ret . consS (show (c::Char)) 

nilDP5 _ = ret nilS

desc05 = consDP (litP5 "lit") $ consDP intP5 nilDP5
desc05r = run $ (reset (desc05 ()) `app` 5)
-- "lit5"

desc5P = consDP intP5
    (consDP (litP5 "-th character after ")
       (consDP charP5
          (consDP (litP5 " is ")
             (consDP charP5
                nilDP5))))

printf5 desc = reset (desc ())

desc5r = run $ printf5 desc5P `app` 5 `app` 'a' `app` 'f'
-- "5-th character after 'a' is 'f'"

-- After several transformations described in the paper (eta-reductions mainly)

litP7 str = \() -> ret str

intP7 = \() ->
  shift (\k -> ret k) >== \n ->
  ret (show (n::Int))

charP7 = \() ->
  shift (\k -> ret k) >== \c ->
  ret (show (c::Char))


infixr 7 ^^^ 
-- Lifted string concatenation
f ^^^ g = \() -> f () >== \s1 ->
                 g () >== \s2 ->
		 ret (s1 ++ s2)


printf7 desc = reset $ desc ()

desc7P = intP7 ^^^ (litP7 "-th character after ") ^^^ charP7 ^^^
	 (litP7 " is ") ^^^ charP7


desc7r = run $ printf7 desc7P `app` 5 `app` 'a' `app` 'f'
-- "5-th character after 'a' is 'f'"
