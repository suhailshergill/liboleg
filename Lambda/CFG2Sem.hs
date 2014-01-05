-- | <http://okmij.org/ftp/gengo/NASSLLI10/>

module Lambda.CFG2Sem where

-- | CFG1Sem with type annotations
--
data Entity = John | Mary
  deriving (Eq, Show)

john, mary :: Entity
like       :: Entity -> Entity -> Bool
r2         :: (Entity -> Entity -> Bool) -> Entity -> (Entity -> Bool)
r1         :: Entity -> (Entity -> Bool) -> Bool

john   = John
mary   = Mary

-- | A new notation for `like' (which will be convenient later)
like   = \o s -> elem (s,o) [(John,Mary), (Mary,John)]

r2 f x = f x
r1 x f = f x

sentence :: Bool
sentence = r1 john (r2 like mary)

-- In the Sem interpretation, the bad_sentence
-- is ill-typed, as it should. Note the error message
{-
bad_sentence :: Bool
bad_sentence = r2 (r2 like mary) john
-}
