--
-- | <http://okmij.org/ftp/gengo/NASSLLI10/>
--

module Lambda.CFG1EN where

-- | Definitions (or, bookmarks) and CFG-like derivations
--
john   = "John"
mary   = "Mary"
like   = "likes"
r2 f x = f ++ " " ++ x
r1 x f = x ++ " " ++ f

sentence = r1 john (r2 like mary)
