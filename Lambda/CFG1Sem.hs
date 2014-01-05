--
-- | <http://okmij.org/ftp/gengo/NASSLLI10/>
--

module Lambda.CFG1Sem where

-- | Semantic interpretation of a CFG derivation
--
-- In conventional notation:
--
-- > D_e = {John, Mary}
--
data Entity = John | Mary
  deriving (Eq, Show)

john   = John
mary   = Mary

like o s =  (o == John && s == Mary ) || 
            (o == Mary && s == John )

-- | A different way of writing it: by cases
like' Mary John = True
like' John Mary = True
like' _    _    = False

r2 f x = f x
r1 x f = f x

-- | sentence has the same form as in CFG1.hs,
-- but a different value (interpretation)
--
sentence = r1 john (r2 like mary)
