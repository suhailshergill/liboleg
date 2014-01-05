
-- | 
--
-- <http://okmij.org/ftp/typed-formatting/FPrintScan.html#print-show>
--
--
-- Generic polyvariadic printf in Haskell98
-- 
-- This generalization of Text.Printf.printf is inspired by the message of Evan Klitzke, who wrote
-- on Haskell-Cafe about frequent occurrences in his code of the lines like
-- 
-- >        infoM $ printf "%s saw %s with %s" (show x) (show y) (show z)
-- 
-- Writing show on and on quickly becomes tiresome. It turns out, we can avoid these repeating show,
-- still conforming to Haskell98.
-- 
-- Our polyvariadic generic printf is like polyvariadic show with the printf-like format string. Our
-- printf handles values of any present and future type for which there is a Show instance. For
-- example:
-- 
-- >        t1 = unR $ printf "Hi there"
-- >        -- "Hi there"
-- 
-- >        t2 = unR $ printf "Hi %s!" "there"
-- >        -- "Hi there!"
-- 
-- >        t3 = unR $ printf "The value of %s is %s" "x" 3
-- >        -- "The value of x is 3"
-- 
-- >        t4 = unR $ printf "The value of %s is %s" "x" [5]
-- >        -- "The value of x is [5]"
-- 
-- The unsightly unR appears solely for Haskell98 compatibility: flexible instances remove the need
-- for it. On the other hand, Evan Klitzke's code post-processes the result of formatting with
-- infoM, which can subsume unR.
-- 
-- A bigger problem with our generic printf, shared with the original Text.Printf.printf, is
-- partiality: The errors like passing too many or too few arguments to printf are caught only at
-- run-time. We can certainly do better.
-- 
-- Version:  The current version is 1.1, June 5, 2009.
--
-- References
--
--  *  The complete source code with the tests. It was published in the message posted on the
--     Haskell-Cafe mailing list on Fri, 5 Jun 2009 00:57:00 -0700 (PDT)
--     <http://okmij.org/ftp/typed-formatting/GenPrintF.hs>
-- 

module Text.GenPrintF where

-- | Needed only for the sake of Haskell98
-- If we are OK with flexible instances, this newtype can be disposed of
newtype RString = RString{unR:: String} 

class SPrintF r where
    pr_aux :: [FDesc] -> [String] -> r

-- | These two instances are all we ever need

instance SPrintF RString where
    pr_aux desc acc = RString . concat . reverse $ foldl f acc desc
     where
     f acc (FD_lit s) = s : acc
     f acc FD_str     = error "Unfulfilled %s formatter"

instance (Show a, SPrintF r) => SPrintF (a->r) where
    pr_aux desc acc x = pr_aux desc' acc'
     where
     (desc',acc') = fmtx desc acc
     fmtx [] acc     = error "No formatting directive for the argument"
     fmtx (FD_lit s:desc) acc = fmtx desc (s:acc)
     fmtx (FD_str : desc) acc = (desc, unq (show x) : acc)
     unq ('"' : str) | last str == '"' = init str
     unq str  = str


printf str = pr_aux (convert_to_fdesc str) []

-- tests

t1 = unR $ printf "Hi there"
-- "Hi there"

t2 = unR $ printf "Hi %s!" "there"
-- "Hi there!"

t3 = unR $ printf "The value of %s is %s" "x" 3
-- "The value of x is 3"

t4 = unR $ printf "The value of %s is %s" "x" [5]
-- "The value of x is [5]"



-- | A very simple language of format descriptors
data FDesc = FD_lit String | FD_str deriving (Eq, Show)

-- Convert "insert %s here" into 
-- [FD_lit "insert ", FD_str, FD_lit " here"]
convert_to_fdesc :: String -> [FDesc]
convert_to_fdesc str = 
    case break (=='%') str of
      (s1,"") -> make_lit s1
      (s1,'%':'s':rest) -> make_lit s1 ++ FD_str : convert_to_fdesc rest
      (_,s2) -> error $ "bad descriptor: " ++ take 5 s2
 where
 make_lit "" = []
 make_lit str = [FD_lit str]

test_cvf = and [
    convert_to_fdesc "Simple lit" ==
       [FD_lit "Simple lit"],
    convert_to_fdesc "%s insert" ==
       [FD_str,FD_lit " insert"],
    convert_to_fdesc "insert %s here" ==
    [FD_lit "insert ",FD_str,FD_lit " here"]
    ]


