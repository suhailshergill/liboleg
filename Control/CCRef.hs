-- | Monad transformer for multi-prompt delimited control
--
-- This library implements the superset of the interface described in
--
-- > A Monadic Framework for Delimited Continuations
-- > R. Kent Dybvig, Simon Peyton Jones, and Amr Sabry
-- > JFP, v17, N6, pp. 687--730, 2007.
-- > http://www.cs.indiana.edu/cgi-bin/techreports/TRNNN.cgi?trnum=TR615
--
-- This code is the straightforward implementation of the
-- definitional machine described in the above paper. To be precise,
-- we implement an equivalent machine, where captured continuations are
-- always sandwiched between two prompts. This equivalence as
-- well as the trick to make it all well-typed are described in
-- the FLOPS 2010 paper. Therefore, to the great extent
-- this code is the straightforward translation of delimcc from OCaml.
-- The parallel stack of delimcc is the `real' stack now (containing
-- parts of the real continuation, that is).
--
-- This code implements, in CPS, what amounts to a segmented stack
-- (the technique of implementing call/cc efficiently, first described in
-- Hieb, Dybvig and Bruggeman's PLDI 1990 paper).
--
module Control.CCRef (-- Types
              CC,
              SubCont,
              Prompt,

              -- Basic delimited control operations
              newPrompt,
              pushPrompt,
              takeSubCont,
              pushSubCont,
              runCC,

              -- Optimized primitives
              abortP,
              pushDelimSubCont,

              -- Useful derived operations
              shiftP,
              shift0P,
              controlP,
              isPromptSet,

              module Control.Mutation           -- re-export
             ) where


import Control.Monad (liftM2)
import Control.Monad.Trans
import Control.Mutation                         -- Generic references

import Control.Monad.ST                 -- For tests only

-- | Delimited-continuation monad transformer
-- The (CC m) monad is the Cont monad with the answer-type (),
-- combined with the persistent-state monad. The state PTop is the
-- `parallel stack' of delimcc, which is the real stack now. 
-- The base monad m must support reference cells, that is,
-- be a member of the type class Mutation.
-- Since we need reference cells anyway, we represent the persistent
-- state as a reference cell PTop, which is passed as the environment.
--
newtype CC m a = CC{unCC:: (a -> m ()) -> PTop m -> m ()}

-- | We manipulate portions of the stack between two exception frames.
-- The type of the exception DelimCCE is ()
--
-- The type of prompts is just like that in OCaml's delimcc
data Prompt m a = Prompt{mbox :: Ref m (CC m a),
                         mark :: Mark m}

-- | A frame of the parallel stack, associated with each active prompt.
-- The frame refers to the prompt indirectly, by pointing to the
-- mark field of the prompt. Different prompts have different marks.
-- Therefore, although prompts generally have different types, all pframes
-- have the same type and can be placed into the same list.
-- A pframe also points to an exception frame (in the pfr_ek field).
-- That exception frame is created by push_prompt, see below.
--
data PFrame m = PFrame{pfr_mark :: Mark m,
                       pfr_ek   :: EK m} -- see scAPI below

type PStack m = [PFrame m]             -- The parallel stack
type PTop m   = Ref m (PStack m)       -- The `machine' stack

-- | The context between two exception frames: The captured sub-continuation
-- It is a fragment of the parallel stack: a list of PFrames in inverse order.
-- Since we are in the Cont monad, there is no `real' stack:
-- the type Ekfragment  is ()
--
data SubCont m a b = SubCont{subcont_pa :: Prompt m a,
                             subcont_pb :: Prompt m b,
                             subcont_ps :: [PFrame m]}


-- --------------------------------------------------------------------
-- scAPI (see the caml-shift paper)

-- | The type of exceptions associated with exception frames
-- Only DelimCCE exceptions could ever be raised
type DelimCCE = ()

-- | The pointer to an exception frame: a continuation accepting DelimCCE
-- (since the monadic action is already a `thunk', we don't need
-- to make another one)
type EK m = m ()

{-
-- How to implement try and obtain the identity EK of the pushed
-- exception frame

-- The code looks like call/cc, but not quite: we split the 
-- machine context at the exception frame, evaluating the body in 
-- essentially the empty environment. To be precise, we evaluate body
-- on the stack that contains a single underflow frame, called pop below.
-- The operation pop switches the control to the `previous' stack.

ctry :: (Monad m, Mutation m) => (EK m -> CC m ()) -> CC m () -> CC m ()
ctry body handler = CC $ \k ptop -> do
      stack <- readRef ptop
      let ek = unCC handler k ptop : stack
      writeRef ptop ek
      let pop () = do
                   (_:t) <- readRef ptop
                   writeRef ptop t
                   k ()
      unCC (body ek) pop ptop
-}


-- in OCaml: reset_ek : ek -> exn -> 'a
-- reset_ek :: EK m -> CC m any
-- reset_ek ek = CC $ \_ _ -> ek ()

-- | Since we are in the Cont monad, there is no `real' stack:
type Ekfragment = ()
-- hence, the rest of scAPI is irrelevant:
-- copy_stack_fragment and push_stack_fragment do nothing at all

-- --------------------------------------------------------------------
-- | CC monad: general monadic operations
--
instance Monad m => Monad (CC m) where
    return x = CC $ \k _ -> k x
    m >>= f  = CC $ \k ptop -> unCC m (\v -> unCC (f v) k ptop) ptop

instance MonadTrans CC where
    lift m = CC $ \k _ -> m >>= k

instance MonadIO m => MonadIO (CC m) where
    liftIO = lift . liftIO

runCC :: (Monad m, Mutation m) => CC m a -> m a
runCC m = do
 ptop <- newRef []              -- make the parallel stack
                                -- where to store the answer to
 ans  <- newRef (error "runCC: no prompt was ever set!")
 unCC m (writeRef ans) ptop
 readRef ans


-- --------------------------------------------------------------------
-- Utilities

-- | Mark is Ref m Bool rather than Ref m () as was in OCaml,
-- since we use equi-mutability rather than physical equality when
-- comparing marks. Normally, mark is Ref False; we flip it to 
-- True when we do the equi-mutability test.
type Mark m = Ref m Bool

new_mark :: Mutation m => m (Mark m)
new_mark = newRef False

-- | Do the equi-mutability test
with_marked_mark :: (Monad m, Mutation m) => Mark m -> m a -> m a
with_marked_mark mark body = do
  writeRef mark True                    -- set the mark
  r <- body
  writeRef mark False                   -- reset it back
  return r

-- | Check if the given mark is marked
is_marked :: Mutation m => Mark m -> m Bool
is_marked = readRef


-- | Contents of the empty mbox 
-- (see the FLOPS 2010 paper for the explanations)
mbox_empty :: CC m a
mbox_empty = error "Empty mbox"

mbox_receive :: (Monad m, Mutation m) => Prompt m a -> CC m a
mbox_receive p = do
  k <- readRef (mbox p)
  writeRef (mbox p) mbox_empty
  k

-- | Operations on the global PStack
--
push_pframe :: (Monad m, Mutation m) => PTop m -> PFrame m -> m ()
push_pframe ptop fr = do
  stack <- readRef ptop
  writeRef ptop (fr:stack)

pop_pframe :: (Monad m, Mutation m) => PTop m -> m (PFrame m)
pop_pframe ptop = readRef ptop >>= check
 where check []    = error "Empty PStack! Can't be happening"
       check (h:t) = writeRef ptop t >> return h
  

get_pstack :: (Monad m, Mutation m) => CC m (PStack m)
get_pstack = CC $ \k ptop -> readRef ptop >>= k


-- | Split the parallel stack at the given mark, remove the prefix
-- (up to but not including the marked frame) and return it in
-- the inverse frame order. The frame that used to be at the top of pstack
-- is now at the bottom of the returned list.
-- The other two returned values are the marked frame and the
-- rest of pstack (which contains the marked frame at the top).
--
unwind :: (Monad m, Mutation m) =>
          [PFrame m] -> Mark m -> PStack m ->
          m (PFrame m, PStack m, [PFrame m])
unwind acc mark stack = with_marked_mark mark (loop acc stack)
 where
 loop acc []      = error "No prompt was set" 
 loop acc s@(h:t) = do
   marked <- is_marked (pfr_mark h)
   if marked then return (h,s,acc) else loop (h:acc) t

-- | The same as above, but the removed frames are discarded
unwind_abort :: (Monad m, Mutation m) =>
                Mark m -> PStack m -> m (PFrame m, PStack m)
unwind_abort mark stack = with_marked_mark mark (loop stack)
 where
 loop []      = error "No prompt was set" 
 loop s@(h:t) = do
   marked <- is_marked (pfr_mark h)
   if marked then return (h,s) else loop t

-- | rev_append l1 l2 == reverse l1 ++ l2
rev_append :: [a] -> [a] -> [a]
rev_append [] l2 = l2
rev_append (h:t) l2 = rev_append t (h:l2)

-- --------------------------------------------------------------------
-- | Basic Operations of the delimited control interface
-- All control operators in the end jump to the exception frame
-- 
-- > (in delimcc, that was `raise DelimCCE'; here it is `pfr_ek h')
--
newPrompt :: (Monad m, Mutation m) => CC m (Prompt m a)
newPrompt = lift $ liftM2 Prompt (newRef mbox_empty) new_mark

-- | The exception-handling part of try in pushPrompt
popPrompt :: (Monad m, Mutation m) =>
             Prompt m w -> CC m w
popPrompt p = CC $ \k ptop -> do
  h <- pop_pframe ptop                -- remove the exception frame
  -- assert (h.pfr_mark == p.mark)
  unCC (mbox_receive p) k ptop

pushPrompt :: (Monad m, Mutation m) =>
              Prompt m w -> CC m w -> CC m w
pushPrompt p body = CC $ \k ptop -> do
  let ek = unCC (popPrompt p) k ptop
  let raise = do                        -- raise the exception
              (h:_) <- readRef ptop
              pfr_ek h                  -- h must be an exception frame
  push_pframe ptop (PFrame (mark p) ek) -- push the exception frame
  unCC body (\res -> writeRef (mbox p) (return res) >> raise) ptop


takeSubCont :: (Monad m, Mutation m) =>
               Prompt m b -> (SubCont m a b -> CC m b) -> CC m a
takeSubCont p f = newPrompt >>= \pa -> CC $ \k ptop -> do
  let ek = unCC (popPrompt pa) k ptop
  stack <- readRef ptop
  (h,s,subcontchain) <- unwind [] (mark p) (PFrame (mark pa) ek:stack)
  writeRef ptop s
  writeRef (mbox p) (f (SubCont pa p subcontchain))
  pfr_ek h                              -- reset_ek is the identity


pushSubCont :: (Monad m, Mutation m) =>
               SubCont m a b -> CC m a -> CC m b
pushSubCont (SubCont pa pb subcontchain) m = CC $ \k ptop -> do
  let ek = unCC (popPrompt pb) k ptop
  ephemeral <- new_mark                 -- p'' in the caml-shift paper
  stack <- readRef ptop
  let stack'@(h:_) = rev_append subcontchain (PFrame ephemeral ek:stack)
  writeRef ptop stack'
  writeRef (mbox pa) m
  pfr_ek h                              -- raise the exception


-- | An optimization: pushing the _delimited_ continuation.
-- This is the optimization of the pattern
--
-- >    pushPrompt (subcont_pb sk) (pushSubcont sk m)
--
-- corresponding to pushing the continuation captured by shift/shift0. 
-- The latter continuation always has the delimiter at the end.
-- Indeed shift can be implemented more efficiently as a primitive
-- rather than via push_prompt/control combination...
--
pushDelimSubCont :: (Monad m, Mutation m) =>
                    SubCont m a b -> CC m a -> CC m b
pushDelimSubCont (SubCont pa pb subcontchain) m = CC $ \k ptop -> do
  let ek = unCC (popPrompt pb) k ptop
  stack <- readRef ptop
  let stack'@(h:_) = rev_append subcontchain (PFrame (mark pb) ek:stack)
  writeRef ptop stack'
  writeRef (mbox pa) m
  pfr_ek h


-- | An efficient variation of take_subcont, which does not capture
-- any continuation.
-- This code makes it clear that abort is essentially raise.
--
abortP :: (Monad m, Mutation m) => 
          Prompt m w -> CC m w -> CC m any
abortP p res = CC $ \k ptop -> do
  stack <- readRef ptop
  (h,s) <- unwind_abort (mark p) stack
  writeRef ptop s
  writeRef (mbox p) res
  pfr_ek h                              -- reset_ek is the identity


-- | Check to see if a prompt is set
isPromptSet :: (Monad m, Mutation m) => 
               Prompt m w -> CC m Bool
isPromptSet p = do
  stack <- get_pstack
  with_marked_mark (mark p) (loop stack)
 where
 loop []      = return False
 loop s@(h:t) = do
   marked <- is_marked (pfr_mark h)
   if marked then return True else loop t

-- pstack_size :: (Monad m, Mutation m) => String -> CC m ()
-- pstack_size str = do
--   stack <- get_pstack
--   trace (unwords ["Pstack:",str,show (length stack)]) (return ())

-- --------------------------------------------------------------------
-- | Useful derived operations
--
shiftP :: (Monad m, Mutation m) => 
          Prompt m w -> ((a -> CC m w) -> CC m w) -> CC m a
shiftP p f = takeSubCont p $ \sk -> 
               pushPrompt p (f (\c -> 
                  pushDelimSubCont sk (return c)))

shift0P :: (Monad m, Mutation m) => 
           Prompt m w -> ((a -> CC m w) -> CC m w) -> CC m a
shift0P p f = takeSubCont p $ \sk -> 
               f (\c -> 
                  pushDelimSubCont sk (return c))

controlP :: (Monad m, Mutation m) => 
            Prompt m w -> ((a -> CC m w) -> CC m w) -> CC m a
controlP p f = takeSubCont p $ \sk -> 
               pushPrompt p (f (\c -> 
                  pushSubCont sk (return c)))

----------------------------------------------------------------------
-- Tests

expect ve vp = if ve == vp then putStrLn $ "expected answer " ++ (show ve)
                  else error $ "expected " ++ (show ve) ++
                               ", computed " ++ (show vp)

assure :: Monad m => CC m Bool -> CC m ()
assure m = do
  v <- m
  if v then return () else error "assertion failed"


test0 = runCC (return 1 >>= (return . (+ 4))) >>= expect 5
-- 5

test1 = (expect 1 =<<) . runCC $ do
  p <- newPrompt
  assure (isPromptSet p >>= return . not)
  pushPrompt p $ (assure (isPromptSet p) >> return 1)

incr :: Monad m => Int -> m Int -> m Int
incr n m = m >>= return . (n +)

test2 = (expect 9 =<<) . runCC $ do
  p <- newPrompt
  incr 4 . pushPrompt p $ pushPrompt p (return 5)

test3 = (expect 9 =<<) . runCC $ do
  p <- newPrompt
  incr 4 . pushPrompt p $ (incr 6 $ abortP p (return 5))

test3' = (expect 9 =<<) . runCC $ do
  p <- newPrompt
  incr 4 . pushPrompt p . pushPrompt p $ (incr 6 $ abortP p (return 5))

-- The same, but less efficient
test3'1 = (expect 9 =<<) . runCC $ do
  p <- newPrompt
  incr 4 . pushPrompt p . pushPrompt p $ 
    (incr 6 $ takeSubCont p (\_ -> (return 5)))

test3'' = (expect 27 =<<) . runCC $ do
  p <- newPrompt
  incr 20 . pushPrompt p $ 
         do
         v1 <- pushPrompt p (incr 6 $ abortP p (return 5))
         v2 <- abortP p (return 7)
         return $ v1 + v2 + 10

test3''1 = (expect 27 =<<) . runCC $ do
  p <- newPrompt
  incr 20 . pushPrompt p $ 
         do
         v1 <- pushPrompt p (incr 6 $ takeSubCont p (\_ -> return 5))
         v2 <- takeSubCont p (\_ -> return 7)
         return $ v1 + v2 + 10

test3''' = (print =<<) . runCC $ do
               p <- newPrompt
               v <- pushPrompt p $ 
                 do
                 v1 <- pushPrompt p (incr 6 $ abortP p (return 5))
                 v2 <- abortP p (return 7)
                 return $ v1 + v2 + 10
               assure (isPromptSet p >>= return . not)
               v <- abortP p (return 9)
               assure (return False)
               return $ v + 20
-- error

test4 = (expect 35 =<<) . runCC $ do 
  p <- newPrompt
  incr 20 . pushPrompt p $
         incr 10 . takeSubCont p $ \sk -> 
                         pushPrompt p (pushSubCont sk (return 5))

test41 = (expect 35 =<<) . runCC $ do
  p <- newPrompt
  incr 20 . pushPrompt p $ 
    incr 10 . takeSubCont p $ \sk -> 
        pushSubCont sk (pushPrompt p (pushSubCont sk (abortP p (return 5))))


-- Danvy/Filinski's test
--(display (+ 10 (reset (+ 2 (shift k (+ 100 (k (k 3))))))))
--; --> 117

test5 = (expect 117 =<<) . runCC $ do
  p <- newPrompt
  incr 10 . pushPrompt p $
     incr 2 . shiftP p $ \sk -> incr 100 $ sk =<< (sk 3)
-- 117

test5'' = (expect 115 =<<) . runCC $ do
  p0 <- newPrompt
  p1 <- newPrompt
  incr 10 . pushPrompt p0 $
     incr 2 . shiftP p0 $ \sk -> 
         incr 100 $ sk =<< 
           (pushPrompt p1 (incr 9 $ sk =<< (abortP p1 (return 3))))

test5''' = (expect 115 =<<) . runCC $ do
  p0 <- newPrompt
  p1 <- newPrompt
  incr 10 . pushPrompt p0 $
     incr 2 . (id =<<) . shiftP p0 $ \sk -> 
         incr 100 $ sk 
           (pushPrompt p1 (incr 9 $ sk (abortP p1 (return 3))))

test54 = (expect 124 =<<) . runCC $ do
  p0 <- newPrompt
  p1 <- newPrompt
  incr 10 . pushPrompt p0 $
     incr 2 . (id =<<) . shiftP p0 $ \sk -> 
         incr 100 $ sk 
           (pushPrompt p1 (incr 9 $ sk (abortP p0 (return 3))))

test6 = (expect 15 =<<) . runCC $ do
  p1 <- newPrompt
  p2 <- newPrompt
  let pushtwice sk = pushSubCont sk (pushSubCont sk (return 3))
  incr 10 . pushPrompt p1 $ 
     incr 1 . pushPrompt p2 $ takeSubCont p1 pushtwice

-- The most difficult test. The difference between the prompts really matters
-- now
test7 = (expect 135 =<<) . runCC $ do
  p1 <- newPrompt
  p2 <- newPrompt
  p3 <- newPrompt
  let pushtwice sk = pushSubCont sk (pushSubCont sk 
                                              (takeSubCont p2
                                               (\sk2 -> pushSubCont sk2
                                                (pushSubCont sk2 (return 3)))))
  incr 100 . pushPrompt p1 $
    incr 1 . pushPrompt p2 $
     incr 10 . pushPrompt p3 $ (takeSubCont p1 pushtwice)
-- 135

test7' = (expect 135 =<<) . runCC $ do
  p1 <- newPrompt
  p2 <- newPrompt
  p3 <- newPrompt
  let pushtwice f = f (f (shiftP p2 (\f2 -> f2 =<< (f2 3))))
  incr 100 . pushPrompt p1 $
    incr 1 . pushPrompt p2 $
     incr 10 . pushPrompt p3 $ (shiftP p1 pushtwice >>= id)
-- 135

test7'' = (expect 135 =<<) . runCC $ do
  p1 <- newPrompt
  p2 <- newPrompt
  p3 <- newPrompt
  let pushtwice f = f (f (shift0P p2 (\f2 -> f2 =<< (f2 3))))
  incr 100 . pushPrompt p1 $
    incr 1 . pushPrompt p2 $
     incr 10 . pushPrompt p3 $ (shift0P p1 pushtwice >>= id)

-- test7 in the ST monad. After all, CC is a monad transformer.
-- The only difference is the presence of runST...
test7st = runST (runCC $ do
  p1 <- newPrompt
  p2 <- newPrompt
  p3 <- newPrompt
  let pushtwice sk = pushSubCont sk (pushSubCont sk 
                                              (takeSubCont p2
                                               (\sk2 -> pushSubCont sk2
                                                (pushSubCont sk2 (return 3)))))
  incr 100 . pushPrompt p1 $
    incr 1 . pushPrompt p2 $
     incr 10 . pushPrompt p3 $ (takeSubCont p1 pushtwice))

test7st_check = return test7st >>= expect 135



-- Checking shift, shift0, control 

testls = (expect ["a"] =<<) . runCC $ do
    p <- newPrompt
    pushPrompt p (
                  do
                  let x = shiftP p (\f -> f [] >>= (return . ("a":)))
                  xv <- x
                  shiftP p (\_ -> return xv))


-- (display (prompt0 (cons 'a (prompt0 (shift0 f (shift0 g '()))))))
testls0 = (expect [] =<<) . runCC $ do
    p <- newPrompt
    pushPrompt p (
       (return . ("a":)) =<< 
          (pushPrompt p (shift0P p (\_ -> (shift0P p (\_ -> return []))))))
  
testls01 = (expect ["a"] =<<) . runCC $ do
    p <- newPrompt
    pushPrompt p (
       (return . ("a":)) =<< 
          (pushPrompt p 
           (shift0P p (\f -> f (shift0P p (\_ -> return []))) >>= id)))
  

testlc = (expect [] =<<) . runCC $ do
    p <- newPrompt
    pushPrompt p (
                  do
                  let x = controlP p (\f -> f [] >>= (return . ("a":)))
                  xv <- x
                  controlP p (\_ -> return xv))
  

testlc' = (expect ["a"] =<<) . runCC $ do
    p <- newPrompt
    pushPrompt p (
                  do
                  let x = controlP p (\f -> f [] >>= (return . ("a":)))
                  xv <- x
                  controlP p (\g -> g xv))
-- ["a"]

testlc1 = (expect 2 =<<) . runCC $ do
    p <- newPrompt
    pushPrompt p (do
                  takeSubCont p (\sk -> 
                                pushPrompt p (pushSubCont sk (return 1)))
                  takeSubCont p (\sk -> pushSubCont sk (return 2)))


-- traversing puzzle by Olivier Danvy

type DelimControl m a b = 
    Prompt m b -> ((a -> CC m b) -> CC m b) -> CC m a

traverse :: Show a => DelimControl IO [a] [a] -> [a] -> IO ()
traverse op lst = (print =<<) . runCC $ do
  p <- newPrompt
  let visit [] = return []
      visit (h:t) = do
                    v <- op p (\f -> f t >>= (return . (h:)))
                    visit v
  pushPrompt p (visit lst)


-- *CC_Refn> traverse shiftP [1,2,3,4,5]
-- [1,2,3,4,5]
-- *CC_Refn> traverse controlP [1,2,3,4,5]
-- [5,4,3,2,1]

doall = sequence_ [test0, test1, test2, test3, test3', test3'1, 
                   test3'', test3''1, 
                   test4, test41, test5, test5'', test5''', test54,
                   test6, test7, test7', test7'', test7st_check,
                   testls, testls0, testls01, testlc, testlc', testlc1
                  ]
-- test3''' should raise an error
