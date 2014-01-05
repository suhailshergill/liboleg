-- Haskell98!

-- | Random and Binary IO with IterateeM
--
-- <http://okmij.org/ftp/Streams.html#random-bin-IO>
--
--
-- Random and binary IO: Reading TIFF
--
--    Iteratees presuppose sequential processing. A general-purpose input method
--    must also support random IO: processing a seek-able input stream from an
--    arbitrary position, jumping back and forth through the stream. We demonstrate
--    random IO with iteratees, as well as reading non-textual files and converting
--    raw bytes into multi-byte quantities such as integers, rationals, and TIFF
--    dictionaries. Positioning of the input stream is evocative of delimited
--    continuations.
--
--    We use random and binary IO to write a general-purpose TIFF library. The
--    library emphasizes incremental processing, relying on iteratees and enumerators
--    for on-demand reading of tag values.  The library extensively uses nested
--    streams, tacitly converting the stream of raw bytes from the file into streams
--    of integers, rationals and other user-friendly items. The pixel matrix is
--    presented as a contiguous stream, regardless of its segmentation into strips
--    and physical arrangement.
--
--    We show a representative application of the library: reading a sample TIFF
--    file, printing selected values from the TIFF dictionary, verifying the values
--    of selected pixels and computing the histogram of pixel values. The pixel
--    verification procedure stops reading the pixel matrix as soon as all specified
--    pixel values are verified. The histogram accumulation does read the entire
--    matrix, but incrementally. Neither pixel matrix processing procedure loads the
--    whole matrix in memory. In fact, we never read and retain more than the
--    IO-buffer-full of raw data.
--
--    Version: The current version is 1.1, December 2008.
--
module System.RandomIO where


import System.Posix
import Foreign.C
import Foreign.Ptr
import Foreign.Marshal.Alloc
import Foreign.Marshal.Array
import Control.Monad.Trans
import Data.Word
import Data.Bits
import Data.IORef
import Text.Printf

import System.IO (SeekMode(..))

import System.IterateeM
import System.LowLevelIO


-- | The type of the IO monad supporting seek requests and endianness
-- The seek_request is not-quite a state, more like a `communication channel'
-- set by the iteratee and answered by the enumerator. Since the
-- base monad is IO, it seems simpler to implement both endianness
-- and seek requests as IORef cells. Their names are grouped in a structure
-- RBState, which is propagated as the `environment.'
newtype RBIO a = RBIO{unRBIO:: RBState -> IO a}

instance Monad RBIO where
    return  = RBIO . const . return
    m >>= f = RBIO( \env -> unRBIO m env >>= (\x -> unRBIO (f x) env) )

instance MonadIO RBIO where
    liftIO = RBIO . const

-- | Generally, RBState is opaque and should not be exported.
data RBState = RBState{msb_first :: IORef Bool,
                       seek_req  :: IORef (Maybe FileOffset) }

-- | The programmer should use the following functions instead
--
rb_empty = do
           mref <- newIORef True
           sref <- newIORef Nothing
           return RBState{msb_first = mref, seek_req = sref}

-- | To request seeking, the iteratee sets seek_req to (Just desired_offset)
-- When the enumerator answers the request, it sets seek_req back
-- to Nothing
--
rb_seek_set :: FileOffset -> RBIO ()
rb_seek_set off = RBIO action
 where action env = writeIORef (seek_req env) (Just off)

rb_seek_answered :: RBIO Bool
rb_seek_answered = RBIO action
 where action env = readIORef (seek_req env) >>= 
                    return . maybe True (const False)

rb_msb_first :: RBIO Bool
rb_msb_first = RBIO action
 where action env = readIORef (msb_first env)

rb_msb_first_set :: Bool -> RBIO ()
rb_msb_first_set flag = RBIO action
 where action env = writeIORef (msb_first env) flag

runRB:: RBState -> IterateeGM el RBIO a -> IO (IterateeG el RBIO a)
runRB rbs m = unRBIO (unIM m) rbs

-- ------------------------------------------------------------------------
-- Binary Random IO Iteratees

-- | A useful combinator.
-- Perhaps a better idea would have been to define
-- Iteratee to have (Maybe a) in IE_done? In that case, we could
-- make IterateeGM to be the instance of MonadPlus
bindm :: Monad m => m (Maybe a) -> (a -> m (Maybe b)) -> m (Maybe b)
bindm m f = m >>= maybe (return Nothing) f


-- | We discard all available input first.
-- We keep discarding the stream s until we determine that our request 
-- has been answered:
-- rb_seek_set sets the state seek_req to (Just off). When the
-- request is answered, the state goes back to Nothing.
-- The above features remind one of delimited continuations.
sseek :: FileOffset -> IterateeGM el RBIO ()
sseek off = lift (rb_seek_set off) >> liftI (IE_cont step)
 where
 step s@(Err _) = liftI $ IE_done () s
 step s   = do
            r <- lift rb_seek_answered
            if r then liftI $ IE_done () s
                 else liftI $ IE_cont step


-- | An iteratee that reports and propagates an error
-- We disregard the input first and then propagate error.
-- It is reminiscent of `abort'
iter_err :: Monad m => String -> IterateeGM el m ()
iter_err err = liftI $ IE_cont step
 where
 step _ = liftI $ IE_done () (Err err)


-- | Read n elements from a stream and apply the given iteratee to the
-- stream of the read elements. If the given iteratee accepted fewer
-- elements, we stop.
-- This is the variation of `stake' with the early termination
-- of processing of the outer stream once the processing of the inner stream
-- finished early. This variation is particularly useful for randomIO,
-- where we do not have to care to `drain the input stream'.
stakeR :: Monad m => Int -> EnumeratorN el el m a
stakeR 0 iter = return iter
stakeR n iter@IE_done{} = return iter
stakeR n (IE_cont k) = liftI $ IE_cont step
 where
 step (Chunk []) = liftI $ IE_cont step
 step chunk@(Chunk str) | length str <= n =
                             stakeR (n - length str) ==<< k chunk
 step (Chunk str) = done (Chunk s1) (Chunk s2)
   where (s1,s2) = splitAt n str
 step stream = done stream stream
 done s1 s2 = k s1 >>== \r -> liftI $ IE_done r s2


-- | Iteratees to read unsigned integers written in Big- or Little-endian ways
--
endian_read2 :: IterateeGM Word8 RBIO (Maybe Word16)
endian_read2 =
  bindm snext $ \c1 ->
  bindm snext $ \c2 -> do
  flag <- lift rb_msb_first
  if flag then
      return $ return $ (fromIntegral c1 `shiftL` 8) .|. fromIntegral c2
     else
      return $ return $ (fromIntegral c2 `shiftL` 8) .|. fromIntegral c1

endian_read4 :: IterateeGM Word8 RBIO (Maybe Word32)
endian_read4 =
  bindm snext $ \c1 ->
  bindm snext $ \c2 ->
  bindm snext $ \c3 ->
  bindm snext $ \c4 -> do
  flag <- lift rb_msb_first
  if flag then
      return $ return $ 
               (((((fromIntegral c1
                `shiftL` 8) .|. fromIntegral c2)
                `shiftL` 8) .|. fromIntegral c3)
                `shiftL` 8) .|. fromIntegral c4
     else
      return $ return $ 
               (((((fromIntegral c4
                `shiftL` 8) .|. fromIntegral c3)
                `shiftL` 8) .|. fromIntegral c2)
                `shiftL` 8) .|. fromIntegral c1


-- ------------------------------------------------------------------------
-- Binary Random IO enumerators

-- | The enumerator of a POSIX Fd: a variation of enum_fd that
-- supports RandomIO (seek requests)
enum_fd_random :: Fd -> EnumeratorGM Word8 RBIO a
enum_fd_random fd iter = 
    IM . RBIO $ (\env -> 
                 allocaBytes (fromIntegral buffer_size) (loop env (0,0) iter))
 where
--  buffer_size = 4096
  buffer_size = 5 -- for tests; in real life, there should be 1024 or so
  -- the second argument of loop is (off,len), describing which part
  -- of the file is currently in the buffer 'p'
  loop :: RBState -> (FileOffset,Int) -> IterateeG Word8 RBIO a -> 
          Ptr Word8 -> IO (IterateeG Word8 RBIO a)
  loop env pos iter@IE_done{} p = return iter
  loop env pos iter p = readIORef (seek_req env) >>= loop' env pos iter p

  loop' env pos@(off,len) iter p (Just off') | 
    off <= off' && off' < off + fromIntegral len =      -- Seek within buffer p
    do
    writeIORef (seek_req env) Nothing
    let local_off = fromIntegral $ off' - off
    str <- peekArray (len - local_off) (p `plusPtr` local_off)
    im  <- runRB env $ enum_pure_1chunk str iter
    loop env pos im p
  loop' env pos iter p (Just off) = do -- Seek outside the buffer
   writeIORef (seek_req env) Nothing
   off <- myfdSeek fd AbsoluteSeek (fromIntegral off)
   putStrLn $ "Read buffer, offset " ++ either (const "IO err") show off
   case off of
    Left errno -> runRB env $ enum_err "IO error" iter
    Right off  -> loop' env (off,0) iter p Nothing
    -- Thanks to John Lato for the strictness annotation
    -- Otherwise, the `off + fromIntegral len' below accumulates thunks
  loop' env (off,len) iter p Nothing | off `seq` len `seq` False = undefined
  loop' env (off,len) iter@(IE_cont step) p Nothing = do
   n <- myfdRead fd (castPtr p) buffer_size
   putStrLn $ "Read buffer, size " ++ either (const "IO err") show n
   case n of
    Left errno -> runRB env $ step (Err "IO error")
    Right 0 -> return iter
    Right n -> do
         str <- peekArray (fromIntegral n) p
         im  <- runRB env $ step (Chunk str)
         loop env (off + fromIntegral len,fromIntegral n) im p


-- ------------------------------------------------------------------------
-- Tests

test1 () = do
           Just s1 <- snext
           Just s2 <- snext
           sseek 0
           Just s3 <- snext
           sseek 100
           Just s4 <- snext
           Just s5 <- snext
           sseek 101
           Just s6 <- snext
           sseek 1
           Just s7 <- snext
           return [s1,s2,s3,s4,s5,s6,s7]

test2 () = do
           sseek 100
           sseek 0
           sseek 100
           Just s4 <- snext
           Just s5 <- snext
           sseek 101
           Just s6 <- snext
           sseek 1
           Just s7 <- snext
           sseek 0
           Just s1 <- snext
           Just s2 <- snext
           sseek 0
           Just s3 <- snext
           return [s1,s2,s3,s4,s5,s6,s7]

test3 () = do
           let show_x fmt = map (\x -> (printf fmt x)::String)
           lift $ rb_msb_first_set True
           Just ns1 <- endian_read2
           Just ns2 <- endian_read2
           Just ns3 <- endian_read2
           Just ns4 <- endian_read2
           sseek 0
           Just nl1 <- endian_read4
           Just nl2 <- endian_read4
           sseek 4
           lift $ rb_msb_first_set False
           Just ns3' <- endian_read2
           Just ns4' <- endian_read2
           sseek 0
           Just ns1' <- endian_read2
           Just ns2' <- endian_read2
           sseek 0
           Just nl1' <- endian_read4
           Just nl2' <- endian_read4
           return [show_x "%04x" [ns1,ns2,ns3,ns4],
                   show_x "%08x" [nl1,nl2],
                   show_x "%04x" [ns1',ns2',ns3',ns4'],
                   show_x "%08x" [nl1',nl2']]
                            
test4 () = do
           lift $ rb_msb_first_set True
           Just ns1 <- endian_read2
           Just ns2 <- endian_read2
           iter_err "Error"
           ns3 <- endian_read2
           return (ns1,ns2,ns3)

test_driver_random iter filepath = do
  fd <- openFd filepath ReadOnly Nothing defaultFileFlags
  rb <- rb_empty
  putStrLn "About to read file"
  result <- runRB rb $ (enum_fd_random fd >. enum_eof) ==<< iter
  closeFd fd
  putStrLn "Finished reading file"
  print_res result
 where
  print_res (IE_done a EOF) = print a >> return a
  print_res (IE_done a (Err err)) = print a >>
                                    putStrLn ("Stream error: " ++ err) >>
                                    return a

test1r = test_driver_random (test1 ()) "test_full1.txt" >>=
         return . (== [104,101,104,13,10,10,101])

test2r = test_driver_random (test2 ()) "test_full1.txt" >>=
         return . (== [104,101,104,13,10,10,101])

test3r = test_driver_random (test3 ()) "test4.txt" >>=
         return . (==
                   [["0001","0203","fffe","fdfc"],
                    ["00010203","fffefdfc"],
                    ["0100","0302","feff","fcfd"],
                    ["03020100","fcfdfeff"]])

test4r = test_driver_random (test4 ()) "test4.txt" >>=
         return . (== (1,515,Nothing))

{-
About to read file
Read buffer, size 5
Finished reading file
(1,515,Nothing)
Stream error: Error
-}
