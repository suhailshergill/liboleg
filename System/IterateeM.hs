-- Haskell98!

-- | Monadic and General Iteratees:
-- incremental input parsers, processors and transformers
--
-- The running example, parts 1 and 2
-- Part 1 is reading the headers, the sequence of lines terminated by an
-- empty line. Each line is terminated by CR, LF, or CRLF.
-- We should return the headers in order. In the case of error,
-- we should return the headers read so far and the description of the error.
-- Part 2 is reading the headers and reading all the lines from the
-- HTTP-chunk-encoded content that follows the headers. Part 2 thus
-- verifies layering of streams, and processing of one stream
-- embedded (chunk encoded) into another stream.

module System.IterateeM where

import System.Posix
import Foreign.C
import Foreign.Ptr
import Foreign.Marshal.Alloc
import Data.List (splitAt)
import Data.Char (isHexDigit, digitToInt, isSpace)
import Control.Monad.Trans
import Control.Monad.Identity

import System.LowLevelIO

-- | A stream is a (continuing) sequence of elements bundled in Chunks.
-- The first two variants indicate termination of the stream.
-- Chunk [a] gives the currently available part of the stream.
-- The stream is not terminated yet.
-- The case (Chunk []) signifies a stream with no currently available
-- data but which is still continuing. A stream processor should,
-- informally speaking, ``suspend itself'' and wait for more data
-- to arrive.
-- Later on, we can add another variant: IE_block (Ptr CChar) CSize
-- so we could parse right from the buffer.
data StreamG a = EOF | Err String | Chunk [a] deriving Show

-- | A particular instance of StreamG: the stream of characters.
-- This stream is used by many input parsers.
type Stream = StreamG Char


-- | Iteratee -- a generic stream processor, what is being folded over
-- a stream
-- When Iteratee is in the 'done' state, it contains the computed
-- result and the remaining part of the stream.
-- In the 'cont' state, the iteratee has not finished the computation
-- and needs more input.
-- We assume that all iteratees are `good' -- given bounded input,
-- they do the bounded amount of computation and take the bounded amount
-- of resources. The monad m describes the sort of computations done
-- by the iteratee as it processes the stream. The monad m could be
-- the identity monad (for pure computations) or the IO monad
-- (to let the iteratee store the stream processing results as they
-- are computed).
-- We also assume that given a terminated stream, an iteratee
-- moves to the done state, so the results computed so far could be returned.
--
-- We could have used existentials instead, by doing the closure conversion

--
data IterateeG el m a = IE_done a (StreamG el)
                      | IE_cont (StreamG el -> IterateeGM el m a)
newtype IterateeGM el m a = IM{unIM:: m (IterateeG el m a)}

type Iteratee  m a = IterateeG  Char m a
type IterateeM m a = IterateeGM Char m a


-- | Useful combinators for implementing iteratees and enumerators
--
liftI :: Monad m => IterateeG el m a -> IterateeGM el m a
liftI = IM . return

-- | Just like bind (at run-time, this is indeed exactly bind)
infixl 1 >>==
(>>==):: Monad m =>
         IterateeGM el m a ->
         (IterateeG el m a -> IterateeGM el' m b) ->
         IterateeGM el' m b
m >>== f = IM (unIM m >>= unIM . f)

-- | Just like an application -- a call-by-value-like application
infixr 1 ==<<
(==<<) :: Monad m =>
          (IterateeG el m a -> IterateeGM el' m b) ->
          IterateeGM el m a ->
          IterateeGM el' m b
f ==<< m = m >>== f

-- | The following is a `variant' of join in the IterateeGM el m monad.
-- When el' is the same as el, the type of joinI is indeed that of
-- true monadic join. However, joinI is subtly different: since
-- generally el' is different from el, it makes no sense to
-- continue using the internal, IterateeG el' m a: we no longer
-- have elements of the type el' to feed to that iteratee.
-- We thus send EOF to the internal Iteratee and propagate its result.
-- This join function is useful when dealing with `derived iteratees'
-- for embedded/nested streams. In particular, joinI is useful to
-- process the result of stake, map_stream, or conv_stream below.
joinI :: Monad m => IterateeGM el m (IterateeG el' m a) -> IterateeGM el m a
joinI m = m >>= (\iter -> enum_eof iter >>== check)
 where
 check (IE_done x (Err str)) = liftI $ (IE_done x (Err str))
 check (IE_done x _)         = liftI $ (IE_done x EOF)
 check (IE_cont _)           = error "joinI: can't happen: EOF didn't terminate"

-- | It turns out, IterateeGM form a monad. We can use the familiar do
-- notation for composing Iteratees
--
instance Monad m => Monad (IterateeGM el m) where
    return x = liftI  $ IE_done  x (Chunk [])
    m >>= f = m >>== docase
     where
     docase (IE_done a (Chunk [])) = f a
     docase (IE_done a stream) = f a >>== (\r -> case r of
                                IE_done x _  -> liftI $ IE_done x stream
                                IE_cont k    -> k stream)
     docase (IE_cont k) = liftI $ IE_cont ((>>= f) . k)

instance MonadTrans (IterateeGM el) where
    lift m = IM (m >>= unIM . return)


-- ------------------------------------------------------------------------
-- Primitive iteratees

-- | Read a stream to the end and return all of its elements as a list
stream2list :: Monad m => IterateeGM el m [el]
stream2list = liftI $ IE_cont (step [])
 where
 step acc (Chunk []) = liftI $ IE_cont (step acc)
 step acc (Chunk ls) = liftI $ IE_cont (step $ acc ++ ls)
 step acc stream     = liftI $ IE_done acc stream

-- | Check to see if the stream is in error
iter_report_err :: Monad m => IterateeGM el m (Maybe String)
iter_report_err = liftI $ IE_cont step
 where step s@(Err str) = liftI $ IE_done (Just str) s
       step s           = liftI $ IE_done Nothing s

-- ------------------------------------------------------------------------
-- Parser combinators

-- | The analogue of List.break
-- It takes an element predicate and returns a pair:
--  (str, Just c) -- the element 'c' is the first element of the stream
--                   satisfying the break predicate;
--                   The list str is the prefix of the stream up
--                   to but including 'c'
--  (str,Nothing) -- The stream is terminated with EOF or error before
--                   any element satisfying the break predicate was found.
--                   str is the scanned part of the stream.
-- None of the element in str satisfy the break predicate.
--
sbreak :: Monad m => (el -> Bool) -> IterateeGM el m ([el],Maybe el)
sbreak cpred = liftI $ IE_cont (liftI . step [])
 where
 step before (Chunk []) = IE_cont (liftI . step before)
 step before (Chunk str) =
     case break cpred str of
       (_,[])       -> IE_cont (liftI . step (before ++ str))
       (str,c:tail) -> done (before ++ str) (Just c) (Chunk tail)
 step before stream = done before Nothing stream
 done line char stream = IE_done (line,char) stream


-- | A particular optimized case of the above: skip all elements of the stream
-- satisfying the given predicate -- until the first element
-- that does not satisfy the predicate, or the end of the stream.
-- This is the analogue of List.dropWhile
sdropWhile :: Monad m => (el -> Bool) -> IterateeGM el m ()
sdropWhile cpred = liftI $ IE_cont step
 where
 step (Chunk []) = sdropWhile cpred
 step (Chunk str) =
     case dropWhile cpred str of
       []  -> sdropWhile cpred
       str ->  liftI $ IE_done () (Chunk str)
 step stream = liftI $ IE_done () stream



-- | Attempt to read the next element of the stream
-- Return (Just c) if successful, return Nothing if the stream is
-- terminated (by EOF or an error)
snext :: Monad m => IterateeGM el m (Maybe el)
snext = liftI $ IE_cont step
 where
 step (Chunk [])    = snext
 step (Chunk (c:t)) = liftI $ IE_done (Just c) (Chunk t)
 step stream        = liftI $ IE_done Nothing stream

-- | Look ahead at the next element of the stream, without removing
-- it from the stream.
-- Return (Just c) if successful, return Nothing if the stream is
-- terminated (by EOF or an error)
speek :: Monad m => IterateeGM el m (Maybe el)
speek = liftI $ IE_cont step
 where
 step (Chunk [])      = speek
 step s@(Chunk (c:_)) = liftI $ IE_done (Just c) s
 step stream          = liftI $ IE_done Nothing stream


-- | Skip the rest of the stream
skip_till_eof :: Monad m => IterateeGM el m ()
skip_till_eof = liftI $ IE_cont step
 where
 step (Chunk _) = skip_till_eof
 step _         = return ()

-- | Skip n elements of the stream, if there are that many
-- This is the analogue of List.drop
sdrop :: Monad m => Int -> IterateeGM el m ()
sdrop 0 = return ()
sdrop n = liftI $ IE_cont step
 where
 step (Chunk str) | length str <= n = sdrop (n - length str)
 step (Chunk str) = liftI $ IE_done () (Chunk s2)
  where (s1,s2) = splitAt n str
 step stream = liftI $ IE_done () stream

-- ------------------------------------------------------------------------
-- | Iteratee converters for stream embedding
-- The converters show a different way of composing two iteratees:
-- `vertical' rather than `horizontal'
--
-- The type of the converter from the stream with elements el_outer
-- to the stream with element el_inner. The result is the iteratee
-- for the outer stream that uses  an `IterateeG el_inner m a'
-- to process the embedded, inner stream as it reads the outer stream.
type EnumeratorN el_outer el_inner m a = 
    IterateeG el_inner m a -> IterateeGM el_outer m (IterateeG el_inner m a)

-- | Read n elements from a stream and apply the given iteratee to the
-- stream of the read elements. Unless the stream is terminated early, we
-- read exactly n elements (even if the iteratee has accepted fewer).
stake :: Monad m => Int -> EnumeratorN el el m a
stake 0 iter = return iter
stake n iter@IE_done{} = sdrop n >> return iter
stake n (IE_cont k) = liftI $ IE_cont step
 where
 step (Chunk []) = liftI $ IE_cont step
 step chunk@(Chunk str) | length str <= n =
                             stake (n - length str) ==<< k chunk
 step (Chunk str) = done (Chunk s1) (Chunk s2)
   where (s1,s2) = splitAt n str
 step stream = done stream stream
 done s1 s2 = k s1 >>== \r -> liftI $ IE_done r s2

-- | Map the stream: yet another iteratee transformer
-- Given the stream of elements of the type el and the function el->el',
-- build a nested stream of elements of the type el' and apply the
-- given iteratee to it.
-- Note the contravariance
--
map_stream :: Monad m => (el -> el') -> EnumeratorN el el' m a
map_stream f iter@IE_done{} = return iter
map_stream f (IE_cont k) = liftI $ IE_cont step
 where
 step (Chunk [])  = liftI $ IE_cont step
 step (Chunk str) = k (Chunk (map f str)) >>== map_stream f
 step EOF         = k EOF       >>== \r -> liftI $ IE_done r EOF
 step (Err err)   = k (Err err) >>== \r -> liftI $ IE_done r (Err err)


-- | Convert one stream into another, not necessarily in `lockstep'
-- The transformer map_stream maps one element of the outer stream
-- to one element of the nested stream. The transformer below is more
-- general: it may take several elements of the outer stream to produce
-- one element of the inner stream, or the other way around.
-- The transformation from one stream to the other is specified as
-- IterateeGM el m (Maybe [el']). The `Maybe' type reflects the
-- possibility of the conversion error.
--
conv_stream :: Monad m =>
        IterateeGM el m (Maybe [el']) -> EnumeratorN el el' m a
conv_stream fi iter@IE_done{} = return iter
conv_stream fi (IE_cont k) = 
    fi >>= (conv_stream fi ==<<) . k . maybe (Err "conv: stream error") Chunk

-- ------------------------------------------------------------------------
-- | Combining the primitive iteratees to solve the running problem:
-- Reading headers and the content from an HTTP-like stream
--
type Line = String      -- The line of text, terminators are not included

-- | Read the line of text from the stream
-- The line can be terminated by CR, LF or CRLF.
-- Return (Right Line) if successful. Return (Left Line) if EOF or
-- a stream error were encountered before the terminator is seen.
-- The returned line is the string read so far.
--
-- The code is the same as that of pure Iteratee, only the signature
-- has changed.
-- Compare the code below with GHCBufferIO.line_lazy
--
line :: Monad m => IterateeM m (Either Line Line)
line = sbreak (\c -> c == '\r' || c == '\n') >>= check_next
 where
 check_next (line,Just '\r') = speek >>= \c ->
        case c of
          Just '\n' -> snext >> return (Right line)
          Just _    -> return (Right line)
          Nothing   -> return (Left line)
 check_next (line,Just _)  = return (Right line)
 check_next (line,Nothing) = return (Left line)




-- | Line iteratees: processors of a stream whose elements are made of Lines
--
-- Collect all read lines and return them as a list
-- see stream2list
--
-- Print lines as they are received. This is the first `impure' iteratee
-- with non-trivial actions during chunk processing
print_lines :: IterateeGM Line IO ()
print_lines = liftI $ IE_cont step
 where
 step (Chunk []) = print_lines
 step (Chunk ls) = lift (mapM_ pr_line ls) >> print_lines
 step EOF        = lift (putStrLn ">> natural end") >> liftI (IE_done () EOF)
 step stream     = lift (putStrLn ">> unnatural end") >>
                   liftI (IE_done () stream)
 pr_line line = putStrLn $ ">> read line: " ++ line


-- | Convert the stream of characters to the stream of lines, and
-- apply the given iteratee to enumerate the latter.
-- The stream of lines is normally terminated by the empty line.
-- When the stream of characters is terminated, the stream of lines
-- is also terminated, abnormally.
-- This is the first proper iteratee-enumerator: it is the iteratee of the
-- character stream and the enumerator of the line stream.
-- More generally, we could have used conv_stream to implement enum_lines.
--
enum_lines :: Monad m => EnumeratorN Char Line m a
enum_lines iter@IE_done{} = return iter
enum_lines (IE_cont k) = line >>= check_line k
 where
 check_line k (Right "") = enum_lines ==<< k EOF      -- empty line, normal term
 check_line k (Right l)  = enum_lines ==<< k (Chunk [l])
 check_line k _          = enum_lines ==<< k (Err "EOF") -- abnormal termin


-- | Convert the stream of characters to the stream of words, and
-- apply the given iteratee to enumerate the latter.
-- Words are delimited by white space.
-- This is the analogue of List.words
-- It is instructive to compare the code below with the code of
-- List.words, which is:
--
-- >words                   :: String -> [String]
-- >words s                 =  case dropWhile isSpace s of
-- >                                "" -> []
-- >                                s' -> w : words s''
-- >                                      where (w, s'') =
-- >                                            break isSpace s'
--
-- One should keep in mind that enum_words is a more general, monadic
-- function.
-- More generally, we could have used conv_stream to implement enum_words.
--
enum_words :: Monad m => EnumeratorN Char String m a
enum_words iter@IE_done{} = return iter
enum_words (IE_cont k) = sdropWhile isSpace >> sbreak isSpace >>= check_word k
 where
 check_word k ("",_)  = enum_words ==<< k EOF
 check_word k (str,_) = enum_words ==<< k (Chunk [str])


-- ------------------------------------------------------------------------
-- | Enumerators
-- Each enumerator takes an iteratee and returns an iteratee
-- an Enumerator is an iteratee transformer.
-- The enumerator normally stops when the stream is terminated
-- or when the iteratee moves to the done state, whichever comes first.
-- When to stop is of course up to the enumerator...
--
-- We have two choices of composition: compose iteratees or compose
-- enumerators. The latter is useful when one iteratee
-- reads from the concatenation of two data sources.
--
type EnumeratorGM el m a = IterateeG el m a -> IterateeGM el m a
type EnumeratorM m a = EnumeratorGM Char m a

-- | The most primitive enumerator: applies the iteratee to the terminated
-- stream. The result is the iteratee usually in the done state.
enum_eof :: Monad m => EnumeratorGM el m a
enum_eof iter@(IE_done _ (Err _)) = liftI iter
enum_eof (IE_done x _) = liftI $ IE_done x EOF
enum_eof (IE_cont k)   = k EOF

-- | Another primitive enumerator: report an error
enum_err :: Monad m => String -> EnumeratorGM el m a
enum_err str iter@(IE_done _ (Err _)) = liftI iter
enum_err str (IE_done x _) = liftI $ IE_done x (Err str)
enum_err str (IE_cont k)   = k (Err str)

-- | The composition of two enumerators: essentially the functional composition
-- It is convenient to flip the order of the arguments of the composition
-- though: in e1 >. e2, e1 is executed first
--
(>.):: Monad m =>
       EnumeratorGM el m a -> EnumeratorGM el m a -> EnumeratorGM el m a
e1 >. e2 = (e2 ==<<) . e1

-- | The pure 1-chunk enumerator
-- It passes a given list of elements to the iteratee in one chunk
-- This enumerator does no IO and is useful for testing of base parsing
enum_pure_1chunk :: Monad m => [el] -> EnumeratorGM el m a
enum_pure_1chunk str iter@IE_done{} = liftI $ iter
enum_pure_1chunk str (IE_cont k) = k (Chunk str)

-- | The pure n-chunk enumerator
-- It passes a given lift of elements to the iteratee in n chunks
-- This enumerator does no IO and is useful for testing of base parsing
-- and handling of chunk boundaries
enum_pure_nchunk :: Monad m => [el] -> Int -> EnumeratorGM el m a
enum_pure_nchunk str n iter@IE_done{} = liftI $ iter
enum_pure_nchunk []  n iter           = liftI $ iter
enum_pure_nchunk str n (IE_cont k)    = enum_pure_nchunk s2 n ==<< k (Chunk s1)
 where (s1,s2) = splitAt n str


-- | The enumerator of a POSIX Fd
-- Unlike fdRead (which allocates a new buffer on
-- each invocation), we use the same buffer all throughout
enum_fd :: Fd -> EnumeratorM IO a
enum_fd fd iter = IM $ allocaBytes (fromIntegral buffer_size) (loop iter)
 where
--  buffer_size = 4096
  buffer_size = 5 -- for tests; in real life, there should be 1024 or so
  loop iter@IE_done{} p = return iter
  loop iter@(IE_cont step) p = do
   n <- myfdRead fd p buffer_size
   putStrLn $ "Read buffer, size " ++ either (const "IO err") show n
   case n of
    Left errno -> unIM $ step (Err "IO error")
    Right 0 -> return iter
    Right n -> do
         str <- peekCAStringLen (p,fromIntegral n)
         im  <- unIM $ step (Chunk str)
         loop im p

enum_file :: FilePath -> EnumeratorM IO a
enum_file filepath iter = IM $ do
  putStrLn $ "opened file " ++ filepath
  fd <- openFd filepath ReadOnly Nothing defaultFileFlags
  r <- unIM $ enum_fd fd iter
  closeFd fd
  putStrLn $ "closed file " ++ filepath
  return r

-- | HTTP chunk decoding
-- Each chunk has the following format:
--
-- >      <chunk-size> CRLF <chunk-data> CRLF
--
-- where <chunk-size> is the hexadecimal number; <chunk-data> is a
-- sequence of <chunk-size> bytes.
-- The last chunk (so-called EOF chunk) has the format
-- 0 CRLF CRLF (where 0 is an ASCII zero, a character with the decimal code 48).
-- For more detail, see "Chunked Transfer Coding", Sec 3.6.1 of
-- the HTTP/1.1 standard:
-- <http://www.w3.org/Protocols/rfc2616/rfc2616-sec3.html#sec3.6.1>
--
-- The following enum_chunk_decoded has the signature of the enumerator
-- of the nested (encapsulated and chunk-encoded) stream. It receives
-- an iteratee for the embedded stream and returns the iteratee for
-- the base, embedding stream. Thus what is an enumerator and what
-- is an iteratee may be a matter of perspective.
--
-- We have a decision to make: Suppose an iteratee has finished (either because
-- it obtained all needed data or encountered an error that makes further
-- processing meaningless). While skipping the rest of the stream/the trailer,
-- we encountered a framing error (e.g., missing CRLF after chunk data).
-- What do we do? We chose to disregard the latter problem.
-- Rationale: when the iteratee has finished, we are in the process
-- of skipping up to the EOF (draining the source).
-- Disregarding the errors seems OK then.
-- Also, the iteratee may have found an error and decided to abort further
-- processing. Flushing the remainder of the input is reasonable then.
-- One can make a different choice...
--
enum_chunk_decoded :: Monad m => Iteratee m a -> IterateeM m a
enum_chunk_decoded = docase
 where
 docase iter@IE_done{} =
    liftI iter >>= (\r -> (enum_chunk_decoded ==<< skip_till_eof) >> return r)
 docase iter@(IE_cont k) = line >>= check_size
  where
  check_size (Right "0") = line >> k EOF
  check_size (Right str) =
     maybe (k . Err $ "Bad chunk size: " ++ str) (read_chunk iter)
         $ read_hex 0 str
  check_size _ = k (Err "Error reading chunk size")

 read_chunk iter size =
     do
     r  <- stake size iter
     c1 <- snext
     c2 <- snext
     case (c1,c2) of
       (Just '\r',Just '\n') -> docase r
       _ -> (enum_chunk_decoded ==<< skip_till_eof) >>
            enum_err "Bad chunk trailer" r

 read_hex acc "" = Just acc
 read_hex acc (d:rest) | isHexDigit d = read_hex (16*acc + digitToInt d) rest
 read_hex acc _ = Nothing


-- ------------------------------------------------------------------------
-- Tests


-- Pure tests, requiring no IO

test_str1 =
    "header1: v1\rheader2: v2\r\nheader3: v3\nheader4: v4\n" ++
    "header5: v5\r\nheader6: v6\r\nheader7: v7\r\n\nrest\n"

testp1 =
    let IE_done (IE_done lines EOF) (Chunk rest)
            = runIdentity . unIM $ enum_pure_1chunk test_str1 ==<<
                                     (enum_lines ==<< stream2list)
    in
    lines == ["header1: v1","header2: v2","header3: v3","header4: v4",
              "header5: v5","header6: v6","header7: v7"]
    && rest == "rest\n"

testp2 =
    let IE_done (IE_done lines EOF) (Chunk rest)
            = runIdentity . unIM $ enum_pure_nchunk test_str1 5 ==<<
                                     (enum_lines ==<< stream2list)
    in
    lines == ["header1: v1","header2: v2","header3: v3","header4: v4",
              "header5: v5","header6: v6","header7: v7"]
    && rest == "r"


testw1 =
    let test_str = "header1: v1\rheader2: v2\r\nheader3:\t v3"
        expected = ["header1:","v1","header2:","v2","header3:","v3"] in
    let run_test test_str =
         let IE_done (IE_done words EOF) EOF
               = runIdentity . unIM $ (enum_pure_nchunk test_str 5 >. enum_eof)
                                        ==<< (enum_words ==<< stream2list)
         in words
    in
    and [run_test test_str == expected,
         run_test (test_str ++ " ") == expected]


-- Test Fd driver

test_driver line_collector filepath = do
  fd <- openFd filepath ReadOnly Nothing defaultFileFlags
  putStrLn "About to read headers"
  result <- unIM $ (enum_fd fd >. enum_eof) ==<< read_lines_and_one_more_line
  closeFd fd
  putStrLn "Finished reading headers"
  case result of
   IE_done (IE_done headers EOF,after) _ ->
       do
       putStrLn $ "The line after headers is: " ++ show after
       putStrLn "Complete headers"
       print headers
   IE_done (IE_done headers err,_) stream ->
       do
       putStrLn $ "Problem " ++ show stream
       putStrLn "Incomplete headers"
       print headers
 where
  read_lines_and_one_more_line = do
     lines <- enum_lines ==<< line_collector
     after <- line
     return (lines,after)


test11 = test_driver stream2list "test1.txt"
test12 = test_driver stream2list "test2.txt"
test13 = test_driver stream2list "test3.txt"
test14 = test_driver stream2list "/dev/null"

test21 = test_driver print_lines "test1.txt"
test22 = test_driver print_lines "test2.txt"
test23 = test_driver print_lines "test3.txt"
test24 = test_driver print_lines "/dev/null"


-- Run the complete test, reading the headers and the body

-- | This simple iteratee is used to process a variety of streams:
-- embedded, interleaved, etc.
line_printer = enum_lines ==<< print_lines

--  |Two sample processors
--
-- Read the headers, print the headers, read the lines of the chunk-encoded
-- body and print each line as it has been read
read_headers_print_body = do
     headers <- enum_lines ==<< stream2list
     case headers of
        IE_done headers EOF -> lift $ do
           putStrLn "Complete headers"
           print headers
        IE_done headers (Err err) -> lift $ do
           putStrLn $ "Incomplete headers due to " ++ err
           print headers

     lift $ putStrLn "\nLines of the body follow"
     enum_chunk_decoded ==<< line_printer

-- | Read the headers and print the header right after it has been read
-- Read the lines of the chunk-encoded body and print each line as
-- it has been read
print_headers_print_body = do
     lift $ putStrLn "\nLines of the headers follow"
     line_printer
     lift $ putStrLn "\nLines of the body follow"
     enum_chunk_decoded ==<< line_printer


test_driver_full iter filepath = do
  fd <- openFd filepath ReadOnly Nothing defaultFileFlags
  putStrLn "About to read headers"
  unIM $ (enum_fd fd >. enum_eof) ==<< iter
  closeFd fd
  putStrLn "Finished reading"

test31 = test_driver_full read_headers_print_body "test_full1.txt"
test32 = test_driver_full read_headers_print_body "test_full2.txt"
test33 = test_driver_full read_headers_print_body "test_full3.txt"

test34 = test_driver_full print_headers_print_body "test_full3.txt"


-- | Interleaved reading from two descriptors using select
--
-- If the two arguments are the names of regular files, the driver
-- does simple round-robin interleaving, reading a block from one
-- file and a block from the other file. If the arguments name
-- pipes or devices, the reading becomes truly supply-driven.
-- We use select for multiplexing.
-- The first argument is the reader-iteratee. It is exactly
-- the same iteratee that is being used in the `sequential' tests above.
-- By design, two Fds are being read independently and in parallel,
-- closely emulating two OS processes each reading from their own file.
-- The code below is a simple, round-robin OS scheduler.
test_driver_mux iter fpath1 fpath2 = do
  fd1 <- openFd fpath1 ReadOnly Nothing defaultFileFlags
  fd2 <- openFd fpath2 ReadOnly Nothing defaultFileFlags
  let fds = [fd1,fd2]
  putStrLn $ "Opened file descriptors: " ++ show fds
  mapM (\(fd,reader) -> unIM reader >>= return . ((,) fd))
       (zip fds (repeat iter)) >>=
     allocaBytes (fromIntegral buffer_size) . loop
  mapM_ closeFd fds
  putStrLn $ "Closed file descriptors. All done"
 where
  -- we use one single IO buffer for reading
  buffer_size = 5 -- for tests; in real life, there should be 1024 or so
  loop fjque buf = do
    let fds = get_fds fjque
    if null fds then return ()
       else do
            selected <- select'read'pending fds
            case selected of
              Left errno -> putStrLn "IO Err" >>
                            tell_iteratee_err "IO Err" fjque >>
                            return ()
              Right []   -> loop fjque buf
              Right sel  -> process buf sel fjque

  -- get Fds from the jobqueue for the unfinished iteratees
  get_fds = foldr (\ (fd,iter) acc ->
                       case iter of {IE_cont _ -> fd:acc; _ -> acc}) []

  -- find the first ready jobqueue element,
  -- that is, the job queue element whose Fd is in selected.
  -- Return the element and the rest of the queue
  get_ready selected jq = (e, before ++ after)
    where (before,e:after) = break (\(fd,_) -> fd `elem` selected) jq

  process buf selected fjque = do
    let ((fd,IE_cont step),fjrest) = get_ready selected fjque
    n <- myfdRead fd buf buffer_size
    putStrLn $ unwords ["Read buffer, size", either (const "IO err") show n,
                        "from fd", show fd]
    case n of
     Left errno -> unIM (step (Err "IO error")) >>
                   loop fjrest buf
     Right 0    -> unIM (step EOF) >>
                   loop fjrest buf
     Right n -> do
         str <- peekCAStringLen (buf,fromIntegral n)
         im  <- unIM $ step (Chunk str)
         loop (fjrest ++ [(fd,im)]) buf -- round-robin

  tell_iteratee_err err = mapM_ (\ (_,iter) -> unIM (enum_err err iter))


-- Running these tests shows true interleaving, of reading from the
-- two file descriptors and of printing the results. All IO is interleaved,
-- and yet it is safe. No unsafe operations are used.
testm1 = test_driver_mux line_printer "test1.txt" "test3.txt"

testm2 = test_driver_mux print_headers_print_body
         "test_full2.txt" "test_full3.txt"
