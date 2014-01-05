{-# LANGUAGE ForeignFunctionInterface #-}
{-# LANGUAGE ScopedTypeVariables      #-}

-- |
-- <http://okmij.org/ftp/Haskell/misc.html#sys_open>
--
-- Haskell interface to sys_open.c:
-- providing openFd and closeFd that can deal with `extended'
-- file names (which can name TCP and bi-directional pipes in addition
-- to the regular disk files)
--      <http://okmij.org/ftp/syscall-interpose.html#Application>
--
-- Also included a useful utility read_line to read a NL-terminated
-- line from an Fd. It deliberately uses no handles and so never
-- messes with Fd (in particular, it doesn't put the file descriptor in the 
-- non-blocking mode)
--
-- Simple and reliable uni- and bi-directional pipes
-- 
--     MySysOpen module offers a reliable, proven way of interacting with another
--     local or remote process via a unidirectional or bidirectional channel. It
--     supports pipes and Unix and TCP sockets. MySysOpen is a simple and explicit
--     alternative to the multi-threaded IO processing of the GHC run-time system. The
--     module is the Haskell binding to sys_open -- the extended, user-level file
--     opening interface.
-- 
--     The second half of MySysOpen.hs contains several bi-directional channel
--     interaction tests. One checks repeated sending and receiving of data; the
--     amount of received data is intentionally large, about 510K. Two other tests
--     interact with programs that are not specifically written for interactive use,
--     such as sort. The latter cannot produce any output before it has read all of
--     the input, accepting no input terminator other than the EOF condition. One test
--     uses shutdown to set the EOF condition. The other test programs the handler for
--     a custom EOF indicator, literally in the file name of the communication pipe.
-- 
module System.SysOpen (mysysOpenFd, mysysCloseFd, mysysCloseOut, read_line) where

import Data.List (elemIndex)

import Foreign
import Foreign.C
import System.Posix

-- For testing
import System.IO                (putStrLn, hPutStrLn, hClose, openTempFile)


-- | Interface with my sys_open, see sys_open.c for detailed
-- description and comments
--
foreign import ccall unsafe "sys_open.h sys_open" c_mysysOpen
  :: CString -> CInt -> CInt -> IO CInt

foreign import ccall unsafe "sys_open.h sys_close" c_mysysClose
  :: CInt -> IO CInt

foreign import ccall unsafe "sys/socket.h shutdown" c_shutdown
  :: CInt -> CInt -> IO CInt

-- from "/usr/include/fcntl.h"
--
open_mode_RDONLY :: CInt = 0x0000
open_mode_WRONLY :: CInt = 0x0001
open_mode_RDWR   :: CInt = 0x0002

-- from "/usr/include/sys/socket.h"
flag_SHUT_RD =        0               -- shut down the reading side
flag_SHUT_WR =        1               -- shut down the writing side
flag_SHUT_RDWR =      2               -- shut down both sides


mysysOpenFd:: FilePath -> OpenMode -> Maybe FileMode -> IO Fd
mysysOpenFd path open_mode fmode = 
  throwErrnoIfMinus1 "sys_open" 
     (withCString path $
                \s -> c_mysysOpen s (open_mode_cnv open_mode)
                          (maybe 0666 fromIntegral fmode))
     >>= return.Fd

 where
 open_mode_cnv ReadOnly  = open_mode_RDONLY
 open_mode_cnv WriteOnly = open_mode_WRONLY
 open_mode_cnv ReadWrite = open_mode_RDWR

mysysCloseFd :: Fd -> IO ()
mysysCloseFd fd = c_mysysClose (fromIntegral fd) >> return ()

-- | Close the output direction of the bi-directional pipe
mysysCloseOut :: Fd -> IO ()
mysysCloseOut fd = do
 throwErrnoIfMinus1Retry_ "shutdown" (c_shutdown (fromIntegral fd) flag_SHUT_WR)

-- | Read up to and including newline, return the line and the remaining
-- data. It should be invoked as:
--
-- > read_line "" fd.
--
-- In the case of EOF, the returned line will NOT be terminated with newline
read_line acc fd =
     case elemIndex '\n' acc of
        Nothing -> do (str,n) <- fdRead fd 4000
                      if n == 0 -- EOF
                         then return (acc,"")
                         else read_line (acc++str) fd
        Just i -> return $ splitAt (succ i) acc -- keep \n in the first part


-- ----------------------------------------------------------------------
-- Tests

-- To run tests, compile this code as
-- ghc -O2 -main-is System.MySysOpen.test_main MySysOpen.hs sys_open.c

-- The first two tests check communication with `third-party' programs
-- such as a SAT solver via a bi-directional pipe.
-- In the tests below, we use the system program `sort'.
-- Generally, a program must be specifically written for interactive use 
-- over a bi-directional pipe: The program should avoid read-ahead, 
-- produce output as soon as it obtained all necessary input data, 
-- and be especially careful with buffering.
-- Most systems programs (including sort) are not written with these 
-- goals in mind. These programs cannot be used with inetd,
-- or with bidirectional pipes. The program sort is quite bad in this 
-- respect: it cannot produce any output before it has read all of the input. 
-- It has no input terminator other than the EOF condition. Alas, to send
-- EOF, we have to close the communication channel. How can we receive
-- the reply from sort then?

-- Fortunately, there are work-arounds.
-- The first one is the shutdown(2) system call, to close only
-- the sending direction of the bi-directional pipe.
-- The second work-around is an intermediary to interpret a custom EOF 
-- indicator. We program this intermediary in the `file name'
-- of the communication channel.
-- Other tricks are described in
--      http://okmij.org/ftp/Communications.html#sh-agents

test_main = do
            test_sort1
            test_sort2
            test_proxy >>= print


-- Illustrating the first trick: shutdown to close one direction
-- of the bi-directional pipe.

test_sort1 = do
    putStrLn "Interacting with sort using shutdown"    
    fd <- mysysOpenFd "| sort" ReadWrite Nothing
    putStrLn "Opened the bi-directional pipe to sort"
    fdWrite fd "zzz\nfoo\nbar\n"
    putStrLn "Shutting down the sending direction"
    mysysCloseOut fd
    putStrLn "Reading the reply from sort\n"
    con@(_,rest) <- read_line "" fd
    print con
    con@(_,rest) <- read_line rest fd
    print con
    con@(_,rest) <- read_line rest fd
    print con
    putStrLn "\nDone"

-- Illustrating the second trick: programming the handler for
-- a custom EOF indicator in the file name

test_sort2 = do
    putStrLn "Interacting with sort using the custom EOF indicator"    
    fd <- mysysOpenFd 
      "| (while read i && test $i != '***EOF***'; do echo $i; done) | sort" 
      ReadWrite Nothing
    putStrLn "Opened the bi-directional pipe to sort"
    fdWrite fd "zzz\nfoo\nbar\n***EOF***\n"
    putStrLn "Sent the custom EOF indicator"
    putStrLn "Reading the reply from sort\n"
    con@(_,rest) <- read_line "" fd
    print con
    con@(_,rest) <- read_line rest fd
    print con
    con@(_,rest) <- read_line rest fd
    print con
    putStrLn "\nDone"

-- Check sys_open and the interaction with a `dumb proxy'.
-- We want this test to be representative of SimpleProxy.hs: we send data to
-- another process, read _large_ amount of data in response;
-- send some data again, read large amount again.
-- The proxy below is dumb: it reads an NL-terminated string and
-- writes it out N times, where N is the large number.
-- Then it writes the string "EOF\n".

dummy_proxy ="\
\import System.IO\n\
\main = do{l<-getLine; mapM_ (const (putStrLn l)) [1..10000]; putStrLn \"EOF\"; main}"

test_proxy = do
   (fp,h) <- openTempFile "/tmp" "dproxy.hs"
   hPutStrLn h dummy_proxy
   hClose h
   putStrLn "Starting the dummy proxy"
   pfd <- mysysOpenFd ("| runghc " ++ fp) ReadWrite Nothing
   let test_string = "123xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxZ\n"
   fdWrite pfd test_string
   n <- read_back 0 "" pfd test_string
   -- do it again
   putStrLn "Doing it again"
   let test_string = "55123\n"
   fdWrite pfd test_string
   n <- read_back 0 "" pfd test_string
   mysysCloseFd pfd
   putStrLn "Finished"
   return n
 where
 read_back count acc pfd test_str = do
   (str,rest) <- read_line acc pfd
   -- putStrLn $ "read: `" ++ str ++ "'"
   if str == "EOF\n" then return count
      else if str == test_str then read_back (succ count) rest pfd test_str
              else error "bad read"

