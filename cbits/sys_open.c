/*
 ************************************************************************
 *
 *		   The lowest but one level file opener
 *
 * This code implements an "extended" system call open(2), which
 * opens a file for reading or writing. A function sys_open() defined
 * in this code takes the same arguments as open(2) and returns the
 * same result (that is, a file handle of an opened file, or -1 in
 * case of error). See "man 2 open" for more details.
 *
 *   int sys_open(const char * filename, const int mode, const int mask)
 *
 * If a filename argument given to sys_open() is a regular file/path
 * name, sys_open() is *identical* to open() (it simply exits
 * to open(), as a matter of fact). Unlike open() however, sys_open() can
 * handle extended file names like "cmd |" or "| cmd", where "cmd" is
 * anything that can be passed to /bin/sh. In that case, shell "/bin/sh"
 * is launched in a subprocess to interpret the "cmd"; the shell's stdin
 * or stdout become the file that is being "opened" by sys_open().
 *
 * An extended file name "cmd |" assumes that cmd's standard output becomes
 * a "file" (a pipe, actually) the caller of sys_open() will read from.
 * That is, "cmd |" assumes a RDONLY open mode. By the same token,
 * a "| cmd" extended file name usually means that the caller of sys_open()
 * would then write into the file; all the data being written will be
 * passed to the stdin of the given "cmd". Still, _regardless_ of how
 * the extended file name is specified, "| cmd" or "cmd |", sys_open() always
 * obeys the opening mode as given by the 'mode' argument. But when
 * a file "cmd |" is open for writing, or "| cmd" is opened for reading,
 * sys_open() writes a gripe about it on the stderr.
 * 
 * Version 4 of this code permits an extended file name to be opened for 
 * both reading _and_ writing, with an O_RDWR open mode. In this case,
 * a *bidirectional* pipe is created -- a pair of sockets. One end of that
 * pipe is returned to the caller as a "handle" to the opened file. The
 * other end is assigned to _both_ stdin and stdout of a forked process
 * (which runs a shell to execute a command).
 * 
 * In extended file names, leading spaces (before the '|' character)
 * and trainling spaces (after the '|' char) are allowed and ignored.
 *
 * This code is patterned after sys_open.cc in the earlier version
 * (v. 2.1) of c++advio distribution. The original inspiration for
 * _popen is due to
 *    Copyright (C) 1991, 1992 Per Bothner. (bothner@cygnus.com)
 *
 * Version 3.0 adds another format of extended file names:
 * 	tcp://hostname:port
 * In this case, sys_open tries to establish a connection to the given
 * host at the given port. If successful, it returns the connected socket
 * (handle). In case of a format, name resolution, network, connection
 * refused etc errors the return result is -1, with errno set appropriately.
 *
 * Version 5.2 adds another format (proposed and implemented by
 * Bernhard Mogens Ege) of extended file names:
 * 	ltcp://hostname:port
 * In this case, sys_open opens a listening socket bound to
 * hostname:port and blocks until it accepts one connection to that
 * socket. If successful, it returns the connected socket (handle). In
 * case of a format, name resolution, network, connection refused etc
 * errors the return result is -1, with errno set appropriately.
 * Normally one would write sys_open("ltcp://0:5000",O_RDWR) to accept
 * the first connection to the port 5000 from any host. To limit the
 * host that is allowed to initiate the connection (e.g., to the
 * localhost) one would write sys_open("ltcp://127.0.0.1:5000",O_RDWR)
 * This implementation is intentionally meant to be simple: only the
 * first incoming connection is accepted. If one wishes to do
 * something more advanced, he can easily do sys_open("nc -l -p port
 * |",O_RDWR), i.e., use a more advanced network program as a filter.
 *
 * Zombie control
 * When we launch a sub-process in response to opening file names such
 * as "cmd |" and "| cmd", we store the child process id and the
 * corresponding file descriptor in a special static table. The table
 * has a fixed size.  If the table is full, we return error EMFILE. On
 * each new open-pipe operation, we scan the table to check if any of
 * the sub-processes terminated. If some have, we clear the
 * corresponding entry. We are not interested in the return code of
 * the sub-process. However, retrieving it (via a call to waitpid)
 * gets rid of a zombie subprocess. This way, we keep the number of
 * zombies under control. We also define a new operation sys_close,
 * which checks the table of subprocesses. If it determines that the
 * file descriptor to close was associated with a pipe, sys_close
 * closes the descriptor and waits until the corresponding process
 * terminates. Otherwise, sys_close is equivalent to the ordinary
 * close(2).
 *
 * $Id: sys_open.c,v 5.3 2007/01/24 22:22:15 oleg Exp oleg $
 *
 ************************************************************************
 */ 

#include <unistd.h>
#include <fcntl.h>
#include <sys/file.h>
#include <errno.h>
#include <assert.h>
#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <limits.h>
#include <sys/wait.h>
#define report_error(MSG,ARG) fprintf(stderr,MSG,(ARG))
#define _XOPEN_SOURCE_EXTENDED
#if 0 /*defined(linux) I guess they fixed it */
typedef unsigned long in_addr_t;
#elif defined(__FreeBSD__)
#include <netinet/in.h>
/*typedef struct in_addr in_addr_t; Fixed in FreeBSD 4.6+ */
#endif
#include <netinet/tcp.h>
#include <sys/socket.h>
#include <arpa/inet.h>
#include <netdb.h>
	/* Convertion between the host and the network byte orders */
#if !defined(htons) && !defined(__htons) && !defined(linux) && !defined(__FreeBSD__)
unsigned short htons(unsigned int data);        /* For a short data item */
unsigned short ntohs(unsigned int data);        /* For a short data item */
unsigned long  htonl(unsigned long data);       /* For a long data item */
#endif
#if !defined(INADDR_NONE)
#define INADDR_NONE (unsigned long)(-1)
#endif

/*
 *------------------------------------------------------------------------
 *
 * Open a connection to a specified host at a specified port, and
 * return the connected socket if successful.
 * A conn_dest parameter must be a string "hostname:port". If it is
 * not in this format, the errno is set to ENXIO.
 */
static const char TCP_EXTENDED_FNAME_PREFIX [] = "tcp://";
static const char TCP_LISTEN_EXTENDED_FNAME_PREFIX [] = "ltcp://";

static struct sockaddr_in parse_dest(const char * conn_dest)
{
  struct sockaddr_in sock_addr;
  char hostname [PATH_MAX+1];
  const char * const colonp = strchr(conn_dest,':');
  sock_addr.sin_family = 0;		/* means invalid, for now */
  
  if( colonp == 0 )
    return report_error("Colon is missing in the destination address '%s'\n",
			conn_dest),
           errno = ENXIO, sock_addr;

  if( (unsigned)(colonp-conn_dest) >= sizeof(hostname) -1 )
    return errno=ENAMETOOLONG, sock_addr;
  strncpy(hostname,conn_dest,colonp-conn_dest);
  hostname[colonp-conn_dest] = '\0';
  
  {			/* Try to parse the port number, after the colon */
    char * endp = (char *)colonp+1;
    const int port_no = strtol(colonp+1,&endp,10);
    if( endp == colonp+1 || *endp != '\0' )
      return report_error("Invalid port specification in the "
			  "destination address '%s'\n",conn_dest),
             errno = ENXIO, sock_addr;
    sock_addr.sin_port = htons((short)port_no);
  }
  
  			/* First check to see if hostname is an IP address in
		   	  the dot notation */
  if( (sock_addr.sin_addr.s_addr = inet_addr(hostname)) != INADDR_NONE )
    return sock_addr.sin_family =  AF_INET, sock_addr;
	
  {			/* Otherwise, try to resolve the hostname */
    struct hostent *host_ptr = gethostbyname(hostname);
    if( host_ptr == 0 )
      return report_error("Hostname '%s' could not be resolved\n",hostname),
             errno = ENXIO, sock_addr;
    if( host_ptr->h_addrtype != AF_INET )
      return report_error("Hostname '%s' isn't an Internet site, or so the DNS says\n",hostname),
             errno = ENXIO, sock_addr;
    memcpy(&sock_addr.sin_addr,host_ptr->h_addr,
	   sizeof(sock_addr.sin_addr.s_addr));
  }
  sock_addr.sin_family =  AF_INET;	/* This makes sock_addr valid	*/
  return sock_addr;
}

static int close_save_errno(const int handle)
{
  const int errno_saved = errno;
  close(handle);
  errno = errno_saved;
  return -1;
}

static int open_connect(const char * conn_dest, int mode)
{
  struct sockaddr_in sock_addr = parse_dest(conn_dest);
  int socket_handle;
   
  if( sock_addr.sin_family == 0 )
    return -1;			/* Failed to parse the connection target addr*/

  if( (socket_handle=socket(AF_INET,SOCK_STREAM,0)) < 0 )
    return socket_handle;

  if( connect(socket_handle, (const struct sockaddr *)&sock_addr,
	      sizeof(sock_addr)) < 0 )
    return close_save_errno(socket_handle);	/* Connection failed */


		/* As the user will probably do his own buffering
		   (via fdopen(), fstream, whatever) 
		   we tell the TCP stack to refrain from buffering
		   See man tcp(7P) for more details on TCP_NODELAY
		 */
  {
    int opt_value = 1;
    if( setsockopt(socket_handle, IPPROTO_TCP, TCP_NODELAY,
	       (char*)&opt_value, sizeof(opt_value)) < 0 )
      return close_save_errno(socket_handle);
  }
  return socket_handle;
}


static int open_listen(const char * conn_dest, int mode)
{
  struct sockaddr_in sock_addr = parse_dest(conn_dest);
  int socket_handle,slaveSocket_handle;
  struct sockaddr_in clientName;
  socklen_t clientLength = sizeof(clientName);
  
  if( sock_addr.sin_family == 0 )
    return -1;			/* Failed to parse the connection target addr*/

  if( (socket_handle=socket(AF_INET,SOCK_STREAM,0)) < 0 )
    return socket_handle;

  {
    int value = 1;
    if( setsockopt(socket_handle, SOL_SOCKET, SO_REUSEADDR,
		   (char*)&value, sizeof(value)) < 0 )
      return close_save_errno(socket_handle);
  }

  if( bind(socket_handle, 
	   (struct sockaddr *)&sock_addr,sizeof(sock_addr)) < 0 )
    return close_save_errno(socket_handle);

  if( listen(socket_handle, 1) < 0 )
    return close_save_errno(socket_handle);

  (void) memset(&clientName, 0, sizeof(clientName));
    
  /* this will block */
  slaveSocket_handle = accept(socket_handle,
			      (struct sockaddr *) &clientName, 
			      &clientLength);

  /* no need for the original listening socket as only one connection
     can be handled per filehandle anyway.
  */
  close(socket_handle);

  if (slaveSocket_handle < 0)		/* if accept() failed. */
    return slaveSocket_handle;
  
		/* As the user will probably do his own buffering
		   (via fdopen(), fstream, whatever) 
		   we tell the TCP stack to refrain from buffering
		   See man tcp(7P) for more details on TCP_NODELAY
		 */
  {
    int opt_value = 1;
    if( setsockopt(slaveSocket_handle, IPPROTO_TCP, TCP_NODELAY,
	       (char*)&opt_value, sizeof(opt_value)) < 0 )
      return close_save_errno(slaveSocket_handle);
  }
  return slaveSocket_handle;
}


/*
 *------------------------------------------------------------------------
 *
 * Launch a shell in a subprocess and have it interpret a string,
 * from cmd_beg up to (but not including) cmd_end. Shell's stdin or
 * stdout is directed to a pipe (depending on the 'mode' argument,
 * which can be either O_RDONLY or O_WRONLY). The other end of this
 * pipe is returned as the result of this function. In case of error,
 * the result is -1.
 * Note, fork() copies parent's address space. So it appears we may
 * modify cmd_beg and cmd_end (see below) at will without affecting
 * the parent. There is a hitch though: sys_open() might be called
 * with a constant string, like sys_open("cat < /tmp/a |"). In which
 * case the string is allocated in a BSS or even TEXT segment, which
 * is read-only. It remains read-only in the child process, so we
 * may not actually modify it.
 */

	/* The table to keep track of pipe sub-processes */
static struct popen_desc {
  pid_t pid;			/* PID for the process on the other end */
  int   fh;			/* The corresponding file descriptor */
} popen_desc_table [5];

static const struct popen_desc * const popen_desc_table_end =
popen_desc_table + sizeof(popen_desc_table)/sizeof(popen_desc_table[0]);

/* Scan the popen_desc_table and check if any of the subprocesses
   terminated. If so, clear (zero out) the corresponding entry.
 */
static void clean_popens(void)
{
  struct popen_desc * pp = (struct popen_desc *)0;
  for(pp=popen_desc_table; pp < popen_desc_table_end; pp++)
  {
    int status;
    if( pp->pid == 0 )
      continue;
    if( waitpid(pp->pid,&status,WNOHANG) != pp->pid )
      continue;		/* pp->pid still runs or waitpid error */
    memset(pp,0,sizeof(pp[0]));
  }
}

/* Try to close fh. Return 0 if successful, 1 if no such fh among
   popen_desc, -1 if there was some error.*/
static int try_close_popen(const int fh)
{
  struct popen_desc * pp = (struct popen_desc *)0;
  for(pp=popen_desc_table; pp < popen_desc_table_end; pp++)
  {
    int status;
    int rc = 0;
    if( pp->fh != fh )
      continue;
    close(fh);
    rc = waitpid(pp->pid,&status,0) < 0 ? -1 : 0;
    if( rc != 0 && errno == ECHILD )
      rc = 0;			/* Ignore the case child being reaped */
    memset(pp,0,sizeof(pp[0]));
    return rc;
  }
  return 1;			/* Didn't find fh among popen_desc_table */
}

static int _popen(const char * cmd_beg, const char * cmd_end, int mode)
{
  struct { int read_fd, write_fd; } pipe_fds;

  int parent_end, child_end;		/* ends of the pipe		*/
  int child_std_end;			/* File handles for stdin/out	*/
  pid_t kid_id;
  struct popen_desc * pp;

  clean_popens();
  for(pp=popen_desc_table; ; pp++)     /* Find empty slot in popen_desc_table*/
  {
    if( pp >= popen_desc_table_end )
      return (errno=EMFILE), -1;
    if( pp->pid == 0 )
      break;
  }
	
  assert( cmd_end > cmd_beg );
  if( pipe((int *)&pipe_fds) < 0 )
    return -1;

  if( mode == O_RDONLY )		/* We're reading, shell is writing */
    parent_end = pipe_fds.read_fd, child_end  = pipe_fds.write_fd,
    child_std_end = 1;			/* command's stdout handle	     */
  else					/* shell is reading, we're writing */
    parent_end = pipe_fds.write_fd, child_end  = pipe_fds.read_fd,
    child_std_end = 0;			/* command's stdin handle	     */

  if( (kid_id = fork()) == 0 )
  {					/* We're in kid's process	     */
					/* which is to execute the command   */
    char * cmd_string = malloc(cmd_end - cmd_beg + 1);
    strncpy(cmd_string,cmd_beg,cmd_end - cmd_beg);
    cmd_string[cmd_end - cmd_beg] = '\0';

    close(parent_end);			
    if( child_end != child_std_end )
    {
      dup2(child_end, child_std_end);
      close(child_end);
    }
    execl("/bin/sh", "sh", "-c", cmd_string, (char *)0);
    _exit(127);				/* Executed only if execl failed!   */
  }

  close(child_end);			/* We're in the parent process	    */
  if( kid_id < 0 )
    close(parent_end), parent_end = -1;	/* if fork failed           */
  else
    pp->pid = kid_id, pp->fh = parent_end;

  return parent_end;
}

/*
 *------------------------------------------------------------------------
 *
 * Launch a shell in a subprocess and have it interpret a string,
 * from cmd_beg up to (but not including) cmd_end. Both shell's stdin _and_
 * stdout are directed to a bidirectional "pipe", which is implemented
 * as a socketpair. One end of the socketpair serves as both stdin and
 * stdout for the kid process; the other end of that pair is returned
 * as the result of this function. In case of error, the result is -1.
 * This function is called when a user has attempted to open a pipe
 * and specified an opening mode of O_RDWR.
 */

static int bidirectional_popen(const char * cmd_beg, const char * cmd_end)
{
  int pair_of_sockets[2];     /* the first element is for the parent,
  				 the other is for the kid */
  int kid_id;
  struct popen_desc * pp;

  clean_popens();
  for(pp=popen_desc_table; ; pp++)     /* Find empty slot in popen_desc_table*/
  {
    if( pp >= popen_desc_table_end )
      return (errno=EMFILE), -1;
    if( pp->pid == 0 )
      break;
  }
	
  assert( cmd_end > cmd_beg );
  if( socketpair(AF_UNIX, SOCK_STREAM, 0, pair_of_sockets) < 0 )
    return -1;

  if( (kid_id = fork()) == 0 )
  {					/* We're in kid's process	     */
					/* which is to execute the command   */
    char * cmd_string = malloc(cmd_end - cmd_beg + 1);
    strncpy(cmd_string,cmd_beg,cmd_end - cmd_beg);
    cmd_string[cmd_end - cmd_beg] = '\0';

    close(pair_of_sockets[0]);		/* close the parent's end	*/
    dup2(pair_of_sockets[1],0);		/* re-direct both stdin and stdout */
    dup2(pair_of_sockets[1],1);
    close(pair_of_sockets[1]);		/* it has been duplicated */
    execl("/bin/sh", "sh", "-c", cmd_string, (char *)0);
    _exit(127);				/* Executed only if execl failed!   */
  }

  close(pair_of_sockets[1]);		/* We're in the parent process	    */
  if( kid_id < 0 )
    return close_save_errno(pair_of_sockets[0]); /* if fork failed          */
  else
    pp->pid = kid_id, pp->fh = pair_of_sockets[0];

  return pair_of_sockets[0];
}

/*
 *------------------------------------------------------------------------
 *			  An extended 'open(2)'
 */
	/* if str begins with a pipe char '|' (after possibly several spaces)
	 * return a pointer to the character right after that.
	 * Otherwise, return NULL
	 */
static const char * check_leading_barchar(const char * str)
{
  register const char * p = str;
  while( *p == ' ' )
    p++;
  return *p == '|' ? p+1 : (char *)0;
}

	/* if str ends with a pipe char '|' (followed by possibly several
	 * spaces) return a pointer to it.
	 * Otherwise, return NULL
	 */
static const char * check_trailing_barchar(const char * str)
{
  register const char * p = str + strlen(str);
  while( *--p == ' ' && p > str )
    ;
  return *p == '|' ? p : (char *)0;
}

int sys_open(const char *filename, const int mode, const int mask)
{
  register const char *p = check_leading_barchar(filename);
  if( p != (char*)0 )
  {				/* fname starts with '|'		*/
  				/* p points to the first char after |   */
    if( *p == '\0' )
      return (errno = EINVAL), -1;	/* Empty command		*/
      
    switch( mode & O_ACCMODE )
    {
      case O_RDONLY:
      	   report_error
	   ("File name '%s' looks like the pipe to write to,"
	    "\nbut the open mode is not WRITE_ONLY\n",filename);
   	   return _popen(p,filename+strlen(filename),O_RDONLY);
   	   
      case O_WRONLY:
   	   return _popen(p,filename+strlen(filename),O_WRONLY);
   	   
      default:
	   return bidirectional_popen(p,filename+strlen(filename));
    }
  }
				/* '|' is the last char of the filename */
  else if( (p=check_trailing_barchar(filename)) != (char *)0 )
  {
    switch( mode & O_ACCMODE )
    {
      case O_RDONLY:
   	   return _popen(filename,p,O_RDONLY);
   	   
      case O_WRONLY:
      	   report_error
	   ("File name '%s' looks like the pipe to read from,"
	    "\nbut the open mode is not READ_ONLY\n",filename);
   	   return _popen(filename,p,O_WRONLY);
   	   
      default:
	   return bidirectional_popen(filename,p);
    }
  }
  else if( strncmp(filename,TCP_EXTENDED_FNAME_PREFIX,
		   strlen(TCP_EXTENDED_FNAME_PREFIX)) == 0 )
    return open_connect(filename+strlen(TCP_EXTENDED_FNAME_PREFIX),mode);
  else if( strncmp(filename,TCP_LISTEN_EXTENDED_FNAME_PREFIX,
		   strlen(TCP_LISTEN_EXTENDED_FNAME_PREFIX)) == 0 )
    return open_listen(filename+strlen(TCP_LISTEN_EXTENDED_FNAME_PREFIX),mode);
  else
    return open(filename,mode,mask);

  return -1;		/* Unnecessary, but gcc really likes it... */
}


/*
 *------------------------------------------------------------------------
 *			  An extended 'close(2)'
 * If needed, clean after ourselves. Otherwise, just do regular close(2).
 * At present, we need to check if fh is a pipe descriptor. If it is,
 * we need to wait for the process to finish.
 */

int sys_close(const int fh)
{
  const int rc = try_close_popen(fh);
  return rc > 0 ? close(fh) : rc;
}
