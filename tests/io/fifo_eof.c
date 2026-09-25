#ifdef _WIN32

// Windows has no FIFO, and its loop waits on sockets only: the FIFO and
// the ack are socket pairs and the child a thread (hi has no meaning:
// WSAPoll has no FD_SETSIZE).
static void* fifo_peer(void* arg) {
  int* p = arg;
  char c;
  for (int i = 0; i < p[2]; i += 1) {
    send(p[0], "x", 1, 0);
  }
  recv(p[1], &c, 1, 0);
  sock_close(p[0]);
  sock_close(p[1]);
  free(p);
  return NULL;
}

// The reader: as the POSIX one below, on a socket.
static Term fifo_drain_more(Env e, IoWork* w) {
  char    b[64];
  ssize_t n = recv((int)w->hand, b, sizeof b, 0);
  if (n > 0) {
    w->size += (u64)n;
    return fifo_drain_more(e, w);
  }
  if (n < 0 && errno == EAGAIN) {
    if (w->code != 0 && w->size == (u64)w->made) {
      sock_close((int)w->code);
      w->code = 0;
    }
    return io_wait_on(w, (int)w->hand, POLLIN, 0, fifo_drain_more);
  }
  sock_close((int)w->hand);
  return (u32)w->size;
}

Term fifo_drain_run(Env e, Term* f, IoWork* w) {
  int*      p = io_mem(malloc(3 * sizeof(int)));
  int       rd[2];
  int       ack[2];
  pthread_t t;
  if (socketpair(AF_UNIX, SOCK_STREAM, 0, rd) != 0
    || socketpair(AF_UNIX, SOCK_STREAM, 0, ack) != 0
    || sock_nonblock(rd[0]) != 0) {
    err_fail("fifo_eof: no socket pair");
  }
  p[0] = rd[1];
  p[1] = ack[0];
  p[2] = (int)f[0];
  if (pthread_create(&t, NULL, fifo_peer, p) != 0) {
    err_fail("fifo_eof: no thread");
  }
  pthread_detach(t);
  w->hand = rd[0];
  w->made = (intptr_t)f[0];
  w->code = (u32)ack[1];
  w->size = 0;
  return fifo_drain_more(e, w);
}

#else
#include <fcntl.h>
#include <sys/resource.h>
#include <sys/stat.h>

// A child writes len bytes into a FIFO, then waits on an ack pipe and
// closes the FIFO only once the reader has drained it and parks again, so
// the reader's last wake is the close alone. The reader's end moves to fd
// hi when hi is nonzero, past FD_SETSIZE if hi is.
static Term fifo_drain_more(Env e, IoWork* w) {
  char    b[64];
  ssize_t n = read((int)w->hand, b, sizeof b);
  if (n > 0) {
    w->size += (u64)n;
    return fifo_drain_more(e, w);
  }
  if (n < 0 && errno == EAGAIN) {
    if (w->code != 0 && w->size == (u64)w->made) {
      close((int)w->code);
      w->code = 0;
    }
    return io_wait_on(w, (int)w->hand, POLLIN, 0, fifo_drain_more);
  }
  close((int)w->hand);
  return (u32)w->size;
}

Term fifo_drain_run(Env e, Term* f, IoWork* w) {
  u32  len = (u32)f[0];
  int  hi  = (int)f[1];
  char path[64];
  snprintf(path, sizeof path, "/tmp/bend_fifo_%d", (int)getpid());
  unlink(path);
  mkfifo(path, 0600);
  int rd = open(path, O_RDONLY | O_NONBLOCK);
  int wr = open(path, O_WRONLY | O_NONBLOCK);
  unlink(path);
  if (hi != 0) {
    struct rlimit r;
    getrlimit(RLIMIT_NOFILE, &r);
    r.rlim_cur = r.rlim_cur > (rlim_t)hi ? r.rlim_cur : (rlim_t)hi + 1;
    setrlimit(RLIMIT_NOFILE, &r);
    dup2(rd, hi);
    close(rd);
    rd = hi;
  }
  int ack[2];
  pipe(ack);
  if (fork() == 0) {
    char c;
    close(ack[1]);
    for (u32 i = 0; i < len; i += 1) {
      write(wr, "x", 1);
    }
    read(ack[0], &c, 1);
    _exit(0);
  }
  close(ack[0]);
  close(wr);
  w->hand = rd;
  w->made = len;
  w->code = (u32)ack[1];
  w->size = 0;
  return fifo_drain_more(e, w);
}
#endif

static void __attribute__((constructor)) fifo_drain_use(void) {
  io_eff(CID(fifo.drain), fifo_drain_run, 0);
}
