#ifdef _WIN32

// Windows has no signals to land in the wait, and its loop waits on
// sockets only: the park is on a loopback UDP socket nobody sends to, so
// any wake of it is spurious.
static Term idle_park_more(Env e, IoWork* w) {
  return term_pak(CID(Unit), 0);
}

Term idle_park_run(Env e, Term* f, IoWork* w) {
  struct sockaddr_in at;
  int fd = socket(AF_INET, SOCK_DGRAM, 0);
  if (fd < 0 || io_sys_addr("127.0.0.1", 0, &at) < 0
    || bind(fd, (struct sockaddr*)&at, sizeof(at)) < 0
    || sock_nonblock(fd) < 0) {
    err_fail("select_eintr: no socket");
  }
  return io_wait_on(w, fd, POLLIN, 0, idle_park_more);
}

#else
#include <fcntl.h>

// A no-op handler for SIGWINCH, installed without SA_RESTART, and a
// thread that sends it to the loop's thread ms later. Then the
// computation parks on the read end of a pipe whose write end stays open
// and unwritten: its fd never becomes ready, so a wake is spurious.
static pthread_t idle_loop;

static void idle_hush(int sig) {
}

static void* idle_ring(void* ms) {
  struct timespec t = { (uintptr_t)ms / 1000, (uintptr_t)ms % 1000 * 1000000 };
  nanosleep(&t, NULL);
  pthread_kill(idle_loop, SIGWINCH);
  return NULL;
}

static Term idle_park_more(Env e, IoWork* w) {
  return term_pak(CID(Unit), 0);
}

Term idle_park_run(Env e, Term* f, IoWork* w) {
  struct sigaction sa = { .sa_handler = idle_hush };
  sigaction(SIGWINCH, &sa, NULL);
  idle_loop = pthread_self();
  pthread_t t;
  pthread_create(&t, NULL, idle_ring, (void*)(uintptr_t)(u32)f[0]);
  pthread_detach(t);
  int p[2];
  pipe(p);
  fcntl(p[0], F_SETFL, O_NONBLOCK);
  return io_wait_on(w, p[0], POLLIN, 0, idle_park_more);
}
#endif

static void __attribute__((constructor)) idle_park_use(void) {
  io_eff(CID(Idle.park), idle_park_run, 0);
}
