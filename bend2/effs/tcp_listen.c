// TCP
// ===

Term tcp_listen_run(Env e, Term* f, IoWork* w) {
  int fd = socket(AF_INET, SOCK_STREAM, 0);
  if (fd < 0) {
    return io_fail(e, (uint32_t)errno, NULL);
  }
#ifndef _WIN32
  int one = 1;
  setsockopt(fd, SOL_SOCKET, SO_REUSEADDR, &one, sizeof(one));
#else
  // not SO_REUSEADDR: on Windows it lets a second socket take the port
#endif
  struct sockaddr_in at;
  if (io_sys_addr("0.0.0.0", (uint32_t)f[0], &at) < 0) {
#ifdef _WIN32
    sock_close(fd);
#else
    close(fd);
#endif
    return io_fail(e, EINVAL, NULL);
  }
  int bound = bind(fd, (struct sockaddr*)&at, sizeof(at));
  if (bound < 0 || listen(fd, 512) < 0
    || fcntl(fd, F_SETFL, fcntl(fd, F_GETFL) | O_NONBLOCK) < 0) {
    uint32_t code = (uint32_t)errno;
#ifdef _WIN32
    sock_close(fd);
#else
    close(fd);
#endif
    return io_fail(e, code, NULL);
  }
  return io_done(e, io_hand(fd));
}

static void __attribute__((constructor)) tcp_listen_use(void) {
  io_eff(CID(TCP.listen), tcp_listen_run, 0);
}
