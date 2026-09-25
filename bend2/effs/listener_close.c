// Listener
// ========

Term listener_close_run(Env e, Term* f, IoWork* w) {
#ifdef _WIN32
  sock_close((int)io_hand_v(f[0]));
#else
  close((int)io_hand_v(f[0]));
#endif
  return term_pak(CID(Unit), 0);
}

static void __attribute__((constructor)) listener_close_use(void) {
  io_eff(CID(Listener.close), listener_close_run, 0);
}
