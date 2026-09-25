// File
// ====

static void file_read_call(IoWork* w) {
  int fd = (int)w->hand;
  w->size = io_sys_end(w, read(fd, w->data, w->word));
}

static Term file_read_start(Term file, u64 max, IoWork* w,
  IoCall call, IoPack pack) {
  w->hand = (intptr_t)io_hand_v(file);
  w->word = max < INT32_MAX ? max : INT32_MAX;
  w->data = io_mem(malloc(w->word + 1));
  return io_work(w, call, pack);
}

#ifdef CID(File.read)

static Term file_read_pack(Env e, IoWork* w) {
  Term r = w->code ? io_fail(e, w->code, NULL)
    : io_done(e, io_str(e, w->data, w->size));
  free(w->data);
  return io_tup(e, io_hand(w->hand), r);
}

Term file_read_run(Env e, Term* f, IoWork* w) {
  return file_read_start(f[0], f[1], w, file_read_call, file_read_pack);
}

static void __attribute__((constructor)) file_read_use(void) {
  io_eff(CID(File.read), file_read_run, 0);
}

#endif

#if defined(CID(File.read_bytes)) || defined(CID(File.read_at))

// The bytes as they are (0..255), one List cell each; a text reader
// would decode them as UTF-8.
static Term file_read_bytes_pack(Env e, IoWork* w) {
  Term r;
  if (w->code) {
    r = io_fail(e, w->code, NULL);
  } else {
    Term xs = term_pak(CID(Nil), 0);
    for (u64 i = w->size; i > 0; i -= 1) {
      xs = io_node(e, CID(Con), ((uint8_t*)w->data)[i - 1], xs);
    }
    r = io_done(e, xs);
  }
  free(w->data);
  return io_tup(e, io_hand(w->hand), r);
}

#endif

#ifdef CID(File.read_bytes)

Term file_read_bytes_run(Env e, Term* f, IoWork* w) {
  return file_read_start(f[0], f[1], w, file_read_call, file_read_bytes_pack);
}

static void __attribute__((constructor)) file_read_bytes_use(void) {
  io_eff(CID(File.read_bytes), file_read_bytes_run, 0);
}

#endif

#ifdef CID(File.read_at)

#ifdef _WIN32
// ReadFile at an offset moves the file's position: put it back.
static ssize_t pread(int fd, void* buf, size_t len, int64_t at) {
  HANDLE        h   = (HANDLE)_get_osfhandle(fd);
  LARGE_INTEGER was = { 0 };
  OVERLAPPED    o   = { .Offset = (DWORD)at, .OffsetHigh = (DWORD)(at >> 32) };
  DWORD         got = 0;
  if (h == INVALID_HANDLE_VALUE
    || !SetFilePointerEx(h, (LARGE_INTEGER){ 0 }, &was, FILE_CURRENT)) {
    errno = EBADF;
    return -1;
  }
  DWORD why = ReadFile(h, buf, (DWORD)len, &got, &o) ? 0 : GetLastError();
  SetFilePointerEx(h, was, NULL, FILE_BEGIN);
  if (why != 0 && why != ERROR_HANDLE_EOF) {
    errno = why == ERROR_ACCESS_DENIED ? EBADF : EIO;
    return -1;
  }
  return (ssize_t)got;
}

#endif
// The bytes at an offset, as file_read_bytes gives them; the position of
// the file does not move.
static void file_read_at_call(IoWork* w) {
  int fd = (int)w->hand;
#ifdef _WIN32
  w->size = io_sys_end(w, pread(fd, w->data, w->word, (int64_t)w->made));
#else
  w->size = io_sys_end(w, pread(fd, w->data, w->word, (off_t)w->made));
#endif
}

Term file_read_at_run(Env e, Term* f, IoWork* w) {
  w->made = (intptr_t)f[1];
  return file_read_start(f[0], f[2], w, file_read_at_call, file_read_bytes_pack);
}

static void __attribute__((constructor)) file_read_at_use(void) {
  io_eff(CID(File.read_at), file_read_at_run, 0);
}

#endif
