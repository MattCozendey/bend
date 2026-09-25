// Process
// =======

#ifndef _WIN32
#include <spawn.h>
#include <sys/ioctl.h>
#include <sys/wait.h>
#ifdef __APPLE__
#include <sys/event.h>
#else
#include <sys/syscall.h>
#endif

extern char** environ;
#endif

typedef struct {
  char** argv;
  u32 argc;
  char* input;
  u64 input_len;
  char* out;
  char* err;
  u64 out_len;
  u64 err_len;
  u64 out_cap;
  u64 err_cap;
  u32 max;
  u32 timeout;
  u32 status;
  u32 code;
} ProcessCall;

static void process_free(ProcessCall* p) {
  for (u32 i = 0; i < p->argc; i += 1) {
    free(p->argv[i]);
  }
  free(p->argv);
  free(p->input);
  free(p->out);
  free(p->err);
  free(p);
}

static bool process_append(ProcessCall* p, bool error, const char* data,
  u64 size) {
  if (size > (u64)p->max - p->out_len - p->err_len) {
    p->code = EFBIG;
    return false;
  }
  char** buf = error ? &p->err : &p->out;
  u64* len  = error ? &p->err_len : &p->out_len;
  u64* cap  = error ? &p->err_cap : &p->out_cap;
  u64 need  = *len + size;
  if (need > *cap) {
    u64 next = *cap ? *cap : 4096;
    while (next < need) {
      next *= 2;
    }
    if (next > p->max) {
      next = p->max;
    }
    *buf = io_mem(realloc(*buf, next + 1));
    *cap = next;
  }
  memcpy(*buf + *len, data, size);
  *len = need;
  return true;
}

#ifdef _WIN32

// Windows: CreateProcessW on the argv joined as CommandLineToArgvW splits
// it (a bare name found as CreateProcess finds one: PATH, .exe added), the
// child inheriting its three pipe ends alone. Anonymous pipes have no poll:
// the loop peeks the outputs, writes the input without waiting and, idle,
// waits a millisecond on the child.
static wchar_t* process_line(ProcessCall* p) {
  u64 size = 1;
  for (u32 i = 0; i < p->argc; i += 1) {
    size += 2 * strlen(p->argv[i]) + 3;
  }
  char* line = io_mem(malloc(size));
  char* at   = line;
  for (u32 i = 0; i < p->argc; i += 1) {
    const char* a = p->argv[i];
    bool        q = *a == '\0' || strpbrk(a, " \t\n\v\"") != NULL;
    at += sprintf(at, i == 0 ? "%s" : " %s", q ? "\"" : "");
    // backslashes double before a quote, which then takes one more
    for (;; a += 1) {
      u64 n = strspn(a, "\\");
      a += n;
      n = !q ? n : *a == '\0' ? 2 * n : *a == '"' ? 2 * n + 1 : n;
      memset(at, '\\', n);
      at += n;
      if (*a == '\0') {
        break;
      }
      *at++ = *a;
    }
    at += sprintf(at, "%s", q ? "\"" : "");
  }
  int      len  = MultiByteToWideChar(CP_UTF8, 0, line, -1, NULL, 0);
  wchar_t* wide = io_mem(malloc((u64)len * sizeof(wchar_t)));
  MultiByteToWideChar(CP_UTF8, 0, line, -1, wide, len);
  free(line);
  return wide;
}

static void process_shut(HANDLE* h) {
  if (*h != NULL) {
    CloseHandle(*h);
    *h = NULL;
  }
}

// Once the child exits, reads only the bytes already in the pipe: the child
// cannot exit blocked on a write, so all of its own output is there, and a
// descendant holding the pipe cannot extend it.
static void process_drain(ProcessCall* p, HANDLE h, bool error) {
  DWORD left = 0;
  if (!PeekNamedPipe(h, NULL, 0, NULL, &left, NULL)) {
    left = 0;
  }
  while (left > 0 && p->code == 0) {
    char  buf[8192];
    DWORD n = 0;
    if (!ReadFile(h, buf, left < sizeof buf ? left : sizeof buf, &n, NULL)
      || n == 0) {
      break;
    }
    process_append(p, error, buf, n);
    left -= n;
  }
}

static void process_call(IoWork* w) {
  ProcessCall* p = (ProcessCall*)w->data;
  HANDLE io[3][2] = {{NULL, NULL}, {NULL, NULL}, {NULL, NULL}};
  HANDLE mine[3];
  PROCESS_INFORMATION pi = {0};
  for (int i = 0; i < 3; i += 1) {
    p->code = CreatePipe(&io[i][0], &io[i][1], NULL, 65536) ? p->code
      : EMFILE;
    mine[i] = io[i][i != 0];
    SetHandleInformation(mine[i], HANDLE_FLAG_INHERIT, HANDLE_FLAG_INHERIT);
  }
  SetNamedPipeHandleState(io[0][1], &(DWORD){ PIPE_NOWAIT }, NULL, NULL);
  SIZE_T size = 0;
  InitializeProcThreadAttributeList(NULL, 1, 0, &size);
  LPPROC_THREAD_ATTRIBUTE_LIST list = io_mem(malloc(size));
  InitializeProcThreadAttributeList(list, 1, 0, &size);
  UpdateProcThreadAttribute(list, 0, PROC_THREAD_ATTRIBUTE_HANDLE_LIST, mine,
    sizeof mine, NULL, NULL);
  STARTUPINFOEXW si = { { .cb = sizeof si, .dwFlags = STARTF_USESTDHANDLES,
    .hStdInput = mine[0], .hStdOutput = mine[1], .hStdError = mine[2] },
    list };
  wchar_t* line = process_line(p);
  if (p->code == 0 && !CreateProcessW(NULL, line, NULL, NULL, TRUE,
    EXTENDED_STARTUPINFO_PRESENT, NULL, NULL, &si.StartupInfo, &pi)) {
    DWORD why = GetLastError();
    p->code = why == ERROR_FILE_NOT_FOUND || why == ERROR_PATH_NOT_FOUND
      ? ENOENT : why == ERROR_ACCESS_DENIED ? EACCES : EIO;
  }
  DeleteProcThreadAttributeList(list);
  free(list);
  free(line);
  for (int i = 0; i < 3; i += 1) {
    process_shut(&io[i][i != 0]);
  }
  if (p->input_len == 0) {
    process_shut(&io[0][1]);
  }
  u64  deadline = io_tick() + (u64)p->timeout * 1000000ull;
  u64  written  = 0;
  bool live     = p->code == 0;
  while (p->code == 0) {
    bool  moved = false;
    DWORD n     = 0;
    for (int i = 1; i < 3 && p->code == 0; i += 1) {
      char buf[8192];
      // a pipe whose every writer closed fails the peek once drained
      if (io[i][0] != NULL
        && !PeekNamedPipe(io[i][0], NULL, 0, NULL, &n, NULL)) {
        process_shut(&io[i][0]);
      } else if (io[i][0] != NULL && n > 0
        && ReadFile(io[i][0], buf, n < sizeof buf ? n : sizeof buf, &n, NULL)) {
        moved = process_append(p, i == 2, buf, n);
      }
    }
    if (io[0][1] != NULL) {
      u64 left = p->input_len - written;
      // a reader gone fails the write, as EPIPE does: the input ends
      n = WriteFile(io[0][1], p->input + written,
        left < 8192 ? (DWORD)left : 8192, &n, NULL) ? n : (DWORD)left;
      written += n;
      moved = moved || n > 0;
      if (written == p->input_len) {
        process_shut(&io[0][1]);
      }
    }
    if (WaitForSingleObject(pi.hProcess, !moved) == WAIT_OBJECT_0) {
      live = false;
      for (int i = 1; i < 3; i += 1) {
        if (io[i][0] != NULL) {
          process_drain(p, io[i][0], i == 2);
        }
      }
      break;
    }
    if (io_tick() >= deadline) {
      p->code = ETIMEDOUT;
    }
  }
  if (live) {
    TerminateProcess(pi.hProcess, 1);
    WaitForSingleObject(pi.hProcess, INFINITE);
  }
  DWORD status = 1;
  GetExitCodeProcess(pi.hProcess, &status);
  p->status = (u32)status;
  for (int i = 0; i < 3; i += 1) {
    process_shut(&io[i][0]);
    process_shut(&io[i][1]);
  }
  process_shut(&pi.hProcess);
  process_shut(&pi.hThread);
}

#else
static void process_drain(ProcessCall* p, int fd, bool error) {
  int left = 0;
  if (ioctl(fd, FIONREAD, &left) != 0) {
    p->code = errno;
  }
  while (left > 0 && p->code == 0) {
    char buf[8192];
    ssize_t n = read(fd, buf, left < 8192 ? (size_t)left : 8192);
    if (n <= 0) {
      p->code = n < 0 ? errno : 0;
      break;
    }
    process_append(p, error, buf, (u64)n);
    left -= (int)n;
  }
}

// A descriptor that polls readable once the child exits.
static int process_exitfd(pid_t child) {
#ifdef __APPLE__
  int kq = kqueue();
  struct kevent ev;
  EV_SET(&ev, child, EVFILT_PROC, EV_ADD | EV_ONESHOT, NOTE_EXIT, 0, NULL);
  if (kq >= 0 && kevent(kq, &ev, 1, NULL, 0, NULL) != 0) {
    close(kq);
    kq = -1;
  }
  return kq;
#elif defined(SYS_pidfd_open)
  return (int)syscall(SYS_pidfd_open, child, 0);
#else
  return -1;
#endif
}

static int process_nonblock(int fd) {
  int flags = fcntl(fd, F_GETFL);
  return flags < 0 ? -1 : fcntl(fd, F_SETFL, flags | O_NONBLOCK);
}

static int process_pipe(int fds[2]) {
  if (pipe(fds) != 0) {
    return -1;
  }
  for (int i = 0; i < 2; i += 1) {
    if (fds[i] < 3) {
      int moved = fcntl(fds[i], F_DUPFD, 3);
      if (moved < 0) {
        return -1;
      }
      close(fds[i]);
      fds[i] = moved;
    }
    if (fcntl(fds[i], F_SETFD, FD_CLOEXEC) != 0) {
      return -1;
    }
  }
  return 0;
}

static void process_call(IoWork* w) {
  ProcessCall* p = (ProcessCall*)w->data;
  int pipes[3][2] = {{-1, -1}, {-1, -1}, {-1, -1}};
  pid_t child = -1;
  int status = 0;
  int exitfd = -1;
  for (int i = 0; i < 3; i += 1) {
    if (process_pipe(pipes[i]) != 0) {
      p->code = errno;
      goto done;
    }
  }
  if (process_nonblock(pipes[0][1]) != 0
    || process_nonblock(pipes[1][0]) != 0
    || process_nonblock(pipes[2][0]) != 0) {
    p->code = errno;
    goto done;
  }
  posix_spawn_file_actions_t actions;
  p->code = posix_spawn_file_actions_init(&actions);
  if (p->code != 0) {
    goto done;
  }
  p->code = posix_spawn_file_actions_adddup2(&actions, pipes[0][0], 0);
  if (p->code == 0) {
    p->code = posix_spawn_file_actions_adddup2(&actions, pipes[1][1], 1);
  }
  if (p->code == 0) {
    p->code = posix_spawn_file_actions_adddup2(&actions, pipes[2][1], 2);
  }
  posix_spawnattr_t attr;
  posix_spawnattr_t* attrp = NULL;
  if (p->code == 0) {
    p->code = posix_spawnattr_init(&attr);
    if (p->code == 0) {
      attrp = &attr;
      sigset_t defaults;
      sigemptyset(&defaults);
      sigaddset(&defaults, SIGPIPE);
      p->code = posix_spawnattr_setsigdefault(&attr, &defaults);
      if (p->code == 0) {
        short flags = POSIX_SPAWN_SETSIGDEF;
#ifdef __APPLE__
        flags |= POSIX_SPAWN_CLOEXEC_DEFAULT;
#endif
        p->code = posix_spawnattr_setflags(&attr, flags);
      }
    }
  }
#ifndef __APPLE__
  if (p->code == 0) {
    p->code = posix_spawn_file_actions_addclosefrom_np(&actions, 3);
  }
#endif
  if (p->code == 0) {
    p->code = posix_spawnp(&child, p->argv[0], &actions, attrp, p->argv,
      environ);
  }
  if (attrp != NULL) {
    posix_spawnattr_destroy(attrp);
  }
  posix_spawn_file_actions_destroy(&actions);
  if (p->code != 0) {
    child = -1;
    goto done;
  }
  close(pipes[0][0]); pipes[0][0] = -1;
  close(pipes[1][1]); pipes[1][1] = -1;
  close(pipes[2][1]); pipes[2][1] = -1;
  if (p->input_len == 0) {
    close(pipes[0][1]); pipes[0][1] = -1;
  }
  exitfd = process_exitfd(child);
  u64 deadline = io_tick() + (u64)p->timeout * 1000000ull;
  u64 written  = 0;
  while (p->code == 0) {
    pid_t got = waitpid(child, &status, WNOHANG);
    if (got == child) {
      child = -1;
      for (int i = 1; i < 3; i += 1) {
        if (pipes[i][0] >= 0) {
          process_drain(p, pipes[i][0], i == 2);
        }
      }
      break;
    }
    if (got < 0 && errno != EINTR) {
      p->code = errno;
      break;
    }
    u64 now = io_tick();
    if (now >= deadline) {
      p->code = ETIMEDOUT;
      break;
    }
    struct pollfd fds[4];
    int roles[3];
    nfds_t count = 0;
    for (int i = 0; i < 3; i += 1) {
      int fd = i == 0 ? pipes[0][1] : pipes[i][0];
      if (fd >= 0) {
        fds[count] = (struct pollfd){fd, i == 0 ? POLLOUT : POLLIN, 0};
        roles[count++] = i;
      }
    }
    if (exitfd >= 0) {
      fds[count++] = (struct pollfd){exitfd, POLLIN, 0};
    }
    u64 left = (deadline - now + 999999ull) / 1000000ull;
    u64 most = exitfd >= 0 ? 1000000 : 50;
    int ready = poll(fds, count, (int)(left > most ? most : left));
    if (ready < 0) {
      if (errno == EINTR) {
        continue;
      }
      p->code = errno;
      break;
    }
    if (exitfd >= 0 && fds[count - 1].revents != 0) {
      continue;
    }
    for (nfds_t k = 0; k < count && p->code == 0; k += 1) {
      if (fds[k].revents == 0) {
        continue;
      }
      int i = roles[k];
      if (i == 0) {
        u64 remain = p->input_len - written;
        size_t size = remain < 8192 ? (size_t)remain : 8192;
        ssize_t n = write(pipes[0][1], p->input + written, size);
        if (n > 0) {
          written += (u64)n;
        } else if (n < 0 && errno != EAGAIN && errno != EINTR
          && errno != EPIPE) {
          p->code = errno;
        }
        if (written == p->input_len || (n < 0 && errno == EPIPE)) {
          close(pipes[0][1]); pipes[0][1] = -1;
        }
      } else {
        char buf[8192];
        ssize_t n = read(pipes[i][0], buf, sizeof buf);
        if (n > 0) {
          process_append(p, i == 2, buf, (u64)n);
        } else if (n == 0) {
          close(pipes[i][0]); pipes[i][0] = -1;
        } else if (errno != EAGAIN && errno != EINTR) {
          p->code = errno;
        }
      }
    }
  }
  if (child >= 0) {
    if (p->code != 0) {
      kill(child, SIGKILL);
    }
    while (waitpid(child, &status, 0) < 0 && errno == EINTR) {
    }
  }
  if (p->code == 0) {
    p->status = WIFEXITED(status) ? (u32)WEXITSTATUS(status)
      : WIFSIGNALED(status) ? 128 + (u32)WTERMSIG(status) : 1;
  }
done:
  if (exitfd >= 0) {
    close(exitfd);
  }
  for (int i = 0; i < 3; i += 1) {
    for (int j = 0; j < 2; j += 1) {
      if (pipes[i][j] >= 0) {
        close(pipes[i][j]);
      }
    }
  }
}
#endif

static Term process_pack(Env e, IoWork* w) {
  ProcessCall* p = (ProcessCall*)w->data;
  Term result;
  if (p->code != 0) {
    result = io_fail(e, p->code, NULL);
  } else {
    Term out = io_str(e, p->out == NULL ? "" : p->out, p->out_len);
    Term err = io_str(e, p->err == NULL ? "" : p->err, p->err_len);
    result = io_done(e, io_tup(e, p->status, io_tup(e, out, err)));
  }
  process_free(p);
  return result;
}

Term process_run_run(Env e, Term* f, IoWork* w) {
  ProcessCall* p = io_mem(calloc(1, sizeof(ProcessCall)));
  u64 len = 0;
  char* command = io_cstr(e, f[0], &len);
  p->code = io_nul(command, len) ? EINVAL : 0;
  u32 capacity = 8;
  p->argv = io_mem(calloc(capacity, sizeof(char*)));
  p->argv[p->argc++] = command;
  Term xs = f[1];
  while (term_aux(xs) == CID_CON) {
    Term pair[2];
    spare_free(e, cls_fit(2), ctr_take(e, xs, 2, pair));
    char* arg = io_cstr(e, pair[0], &len);
    if (io_nul(arg, len)) {
      p->code = EINVAL;
    }
    if (p->argc + 1 >= capacity) {
      capacity *= 2;
      p->argv = io_mem(realloc(p->argv, capacity * sizeof(char*)));
    }
    p->argv[p->argc++] = arg;
    xs = pair[1];
  }
  p->argv[p->argc] = NULL;
  p->input = io_cstr(e, f[2], &p->input_len);
  p->max = (u32)f[3];
  p->timeout = (u32)f[4];
  if (p->max == 0 || p->timeout == 0) {
    p->code = EINVAL;
  }
  w->data = (char*)p;
  return p->code != 0 ? process_pack(e, w)
    : io_work(w, process_call, process_pack);
}

static void __attribute__((constructor)) process_run_use(void) {
  io_eff(CID(Process.run), process_run_run, 0);
}
