// Process
// =======

#ifndef _WIN32
#include <spawn.h>
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

static void process_append(ProcessCall* p, bool error, const char* data,
  u64 size) {
  if (size > (u64)p->max - p->out_len - p->err_len) {
    p->code = EFBIG;
    return;
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
}

#ifdef _WIN32

// Windows: CreateProcessW on the argv joined as CommandLineToArgvW splits
// it (a bare name found as CreateProcess finds one: PATH, .exe added), the
// child inheriting its three pipe ends alone. Anonymous pipes have no poll:
// the loop peeks the outputs, writes the input without waiting and, idle,
// sleeps a millisecond.
static wchar_t* process_wide(const char* s) {
  int      len  = MultiByteToWideChar(CP_UTF8, 0, s, -1, NULL, 0);
  wchar_t* wide = io_mem(malloc((u64)len * sizeof(wchar_t)));
  MultiByteToWideChar(CP_UTF8, 0, s, -1, wide, len);
  return wide;
}

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
  wchar_t* wide = process_wide(line);
  free(line);
  return wide;
}

// A name CreateProcess cannot start, a .cmd or .bat script found as cmd.exe
// finds one (Bun.spawn starts those, so the JS lane does), runs through
// %ComSpec%. cmd.exe expands " % ! and line ends even inside quotes, so an
// argument holding one is refused (EINVAL) rather than escaped, as
// CVE-2024-24576 warns.
static const char PROCESS_CMD_BAD[] = "\"%!\r\n";

static char* process_narrow(const wchar_t* s) {
  int   len = WideCharToMultiByte(CP_UTF8, 0, s, -1, NULL, 0, NULL, NULL);
  char* out = io_mem(malloc((u64)len));
  WideCharToMultiByte(CP_UTF8, 0, s, -1, out, len, NULL, NULL);
  return out;
}

static wchar_t* process_search(const wchar_t* name, const wchar_t* ext) {
  DWORD n = SearchPathW(NULL, name, ext, 0, NULL, NULL);
  if (n == 0) {
    return NULL;
  }
  wchar_t* out = io_mem(malloc((u64)n * sizeof(wchar_t)));
  DWORD    got = SearchPathW(NULL, name, ext, n, out, NULL);
  if (got == 0 || got >= n) {
    free(out);
    return NULL;
  }
  return out;
}

static bool process_is_script(const wchar_t* path) {
  size_t n = wcslen(path);
  return n >= 4 && (_wcsicmp(path + n - 4, L".cmd") == 0
    || _wcsicmp(path + n - 4, L".bat") == 0);
}

// The script a name with a folder in it names, if it is one.
static wchar_t* process_script_at(const wchar_t* name) {
  DWORD n = GetFullPathNameW(name, 0, NULL, NULL);
  wchar_t* full = io_mem(malloc((u64)(n + 1) * sizeof(wchar_t)));
  DWORD got = GetFullPathNameW(name, n + 1, full, NULL);
  if (got == 0 || got > n || GetFileAttributesW(full) == INVALID_FILE_ATTRIBUTES) {
    free(full);
    return NULL;
  }
  return full;
}

// The script a bare name with no extension names: none when an .exe is
// found, as CreateProcess then starts it; else the first PATHEXT match.
static wchar_t* process_script_bare(const wchar_t* name) {
  wchar_t* exe = process_search(name, L".exe");
  if (exe != NULL) {
    free(exe);
    return NULL;
  }
  wchar_t exts[1024];
  DWORD   n = GetEnvironmentVariableW(L"PATHEXT", exts, 1024);
  if (n == 0 || n >= 1024) {
    wcscpy(exts, L".COM;.EXE;.BAT;.CMD");
  }
  wchar_t* rest  = NULL;
  wchar_t* found = NULL;
  for (wchar_t* ext = wcstok_s(exts, L";", &rest); ext != NULL && found == NULL;
    ext = wcstok_s(NULL, L";", &rest)) {
    found = process_search(name, ext);
  }
  return found;
}

// The full path of the .cmd or .bat script program names, or NULL.
static wchar_t* process_script(const char* program) {
  wchar_t* name  = process_wide(program);
  wchar_t* found = strpbrk(program, "\\/:") != NULL ? process_script_at(name)
    : strchr(program, '.') != NULL ? process_search(name, NULL)
    : process_script_bare(name);
  free(name);
  if (found != NULL && !process_is_script(found)) {
    free(found);
    return NULL;
  }
  return found;
}

// cmd.exe's line for a script: every argument quoted, its trailing
// backslashes doubled so the closing quote stays one; NULL when the program
// is no script, or, with EINVAL, when an argument cannot pass cmd.exe.
static wchar_t* process_script_line(ProcessCall* p, wchar_t** app) {
  wchar_t* script = process_script(p->argv[0]);
  if (script == NULL) {
    return NULL;
  }
  char* path = process_narrow(script);
  free(script);
  bool bad = strpbrk(path, PROCESS_CMD_BAD) != NULL;
  u64  size = strlen(path) + 32;
  for (u32 i = 1; i < p->argc; i += 1) {
    bad |= strpbrk(p->argv[i], PROCESS_CMD_BAD) != NULL;
    size += 2 * strlen(p->argv[i]) + 3;
  }
  if (bad) {
    free(path);
    p->code = EINVAL;
    return NULL;
  }
  char* line = io_mem(malloc(size));
  char* at   = line + sprintf(line, "cmd.exe /d /s /v:off /c \"\"%s\"", path);
  free(path);
  for (u32 i = 1; i < p->argc; i += 1) {
    const char* a = p->argv[i];
    u64         n = strlen(a);
    u64         k = 0;
    while (k < n && a[n - 1 - k] == '\\') {
      k += 1;
    }
    at += sprintf(at, " \"%s", a);
    memset(at, '\\', k);
    at += k;
    *at++ = '"';
  }
  *at++ = '"';
  *at   = '\0';
  wchar_t spec[MAX_PATH];
  DWORD   m = GetEnvironmentVariableW(L"ComSpec", spec, MAX_PATH);
  if (m == 0 || m >= MAX_PATH) {
    UINT s = GetSystemDirectoryW(spec, MAX_PATH - 9);
    wcscpy(spec + (s == 0 || s >= MAX_PATH - 9 ? 0 : s), L"\\cmd.exe");
  }
  *app = io_mem(malloc((wcslen(spec) + 1) * sizeof(wchar_t)));
  wcscpy(*app, spec);
  wchar_t* wide = process_wide(line);
  free(line);
  return wide;
}

static void process_shut(HANDLE* h) {
  if (*h != NULL) {
    CloseHandle(*h);
    *h = NULL;
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
  wchar_t* app  = NULL;
  wchar_t* line = process_script_line(p, &app);
  line = line != NULL || p->code != 0 ? line : process_line(p);
  if (p->code == 0 && !CreateProcessW(app, line, NULL, NULL, TRUE,
    EXTENDED_STARTUPINFO_PRESENT, NULL, NULL, &si.StartupInfo, &pi)) {
    DWORD why = GetLastError();
    p->code = why == ERROR_FILE_NOT_FOUND || why == ERROR_PATH_NOT_FOUND
      ? ENOENT : why == ERROR_ACCESS_DENIED ? EACCES : EIO;
  }
  DeleteProcThreadAttributeList(list);
  free(list);
  free(app);
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
        process_append(p, i == 2, buf, n);
        moved = true;
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
    // as on POSIX, the child is done once its pipes close and it exited
    bool reading = io[1][0] != NULL || io[2][0] != NULL;
    if (!reading && WaitForSingleObject(pi.hProcess, !moved) == WAIT_OBJECT_0) {
      live = false;
      break;
    }
    if (reading && !moved) {
      Sleep(1);
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
    bool reading = pipes[1][0] >= 0 || pipes[2][0] >= 0;
    pid_t got = reading ? 0 : waitpid(child, &status, WNOHANG);
    if (got == child) {
      child = -1;
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
    struct pollfd fds[4] = {
      {pipes[0][1], POLLOUT, 0},
      {pipes[1][0], POLLIN, 0},
      {pipes[2][0], POLLIN, 0},
      {reading ? -1 : exitfd, POLLIN, 0}
    };
    u64 left = (deadline - now + 999999ull) / 1000000ull;
    u64 most = reading || exitfd >= 0 ? 1000000 : 50;
    int ready = poll(fds, 4, (int)(left > most ? most : left));
    if (ready < 0) {
      if (errno == EINTR) {
        continue;
      }
      p->code = errno;
      break;
    }
    for (int i = 0; i < 3 && p->code == 0; i += 1) {
      if (fds[i].revents == 0) {
        continue;
      }
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
  io_eff(CID(Process.run), process_run_run);
}
