# Process.run on POSIX alone (the gate skips a _posix test on Windows):
# a child a signal ends answers 128 + the signal, the child starts with
# SIGPIPE at its default, and a descendant holding the pipes cannot extend
# the run. Windows has no signals, and Bun's spawnSync there reads until
# every writer closes the pipes, so the JS lane cannot stop at the child's
# exit.
import Base

def answer(r: Result<&1, &1, U32 & String, U32 & (String & String)>,
  want: U32, out: String, err: String) -> String:
  match r:
    case Done{(code, (stdout, stderr))}:
      Bool.show(Bool.and(U32.is_eq(code, want),
        Bool.and(String.eq(stdout, out), String.eq(stderr, err))))
    case Fail{error}:
      "unexpected failure"

def contains_answer(r: Result<&1, &1, U32 & String, U32 & (String & String)>,
  want: U32, needle: String) -> String:
  match r:
    case Done{(code, (stdout, stderr))}:
      Bool.show(Bool.and(U32.is_eq(code, want),
        Bool.and(String.contains(stdout, needle), String.eq(stderr, ""))))
    case Fail{error}:
      "unexpected failure"

def main() -> IO(Unit):
  do IO<Unit>:
    m : Result<&1, &1, U32 & String, U32 & (String & String)> <-
      Process.run("/bin/sh", ["-c", "kill -TERM $$"], "", 128, 1000)
    x : Unit <- IO.print("signal: " ++ answer(m, 143, "", ""))
    n : Result<&1, &1, U32 & String, U32 & (String & String)> <-
      Process.run("/usr/bin/perl", ["-e", "print $SIG{PIPE} // q(default)"],
        "", 128, 2000)
    y : Unit <- IO.print("sigpipe default: " ++ answer(n, 0, "default", ""))
    q : Result<&1, &1, U32 & String, U32 & (String & String)> <-
      Process.run("/bin/sh", ["-c", "yes & echo hi"], "", 1048576, 1500)
    IO.print("descendant output: " ++ contains_answer(q, 0, "hi"))

#|signal: True
#|sigpipe default: True
#|descendant output: True
