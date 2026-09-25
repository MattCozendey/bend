# Process.run feeds stdin without a shell, captures both streams and the
# exit code, and bounds execution and combined output on the C and JS lanes.
# Programs go by name, found on PATH (Git's usr/bin on Windows); a timeout
# fails with the host's ETIMEDOUT (110 Linux, 60 macOS, 138 Windows).
# process_run_posix holds the signal and descendant cases.
import Base

def answer(r: Result<&1, &1, U32 & String, U32 & (String & String)>,
  want: U32, out: String, err: String) -> String:
  match r:
    case Done{(code, (stdout, stderr))}:
      Bool.show(Bool.and(U32.is_eq(code, want),
        Bool.and(String.eq(stdout, out), String.eq(stderr, err))))
    case Fail{error}:
      "unexpected failure"

def failure(r: Result<&1, &1, U32 & String, U32 & (String & String)>,
  want: U32) -> String:
  match r:
    case Done{value}:
      "unexpected success"
    case Fail{(code, message)}:
      Bool.show(U32.is_eq(code, want))

def timeout(r: Result<&1, &1, U32 & String, U32 & (String & String)>) ->
  String:
  match r:
    case Done{value}:
      "unexpected success"
    case Fail{(+code, message)}:
      Bool.show(Bool.or(U32.is_eq(code, 110),
        Bool.or(U32.is_eq(code, 60), U32.is_eq(code, 138))))

def main() -> IO(Unit):
  do IO<Unit>:
    a : Result<&1, &1, U32 & String, U32 & (String & String)> <-
      Process.run("cat", [], "Привет 🌍\n", 128, 1000)
    x : Unit <- IO.print("stdin: " ++ answer(a, 0, "Привет 🌍\n", ""))
    b : Result<&1, &1, U32 & String, U32 & (String & String)> <-
      Process.run("echo", ["x; echo injected"], "", 128, 1000)
    y : Unit <- IO.print("literal argv: " ++ answer(b, 0,
      "x; echo injected\n", ""))
    c : Result<&1, &1, U32 & String, U32 & (String & String)> <-
      Process.run("sh", ["-c", "printf out; printf err >&2; exit 7"],
        "", 128, 1000)
    z : Unit <- IO.print("exit and stderr: " ++ answer(c, 7, "out", "err"))
    d : Result<&1, &1, U32 & String, U32 & (String & String)> <-
      Process.run("sh", ["-c", "printf 1234"], "", 4, 1000)
    s : Unit <- IO.print("at limit: " ++ answer(d, 0, "1234", ""))
    e : Result<&1, &1, U32 & String, U32 & (String & String)> <-
      Process.run("sh", ["-c", "printf 12345"], "", 4, 1000)
    t : Unit <- IO.print("over limit: " ++ failure(e, 27))
    p : Result<&1, &1, U32 & String, U32 & (String & String)> <-
      Process.run("sh", ["-c", "printf abc; printf def >&2"],
        "", 5, 1000)
    q : Unit <- IO.print("combined limit: " ++ failure(p, 27))
    f : Result<&1, &1, U32 & String, U32 & (String & String)> <-
      Process.run("sleep", ["2"], "", 128, 30)
    u : Unit <- IO.print("timeout: " ++ timeout(f))
    g : Result<&1, &1, U32 & String, U32 & (String & String)> <-
      Process.run("/__bend_missing_executable__", [], "", 128, 1000)
    v : Unit <- IO.print("missing: " ++ failure(g, 2))
    h : Result<&1, &1, U32 & String, U32 & (String & String)> <-
      Process.run("cat", [], "", 0, 1000)
    w : Unit <- IO.print("invalid limit: " ++ failure(h, 22))
    h0 : Result<&1, &1, U32 & String, U32 & (String & String)> <-
      Process.run("cat", [], "", 1, 0)
    w0 : Unit <- IO.print("invalid timeout: " ++ failure(h0, 22))
    i : Result<&1, &1, U32 & String, U32 & (String & String)> <-
      Process.run("echo", ["bad\u{0}arg"], "", 128, 1000)
    j : Unit <- IO.print("nul argument: " ++ failure(i, 22))
    k : Result<&1, &1, U32 & String, U32 & (String & String)> <-
      Process.run("cat", [], "", 1, 1000)
    l : Unit <- IO.print("empty stdin: " ++ answer(k, 0, "", ""))
    p : Result<&1, &1, U32 & String, U32 & (String & String)> <-
      Process.run("sh", ["-c", "sleep 3 & echo hi"], "", 128, 1500)
    IO.print("inherited pipe: " ++ answer(p, 0, "hi\n", ""))

#|stdin: True
#|literal argv: True
#|exit and stderr: True
#|at limit: True
#|over limit: True
#|combined limit: True
#|timeout: True
#|missing: True
#|invalid limit: True
#|invalid timeout: True
#|nul argument: True
#|empty stdin: True
#|inherited pipe: True
