import Bootstrap.Kernel

-- for now, the kernel's own check: it shows this program imports the
-- kernel and declares its own main
def main (args : List String) : IO UInt32 := do
  match args with
  | [path] =>
    let s ← IO.FS.readFile path
    match Book.parse s >>= Book.check with
    | .ok _ =>
      IO.println "CHECKED"
      pure 0
    | .error e =>
      IO.println ("REJECTED\n" ++ e)
      pure 1
  | _ =>
    IO.println "usage: bootstrap <file.bendtt>"
    pure 2
