import Lean

/-- Temporary wrapper used only to export the checked numbered WOWII 146 proof. -/
def main (_args : List String) : IO UInt32 := do
  let result ← IO.Process.output {
    cmd := "python3"
    args := #["scripts/mk_all_146.py"]
  }
  IO.print result.stdout
  IO.eprint result.stderr
  return result.exitCode
