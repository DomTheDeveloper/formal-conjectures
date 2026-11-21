import Lean.Elab.ParseImportsFast

open Lean

/-- Encode a native Lake header while keeping all visibility and phase flags. -/
private def header (path : System.FilePath) : IO Json := do
  let h ← parseImports' (← IO.FS.readFile path) path.toString
  let imports := h.imports.map fun i =>
    Json.arr #[toJson i.module.toString, toJson i.importAll, toJson i.isExported, toJson i.isMeta]
  return Json.arr #[toJson h.isModule, Json.arr imports]

/-- Read source paths relative to the original and reduced src directories on stdin. -/
def main (args : List String) : IO Unit := do
  let [before, after] := args | throw <| IO.userError "expected original-src reduced-src"
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  repeat
    let line ← stdin.getLine
    if line.isEmpty then break
    let path := line.trimAsciiEnd.toString
    let original ← header (System.FilePath.mk before / path)
    let reduced := System.FilePath.mk after / path
    let newHeader ← if ← reduced.pathExists then header reduced else pure original
    let entry := Json.arr #[toJson path, original, if original == newHeader then Json.null else newHeader]
    stdout.putStrLn entry.compress
