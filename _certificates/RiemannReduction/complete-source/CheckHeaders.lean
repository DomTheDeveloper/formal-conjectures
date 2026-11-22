import Lean.Elab.ParseImportsFast

open Lean

/-- Emit each module's imports, including the module, visibility and phase flags. -/
def main (args : List String) : IO Unit := do
  let [root] := args | throw <| IO.userError "expected the source directory"
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  repeat
    let line ← stdin.getLine
    if line.isEmpty then break
    let path := line.trimAsciiEnd.toString
    let header ← parseImports' (← IO.FS.readFile (System.FilePath.mk root / path)) path
    let imports := header.imports.map fun imp =>
      Json.arr #[toJson imp.module.toString, toJson imp.importAll, toJson imp.isExported, toJson imp.isMeta]
    stdout.putStrLn (Json.arr #[toJson path, toJson header.isModule, Json.arr imports]).compress
