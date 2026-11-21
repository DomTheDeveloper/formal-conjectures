import Export

open Lean

def main (args : List String) : IO Unit := do
  let [inventory, module, target] := args | throw <| IO.userError "expected catalog, module, and root"
  initSearchPath (← findSysroot)
  let env ← importModules #[{module := module.toName}] {}
  let mut original : Std.HashSet String := {}
  let source ← IO.FS.Handle.mk inventory .read
  repeat
    let line ← source.getLine
    if line.isEmpty then break
    let [_, _, n] := line.trimAsciiEnd.toString.splitOn "\t" | throw <| IO.userError "bad catalog row"
    original := original.insert n
  let mut provided : NameHashSet := {}
  for (n, _) in env.constants do
    if original.contains (n.toString false) then provided := provided.insert n
  let root := target.toName
  if provided.contains root then throw <| IO.userError "the new root already occurs in the original"
  M.run env do
    initState env
    modify fun s => { s with visitedConstants := provided }
    dumpMetadata
    dumpConstant root
