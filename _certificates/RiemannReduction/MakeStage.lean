import Lean.Environment
import ParseExport33

open Lean

deriving instance BEq for Lean.QuotKind
deriving instance BEq for Lean.QuotVal
deriving instance BEq for Lean.InductiveVal
deriving instance BEq for Lean.ConstantInfo

def main (args : List String) : IO UInt32 := do
  let [source, prior, module, outFile] := args | throw <| IO.userError "expected input, previous module, current module and output"
  let records ← IO.FS.withFile source .read fun handle => Export.parseStream (.ofHandle handle)
  let mut declarations := #[]
  for n in records.constOrder do
    let some c := records.constMap[n]? | throw <| IO.userError s!"missing {n}"
    if c.isUnsafe || c.isPartial then throw <| IO.userError s!"unsupported declaration {n}"
    if c.isAxiom && !([`propext, `Classical.choice, `Quot.sound].contains n) then
      throw <| IO.userError s!"unexpected axiom {n}"
    declarations := declarations.push c
  if declarations.size != records.constMap.size then throw <| IO.userError "constant count mismatch"
  let imports : Array Import := if prior == "-" then #[] else #[{module := prior.toName}]
  let data : ModuleData := {isModule := false, imports, constNames := records.constOrder,
                            constants := declarations, extraConstNames := #[], entries := #[]}
  saveModuleData outFile module.toName data
  let (saved, _) ← readModuleData outFile
  if saved.constNames != data.constNames || saved.constants != data.constants || saved.imports != imports then
    throw <| IO.userError "on-disk module differs from parsed declarations"
  IO.println s!"{module}: serialized {declarations.size} constants"
  return 0
