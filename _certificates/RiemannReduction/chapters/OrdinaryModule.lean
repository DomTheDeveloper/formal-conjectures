import Lean

open Lean

deriving instance BEq for Lean.QuotKind
deriving instance BEq for Lean.QuotVal
deriving instance BEq for Lean.InductiveVal
deriving instance BEq for Lean.ConstantInfo

private def checkedData (path : System.FilePath) : IO ModuleData := do
  let (d, _) ← readModuleData path
  unless d.constNames == d.constants.map (·.name) && d.entries.isEmpty && d.extraConstNames.isEmpty do
    throw <| IO.userError s!"unexpected proof module format in {path}"
  return d

def main (args : List String) : IO Unit := do
  let [input, output, mod, prev, changes, supplement] := args
    | throw <| IO.userError "expected input, output, module name, predecessor, delta and supplement directory"
  let mut drop : NameSet := {}
  let mut add : NameSet := {}
  for line in (← IO.FS.readFile changes).splitOn "\n" do
    if line.isEmpty then continue
    match line.splitOn "\t" with
    | ["drop", n] => drop := drop.insert n.toName
    | ["add", n] => add := add.insert n.toName
    | _ => throw <| IO.userError s!"invalid declaration delta line {line}"
  let d ← checkedData input
  let imports : Array Import := if prev == "-" then #[] else #[{module := prev.toName}]
  unless d.imports == imports do throw <| IO.userError s!"unexpected imports in {mod}"
  let removed := d.constants.filter (fun c => drop.contains c.name)
  for c in removed do IO.println s!"removed\t{c.name}"
  if removed.isEmpty && supplement == "-" then
    IO.println s!"unchanged\t{d.constants.size}"
    return
  let mut final := d.constants.filter (fun c => !drop.contains c.name)
  if supplement != "-" then
    let dir : System.FilePath := supplement
    let arithmetic ← checkedData (dir / "Arithmetic.olean")
    unless arithmetic.constants.size == 4 && arithmetic.constants.all (fun c => add.contains c.name) do
      throw <| IO.userError "arithmetic supplement differs from the four required original declarations"
    let chapters ← checkedData (dir / "Proof.olean")
    unless chapters.constants.size == 38 && chapters.constants.all (fun c => !c.isAxiom && !c.isUnsafe) do
      throw <| IO.userError "expected the 38 safe chapter declarations"
    final := final ++ arithmetic.constants ++ chapters.constants
    let newRoot := `RH17.riemannHypothesisFromPublishedArithmetic
    unless final.any (fun c => c.name == newRoot && c.type == mkConst `RiemannHypothesis) do
      throw <| IO.userError "missing the chapter proof of Mathlib's exact proposition"
    let publicRoot := `riemannHypothesis
    let alias : TheoremVal := {name := publicRoot, levelParams := [], type := mkConst `RiemannHypothesis,
                               value := mkConst newRoot, all := [publicRoot]}
    final := final.push (.thmInfo alias)
  let names := final.map (·.name)
  let unique := names.foldl (init := ({} : Std.HashSet Name)) (fun seen n => seen.insert n)
  unless unique.size == names.size do throw <| IO.userError s!"duplicate name in {mod}"
  let data := {d with constNames := names, constants := final}
  saveModuleData output mod.toName data
  let saved ← checkedData output
  unless saved.constNames == names && saved.constants == final && saved.imports == imports do
    throw <| IO.userError s!"proof objects changed during serialization in {mod}"
  IO.println s!"rebuilt\t{final.size}"
