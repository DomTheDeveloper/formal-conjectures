import Mathlib
import Lean
import Lean.Replay

open Lean Elab Command

private def sameBinders : Expr → Expr → Bool
  | .forallE n _ b i, .forallE n' _ b' i' => n == n' && i == i' && sameBinders b b'
  | .forallE .., _ | _, .forallE .. => false
  | _, _ => true

private def kind : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "definition"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

/-- Replay the fresh module under disjoint names so its private helpers retain their new meanings. -/
private def renamed (locals : NameSet) (c : ConstantInfo) : Except String ConstantInfo := do
  let name := fun (n : Name) => if locals.contains n then `RHRefactoringAudit ++ n else n
  let expr := fun (e : Expr) => e.replace fun
    | .const n us => if locals.contains n then some (.const (name n) us) else none
    | .proj n i t => if locals.contains n then some (.proj (name n) i t) else none
    | _ => none
  match c with
  | .defnInfo d =>
    return .defnInfo { d with
      name := name d.name
      type := expr d.type
      value := expr d.value
      all := d.all.map name }
  | .thmInfo d =>
    return .thmInfo { d with
      name := name d.name
      type := expr d.type
      value := expr d.value
      all := d.all.map name }
  | .opaqueInfo d =>
    return .opaqueInfo { d with
      name := name d.name
      type := expr d.type
      value := expr d.value
      all := d.all.map name }
  | _ => throw s!"unsupported declaration in the refactored module: {c.name}"

private def checkPair (env : Environment) (a b : ConstantInfo) : List String := Id.run do
  let eq := fun (x y : Expr) => x == y || (Kernel.isDefEq env {} x y).toOption == some true
  let mut errors := []
  if kind a != kind b then errors := "declaration kind" :: errors
  if a.levelParams != b.levelParams then errors := "universe parameters" :: errors
  if !eq a.type b.type then errors := "statement" :: errors
  if !sameBinders a.type b.type then errors := "explicit or named parameters" :: errors
  if a.isUnsafe != b.isUnsafe then errors := "safety" :: errors
  if let .defnInfo da := a then
    if let .defnInfo db := b then
      if !eq da.value db.value then errors := "definition body" :: errors
      if da.hints != db.hints then errors := "reducibility" :: errors
      if da.safety != db.safety then errors := "definition safety" :: errors
  return errors

elab "#compare_modules" : command => do
  let tests ← IO.FS.lines (← IO.getEnv "RH_COMPARE_FILES").get!
  let out ← IO.FS.Handle.mk (← IO.getEnv "RH_COMPARE_OUTPUT").get! .write
  let env ← getEnv
  for line in tests do
    let [mod, a, b] := line.splitOn "\t" | throwError "expected three tab-separated fields"
    let (original, _) ← readModuleData a
    let (reduced, _) ← readModuleData b
    let locals : NameSet := reduced.constNames.foldl (fun acc n => acc.insert n) {}
    let mut byName : Std.HashMap Name ConstantInfo := {}
    let mut replay : Std.HashMap Name ConstantInfo := {}
    for c in reduced.constants do
      if c.isUnsafe || c.isPartial || c.type.hasSorry then throwError "unsupported declaration {c.name}"
      if let some value := c.value? then
        if value.hasSorry then throwError "placeholder in {c.name}"
      let .ok fresh := renamed locals c | throwError "unsupported declaration {c.name}"
      byName := byName.insert c.name fresh
      replay := replay.insert fresh.name fresh
    let mut originalNames : Std.HashMap Name ConstantInfo := {}
    for c in original.constants do originalNames := originalNames.insert c.name c
    let base ← env.replay originalNames
    let checkedEnv ← base.replay replay
    let mut failures : Array (String × List String) := #[]
    let mut checked := 0
    let mut checkedDefs := 0
    for old in original.constants do
      -- Private helpers can change when Lean elaborates new notation. Check every public constant.
      if isPrivateName old.name || old.name.isInternal then continue
      match byName[old.name]? with
      | none => failures := failures.push (toString old.name, ["missing declaration"])
      | some fresh =>
        checked := checked + 1
        if old.isDefinition then checkedDefs := checkedDefs + 1
        let issues := checkPair checkedEnv old fresh
        if !issues.isEmpty then failures := failures.push (toString old.name, issues)
    out.putStrLn <| (Json.mkObj [("module", toJson mod), ("publicDeclarations", toJson checked),
      ("definitions", toJson checkedDefs), ("failures", toJson failures)]).compress
    out.flush
    if !failures.isEmpty then logError m!"{mod}: {failures.size} interface differences"

#compare_modules
