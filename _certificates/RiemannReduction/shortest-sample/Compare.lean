import Lean

open Lean

namespace RHShortSourceCheck

deriving instance BEq for InductiveVal
deriving instance BEq for RecursorVal
deriving instance BEq for QuotKind
deriving instance BEq for QuotVal
deriving instance BEq for ConstantInfo

private def binders : Expr → Expr → Bool
  | .forallE n _ b i, .forallE n' _ b' i' => n == n' && i == i' && binders b b'
  | .forallE .., _ | _, .forallE .. => false
  | _, _ => true

private def publicConstant (c : ConstantInfo) := !isPrivateName c.name && !c.name.isInternal

private def compare (name oldPath newPath : String) : IO Json := do
  let (old, _) ← readModuleData oldPath
  let (new, _) ← readModuleData newPath
  let mut table : Std.HashMap Name ConstantInfo := {}
  for c in new.constants do
    if c.type.hasSorry || (c.value?.any Expr.hasSorry) then throw <| IO.userError s!"placeholder in {c.name}"
    if publicConstant c then table := table.insert c.name c
  let mut exactCount := 0
  let mut newProofs := 0
  let mut issues := #[]
  for a in old.constants do
    unless publicConstant a do continue
    let some b := table[a.name]? | issues := issues.push s!"missing {a.name}"; continue
    table := table.erase a.name
    if a == b && binders a.type b.type then exactCount := exactCount + 1; continue
    if let .thmInfo x := a then
      if let .thmInfo y := b then
        if x.toConstantVal == y.toConstantVal && x.all == y.all && binders x.type y.type then
          newProofs := newProofs + 1
          continue
    issues := issues.push s!"difference in public declaration {a.name}"
  for (n, _) in table do issues := issues.push s!"new public declaration {n}"
  return Json.mkObj [("module",toJson name),("identicalPublicRecords",toJson exactCount),
                     ("newProofsWithOriginalType",toJson newProofs),("differences",toJson issues)]

def go (specPath output : String) : IO Unit := do
  let pairs ← IO.FS.lines specPath
  let file ← IO.FS.Handle.mk output .write
  let mut differences := 0
  for line in pairs do
    let [mod, old, new] := line.splitOn "\t" | throw <| IO.userError "bad input"
    let row ← compare mod old new
    let .ok issues := row.getObjValAs? (Array String) "differences" | throw <| IO.userError "missing differences"
    differences := differences + issues.size
    file.putStrLn row.compress
  file.flush
  if differences != 0 then throw <| IO.userError s!"{differences} differences in the compared files"

end RHShortSourceCheck

def main (args : List String) : IO Unit := do
  let [spec, out] := args | throw <| IO.userError "Expected two input paths"
  RHShortSourceCheck.go spec out
