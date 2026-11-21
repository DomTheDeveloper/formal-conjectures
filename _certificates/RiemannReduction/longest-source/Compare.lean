import Lean

open Lean

namespace LongestProofAudit

deriving instance BEq for InductiveVal
deriving instance BEq for RecursorVal
deriving instance BEq for QuotKind
deriving instance BEq for QuotVal
deriving instance BEq for ConstantInfo

private def sameBinders : Expr → Expr → Bool
  | .forallE n _ b bi, .forallE n' _ b' bi' => n == n' && bi == bi' && sameBinders b b'
  | .forallE .., _ | _, .forallE .. => false
  | _, _ => true

def compare (oldFile newFile : String) : IO Unit := do
  let (old, _) ← readModuleData oldFile
  let (new, _) ← readModuleData newFile
  unless old.imports == new.imports do throw <| IO.userError "The import headers differ"
  let mut byName : Std.HashMap Name ConstantInfo := {}
  for c in new.constants do byName := byName.insert c.name c
  let mut identical := 0
  let mut proofsChanged := 0
  let mut mismatches := #[]
  let mut publicCount := 0
  for a in old.constants do
    unless isPrivateName a.name || a.name.isInternal do publicCount := publicCount + 1
    let some b := byName[a.name]? | mismatches := mismatches.push (toString a.name ++ " (missing)"); continue
    byName := byName.erase a.name
    if a == b && sameBinders a.type b.type then
      identical := identical + 1
    else if let .thmInfo x := a then
      if let .thmInfo y := b then
        if x.toConstantVal == y.toConstantVal && x.all == y.all && sameBinders x.type y.type && !y.value.hasSorry then
          proofsChanged := proofsChanged + 1
          continue
      mismatches := mismatches.push (toString a.name ++ " (theorem signature)")
    else
      mismatches := mismatches.push (toString a.name ++ " (definition or datatype)")
  for (name, _) in byName do mismatches := mismatches.push (toString name ++ " (new)")
  let r := Json.mkObj [("originalConstants", toJson old.constants.size), ("revisedConstants", toJson new.constants.size),
    ("publicConstants", toJson publicCount), ("identicalKernelRecords", toJson identical),
    ("sameTypeFreshlyCheckedTheoremBodies", toJson proofsChanged), ("differences", toJson mismatches)]
  IO.println r.compress
  unless mismatches.isEmpty do throw <| IO.userError s!"{mismatches.size} kernel entries differ"

end LongestProofAudit

def main (args : List String) : IO Unit := do
  let [oldFile, newFile] := args | throw <| IO.userError "Expected two native Lean objects"
  LongestProofAudit.compare oldFile newFile
