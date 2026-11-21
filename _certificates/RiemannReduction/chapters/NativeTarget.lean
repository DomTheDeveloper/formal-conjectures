import Lean

open Lean

def main (args : List String) : IO Unit := do
  let [path] := args | throw <| IO.userError "expected the native proof object"
  let (data, _) ← readModuleData path
  let candidate := data.constants.find? (·.name == `RH17.riemannHypothesisFromPublishedArithmetic)
  let some (.thmInfo t) := candidate | throw <| IO.userError "missing ordinary RH theorem"
  unless t.levelParams.isEmpty && t.type == mkConst `RiemannHypothesis do
    throw <| IO.userError "expected the unchanged Mathlib proposition with no hypotheses"
  IO.println "The checked native declaration has type RiemannHypothesis with no hypotheses."
