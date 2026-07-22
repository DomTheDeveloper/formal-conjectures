/-
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0.
-/
import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.C217BitVecGraph
import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.C217BooleanGraph
import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.C217HamiltonDP
import Std.Tactic.BVDecide

/-!
# LRAT generation for the four regular C217 boundary rows

Run this file once with Lean. Each `bv_decide?` call writes a text LRAT proof
next to this source file and prints the corresponding `bv_check` replacement.
The generated proof files are then committed, and the final imported module
uses only `bv_check`; it does not retain the native `bv_decide` axiom.
-/

namespace SimpleGraph.C217RegularLRATGenerator

open SimpleGraph
open SimpleGraph.C217BitVecGraph
open SimpleGraph.C217BooleanGraph
open SimpleGraph.C217HamiltonDP

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- Boolean certificate statement for a connected `k`-regular graph on `n`
vertices. -/
def regularCertificate (n k : ℕ) : Prop :=
  ∀ bits : BitVec (n * n),
    connectedCutBool (graphOfBitVec bits) = true →
    degreeProfileBool (graphOfBitVec bits) (List.replicate n k) = true →
    hasHamiltonPathBool (graphOfBitVec bits) = true

/-- Connected cubic graphs on eight vertices are traceable. -/
theorem regular_8_3 : regularCertificate 8 3 := by
  bv_decide? (config := {
    timeout := 1800
    binaryProofs := false
    trimProofs := true
    solverMode := .proof })

/-- Connected four-regular graphs on ten vertices are traceable. -/
theorem regular_10_4 : regularCertificate 10 4 := by
  bv_decide? (config := {
    timeout := 3600
    binaryProofs := false
    trimProofs := true
    solverMode := .proof })

/-- Connected five-regular graphs on twelve vertices are traceable. -/
theorem regular_12_5 : regularCertificate 12 5 := by
  bv_decide? (config := {
    timeout := 7200
    binaryProofs := false
    trimProofs := true
    solverMode := .proof })

/-- Connected six-regular graphs on fourteen vertices are traceable. -/
theorem regular_14_6 : regularCertificate 14 6 := by
  bv_decide? (config := {
    timeout := 14400
    binaryProofs := false
    trimProofs := true
    solverMode := .proof })

end SimpleGraph.C217RegularLRATGenerator
