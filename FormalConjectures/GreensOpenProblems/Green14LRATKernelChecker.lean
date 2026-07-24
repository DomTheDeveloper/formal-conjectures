/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import FormalConjectures.GreensOpenProblems.Green14LRATKernelConversion

/-!
# Kernel-reducible LRAT checking loop for Lean 4.27

This module supplies a list-based RAT hint enumeration and a structurally
recursive checker, then transfers soundness from Lean core's verified
`lratCheckerSound` theorem.
-/

open Std.Sat Std.Tactic.BVDecide.LRAT
open Std.Tactic.BVDecide.LRAT.Internal

namespace Green14.LRATKernelV2

/-- List-based enumeration of clauses containing the negated RAT pivot. -/
def getRatClauseIndicesK {n : Nat}
    (clauses : Array (Option (DefaultClause n)))
    (pivot : Literal (PosFin n)) : List Nat :=
  (List.range clauses.size).filter fun index =>
    match clauses[index]! with
    | none => false
    | some clause => clause.contains (Literal.negate pivot)

theorem getRatClauseIndicesK_eq {n : Nat}
    (clauses : Array (Option (DefaultClause n)))
    (pivot : Literal (PosFin n)) :
    getRatClauseIndicesK clauses pivot =
      (DefaultFormula.getRatClauseIndices clauses pivot).toList := by
  simp only [getRatClauseIndicesK, DefaultFormula.getRatClauseIndices,
    Array.toList_filter, Array.toList_range]
  rfl

/-- Reducible check that RAT hints mention exactly the required clauses. -/
def ratHintsExhaustiveK {n : Nat} (formula : DefaultFormula n)
    (pivot : Literal (PosFin n))
    (ratHints : Array (Nat × Array Nat)) : Bool :=
  getRatClauseIndicesK formula.clauses pivot =
    ratHints.toList.map (fun hint => hint.1)

theorem ratHintsExhaustiveK_eq {n : Nat} (formula : DefaultFormula n)
    (pivot : Literal (PosFin n))
    (ratHints : Array (Nat × Array Nat)) :
    ratHintsExhaustiveK formula pivot ratHints =
      DefaultFormula.ratHintsExhaustive formula pivot ratHints := by
  unfold ratHintsExhaustiveK DefaultFormula.ratHintsExhaustive
  apply decide_eq_decide.mpr
  rw [getRatClauseIndicesK_eq, ← Array.toList_map, Array.toList_inj]

/-- Clone of the verified RAT update using the reducible exhaustive-hint test. -/
def performRatAddK {n : Nat} (formula : DefaultFormula n)
    (clause : DefaultClause n) (pivot : Literal (PosFin n))
    (rupHints : Array Nat) (ratHints : Array (Nat × Array Nat)) :
    DefaultFormula n × Bool :=
  if ratHintsExhaustiveK formula pivot ratHints then
    let negated := DefaultClause.negate clause
    let (formula, contradictionFound) :=
      DefaultFormula.insertRupUnits formula negated
    if contradictionFound then (formula, false)
    else
      let (formula, derivedLits, derivedEmpty, encounteredError) :=
        DefaultFormula.performRupCheck formula rupHints
      if encounteredError then (formula, false)
      else if derivedEmpty then (formula, false)
      else
        let foldFn := fun (acc : DefaultFormula n × Bool) ratHint =>
          if acc.2 then
            DefaultFormula.performRatCheck acc.1 (Literal.negate pivot) ratHint
          else
            (acc.1, false)
        let (formula, allChecksPassed) := ratHints.foldl foldFn (formula, true)
        if !allChecksPassed then (formula, false)
        else
          match formula with
          | ⟨clauses, rupUnits, ratUnits, assignments⟩ =>
              let assignments :=
                DefaultFormula.restoreAssignments assignments derivedLits
              let formula := DefaultFormula.clearRupUnits
                ⟨clauses, rupUnits, ratUnits, assignments⟩
              (formula.insert clause, true)
  else
    (formula, false)

theorem performRatAddK_eq {n : Nat} (formula : DefaultFormula n)
    (clause : DefaultClause n) (pivot : Literal (PosFin n))
    (rupHints : Array Nat) (ratHints : Array (Nat × Array Nat)) :
    performRatAddK formula clause pivot rupHints ratHints =
      DefaultFormula.performRatAdd formula clause pivot rupHints ratHints := by
  unfold performRatAddK DefaultFormula.performRatAdd
  rw [ratHintsExhaustiveK_eq]

/-- Structurally recursive checker using the reducible RAT path. -/
def lratCheckerK {n : Nat} (formula : DefaultFormula n)
    (proof : List (DefaultClauseAction n)) : Result :=
  match proof with
  | [] => .outOfProof
  | .addEmpty _ rupHints :: _ =>
      let (_, success) :=
        DefaultFormula.performRupAdd formula DefaultClause.empty rupHints
      if success then .success else .rupFailure
  | .addRup _ clause rupHints :: rest =>
      let (formula, success) :=
        DefaultFormula.performRupAdd formula clause rupHints
      if success then lratCheckerK formula rest else .rupFailure
  | .addRat _ clause pivot rupHints ratHints :: rest =>
      let (formula, success) :=
        performRatAddK formula clause pivot rupHints ratHints
      if success then lratCheckerK formula rest else .rupFailure
  | .del ids :: rest =>
      lratCheckerK (DefaultFormula.delete formula ids) rest

theorem lratCheckerK_eq {n : Nat} (formula : DefaultFormula n)
    (proof : List (DefaultClauseAction n)) :
    lratCheckerK formula proof = lratChecker formula proof := by
  induction proof generalizing formula with
  | nil => rfl
  | cons action rest ih =>
      cases action with
      | addEmpty id rupHints => rfl
      | addRup id clause rupHints =>
          simp only [lratCheckerK, lratChecker, ih]
      | addRat id clause pivot rupHints ratHints =>
          simp only [lratCheckerK, lratChecker, performRatAddK_eq, ih]
      | del ids =>
          simp only [lratCheckerK, lratChecker, ih]
          rfl

/-- Kernel-mode check for a parsed LRAT proof. -/
def checkKernel (cnf : CNF Nat) (proof : List IntAction) : Bool :=
  let actions := proof.filterMap (intActionToDCAK (cnf.numLiterals + 2))
  let actions := actions.filter fun action =>
    match action with
    | .addRat _ clause pivot _ _ => clause.contains pivot
    | _ => true
  lratCheckerK (convertK cnf) actions = .success

/-- Soundness of `checkKernel` follows only from Lean core's verified checker. -/
theorem checkKernel_sound (cnf : CNF Nat) (proof : List IntAction)
    (h : checkKernel cnf proof = true) : cnf.Unsat := by
  apply unsat_of_convertK_unsat
  simp only [checkKernel, lratCheckerK_eq, decide_eq_true_eq] at h
  apply lratCheckerSound _ (readyForRupAdd_convertK cnf)
    (readyForRatAdd_convertK cnf) _ ?_ h
  intro action ha
  have hfilter := (List.mem_filter.mp ha).2
  cases action with
  | addEmpty id rupHints => trivial
  | addRup id clause rupHints => trivial
  | del ids => trivial
  | addRat id clause pivot rupHints ratHints =>
      simp only [WellFormedAction]
      rw [Clause.limplies_iff_mem]
      exact (DefaultClause.contains_iff clause pivot).mp (by simpa using hfilter)

end Green14.LRATKernelV2
