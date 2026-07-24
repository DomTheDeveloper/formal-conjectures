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

import Std.Tactic.BVDecide.LRAT

/-!
# Kernel-reducible LRAT checking for Lean 4.27 list CNFs

Lean core proves the LRAT checker sound, but several implementation details of
the default conversion path do not reduce in the kernel. This file replaces
only those implementation details with structurally recursive equivalents and
then transfers soundness from `lratCheckerSound`.

This is adapted to Lean 4.27, where `Std.Sat.CNF` is a list of clauses. It does
not use `native_decide`, `Lean.ofReduceBool`, or `Lean.trustCompiler`.
-/

open Std.Sat Std.Tactic.BVDecide.LRAT
open Std.Tactic.BVDecide.LRAT.Internal

namespace Green14.LRATKernel

private theorem nodupkey_of_no_compl {n : Nat} {ls : List (Literal (PosFin n))}
    (h : ∀ l ∈ ls, (l.1, !l.2) ∉ ls) :
    ∀ l : PosFin n, (l, true) ∉ ls ∨ (l, false) ∉ ls := by
  intro l
  by_cases h1 : (l, true) ∈ ls
  · exact Or.inr (h (l, true) h1)
  · exact Or.inl h1

/-- Kernel-reducible clause construction: remove duplicate literals, then
reject complementary literal pairs. -/
def mkClauseK {n : Nat} (ls : List (Literal (PosFin n))) :
    Option (DefaultClause n) :=
  if h : ls.eraseDups.Nodup ∧
      ∀ l ∈ ls.eraseDups, (l.1, !l.2) ∉ ls.eraseDups then
    some ⟨ls.eraseDups, nodupkey_of_no_compl h.2, h.1⟩
  else
    none

theorem mkClauseK_clause {n : Nat} {ls : List (Literal (PosFin n))}
    {c : DefaultClause n} (h : mkClauseK ls = some c) :
    c.clause = ls.eraseDups := by
  simp only [mkClauseK] at h
  split at h
  · cases h
    rfl
  · simp at h

/-- Kernel-reducible conversion from parsed integer LRAT actions. -/
def intActionToDCAK (n : Nat) : IntAction → Option (DefaultClauseAction n)
  | .addEmpty cId rupHints => some <| .addEmpty cId rupHints
  | .addRup cId c rupHints => do
      let c ← c.toList.mapM intToLiteral
      let c ← mkClauseK c
      return .addRup cId c rupHints
  | .addRat cId c pivot rupHints ratHints => do
      let pivot ← natLiteralToPosFinLiteral pivot
      let c ← c.toList.mapM intToLiteral
      let c ← mkClauseK c
      return .addRat cId c pivot rupHints ratHints
  | .del ids => return .del ids

/-- Relabel a zero-based CNF variable into a positive bounded LRAT variable. -/
def liftFun (cnf : CNF Nat) (v : Nat) : PosFin (cnf.numLiterals + 2) :=
  if h : v < cnf.numLiterals then ⟨v + 1, by omega⟩
  else ⟨cnf.numLiterals + 1, by omega⟩

/-- Kernel-reducible replacement for the classically branching `relabelFin`
conversion used by the standard checker. -/
def liftK (cnf : CNF Nat) : CNF (PosFin (cnf.numLiterals + 2)) :=
  CNF.relabel (liftFun cnf) cnf

 theorem unsat_of_liftK_unsat (cnf : CNF Nat) :
    (liftK cnf).Unsat → cnf.Unsat := by
  intro h
  apply (CNF.unsat_relabel_iff ?_).mp h
  intro v1 v2 hv1 hv2 heq
  have h1 := CNF.lt_numLiterals hv1
  have h2 := CNF.lt_numLiterals hv2
  simp only [liftK, liftFun, h1, h2, reduceDIte] at heq
  have heq' : v1 + 1 = v2 + 1 := congrArg Subtype.val heq
  omega

/-- Convert each source clause without HashMap-based clause construction. -/
def convertClausesK {n : Nat} (cls : CNF (PosFin n)) :
    List (Option (DefaultClause n)) :=
  cls.filterMap fun cl => (mkClauseK cl).map some

/-- Kernel-reducible initial LRAT formula. The leading `none` aligns formula
indices with one-based LRAT clause identifiers. -/
def convertK (cnf : CNF Nat) : DefaultFormula (cnf.numLiterals + 2) :=
  DefaultFormula.ofArray (none :: convertClausesK (liftK cnf)).toArray

theorem readyForRupAdd_convertK (cnf : CNF Nat) :
    DefaultFormula.ReadyForRupAdd (convertK cnf) :=
  DefaultFormula.readyForRupAdd_ofArray _

theorem readyForRatAdd_convertK (cnf : CNF Nat) :
    DefaultFormula.ReadyForRatAdd (convertK cnf) :=
  DefaultFormula.readyForRatAdd_ofArray _

/-- Semantic soundness of the kernel-reducible initial formula conversion. -/
theorem unsat_of_convertK_unsat (cnf : CNF Nat) :
    Unsatisfiable (PosFin (cnf.numLiterals + 2)) (convertK cnf) → cnf.Unsat := by
  intro h1
  apply unsat_of_liftK_unsat
  intro assignment
  replace h1 := (unsat_of_cons_none_unsat _ h1) assignment
  apply eq_false_of_ne_true
  intro h2
  apply h1
  simp only [Formula.formulaEntails_def, List.all_eq_true, decide_eq_true_eq]
  intro lratClause hlclause
  simp only [Formula.toList, DefaultFormula.toList, DefaultFormula.ofArray,
    List.toList_toArray, List.map_nil, List.append_nil, convertClausesK,
    List.filterMap_filterMap, List.mem_filterMap] at hlclause
  rcases hlclause with ⟨reflectClause, hrclause1, hrclause2⟩
  have hmk : mkClauseK reflectClause = some lratClause := by
    cases hcase : mkClauseK reflectClause <;> simp_all
  simp only [CNF.eval, List.all_eq_true] at h2
  have heval := h2 reflectClause (by simpa using hrclause1)
  simp only [CNF.Clause.eval, List.any_eq_true] at heval
  rcases heval with ⟨lit, hlit1, hlit2⟩
  simp only [(· ⊨ ·), Clause.eval, List.any_eq_true, decide_eq_true_eq]
  refine ⟨lit, ?_, by simpa using hlit2⟩
  simp only [Clause.toList, DefaultClause.toList, mkClauseK_clause hmk]
  exact List.mem_eraseDups.mpr hlit1

/-- List-based clone of the formula indices containing the negated RAT pivot. -/
def getRatClauseIndicesK {n : Nat}
    (clauses : Array (Option (DefaultClause n)))
    (l : Literal (PosFin n)) : List Nat :=
  (List.range clauses.size).filter fun i =>
    match clauses[i]! with
    | none => false
    | some c => c.contains (Literal.negate l)

theorem getRatClauseIndicesK_eq {n : Nat}
    (clauses : Array (Option (DefaultClause n)))
    (l : Literal (PosFin n)) :
    getRatClauseIndicesK clauses l =
      (DefaultFormula.getRatClauseIndices clauses l).toList := by
  simp only [getRatClauseIndicesK, DefaultFormula.getRatClauseIndices,
    Array.toList_filter, Array.toList_range]
  rfl

/-- Kernel-reducible RAT-hint exhaustiveness check. -/
def ratHintsExhaustiveK {n : Nat} (f : DefaultFormula n)
    (pivot : Literal (PosFin n))
    (ratHints : Array (Nat × Array Nat)) : Bool :=
  getRatClauseIndicesK f.clauses pivot =
    ratHints.toList.map (fun x => x.1)

theorem ratHintsExhaustiveK_eq {n : Nat} (f : DefaultFormula n)
    (pivot : Literal (PosFin n))
    (ratHints : Array (Nat × Array Nat)) :
    ratHintsExhaustiveK f pivot ratHints =
      DefaultFormula.ratHintsExhaustive f pivot ratHints := by
  unfold ratHintsExhaustiveK DefaultFormula.ratHintsExhaustive
  apply decide_eq_decide.mpr
  rw [getRatClauseIndicesK_eq, ← Array.toList_map, Array.toList_inj]

/-- Clone of the standard RAT update using the reducible exhaustive-hint check. -/
def performRatAddK {n : Nat} (f : DefaultFormula n) (c : DefaultClause n)
    (pivot : Literal (PosFin n)) (rupHints : Array Nat)
    (ratHints : Array (Nat × Array Nat)) : DefaultFormula n × Bool :=
  if ratHintsExhaustiveK f pivot ratHints then
    let negC := DefaultClause.negate c
    let (f, contradictionFound) := DefaultFormula.insertRupUnits f negC
    if contradictionFound then (f, false)
    else
      let (f, derivedLits, derivedEmpty, encounteredError) :=
        DefaultFormula.performRupCheck f rupHints
      if encounteredError then (f, false)
      else if derivedEmpty then (f, false)
      else
        let foldFn := fun (acc : DefaultFormula n × Bool) ratHint =>
          if acc.2 then
            DefaultFormula.performRatCheck acc.1 (Literal.negate pivot) ratHint
          else
            (acc.1, false)
        let (f, allChecksPassed) := ratHints.foldl foldFn (f, true)
        if !allChecksPassed then (f, false)
        else
          match f with
          | ⟨clauses, rupUnits, ratUnits, assignments⟩ =>
              let assignments :=
                DefaultFormula.restoreAssignments assignments derivedLits
              let f := DefaultFormula.clearRupUnits
                ⟨clauses, rupUnits, ratUnits, assignments⟩
              (f.insert c, true)
  else
    (f, false)

theorem performRatAddK_eq {n : Nat} (f : DefaultFormula n)
    (c : DefaultClause n) (pivot : Literal (PosFin n))
    (rupHints : Array Nat) (ratHints : Array (Nat × Array Nat)) :
    performRatAddK f c pivot rupHints ratHints =
      DefaultFormula.performRatAdd f c pivot rupHints ratHints := by
  unfold performRatAddK DefaultFormula.performRatAdd
  rw [ratHintsExhaustiveK_eq]

/-- Structurally recursive LRAT checker using the kernel-reducible RAT path. -/
def lratCheckerK {n : Nat} (f : DefaultFormula n)
    (proof : List (DefaultClauseAction n)) : Result :=
  match proof with
  | [] => .outOfProof
  | .addEmpty _ rupHints :: _ =>
      let (_, success) :=
        DefaultFormula.performRupAdd f DefaultClause.empty rupHints
      if success then .success else .rupFailure
  | .addRup _ c rupHints :: rest =>
      let (f, success) := DefaultFormula.performRupAdd f c rupHints
      if success then lratCheckerK f rest else .rupFailure
  | .addRat _ c pivot rupHints ratHints :: rest =>
      let (f, success) := performRatAddK f c pivot rupHints ratHints
      if success then lratCheckerK f rest else .rupFailure
  | .del ids :: rest => lratCheckerK (DefaultFormula.delete f ids) rest

theorem lratCheckerK_eq {n : Nat} (f : DefaultFormula n)
    (proof : List (DefaultClauseAction n)) :
    lratCheckerK f proof = lratChecker f proof := by
  induction proof generalizing f with
  | nil => rfl
  | cons action rest ih =>
      cases action with
      | addEmpty id rupHints => rfl
      | addRup id c rupHints => simp only [lratCheckerK, lratChecker, ih]
      | addRat id c pivot rupHints ratHints =>
          simp only [lratCheckerK, lratChecker, performRatAddK_eq, ih]
      | del ids =>
          simp only [lratCheckerK, lratChecker, ih]
          rfl

/-- Kernel-mode LRAT check for Lean 4.27 list CNFs. -/
def checkKernel (cnf : CNF Nat) (proof : List IntAction) : Bool :=
  let actions := proof.filterMap (intActionToDCAK (cnf.numLiterals + 2))
  let actions := actions.filter fun action =>
    match action with
    | .addRat _ c pivot _ _ => c.contains pivot
    | _ => true
  lratCheckerK (convertK cnf) actions = .success

/-- Soundness of the kernel-mode checker follows from Lean core's verified
`lratCheckerSound` theorem. -/
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
  | addRup id c rupHints => trivial
  | del ids => trivial
  | addRat id c pivot rupHints ratHints =>
      simp only [WellFormedAction]
      rw [Clause.limplies_iff_mem]
      exact (DefaultClause.contains_iff c pivot).mp (by simpa using hfilter)

end Green14.LRATKernel
