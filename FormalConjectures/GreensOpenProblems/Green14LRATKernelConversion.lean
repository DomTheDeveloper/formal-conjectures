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
# Kernel-reducible LRAT conversion for Lean 4.27

Lean 4.27 uses list-based SAT clauses.  This module replaces the parts of the
standard LRAT conversion that do not reduce conveniently in the kernel while
proving that the converted formula remains semantically sound.
-/

open Std.Sat Std.Tactic.BVDecide.LRAT
open Std.Tactic.BVDecide.LRAT.Internal

namespace Green14.LRATKernelV2

private theorem nodupkey_of_no_compl {n : Nat} {ls : List (Literal (PosFin n))}
    (h : ∀ l ∈ ls, (l.1, !l.2) ∉ ls) :
    ∀ l : PosFin n, (l, true) ∉ ls ∨ (l, false) ∉ ls := by
  intro l
  by_cases hpos : (l, true) ∈ ls
  · exact Or.inr (h (l, true) hpos)
  · exact Or.inl hpos

/-- Construct a checker clause by list deduplication, rejecting tautologies. -/
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

/-- Convert parsed integer actions without HashMap-backed clause construction. -/
def intActionToDCAK (n : Nat) : IntAction → Option (DefaultClauseAction n)
  | .addEmpty cId rupHints => some (.addEmpty cId rupHints)
  | .addRup cId c rupHints => do
      let lits ← c.toList.mapM intToLiteral
      let clause ← mkClauseK lits
      return .addRup cId clause rupHints
  | .addRat cId c pivot rupHints ratHints => do
      let pivot ← natLiteralToPosFinLiteral pivot
      let lits ← c.toList.mapM intToLiteral
      let clause ← mkClauseK lits
      return .addRat cId clause pivot rupHints ratHints
  | .del ids => some (.del ids)

/-- Relabel a zero-based source variable into a positive bounded variable. -/
def liftFun (cnf : CNF Nat) (v : Nat) : PosFin (cnf.numLiterals + 2) :=
  if h : v < cnf.numLiterals then ⟨v + 1, by omega⟩
  else ⟨cnf.numLiterals + 1, by omega⟩

/-- Kernel-reducible replacement for the classically branching relabeling. -/
def liftK (cnf : CNF Nat) : CNF (PosFin (cnf.numLiterals + 2)) :=
  CNF.relabel (liftFun cnf) cnf

theorem unsat_of_liftK_unsat (cnf : CNF Nat) :
    (liftK cnf).Unsat → cnf.Unsat := by
  intro h
  apply (CNF.unsat_relabel_iff ?_).mp h
  intro v₁ v₂ hv₁ hv₂ heq
  have h₁ := CNF.lt_numLiterals hv₁
  have h₂ := CNF.lt_numLiterals hv₂
  simp only [liftK, liftFun, h₁, h₂, reduceDIte] at heq
  have : v₁ + 1 = v₂ + 1 := congrArg Subtype.val heq
  omega

/-- Convert source clauses while preserving their original order and indices. -/
def convertClausesK {n : Nat} (clauses : CNF (PosFin n)) :
    List (Option (DefaultClause n)) :=
  clauses.filterMap fun clause => (mkClauseK clause).map some

/-- Initial checker formula.  The leading `none` aligns one-based LRAT IDs. -/
def convertK (cnf : CNF Nat) : DefaultFormula (cnf.numLiterals + 2) :=
  DefaultFormula.ofArray (none :: convertClausesK (liftK cnf)).toArray

theorem readyForRupAdd_convertK (cnf : CNF Nat) :
    DefaultFormula.ReadyForRupAdd (convertK cnf) :=
  DefaultFormula.readyForRupAdd_ofArray _

theorem readyForRatAdd_convertK (cnf : CNF Nat) :
    DefaultFormula.ReadyForRatAdd (convertK cnf) :=
  DefaultFormula.readyForRatAdd_ofArray _

/-- Deduplication preserves every satisfying literal of a converted clause. -/
theorem clause_sat_of_mkClauseK
    {n : Nat} (source : CNF.Clause (PosFin n))
    {target : DefaultClause n} (hconvert : mkClauseK source = some target)
    {assignment : PosFin n → Bool} :
    source.eval assignment = true → assignment ⊨ target := by
  intro hsource
  simp only [CNF.Clause.eval, List.any_eq_true] at hsource
  rcases hsource with ⟨lit, hlitSource, hlitEval⟩
  simp only [(· ⊨ ·), Clause.eval, List.any_eq_true, decide_eq_true_eq]
  refine ⟨lit, ?_, by simpa using hlitEval⟩
  simp only [Clause.toList, DefaultClause.toList, mkClauseK_clause hconvert]
  exact List.mem_eraseDups.mpr hlitSource

/-- Semantic soundness of the kernel-reducible initial formula conversion. -/
theorem unsat_of_convertK_unsat (cnf : CNF Nat) :
    Unsatisfiable (PosFin (cnf.numLiterals + 2)) (convertK cnf) → cnf.Unsat := by
  intro hConverted
  apply unsat_of_liftK_unsat
  intro assignment
  replace hConverted := (unsat_of_cons_none_unsat _ hConverted) assignment
  apply eq_false_of_ne_true
  intro hLifted
  apply hConverted
  simp only [Formula.formulaEntails_def, List.all_eq_true, decide_eq_true_eq]
  intro targetClause hTargetMem
  change targetClause ∈ (convertClausesK (liftK cnf)).filterMap id at hTargetMem
  rcases List.mem_filterMap.mp hTargetMem with
    ⟨optionalClause, hOptionalMem, hOptionalEq⟩
  have hOptional : optionalClause = some targetClause := by
    simpa using hOptionalEq
  subst optionalClause
  rcases List.mem_filterMap.mp hOptionalMem with
    ⟨sourceClause, hSourceMem, hMapEq⟩
  have hConvert : mkClauseK sourceClause = some targetClause := by
    cases hmk : mkClauseK sourceClause with
    | none => simp [hmk] at hMapEq
    | some converted =>
        simp [hmk] at hMapEq
        subst converted
        exact hmk
  simp only [CNF.eval, List.all_eq_true] at hLifted
  exact clause_sat_of_mkClauseK sourceClause hConvert
    (hLifted sourceClause hSourceMem)

end Green14.LRATKernelV2
