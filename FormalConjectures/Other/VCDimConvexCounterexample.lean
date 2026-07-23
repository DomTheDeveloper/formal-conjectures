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

import FormalConjectures.Other.VCDimConvex

/-!
# Explicit counterexample to the convex additive-VC₂ bound in `ℝ³`

This file formalizes a finite exact certificate disproving
`VCDimConvex.hasAddVCNDimAtMost_two_one_of_convex_r3`.

The convex set is an intersection of thirteen closed half-spaces. For each of
the sixteen subsets of `Fin 2 → Fin 2`, one explicit point `y s` translates
four fixed points `x i`; exact integer arithmetic proves that the resulting
membership pattern is precisely `s`.
-/

open Finset Set
open scoped BigOperators

namespace VCDimConvexCounterexample

abbrev R3 := Fin 3 → ℝ

private def x0 : R3 := ![0, 0, 0]
private def x1 : R3 := ![1, 0, 0]
private def x2 : R3 := ![0, 1, 0]
private def x3 : R3 := ![0, 0, 1]

/-- Four fixed points indexed by `Fin 2 → Fin 2`. -/
def x (i : Fin 2 → Fin 2) : R3 :=
  match i 0, i 1 with
  | 0, 0 => x0
  | 0, 1 => x1
  | 1, 0 => x2
  | 1, 1 => x3

private def mask (s : Finset (Fin 2 → Fin 2)) : Fin 16 :=
  ⟨(if (fun _ => (0 : Fin 2)) ∈ s then 1 else 0) +
      (if (fun i => if i = 0 then 0 else 1) ∈ s then 2 else 0) +
      (if (fun i => if i = 0 then 1 else 0) ∈ s then 4 else 0) +
      (if (fun _ => (1 : Fin 2)) ∈ s then 8 else 0), by
        split_ifs <;> omega⟩

private def yTable : Fin 16 → R3
  | ⟨0, _⟩ => ![0, 0, -7]
  | ⟨1, _⟩ => ![-10, -10, 2]
  | ⟨2, _⟩ => ![4, -2, 0]
  | ⟨3, _⟩ => ![4, -4, 4]
  | ⟨4, _⟩ => ![0, 5, 5]
  | ⟨5, _⟩ => ![-4, 5, 5]
  | ⟨6, _⟩ => ![4, 0, 1]
  | ⟨7, _⟩ => ![4, 3, 3]
  | ⟨8, _⟩ => ![1, 1, 1]
  | ⟨9, _⟩ => ![-4, 2, 0]
  | ⟨10, _⟩ => ![2, -2, 0]
  | ⟨11, _⟩ => ![2, 0, -1]
  | ⟨12, _⟩ => ![1, 2, 2]
  | ⟨13, _⟩ => ![0, 1, 1]
  | ⟨14, _⟩ => ![1, 0, 0]
  | ⟨15, _⟩ => ![0, 0, 0]

/-- Translation vector selecting a prescribed membership pattern. -/
def y (s : Finset (Fin 2 → Fin 2)) : R3 := yTable (mask s)

private def code (i : Fin 2 → Fin 2) : Fin 4 :=
  match i 0, i 1 with
  | 0, 0 => 0
  | 0, 1 => 1
  | 1, 0 => 2
  | 1, 1 => 3

private def Z : Fin 4 → R3
  | 0 => ![0, 0, 0]
  | 1 => ![1, 0, 0]
  | 2 => ![0, 1, 0]
  | 3 => ![0, 0, 1]

private def Y : Fin 16 → R3 := yTable

private def a : Fin 13 → R3
  | 0 => ![1, -9, 9]
  | 1 => ![1, -1, 1]
  | 2 => ![1, 0, 2]
  | 3 => ![1, 0, 3]
  | 4 => ![2, -1, 2]
  | 5 => ![3, -9, 9]
  | 6 => ![3, -7, 7]
  | 7 => ![4, -10, 10]
  | 8 => ![7, -1, 1]
  | 9 => ![7, 1, 4]
  | 10 => ![8, 0, 1]
  | 11 => ![9, -2, 3]
  | 12 => ![9, -1, 8]

private def b : Fin 13 → ℝ
  | 0 => 7
  | 1 => 2
  | 2 => 2
  | 3 => 2
  | 4 => 4
  | 5 => 1
  | 6 => 4
  | 7 => 5
  | 8 => 5
  | 9 => 4
  | 10 => 3
  | 11 => 4
  | 12 => 8

private def dot (u v : R3) : ℝ := ∑ k, u k * v k

private def halfspace (r : Fin 13) : Set R3 :=
  {p | dot (a r) p ≤ b r}

/-- The certified convex polyhedron. -/
def C : Set R3 := ⋂ r, halfspace r

private theorem halfspace_convex (r : Fin 13) : Convex ℝ (halfspace r) := by
  intro p hp q hq α β hα hβ hsum
  change dot (a r) (α • p + β • q) ≤ b r
  change (∑ k, a r k * (α * p k + β * q k)) ≤ b r
  rw [Finset.sum_congr rfl fun k _ => by ring,
    Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  dsimp [halfspace] at hp hq
  nlinarith

/-- Convexity of the certificate polyhedron. -/
theorem C_convex : Convex ℝ C := by
  unfold C
  exact convex_iInter fun r => halfspace_convex r

private theorem x_eq_Z (i : Fin 2 → Fin 2) : x i = Z (code i) := by
  funext k
  fin_cases i 0 <;> fin_cases i 1 <;> fin_cases k <;> rfl

private theorem target_mask (s : Finset (Fin 2 → Fin 2)) (i : Fin 2 → Fin 2) :
    mask s = code i ↔ i ∈ s := by
  fun_cases i <;> simp [mask, code]

private theorem mem_Y_add_Z_iff (m : Fin 16) (c : Fin 4) :
    Y m + Z c ∈ C ↔ m = c := by
  unfold C halfspace dot a b Y Z yTable
  fin_cases m <;> fin_cases c <;>
    simp only [Set.mem_iInter, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
      Matrix.tail_cons, Fin.sum_univ_four, Fin.sum_univ_three,
      Fin.sum_univ_two, Fin.sum_univ_one] <;>
    constructor
  all_goals
    · intro h
      first
      | rfl
      | have := h 0
        norm_num at this
      | have := h 1
        norm_num at this
      | have := h 2
        norm_num at this
      | have := h 3
        norm_num at this
      | have := h 4
        norm_num at this
      | have := h 5
        norm_num at this
      | have := h 6
        norm_num at this
      | have := h 7
        norm_num at this
      | have := h 8
        norm_num at this
      | have := h 9
        norm_num at this
      | have := h 10
        norm_num at this
      | have := h 11
        norm_num at this
      | have := h 12
        norm_num at this
    · intro h
      subst h
      intro r
      fin_cases r <;> norm_num

private theorem sum_x_eq_Z (i : Fin 2 → Fin 2) :
    ∑ j, x (i j) = Z (code i) := by
  simp only [Fin.sum_univ_two, x_eq_Z]
  funext k
  fin_cases i 0 <;> fin_cases i 1 <;> fin_cases k <;> norm_num [Z, code]

/-- Exact shattering certificate: each subset is realized by one translation. -/
theorem shattering_certificate (s : Finset (Fin 2 → Fin 2)) (i : Fin 2 → Fin 2) :
    y s + ∑ j, x (i j) ∈ C ↔ i ∈ s := by
  rw [sum_x_eq_Z]
  change Y (mask s) + Z (code i) ∈ C ↔ i ∈ s
  rw [mem_Y_add_Z_iff]
  exact target_mask s i

/-- The supplied polyhedron disproves the proposed convex additive-VC₂ bound. -/
theorem convex_additive_vc2_counterexample :
    ∃ D : Set R3, Convex ℝ D ∧ ¬ HasAddVCNDimAtMost D 2 1 := by
  refine ⟨C, C_convex, ?_⟩
  rw [hasAddVCNDimAtMost_iff]
  push_neg
  exact ⟨x, 2, by norm_num, y, shattering_certificate⟩

/-- Therefore the universal conjecture in `VCDimConvex` is false. -/
theorem convex_additive_vc2_universal_false :
    ¬ ∀ D : Set R3, Convex ℝ D → HasAddVCNDimAtMost D 2 1 := by
  intro h
  exact convex_additive_vc2_counterexample.choose_spec.2
    (h _ convex_additive_vc2_counterexample.choose_spec.1)

#print axioms convex_additive_vc2_counterexample
#print axioms convex_additive_vc2_universal_false

end VCDimConvexCounterexample
