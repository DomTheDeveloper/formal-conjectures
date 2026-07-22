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
# A counterexample to the convex additive-VC₂ bound in ℝ³

This file kernel-checks an explicit convex polyhedron in `ℝ³` whose additive
`VC₂` dimension is at least two.  In particular, it refutes
`VCDimConvex.hasAddVCNDimAtMost_two_one_of_convex_r3`.
-/

open scoped BigOperators

namespace VCDimConvexCounterexample

private def point (x y z : ℝ) : ℝ³ := ![x, y, z]

private def coeff : Fin 13 → ℝ³ := ![
  point 1 1 1,
  point 1 0 (-1),
  point 1 1 (-1),
  point (-1) 0 (-1),
  point (-1) 1 (-1),
  point 0 1 (-1),
  point 1 50000 (-50000),
  point 1 (-1) (-1),
  point (-1) (-1) (-1),
  point 0 (-1) (-1),
  point 1 (-1) 1,
  point (-1) 1 50000,
  point (-1) 50000 50000]

private def bound : Fin 13 → ℝ := ![
  150002,
  100001,
  150002,
  -49998,
  4,
  50002,
  2500150001,
  99999,
  -50001,
  -1,
  99999,
  4,
  2500050002]

private def lin (u p : ℝ³) : ℝ := u 0 * p 0 + u 1 * p 1 + u 2 * p 2

private def halfspace (r : Fin 13) : Set ℝ³ := {p | lin (coeff r) p ≤ bound r}

private def C : Set ℝ³ := ⋂ r : Fin 13, halfspace r

private lemma mem_C {p : ℝ³} : p ∈ C ↔ ∀ r : Fin 13, lin (coeff r) p ≤ bound r := by
  simp [C, halfspace]

private lemma convex_halfspace (r : Fin 13) : Convex ℝ (halfspace r) := by
  rw [convex_iff_add_mem]
  intro p hp q hq a b ha hb hab
  simp only [halfspace, Set.mem_setOf_eq] at hp hq ⊢
  simp only [lin, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hp hq ⊢
  nlinarith [mul_nonneg ha (sub_nonneg.mpr hp), mul_nonneg hb (sub_nonneg.mpr hq)]

private lemma convex_C : Convex ℝ C := by
  exact convex_iInter fun r => convex_halfspace r

private def Y : Fin 16 → ℝ³ := ![
  point 50001 50001 50001,
  point 100001 2 0,
  point 0 3 0,
  point 49998 3 0,
  point 100000 0 0,
  point 50002 1 0,
  point 49998 2 0,
  point 50001 2 0,
  point 0 0 0,
  point 50000 0 1,
  point 0 1 0,
  point 49998 2 1,
  point 49998 0 0,
  point 50001 1 0,
  point 49998 1 0,
  point 50000 1 0]

private def Z : Fin 4 → ℝ³ := ![
  point 0 0 0,
  point 50000 0 0,
  point 0 50000 0,
  point 50000 50000 0]

private def target : Fin 16 → Fin 4 → Prop := ![
  ![False, False, False, False],
  ![True,  False, False, False],
  ![False, True,  False, False],
  ![True,  True,  False, False],
  ![False, False, True,  False],
  ![True,  False, True,  False],
  ![False, True,  True,  False],
  ![True,  True,  True,  False],
  ![False, False, False, True],
  ![True,  False, False, True],
  ![False, True,  False, True],
  ![True,  True,  False, True],
  ![False, False, True,  True],
  ![True,  False, True,  True],
  ![False, True,  True,  True],
  ![True,  True,  True,  True]]

/-- A violated row for every excluded incidence.  Entries on included incidences are unused. -/
private def bad : Fin 16 → Fin 4 → Fin 13 := ![
  ![0, 0, 0, 0],
  ![0, 0, 0, 0],
  ![3, 0, 3, 5],
  ![0, 0, 4, 5],
  ![7, 1, 0, 0],
  ![0, 1, 0, 0],
  ![8, 0, 0, 6],
  ![0, 0, 0, 0],
  ![3, 8, 3, 0],
  ![0, 10, 11, 0],
  ![3, 0, 3, 0],
  ![0, 0, 11, 0],
  ![8, 9, 0, 0],
  ![0, 7, 0, 0],
  ![8, 0, 0, 0],
  ![0, 0, 0, 0]]

private lemma mem_of_target {m : Fin 16} {j : Fin 4} (h : target m j) : Y m + Z j ∈ C := by
  fin_cases m <;> fin_cases j <;> simp [target] at h
  all_goals
    rw [mem_C]
    intro r
    fin_cases r <;> norm_num [Y, Z, point, lin, coeff, bound]

private lemma not_mem_of_not_target {m : Fin 16} {j : Fin 4} (h : ¬ target m j) :
    Y m + Z j ∉ C := by
  intro hp
  rw [mem_C] at hp
  have hb := hp (bad m j)
  fin_cases m <;> fin_cases j <;> simp [target] at h <;>
    norm_num [bad, Y, Z, point, lin, coeff, bound] at hb

private lemma mem_Y_add_Z_iff (m : Fin 16) (j : Fin 4) :
    Y m + Z j ∈ C ↔ target m j := by
  constructor
  · intro hmem
    by_contra htarget
    exact not_mem_of_not_target htarget hmem
  · exact mem_of_target

private def I : Fin 4 → (Fin 2 → Fin 2) := ![
  ![0, 0],
  ![1, 0],
  ![0, 1],
  ![1, 1]]

private def code (i : Fin 2 → Fin 2) : Fin 4 :=
  ⟨(i 0).val + 2 * (i 1).val, by omega⟩

private lemma I_code (i : Fin 2 → Fin 2) : I (code i) = i := by
  fin_cases h0 : i 0 <;> fin_cases h1 : i 1
  all_goals
    funext k
    fin_cases k <;> simp [I, code, h0, h1]

private def x : Fin 2 → Fin 2 → ℝ³ := ![
  ![point 0 0 0, point 50000 0 0],
  ![point 0 0 0, point 0 50000 0]]

private lemma sum_x_eq_Z (i : Fin 2 → Fin 2) : (∑ k, x k (i k)) = Z (code i) := by
  fin_cases h0 : i 0 <;> fin_cases h1 : i 1 <;>
    simp [Fin.sum_univ_two, x, Z, point, code, h0, h1]

private def mask (s : Set (Fin 2 → Fin 2)) : Fin 16 :=
  ⟨(if I 0 ∈ s then 1 else 0) +
      (if I 1 ∈ s then 2 else 0) +
      (if I 2 ∈ s then 4 else 0) +
      (if I 3 ∈ s then 8 else 0), by
    split_ifs <;> omega⟩

private def y (s : Set (Fin 2 → Fin 2)) : ℝ³ := Y (mask s)

private lemma target_mask (s : Set (Fin 2 → Fin 2)) (j : Fin 4) :
    target (mask s) j ↔ I j ∈ s := by
  classical
  fin_cases j <;>
    by_cases h0 : I 0 ∈ s <;>
    by_cases h1 : I 1 ∈ s <;>
    by_cases h2 : I 2 ∈ s <;>
    by_cases h3 : I 3 ∈ s <;>
    simp [mask, target, h0, h1, h2, h3]

private lemma shattering_certificate (i : Fin 2 → Fin 2) (s : Set (Fin 2 → Fin 2)) :
    y s + ∑ k, x k (i k) ∈ C ↔ i ∈ s := by
  rw [sum_x_eq_Z, mem_Y_add_Z_iff, target_mask]
  simpa [I_code]

/-- The explicit convex polyhedron has additive `VC₂` dimension at least two. -/
@[category research solved, AMS 5 52]
theorem exists_convex_r3_not_hasAddVCNDimAtMost_two_one :
    ∃ C : Set ℝ³, Convex ℝ C ∧ ¬ HasAddVCNDimAtMost C 2 1 := by
  refine ⟨C, convex_C, ?_⟩
  intro h
  exact h x y shattering_certificate

/-- The open convex additive-`VC₂` conjecture in `ℝ³` is false. -/
@[category research solved, AMS 5 52]
theorem not_forall_convex_r3_hasAddVCNDimAtMost_two_one :
    ¬ ∀ C : Set ℝ³, Convex ℝ C → HasAddVCNDimAtMost C 2 1 := by
  rintro h
  obtain ⟨C, hC, hnot⟩ := exists_convex_r3_not_hasAddVCNDimAtMost_two_one
  exact hnot (h C hC)

#print axioms exists_convex_r3_not_hasAddVCNDimAtMost_two_one
#print axioms not_forall_convex_r3_hasAddVCNDimAtMost_two_one

end VCDimConvexCounterexample
