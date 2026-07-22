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
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public import Mathlib.Analysis.Normed.Group.AddCircle

@[expose] public section

open Set Filter MeasureTheory
open scoped Topology ENNReal

noncomputable section

namespace UnitAddCircle

/-- The arc with fractional representatives in `(1-a,1)`. -/
def terminalArc (a : ℝ) : Set UnitAddCircle :=
  Metric.ball ((1 - a / 2 : ℝ) : UnitAddCircle) (a / 2)

/-- The preimage of a ball under the real quotient map is the union of its integer translates. -/
theorem coe_preimage_ball_eq_iUnion (x ε : ℝ) :
    ((↑) : ℝ → UnitAddCircle) ⁻¹' Metric.ball (x : UnitAddCircle) ε =
      ⋃ z : ℤ, Metric.ball (x + z) ε := by
  ext y
  simp only [Metric.mem_ball, Set.mem_preimage, Set.mem_iUnion, Real.dist_eq,
    dist_eq_norm, ← QuotientAddGroup.mk_sub, UnitAddCircle.norm_eq]
  constructor
  · intro h
    refine ⟨Int.round (y - x), ?_⟩
    simpa [sub_sub, add_comm, add_left_comm, add_assoc] using h
  · rintro ⟨z, hz⟩
    have hmin := Int.round_le (y - x) z
    exact hmin.trans_lt (by simpa [sub_sub, add_comm, add_left_comm, add_assoc] using hz)

/-- Membership in the terminal metric arc is exactly a strict fractional-coordinate inequality. -/
theorem coe_mem_terminalArc_iff {a t : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (ht : t ∈ Set.Ico (0 : ℝ) 1) :
    ((t : ℝ) : UnitAddCircle) ∈ terminalArc a ↔ 1 - a < t := by
  change t ∈ ((↑) : ℝ → UnitAddCircle) ⁻¹'
    Metric.ball ((1 - a / 2 : ℝ) : UnitAddCircle) (a / 2) ↔ _
  rw [coe_preimage_ball_eq_iUnion]
  simp only [Set.mem_iUnion, Metric.mem_ball, Real.dist_eq]
  constructor
  · rintro ⟨z, hz⟩
    obtain ⟨hzl, hzu⟩ := abs_lt.mp hz
    by_cases hzero : z = 0
    · subst z
      norm_num at hzl hzu
      linarith
    · rcases lt_or_gt_of_ne hzero with hzneg | hzpos
      · have hzle : (z : ℝ) ≤ -1 := by exact_mod_cast (show z ≤ -1 by omega)
        linarith [ht.1]
      · have hzone : (1 : ℝ) ≤ z := by exact_mod_cast (show (1 : ℤ) ≤ z by omega)
        linarith [ht.2]
  · intro h
    refine ⟨0, ?_⟩
    rw [Int.cast_zero, add_zero, abs_lt]
    constructor <;> linarith [ht.2]

/-- Fractional representatives are unchanged by passing to `UnitAddCircle`. -/
theorem coe_fract_eq (x : ℝ) :
    ((x : ℝ) : UnitAddCircle) = ((Int.fract x : ℝ) : UnitAddCircle) := by
  rw [← Int.floor_add_fract x]
  simp

/-- A rotation point lies in the terminal arc precisely when its fractional part lies in the
corresponding terminal interval. -/
theorem nsmul_mem_terminalArc_iff {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (n : ℕ) :
    n • (a : UnitAddCircle) ∈ terminalArc a ↔
      1 - a < Int.fract ((n : ℝ) * a) := by
  have hfract := Int.fract_mem ((n : ℝ) * a)
  rw [show n • (a : UnitAddCircle) = (((n : ℝ) * a : ℝ) : UnitAddCircle) by
    simp [nsmul_eq_mul]]
  rw [coe_fract_eq]
  exact coe_mem_terminalArc_iff ha0 ha1 hfract

/-- Spheres in the additive circle have Haar measure zero. -/
theorem volume_sphere_eq_zero {c r : ℝ} (_hr0 : 0 ≤ r) (_hr : r < 1 / 2) :
    volume (Metric.sphere (c : UnitAddCircle) r) = 0 := by
  rw [← ae_eq_empty]
  filter_upwards [AddCircle.closedBall_ae_eq_ball
    (x := (c : UnitAddCircle)) (ε := r)] with y hy
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hysphere
  have hclosed : y ∈ Metric.closedBall (c : UnitAddCircle) r :=
    Metric.mem_closedBall.mpr (Metric.mem_sphere.mp hysphere).le
  have hball : y ∈ Metric.ball (c : UnitAddCircle) r := by
    rw [← hy]
    exact hclosed
  exact (Metric.mem_ball.mp hball).ne (Metric.mem_sphere.mp hysphere)

/-- The terminal arc has length `a`. -/
theorem volume_terminalArc {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    volume (terminalArc a) = ENNReal.ofReal a := by
  calc
    volume (terminalArc a) =
        volume (Metric.closedBall ((1 - a / 2 : ℝ) : UnitAddCircle) (a / 2)) := by
          exact measure_congr (AddCircle.closedBall_ae_eq_ball
            (x := ((1 - a / 2 : ℝ) : UnitAddCircle)) (ε := a / 2)).symm
    _ = ENNReal.ofReal a := by
      rw [AddCircle.volume_closedBall]
      congr 1
      rw [min_eq_right]
      · ring
      · linarith

/-- The terminal arc is measurable. -/
theorem measurableSet_terminalArc (a : ℝ) : MeasurableSet (terminalArc a) :=
  Metric.isOpen_ball.measurableSet

/-- The terminal arc has null frontier. -/
theorem volume_frontier_terminalArc {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    volume (frontier (terminalArc a)) = 0 := by
  apply measure_mono_null Metric.frontier_ball_subset_sphere
  exact volume_sphere_eq_zero (by positivity) (by linarith)

/-- The complement of a terminal arc has null frontier as well. -/
theorem volume_frontier_terminalArc_compl {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    volume (frontier (terminalArc a)ᶜ) = 0 := by
  simpa using volume_frontier_terminalArc ha0 ha1

/-- The complement of a terminal arc has length `1-a`. -/
theorem volume_terminalArc_compl {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    volume (terminalArc a)ᶜ = ENNReal.ofReal (1 - a) := by
  rw [measure_compl (measurableSet_terminalArc a) (measure_ne_top _ _)]
  rw [AddCircle.measure_univ, volume_terminalArc ha0 ha1]
  norm_num [ENNReal.ofReal_sub 1 ha0.le]

end UnitAddCircle
