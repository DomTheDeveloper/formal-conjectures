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

public import FormalConjecturesForMathlib.Analysis.Equidistribution.UnitAddTorus
public import FormalConjecturesForMathlib.MeasureTheory.Group.UnitAddCircleArc
public import FormalConjecturesForMathlib.MeasureTheory.Probability.Empirical
public import FormalConjecturesForMathlib.MeasureTheory.Probability.PiContinuitySet

@[expose] public section

open Filter Set MeasureTheory
open scoped Topology BigOperators ENNReal NNReal

noncomputable section

namespace UnitAddTorus

variable {ι : Type*} [Fintype ι]

/-- The coordinate event saying that the distinguished coordinate hits its terminal arc and every
other coordinate misses its terminal arc. -/
def terminalCoordinateSet [DecidableEq ι] (j : ι) (a : ι → ℝ) (i : ι) :
    Set UnitAddCircle :=
  if i = j then UnitAddCircle.terminalArc (a i)
  else (UnitAddCircle.terminalArc (a i))ᶜ

/-- The corresponding rectangle in the finite unit torus. -/
def terminalBox [DecidableEq ι] (j : ι) (a : ι → ℝ) : Set (UnitAddTorus ι) :=
  Set.pi univ (terminalCoordinateSet j a)

/-- Orbit membership in the terminal box is exactly one hit and all other misses. -/
theorem nsmul_mem_terminalBox_iff [DecidableEq ι]
    (j : ι) (a : ι → ℝ) (ha0 : ∀ i, 0 < a i) (ha1 : ∀ i, a i < 1) (n : ℕ) :
    n • (fun i => (a i : UnitAddCircle)) ∈ terminalBox j a ↔
      (1 - a j < Int.fract ((n : ℝ) * a j) ∧
        ∀ i, i ≠ j → ¬(1 - a i < Int.fract ((n : ℝ) * a i))) := by
  classical
  simp only [terminalBox, Set.mem_pi, Set.mem_univ, forall_true_left,
    terminalCoordinateSet, Pi.smul_apply]
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · have hj := h j
      simp only [if_pos rfl] at hj
      exact (UnitAddCircle.nsmul_mem_terminalArc_iff (ha0 j) (ha1 j) n).mp hj
    · intro i hij hi
      have hmiss := h i
      simp only [if_neg hij] at hmiss
      exact hmiss ((UnitAddCircle.nsmul_mem_terminalArc_iff (ha0 i) (ha1 i) n).mpr hi)
  · rintro ⟨hj, hother⟩ i
    by_cases hij : i = j
    · subst i
      simp only [if_pos rfl]
      exact (UnitAddCircle.nsmul_mem_terminalArc_iff (ha0 j) (ha1 j) n).mpr hj
    · simp only [if_neg hij, Set.mem_compl_iff]
      intro hi
      exact hother i hij ((UnitAddCircle.nsmul_mem_terminalArc_iff (ha0 i) (ha1 i) n).mp hi)

/-- The terminal box is measurable. -/
theorem measurableSet_terminalBox [DecidableEq ι]
    (j : ι) (a : ι → ℝ) : MeasurableSet (terminalBox j a) := by
  apply MeasurableSet.univ_pi
  intro i
  by_cases h : i = j
  · simp [terminalCoordinateSet, h, UnitAddCircle.measurableSet_terminalArc]
  · simp [terminalCoordinateSet, h, UnitAddCircle.measurableSet_terminalArc]

/-- Every coordinate set of the terminal box has null frontier. -/
theorem volume_frontier_terminalCoordinateSet [DecidableEq ι]
    (j : ι) (a : ι → ℝ) (ha0 : ∀ i, 0 < a i) (ha1 : ∀ i, a i < 1) (i : ι) :
    volume (frontier (terminalCoordinateSet j a i)) = 0 := by
  by_cases h : i = j
  · subst i
    simpa [terminalCoordinateSet] using
      UnitAddCircle.volume_frontier_terminalArc (ha0 j) (ha1 j)
  · simpa [terminalCoordinateSet, h] using
      UnitAddCircle.volume_frontier_terminalArc_compl (ha0 i) (ha1 i)

/-- The terminal box is a continuity set for Haar probability measure. -/
theorem volume_frontier_terminalBox [DecidableEq ι]
    (j : ι) (a : ι → ℝ) (ha0 : ∀ i, 0 < a i) (ha1 : ∀ i, a i < 1) :
    volume (frontier (terminalBox j a)) = 0 := by
  exact measure_frontier_pi_eq_zero (fun _ : ι => (volume : Measure UnitAddCircle))
    (terminalCoordinateSet j a) (volume_frontier_terminalCoordinateSet j a ha0 ha1)

/-- Haar mass of a terminal coordinate event. -/
theorem volume_terminalCoordinateSet [DecidableEq ι]
    (j : ι) (a : ι → ℝ) (ha0 : ∀ i, 0 < a i) (ha1 : ∀ i, a i < 1) (i : ι) :
    volume (terminalCoordinateSet j a i) =
      ENNReal.ofReal (if i = j then a i else 1 - a i) := by
  by_cases h : i = j
  · subst i
    simpa [terminalCoordinateSet] using
      UnitAddCircle.volume_terminalArc (ha0 j) (ha1 j)
  · simpa [terminalCoordinateSet, h] using
      UnitAddCircle.volume_terminalArc_compl (ha0 i) (ha1 i)

/-- Haar mass of the terminal box. -/
theorem volume_terminalBox [DecidableEq ι]
    (j : ι) (a : ι → ℝ) (ha0 : ∀ i, 0 < a i) (ha1 : ∀ i, a i < 1) :
    volume (terminalBox j a) =
      ENNReal.ofReal (a j * ∏ i ∈ (Finset.univ.erase j), (1 - a i)) := by
  rw [show (volume : Measure (UnitAddTorus ι)) =
      Measure.pi (fun _ : ι => (volume : Measure UnitAddCircle)) by rfl]
  rw [terminalBox, Measure.pi_pi]
  simp_rw [volume_terminalCoordinateSet j a ha0 ha1]
  rw [← ENNReal.ofReal_prod_of_nonneg]
  · congr 1
    calc
      (∏ i, if i = j then a i else 1 - a i) =
          (if j = j then a j else 1 - a j) *
            ∏ i ∈ Finset.univ.erase j, (if i = j then a i else 1 - a i) := by
        exact (Finset.mul_prod_erase Finset.univ
          (fun i => if i = j then a i else 1 - a i) (Finset.mem_univ j)).symm
      _ = a j * ∏ i ∈ Finset.univ.erase j, (1 - a i) := by
        simp only [if_pos rfl]
        apply congrArg (fun x => a j * x)
        apply Finset.prod_congr rfl
        intro i hi
        have hij : i ≠ j := (Finset.mem_erase.mp hi).1
        simp [hij]
  · intro i hi
    split_ifs
    · exact (ha0 i).le
    · exact sub_nonneg.mpr (ha1 i).le

/-- The terminal-box orbit event has the expected natural density. -/
theorem hasDensity_terminalBox [DecidableEq ι]
    (j : ι) (a : ι → ℝ) (ha0 : ∀ i, 0 < a i) (ha1 : ∀ i, a i < 1)
    (hrel : NoIntegerRelation a) :
    {n : ℕ | n • (fun i => (a i : UnitAddCircle)) ∈ terminalBox j a}.HasDensity
      (a j * ∏ i ∈ (Finset.univ.erase j), (1 - a i)) := by
  let μ : ProbabilityMeasure (UnitAddTorus ι) := ⟨volume, inferInstance⟩
  have havg : ∀ F : C(UnitAddTorus ι, ℂ),
      Tendsto
        (fun N : ℕ =>
          (∑ n ∈ Finset.range N, F (n • (fun i => (a i : UnitAddCircle)))) / (N : ℂ))
        atTop
        (𝓝 (∫ x, F x ∂(μ : Measure (UnitAddTorus ι)))) := by
    simpa [μ] using tendsto_average_rotation a hrel
  have hd := MeasureTheory.hasDensity_of_tendsto_average
    (Y := fun n => n • (fun i => (a i : UnitAddCircle))) μ havg
    (measurableSet_terminalBox j a) (by
      change (volume (frontier (terminalBox j a))).toNNReal = 0
      rw [volume_frontier_terminalBox j a ha0 ha1]
      rfl)
    {n : ℕ | n • (fun i => (a i : UnitAddCircle)) ∈ terminalBox j a} (fun _ => Iff.rfl)
  convert hd using 1
  change a j * ∏ i ∈ Finset.univ.erase j, (1 - a i) =
    (volume (terminalBox j a)).toReal
  have hnonneg : 0 ≤ a j * ∏ i ∈ Finset.univ.erase j, (1 - a i) := by
    apply mul_nonneg (ha0 j).le
    apply Finset.prod_nonneg
    intro i hi
    exact sub_nonneg.mpr (ha1 i).le
  rw [volume_terminalBox j a ha0 ha1, ENNReal.toReal_ofReal hnonneg]

end UnitAddTorus