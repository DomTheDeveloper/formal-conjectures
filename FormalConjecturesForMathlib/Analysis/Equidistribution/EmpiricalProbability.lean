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
public import Mathlib.MeasureTheory.Measure.Portmanteau

@[expose] public section

/-!
# Empirical probability measures on a finite torus

This file packages the measure-theoretic bridge used after Weyl's criterion.
The empirical measure of the first `N + 1` points of a sequence is a genuine
probability measure, and convergence of all continuous empirical averages
implies weak convergence of these empirical measures.
-/

noncomputable section

open Filter MeasureTheory Set Topology
open scoped BigOperators ENNReal NNReal Topology

namespace UnitAddTorus

variable {d : Type*} [Fintype d]

/-- The uniform empirical probability measure on `Y 0, ..., Y N`. -/
def empiricalProbability (Y : ℕ → UnitAddTorus d) (N : ℕ) :
    ProbabilityMeasure (UnitAddTorus d) :=
  ⟨((N + 1 : ℕ) : ℝ≥0∞)⁻¹ •
      ∑ n ∈ Finset.range (N + 1), Measure.dirac (Y n), by
    rw [isProbabilityMeasure_iff]
    simp [Measure.smul_apply, ENNReal.inv_mul_cancel]⟩

/-- Integrating against the empirical probability measure is the finite
arithmetic average over the orbit segment. -/
theorem integral_empiricalProbability (Y : ℕ → UnitAddTorus d) (N : ℕ)
    (F : C(UnitAddTorus d, ℂ)) :
    ∫ x, F x ∂(empiricalProbability Y N : Measure (UnitAddTorus d)) =
      (∑ n ∈ Finset.range (N + 1), F (Y n)) / (N + 1) := by
  classical
  rw [empiricalProbability, integral_smul_measure]
  rw [integral_finset_sum_measure]
  · simp only [integral_dirac]
    simp [div_eq_mul_inv, smul_eq_mul, mul_comm]
  · intro n hn
    exact integrable_dirac (by simp)

/-- The mass assigned by the empirical probability measure to a measurable
set is its relative frequency in the orbit segment. -/
theorem empiricalProbability_apply (Y : ℕ → UnitAddTorus d) (N : ℕ)
    {s : Set (UnitAddTorus d)} (hs : MeasurableSet s) :
    (empiricalProbability Y N : Measure (UnitAddTorus d)) s =
      (((Finset.range (N + 1)).filter fun n => Y n ∈ s).card : ℝ≥0∞) /
        (N + 1) := by
  classical
  simp [empiricalProbability, Measure.smul_apply, hs, div_eq_mul_inv]

/-- If every continuous empirical average converges to its Haar integral,
then the empirical probability measures converge weakly to Haar measure. -/
theorem tendsto_empiricalProbability_of_tendsto_average
    (Y : ℕ → UnitAddTorus d)
    (havg : ∀ F : C(UnitAddTorus d, ℂ),
      Tendsto
        (fun N : ℕ => (∑ n ∈ Finset.range N, F (Y n)) / N)
        atTop
        (𝓝 (∫ x, F x))) :
    Tendsto (empiricalProbability Y) atTop
      (𝓝 (⟨volume, inferInstance⟩ : ProbabilityMeasure (UnitAddTorus d))) := by
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ]
  intro f
  let F : C(UnitAddTorus d, ℂ) :=
    (ContinuousMap.equivBoundedOfCompact (UnitAddTorus d) ℂ).symm f
  have hsucc : Tendsto (fun N : ℕ => N + 1) atTop atTop := by
    refine tendsto_atTop.2 fun b => ⟨b, ?_⟩
    intro a ha
    exact ha.trans (Nat.le_add_right a 1)
  have h := (havg F).comp hsucc
  simpa [integral_empiricalProbability, F] using h

/-- The empirical probability measures of a torus rotation with no integer
relation converge weakly to Haar probability measure. -/
theorem tendsto_empiricalProbability_rotation
    (a : d → ℝ) (ha : NoIntegerRelation a) :
    Tendsto
      (empiricalProbability
        (fun n => n • (fun i => (a i : UnitAddCircle))))
      atTop
      (𝓝 (⟨volume, inferInstance⟩ : ProbabilityMeasure (UnitAddTorus d))) :=
  tendsto_empiricalProbability_of_tendsto_average _
    (tendsto_average_rotation a ha)

end UnitAddTorus
