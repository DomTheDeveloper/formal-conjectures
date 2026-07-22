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

public import Mathlib.MeasureTheory.Measure.Portmanteau
public import Mathlib.Probability.Distributions.Uniform
public import Mathlib.Probability.ProbabilityMassFunction.Integrals
public import FormalConjecturesForMathlib.Data.Set.Density

@[expose] public section

open Filter MeasureTheory Set Topology
open scoped ENNReal NNReal Topology BigOperators Classical

noncomputable section

namespace MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]

private theorem range_nonempty_of_ne_zero {N : ℕ} (hN : N ≠ 0) :
    (Finset.range N).Nonempty :=
  ⟨0, Finset.mem_range.mpr (Nat.pos_of_ne_zero hN)⟩

/-- The empirical probability measure of the first `N` values of a sequence.
At `N = 0` we use a harmless Dirac measure. -/
def empiricalProbabilityMeasure (Y : ℕ → Ω) (N : ℕ) : ProbabilityMeasure Ω := by
  classical
  by_cases hN : N = 0
  · exact ⟨Measure.dirac (Y 0), Measure.dirac.isProbabilityMeasure⟩
  · let p : PMF ℕ := PMF.uniformOfFinset (Finset.range N) (range_nonempty_of_ne_zero hN)
    let ν : ProbabilityMeasure ℕ := ⟨p.toMeasure, inferInstance⟩
    exact ProbabilityMeasure.map ν (measurable_of_countable Y).aemeasurable

lemma empiricalProbabilityMeasure_ne_zero (Y : ℕ → Ω) {N : ℕ} (hN : N ≠ 0) :
    empiricalProbabilityMeasure Y N =
      ProbabilityMeasure.map
        (⟨(PMF.uniformOfFinset (Finset.range N)
            (range_nonempty_of_ne_zero hN)).toMeasure,
          inferInstance⟩ : ProbabilityMeasure ℕ)
        (measurable_of_countable Y).aemeasurable := by
  simp [empiricalProbabilityMeasure, hN, range_nonempty_of_ne_zero]

variable [TopologicalSpace Ω] [BorelSpace Ω]

/-- Integration against the empirical measure is the corresponding finite average. -/
theorem integral_empiricalProbabilityMeasure
    (Y : ℕ → Ω) {N : ℕ} (hN : N ≠ 0) (f : BoundedContinuousFunction Ω ℂ) :
    ∫ x, f x ∂(empiricalProbabilityMeasure Y N : Measure Ω) =
      (∑ n ∈ Finset.range N, f (Y n)) / (N : ℂ) := by
  classical
  rw [empiricalProbabilityMeasure_ne_zero Y hN]
  let p : PMF ℕ := PMF.uniformOfFinset (Finset.range N) (range_nonempty_of_ne_zero hN)
  have hY : Measurable Y := measurable_of_countable Y
  rw [ProbabilityMeasure.toMeasure_map]
  rw [integral_map hY.aemeasurable f.continuous.aestronglyMeasurable]
  have hfint : Integrable (fun n => f (Y n)) p.toMeasure := by
    refine (integrable_const ‖f‖).mono ?_ ?_
    · exact (measurable_of_countable (fun n => f (Y n))).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun n => f.norm_coe_le_norm (Y n)
  rw [PMF.integral_eq_tsum p (fun n => f (Y n)) hfint]
  rw [tsum_eq_sum (s := Finset.range N)]
  · calc
      (∑ n ∈ Finset.range N, (p n).toReal • f (Y n)) =
          ∑ n ∈ Finset.range N, ((N : ℝ)⁻¹ : ℝ) • f (Y n) := by
            apply Finset.sum_congr rfl
            intro n hn
            simp [p, PMF.uniformOfFinset_apply, hn, hN]
      _ = ((N : ℝ)⁻¹ : ℝ) • ∑ n ∈ Finset.range N, f (Y n) := by
            rw [Finset.smul_sum]
      _ = (∑ n ∈ Finset.range N, f (Y n)) / (N : ℂ) := by
            rw [RCLike.real_smul_eq_coe_mul]
            push_cast
            field_simp [hN]
  · intro n hn
    simp [p, PMF.uniformOfFinset_apply, hn]

/-- The mass of a measurable set under an empirical measure is its finite frequency. -/
theorem empiricalProbabilityMeasure_apply (Y : ℕ → Ω) {N : ℕ} (hN : N ≠ 0)
    {A : Set Ω} (hA : MeasurableSet A) :
    empiricalProbabilityMeasure Y N A =
      (((Finset.range N).filter fun n => Y n ∈ A).card : ℝ≥0) / N := by
  classical
  rw [empiricalProbabilityMeasure_ne_zero Y hN]
  rw [ProbabilityMeasure.map_apply]
  · change (((PMF.uniformOfFinset (Finset.range N)
        (range_nonempty_of_ne_zero hN)).toMeasure
          (Y ⁻¹' A)).toNNReal) = _
    rw [PMF.toMeasure_uniformOfFinset_apply]
    · norm_num [ENNReal.toNNReal_div, Finset.filter_filter, and_comm]
    · exact (measurable_of_countable Y) hA
  · exact hA

variable [CompactSpace Ω] [PseudoMetricSpace Ω]

/-- Continuous-test-function convergence of finite orbit averages gives weak convergence of the
empirical probability measures. -/
theorem tendsto_empiricalProbabilityMeasure
    (Y : ℕ → Ω) (μ : ProbabilityMeasure Ω)
    (havg : ∀ F : C(Ω, ℂ),
      Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, F (Y n)) / (N : ℂ))
        atTop (𝓝 (∫ x, F x ∂(μ : Measure Ω)))) :
    Tendsto (empiricalProbabilityMeasure Y) atTop (𝓝 μ) := by
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ]
  intro f
  have h := havg ⟨f, f.continuous⟩
  apply h.congr'
  filter_upwards [eventually_ne_atTop 0] with N hN
  exact integral_empiricalProbabilityMeasure Y hN f

/-- The finite frequency of a continuity set converges to its limiting probability. -/
theorem tendsto_frequency_of_null_frontier
    (Y : ℕ → Ω) (μ : ProbabilityMeasure Ω)
    (havg : ∀ F : C(Ω, ℂ),
      Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, F (Y n)) / (N : ℂ))
        atTop (𝓝 (∫ x, F x ∂(μ : Measure Ω))))
    {A : Set Ω} (hA : MeasurableSet A) (hfront : μ (frontier A) = 0) :
    Tendsto
      (fun N : ℕ =>
        (((Finset.range N).filter fun n => Y n ∈ A).card : ℝ) / N)
      atTop (𝓝 ((μ A : ℝ≥0) : ℝ)) := by
  classical
  have hweak := tendsto_empiricalProbabilityMeasure Y μ havg
  have hport := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto hweak hfront
  have hcoe := (NNReal.continuous_coe.tendsto (μ A)).comp hport
  apply hcoe.congr'
  filter_upwards [eventually_ne_atTop 0] with N hN
  rw [empiricalProbabilityMeasure_apply Y hN hA]
  norm_num [NNReal.coe_div]

/-- A continuity-set frequency theorem expressed in the `Set.HasDensity` API. -/
theorem hasDensity_of_tendsto_average
    (Y : ℕ → Ω) (μ : ProbabilityMeasure Ω)
    (havg : ∀ F : C(Ω, ℂ),
      Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, F (Y n)) / (N : ℂ))
        atTop (𝓝 (∫ x, F x ∂(μ : Measure Ω))))
    {A : Set Ω} (hA : MeasurableSet A) (hfront : μ (frontier A) = 0)
    (S : Set ℕ) (hS : ∀ n, n ∈ S ↔ Y n ∈ A) :
    S.HasDensity ((μ A : ℝ≥0) : ℝ) := by
  classical
  have hfreq := tendsto_frequency_of_null_frontier Y μ havg hA hfront
  change Tendsto
    (fun N : ℕ => (((S ∩ Set.univ) ∩ Set.Iio N).ncard : ℝ) /
      ((Set.univ ∩ Set.Iio N).ncard : ℝ))
    atTop (𝓝 ((μ A : ℝ≥0) : ℝ))
  apply hfreq.congr'
  filter_upwards with N
  have hfinite : ((S ∩ Set.univ) ∩ Set.Iio N).Finite :=
    (Set.finite_Iio N).subset Set.inter_subset_right
  have hcard :
      ((S ∩ Set.univ) ∩ Set.Iio N).ncard =
        ((Finset.range N).filter fun n => Y n ∈ A).card := by
    rw [Set.ncard_eq_toFinset_card _ hfinite]
    congr 1
    ext n
    simp [hS]
  rw [hcard]
  simp

end MeasureTheory
