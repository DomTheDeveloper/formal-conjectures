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

public import Mathlib.Analysis.Fourier.AddCircleMulti

@[expose] public section

/-!
# A continuous Weyl criterion on a finite-dimensional unit torus

Mathlib proves that the multivariate Fourier monomials have dense complex
linear span in the continuous functions on `UnitAddTorus d`.  This file
packages the standard consequence needed for equidistribution arguments:
convergence of the empirical averages of every Fourier monomial implies
convergence of the empirical averages of every continuous function.
-/

open Filter MeasureTheory Topology
open scoped Topology

namespace UnitAddTorus

variable {d : Type*} [Fintype d]

/--
**Continuous Weyl criterion on a finite unit torus.**

If the empirical averages along `Y` converge to the `μ`-integral for every
multivariate Fourier monomial, then they converge to the `μ`-integral for
every continuous complex-valued function.  The proof extends convergence
from the linear span of the monomials to its uniform closure, which is all of
`C(UnitAddTorus d, ℂ)` by `span_mFourier_closure_eq_top`.
-/
theorem tendsto_average_of_tendsto_mFourier
    (Y : ℕ → UnitAddTorus d) (μ : Measure (UnitAddTorus d))
    [IsProbabilityMeasure μ]
    (hfou : ∀ k : d → ℤ,
      Tendsto
        (fun N : ℕ => (∑ n ∈ Finset.range N, mFourier k (Y n)) / N)
        atTop
        (𝓝 (∫ x, mFourier k x ∂μ))) :
    ∀ F : C(UnitAddTorus d, ℂ),
      Tendsto
        (fun N : ℕ => (∑ n ∈ Finset.range N, F (Y n)) / N)
        atTop
        (𝓝 (∫ x, F x ∂μ)) := by
  have hint : ∀ g : C(UnitAddTorus d, ℂ), Integrable g μ := fun g =>
    g.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hspan : ∀ g ∈ Submodule.span ℂ (Set.range (mFourier (d := d))),
      Tendsto
        (fun N : ℕ => (∑ n ∈ Finset.range N, g (Y n)) / N)
        atTop
        (𝓝 (∫ x, g x ∂μ)) := by
    intro g hg
    induction hg using Submodule.span_induction with
    | mem g hgmem =>
        obtain ⟨k, rfl⟩ := hgmem
        exact hfou k
    | zero =>
        simp only [ContinuousMap.zero_apply, Finset.sum_const_zero, zero_div, integral_zero]
        exact tendsto_const_nhds
    | add g₁ g₂ _ _ ih₁ ih₂ =>
        simp only [ContinuousMap.add_apply, Finset.sum_add_distrib, add_div,
          integral_add (hint g₁) (hint g₂)]
        exact ih₁.add ih₂
    | smul c g _ ih =>
        simp only [ContinuousMap.smul_apply, smul_eq_mul, ← Finset.mul_sum, mul_div_assoc,
          integral_const_mul]
        exact ih.const_mul c
  intro F
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hF : F ∈ closure (Submodule.span ℂ (Set.range (mFourier (d := d))) : Set _) := by
    rw [← Submodule.topologicalClosure_coe, span_mFourier_closure_eq_top,
      Submodule.top_coe]
    exact Set.mem_univ F
  obtain ⟨p, hp, hdist⟩ := Metric.mem_closure_iff.mp hF (ε / 3) (by positivity)
  rw [dist_eq_norm] at hdist
  obtain ⟨N₀, hN₀⟩ :=
    (Metric.tendsto_atTop.mp (hspan p hp)) (ε / 3) (by positivity)
  refine ⟨N₀, fun N hN => ?_⟩
  have hbound : ∀ z : UnitAddTorus d, ‖F z - p z‖ ≤ ‖F - p‖ := fun z => by
    simpa using (F - p).norm_coe_le_norm z
  have h1 :
      ‖(∑ n ∈ Finset.range N, F (Y n)) / N -
          (∑ n ∈ Finset.range N, p (Y n)) / N‖ ≤ ‖F - p‖ := by
    rw [div_sub_div_same, ← Finset.sum_sub_distrib, norm_div, Complex.norm_natCast]
    rcases Nat.eq_zero_or_pos N with h | h
    · simp [h]
    · rw [div_le_iff₀ (by exact_mod_cast h)]
      calc
        ‖∑ n ∈ Finset.range N, (F (Y n) - p (Y n))‖
            ≤ ∑ n ∈ Finset.range N, ‖F (Y n) - p (Y n)‖ := norm_sum_le _ _
        _ ≤ ∑ _n ∈ Finset.range N, ‖F - p‖ :=
          Finset.sum_le_sum (fun n _ => hbound _)
        _ = ‖F - p‖ * N := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_comm]
  have h2 : ‖(∫ x, p x ∂μ) - ∫ x, F x ∂μ‖ ≤ ‖F - p‖ := by
    rw [← integral_sub (hint p) (hint F)]
    calc
      ‖∫ x, (p x - F x) ∂μ‖ ≤ ∫ x, ‖p x - F x‖ ∂μ :=
        norm_integral_le_integral_norm _
      _ ≤ ∫ _x, ‖F - p‖ ∂μ := by
        refine integral_mono_of_nonneg
          (by filter_upwards with z using norm_nonneg (p z - F z))
          (integrable_const _) ?_
        filter_upwards with z
        rw [norm_sub_rev]
        exact hbound z
      _ = ‖F - p‖ := by simp
  have hN0' := hN₀ N hN
  rw [dist_eq_norm] at hN0' ⊢
  have htri :
      ‖(∑ n ∈ Finset.range N, F (Y n)) / N - ∫ x, F x ∂μ‖ ≤
        ‖(∑ n ∈ Finset.range N, F (Y n)) / N -
            (∑ n ∈ Finset.range N, p (Y n)) / N‖ +
          ‖(∑ n ∈ Finset.range N, p (Y n)) / N - ∫ x, p x ∂μ‖ +
          ‖(∫ x, p x ∂μ) - ∫ x, F x ∂μ‖ := by
    have heq :
        (∑ n ∈ Finset.range N, F (Y n)) / N - ∫ x, F x ∂μ =
          ((∑ n ∈ Finset.range N, F (Y n)) / N -
              (∑ n ∈ Finset.range N, p (Y n)) / N) +
            ((∑ n ∈ Finset.range N, p (Y n)) / N - ∫ x, p x ∂μ) +
            ((∫ x, p x ∂μ) - ∫ x, F x ∂μ) := by ring
    rw [heq]
    exact norm_add₃_le
  linarith [htri, h1, h2, hN0', hdist]

end UnitAddTorus
