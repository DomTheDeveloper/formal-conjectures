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
public import Mathlib.Algebra.Field.GeomSum
public import Mathlib.Analysis.SpecificLimits.Normed

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

/-- On a unit torus, the standard product volume is the product of the probability-normalized
Haar measures used by Mathlib's Fourier basis. -/
lemma volume_eq_fourierVolume :
    (volume : Measure (UnitAddTorus d)) =
      Measure.pi (fun _ : d => AddCircle.haarAddCircle) := by
  change Measure.pi (fun _ : d => (volume : Measure UnitAddCircle)) =
    Measure.pi (fun _ : d => AddCircle.haarAddCircle)
  apply congrArg (fun μ : d → Measure UnitAddCircle => Measure.pi μ)
  funext i
  simpa using (AddCircle.volume_eq_smul_haarAddCircle (T := (1 : ℝ)))

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
  rw [dist_eq_norm, norm_sub_rev] at hdist
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

/-- There is no nontrivial integer relation among `a` and `1`. -/
def NoIntegerRelation (a : d → ℝ) : Prop :=
  ∀ k : d → ℤ, (∃ z : ℤ, ∑ i, (k i : ℝ) * a i = z) → k = 0

/-- A multivariate Fourier monomial turns addition on the torus into multiplication. -/
lemma mFourier_add_point (k : d → ℤ) (x y : UnitAddTorus d) :
    mFourier k (x + y) = mFourier k x * mFourier k y := by
  simp only [mFourier, ContinuousMap.coe_mk, Pi.add_apply, fourier_apply, smul_add,
    AddCircle.toCircle_add, Circle.coe_mul, Finset.prod_mul_distrib]

/-- A Fourier monomial along a rotation orbit is a geometric progression. -/
lemma mFourier_nsmul (k : d → ℤ) (x : UnitAddTorus d) (n : ℕ) :
    mFourier k (n • x) = (mFourier k x) ^ n := by
  induction n with
  | zero => simp [mFourier_zero]
  | succ n ih =>
      rw [succ_nsmul, mFourier_add_point, ih, pow_succ]

/-- A Fourier monomial is the canonical circle character evaluated on the corresponding
integer linear combination of the coordinates. -/
lemma mFourier_eq_toCircle_sum (k : d → ℤ) (x : UnitAddTorus d) :
    mFourier k x =
      ((AddCircle.toCircle (∑ i, k i • x i) : Circle) : ℂ) := by
  classical
  simp only [mFourier, ContinuousMap.coe_mk, fourier_apply]
  let s : Finset d := Finset.univ
  change (∏ i ∈ s, ((AddCircle.toCircle (k i • x i) : Circle) : ℂ)) = _
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha, AddCircle.toCircle_add,
        Circle.coe_mul, ih]

/-- Under `NoIntegerRelation`, every nonconstant Fourier monomial is nontrivial on the
rotation vector. -/
lemma mFourier_coe_ne_one {a : d → ℝ} (ha : NoIntegerRelation a)
    {k : d → ℤ} (hk : k ≠ 0) :
    mFourier k (fun i => (a i : UnitAddCircle)) ≠ 1 := by
  intro h
  have hcirc :
      AddCircle.toCircle (∑ i, k i • (a i : UnitAddCircle)) = (1 : Circle) := by
    apply Subtype.ext
    simpa [mFourier_eq_toCircle_sum] using h
  have hzero : (∑ i, k i • (a i : UnitAddCircle)) = 0 := by
    apply AddCircle.injective_toCircle one_ne_zero
    simpa using hcirc
  have hzero' : ((∑ i, (k i : ℝ) * a i : ℝ) : UnitAddCircle) = 0 := by
    simpa [zsmul_eq_mul] using hzero
  obtain ⟨z, hz⟩ := AddCircle.coe_eq_zero_iff.mp hzero'
  apply hk
  apply ha k
  exact ⟨z, by simpa [zsmul_eq_mul] using hz.symm⟩

/-- The Haar integral of a torus Fourier monomial is `1` at frequency zero and `0`
otherwise. -/
lemma integral_mFourier (k : d → ℤ) :
    ∫ x : UnitAddTorus d, mFourier k x = if k = 0 then 1 else 0 := by
  rw [volume_eq_fourierVolume (d := d)]
  have h := (orthonormal_iff_ite.mp (orthonormal_mFourier (d := d))) (0 : d → ℤ) k
  simpa only [ContinuousMap.inner_toLp, mFourier_zero, ContinuousMap.one_apply,
    map_one, one_mul, Pi.zero_apply, neg_zero, zero_add, eq_comm] using h

/-- The Cesàro averages of a nontrivial unit-modulus geometric progression tend to zero. -/
lemma tendsto_geom_average_zero {z : ℂ} (hz : z ≠ 1) (hnorm : ‖z‖ = 1) :
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, z ^ n) / N) atTop (𝓝 0) := by
  have hbound : ∀ N : ℕ,
      ‖(∑ n ∈ Finset.range N, z ^ n) / N‖ ≤
        (2 / ‖z - 1‖) / (N : ℝ) := by
    intro N
    rw [geom_sum_eq hz, norm_div, norm_div, Complex.norm_natCast]
    by_cases hN : N = 0
    · simp [hN]
    have hden : 0 < ‖z - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hz)
    have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
    apply div_le_div_of_nonneg_right _ hNpos.le
    apply div_le_div_of_nonneg_right _ hden.le
    calc
      ‖z ^ N - 1‖ ≤ ‖z ^ N‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by simp [norm_pow, hnorm]
  refine squeeze_zero_norm hbound ?_
  exact tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop

/-- Weyl equidistribution for a torus rotation whose coordinates, together with `1`,
have no nontrivial integer relation. -/
theorem tendsto_average_rotation
    (a : d → ℝ) (ha : NoIntegerRelation a) :
    ∀ F : C(UnitAddTorus d, ℂ),
      Tendsto
        (fun N : ℕ =>
          (∑ n ∈ Finset.range N, F (n • (fun i => (a i : UnitAddCircle)))) / N)
        atTop
        (𝓝 (∫ x, F x)) := by
  apply tendsto_average_of_tendsto_mFourier
    (Y := fun n => n • (fun i => (a i : UnitAddCircle))) volume
  intro k
  by_cases hk : k = 0
  · subst k
    have heq :
        (fun N : ℕ =>
          (∑ n ∈ Finset.range N,
            mFourier (0 : d → ℤ) (n • (fun i => (a i : UnitAddCircle)))) / N) =ᶠ[atTop]
          fun _ => (1 : ℂ) := by
      filter_upwards [eventually_gt_atTop 0] with N hN
      simp [mFourier_zero, hN.ne']
    simpa [integral_mFourier] using tendsto_const_nhds.congr' heq.symm
  · have hz : mFourier k (fun i => (a i : UnitAddCircle)) ≠ 1 :=
      mFourier_coe_ne_one ha hk
    have hnorm : ‖mFourier k (fun i => (a i : UnitAddCircle))‖ = 1 := by
      simp [mFourier, fourier_apply, norm_prod, Circle.norm_coe]
    have hgeom := tendsto_geom_average_zero hz hnorm
    rw [integral_mFourier, if_neg hk]
    simpa only [mFourier_nsmul] using hgeom

end UnitAddTorus
