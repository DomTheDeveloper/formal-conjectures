/-
Copyright (c) 2024 Thomas Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Zhu, Etienne Marion
-/
module

public import Mathlib.Analysis.Calculus.Taylor
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction

import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Probability.Notation

/-!
# Taylor expansion of a real characteristic function

This is a minimal compatibility backport for the mathlib snapshot pinned by formal-conjectures.
Only the real, second-order expansion needed by the central limit theorem is provided.
-/

public section

open ProbabilityTheory Complex Set VectorFourier
open scoped Nat RealInnerProductSpace Topology

namespace MeasureTheory

variable {μ : Measure ℝ} [IsFiniteMeasure μ]

@[fun_prop]
theorem contDiff_charFun {n : ℕ} (hint : MemLp id n μ) :
    ContDiff ℝ n (charFun μ) := by
  simp_rw [funext charFun_eq_fourierIntegral']
  refine (contDiff_fourierIntegral (L := innerSL ℝ) fun k hk ↦ ?_).comp (by fun_prop)
  simp only [Pi.one_apply, one_mem, CStarRing.norm_of_mem_unitary, mul_one]
  exact MemLp.integrable_norm_pow' (hint.mono_exponent (by simp_all))

private theorem iteratedDeriv_charFun {n : ℕ} {t : ℝ} (hint : MemLp id n μ) :
    iteratedDeriv n (charFun μ) t = I ^ n * ∫ x, x ^ n * exp (t * x * I) ∂μ := by
  let F : ℝ → ℂ :=
    fourierIntegral Real.fourierChar μ (innerSL ℝ).toLinearMap₁₂ (1 : ℝ → ℂ)
  let c : ℝ := -(2 * Real.pi)⁻¹
  have hint' (k : ℕ) (hk : k ≤ (n : ℕ∞)) :
      Integrable (fun x : ℝ ↦ ‖x‖ ^ k * ‖(1 : ℝ → ℂ) x‖) μ := by
    simp only [Pi.one_apply, one_mem, CStarRing.norm_of_mem_unitary, mul_one]
    exact MemLp.integrable_norm_pow' (hint.mono_exponent (by simp_all))
  have hF : ContDiff ℝ n F := by
    dsimp [F]
    exact contDiff_fourierIntegral (innerSL ℝ) hint'
  have hchar : charFun μ = fun s ↦ F (c * s) := by
    funext s
    rw [charFun_eq_fourierIntegral']
    rfl
  rw [hchar, iteratedDeriv_comp_const_smul hF c]
  dsimp [F]
  rw [iteratedDeriv, iteratedFDeriv_fourierIntegral (innerSL ℝ) hint' (by fun_prop) le_rfl]
  rw [Real.fourierIntegral_continuousMultilinearMap_apply']
  · simp only [fourierIntegral, Real.fourierChar, Circle.exp, ContinuousMap.coe_mk,
      ofReal_mul, ofReal_ofNat, innerSL, ContinuousLinearMap.toLinearMap₁₂_apply,
      LinearMap.mkContinuous₂_apply, innerₛₗ_apply_apply, smul_eq_mul, AddChar.coe_mk,
      fourierPowSMulRight_apply, Pi.ofNat_apply, real_smul, ofReal_prod, mul_one,
      Circle.smul_def, c]
    simp_rw [mul_left_comm (exp _), integral_const_mul, ← mul_assoc, ← mul_pow]
    congr with x
    ring
  · apply integrable_fourierPowSMulRight _
    · simpa only [id_eq, Pi.one_apply, norm_one, mul_one] using hint.integrable_norm_pow'
    · fun_prop

private theorem iteratedDeriv_charFun_zero {n : ℕ} (hint : MemLp id n μ) :
    iteratedDeriv n (charFun μ) 0 = I ^ n * ∫ x, x ^ n ∂μ := by
  rw [iteratedDeriv_charFun hint]
  simp only [zero_mul, ofReal_zero, exp_zero, mul_one]
  congr 1
  have hcast :
      (∫ x : ℝ, ((x ^ n : ℝ) : ℂ) ∂μ) = ((∫ x : ℝ, x ^ n ∂μ : ℝ) : ℂ) :=
    integral_ofReal
  simpa only [ofReal_pow] using hcast

private lemma taylorWithinEval_charFun_zero {n : ℕ} (hint : MemLp id n μ) (t : ℝ) :
    taylorWithinEval (charFun μ) n univ 0 t
      = ∑ k ∈ Finset.range (n + 1), (k ! : ℂ)⁻¹ * (t * I) ^ k * ∫ x, x ^ k ∂μ := by
  simp_rw [taylor_within_apply, sub_zero, RCLike.real_smul_eq_coe_mul]
  refine Finset.sum_congr rfl fun k hkn ↦ ?_
  push_cast
  have hint' : MemLp id k μ := hint.mono_exponent (by simp_all)
  simp [iteratedDeriv_charFun_zero hint', mul_pow, mul_comm, mul_assoc, mul_left_comm]

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {X : Ω → ℝ}

private lemma taylorWithinEval_charFun_two_zero (hX : AEMeasurable X P)
    (hint : MemLp id 2 (P.map X)) (t : ℝ) :
    taylorWithinEval (charFun (P.map X)) 2 univ 0 t =
      1 + (P[X] : ℝ) * t * I - (P[X ^ 2] : ℝ) * t ^ 2 / 2 := by
  have : IsProbabilityMeasure (P.map X) := Measure.isProbabilityMeasure_map hX
  rw [taylorWithinEval_charFun_zero hint]
  simp only [Pi.pow_apply, Nat.reduceAdd, Finset.sum_range_succ, Finset.range_one,
    Finset.sum_singleton, Nat.factorial_zero, Nat.cast_one, inv_one, pow_zero, mul_one,
    integral_const, probReal_univ, smul_eq_mul, ofReal_one, Nat.factorial_one, pow_one, one_mul,
    Nat.factorial_two, Nat.cast_ofNat]
  rw [integral_map, integral_map]
  any_goals fun_prop
  simp [field]
  ring

private lemma taylorWithinEval_charFun_two_zero' (hX : AEMeasurable X P)
    (h0 : P[X] = 0) (h1 : P[X ^ 2] = 1) (t : ℝ) :
    taylorWithinEval (charFun (P.map X)) 2 univ 0 t = 1 - t ^ 2 / 2 := by
  rw [taylorWithinEval_charFun_two_zero hX, h0, h1]
  · simp
  exact (memLp_two_iff_integrable_sq (by fun_prop)).2 (.of_integral_ne_zero <| by
    rw [integral_map]
    any_goals fun_prop
    simp [← Pi.pow_apply, h1])

lemma taylor_charFun_two (hX : AEMeasurable X P) (h0 : P[X] = 0) (h1 : P[X ^ 2] = 1) :
    (fun t ↦ charFun (P.map X) t - (1 - t ^ 2 / 2)) =o[𝓝 0] fun t ↦ t ^ 2 := by
  have hcont : ContDiff ℝ 2 (charFun (P.map X)) := by
    refine contDiff_charFun <|
      (memLp_two_iff_integrable_sq (by fun_prop)).2 (.of_integral_ne_zero ?_)
    rw [integral_map]
    any_goals fun_prop
    simp_all
  have hTaylor :=
    taylor_isLittleO (s := univ) (x₀ := 0) (n := 2)
      convex_univ (Set.mem_univ 0) hcont.contDiffOn
  simp_rw [taylorWithinEval_charFun_two_zero' hX h0 h1] at hTaylor
  simpa only [nhdsWithin_univ, sub_zero] using hTaylor

end MeasureTheory
