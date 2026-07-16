/-
Copyright (c) 2026 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion, David Ledvinka
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction
public import Mathlib.Topology.UnitInterval

/-!
# Bernoulli probability measures

A minimal compatibility backport for the mathlib snapshot pinned by formal-conjectures.
-/

public section

open MeasureTheory Measure unitInterval Complex
open scoped ENNReal

namespace ProbabilityTheory

variable {X : Type*} [MeasurableSpace X] {x y : X} {p : I}

/-- The Bernoulli measure giving mass `p` to `x` and mass `1 - p` to `y`. -/
@[expose]
noncomputable def bernoulliMeasure (x y : X) (p : I) : Measure X :=
  toNNReal p • dirac x + toNNReal (σ p) • dirac y

@[inherit_doc]
scoped notation "Ber(" x ", " y ", " p ")" => bernoulliMeasure x y p

lemma bernoulliMeasure_def (x y : X) (p : I) :
    Ber(x, y, p) = toNNReal p • dirac x + toNNReal (σ p) • dirac y := rfl

instance isProbabilityMeasure_bernoulliMeasure : IsProbabilityMeasure Ber(x, y, p) where
  measure_univ := by simp [bernoulliMeasure_def]

@[simp]
lemma bernoulliMeasure_zero (x y : X) : bernoulliMeasure x y 0 = dirac y := by
  simp [bernoulliMeasure_def]

@[simp]
lemma bernoulliMeasure_one (x y : X) : bernoulliMeasure x y 1 = dirac x := by
  simp [bernoulliMeasure_def]

section Integral

variable {E : Type*} [NormedAddCommGroup E]

lemma integrable_bernoulliMeasure [MeasurableSingletonClass X]
    (x y : X) (p : I) (f : X → E) : Integrable f Ber(x, y, p) := by
  simp [bernoulliMeasure_def, integrable_add_measure, integrable_dirac,
    Integrable.smul_measure_nnreal]

variable [NormedSpace ℝ E] [CompleteSpace E]

lemma integral_bernoulliMeasure [MeasurableSingletonClass X]
    (x y : X) (p : I) (f : X → E) :
    ∫ z, f z ∂Ber(x, y, p) = (p : ℝ) • f x + (1 - p : ℝ) • f y := by
  rw [bernoulliMeasure_def, integral_add_measure]
  · simp [NNReal.smul_def]
  all_goals exact (integrable_dirac (by simp)).smul_measure_nnreal

end Integral

section Standardized

/-- Standard deviation of a nondegenerate Bernoulli variable with success probability `p`. -/
@[expose]
noncomputable def bernoulliStdDev (p : I) : ℝ := Real.sqrt ((p : ℝ) * (1 - p))

/-- Center and normalize a real Bernoulli variable. -/
@[expose]
noncomputable def standardizedBernoulli (p : I) (z : ℝ) : ℝ :=
  (z - p) / bernoulliStdDev p

@[fun_prop]
lemma continuous_standardizedBernoulli (p : I) : Continuous (standardizedBernoulli p) := by
  unfold standardizedBernoulli
  fun_prop

lemma bernoulliStdDev_pos (p : I) (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    0 < bernoulliStdDev p := by
  rw [bernoulliStdDev, Real.sqrt_pos]
  exact mul_pos hp0 (sub_pos.mpr hp1)

lemma integral_standardizedBernoulli (p : I) (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    ∫ z, standardizedBernoulli p z ∂Ber((1 : ℝ), 0, p) = 0 := by
  rw [integral_bernoulliMeasure]
  simp only [smul_eq_mul, standardizedBernoulli]
  have hs : bernoulliStdDev p ≠ 0 := (bernoulliStdDev_pos p hp0 hp1).ne'
  field_simp [hs]
  ring

lemma integral_sq_standardizedBernoulli
    (p : I) (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    ∫ z, standardizedBernoulli p z ^ 2 ∂Ber((1 : ℝ), 0, p) = 1 := by
  rw [integral_bernoulliMeasure]
  simp only [smul_eq_mul, standardizedBernoulli]
  have hvar : 0 ≤ (p : ℝ) * (1 - p) :=
    (mul_pos hp0 (sub_pos.mpr hp1)).le
  rw [div_pow, div_pow, bernoulliStdDev, Real.sq_sqrt hvar]
  have hq : 1 - (p : ℝ) ≠ 0 := sub_ne_zero.mpr hp1.ne.symm
  field_simp [hp0.ne', hq]
  ring

lemma charFun_standardizedBernoulli
    (p : I) (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) (t : ℝ) :
    charFun (Ber((1 : ℝ), 0, p).map (standardizedBernoulli p)) t =
      (p : ℂ) * exp (t * ((1 - (p : ℝ)) / bernoulliStdDev p) * Complex.I) +
        ((1 - (p : ℝ) : ℝ) : ℂ) *
          exp (t * (-(p : ℝ) / bernoulliStdDev p) * Complex.I) := by
  rw [charFun_apply_real, integral_map]
  · rw [integral_bernoulliMeasure]
    simp only [RCLike.real_smul_eq_coe_mul, standardizedBernoulli, sub_zero, zero_sub]
    push_cast
    congr 1 <;> ring
  · exact (continuous_standardizedBernoulli p).aemeasurable
  · fun_prop

end Standardized

end ProbabilityTheory
