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

public import Mathlib.MeasureTheory.Measure.CharacteristicFunction
public import Mathlib.Probability.ProbabilityMassFunction.Binomial
public import Mathlib.Probability.ProbabilityMassFunction.Integrals

/-!
# Finite binomial PMFs and their real-valued pushforwards

The pinned mathlib release supplies the finite binomial PMF on `Fin (n + 1)`.  This file packages
its pushforwards to `ℕ` and `ℝ`, records their probability-measure instances, and proves the finite
sum formulas needed for characteristic functions and moment-generating functions.
-/

public section

open MeasureTheory Measure Complex unitInterval
open scoped unitInterval ENNReal ProbabilityTheory

namespace ProbabilityTheory

/-- The finite binomial PMF on `Fin (n + 1)`. -/
@[expose]
noncomputable def binomialPMF (n : ℕ) (p : I) : PMF (Fin (n + 1)) :=
  PMF.binomial (toNNReal p) (by simpa using p.2.2) n

/-- The binomial counting measure on `ℕ`. -/
@[expose]
noncomputable def binomialNatMeasure (n : ℕ) (p : I) : Measure ℕ :=
  (binomialPMF n p).toMeasure.map (Fin.val : Fin (n + 1) → ℕ)

instance isProbabilityMeasure_binomialNatMeasure (n : ℕ) (p : I) :
    IsProbabilityMeasure (binomialNatMeasure n p) :=
  Measure.isProbabilityMeasure_map Measurable.of_discrete.aemeasurable

/-- The real-valued binomial measure. -/
@[expose]
noncomputable def binomialRealMeasure (n : ℕ) (p : I) : Measure ℝ :=
  (binomialPMF n p).toMeasure.map (fun k : Fin (n + 1) ↦ (k : ℝ))

instance isProbabilityMeasure_binomialRealMeasure (n : ℕ) (p : I) :
    IsProbabilityMeasure (binomialRealMeasure n p) :=
  Measure.isProbabilityMeasure_map Measurable.of_discrete.aemeasurable

/-- The counting measure is exactly the pushforward of the finite PMF by `Fin.val`. -/
lemma binomial_eq_binomialPMF_toMeasure_map_val (n : ℕ) (p : I) :
    binomialNatMeasure n p =
      (binomialPMF n p).toMeasure.map (Fin.val : Fin (n + 1) → ℕ) := rfl

lemma binomialPMF_apply_toReal (n : ℕ) (p : I) (k : Fin (n + 1)) :
    ((binomialPMF n p) k).toReal =
      (p : ℝ) ^ (k : ℕ) *
        (1 - (p : ℝ)) ^ ((Fin.last n - k : Fin (n + 1)) : ℕ) *
          (n.choose (k : ℕ) : ℝ) := by
  rw [binomialPMF, PMF.binomial_apply]
  have hq : ((1 : ℝ≥0∞) - (toNNReal p : ℝ≥0∞)).toReal = 1 - (p : ℝ) := by
    rw [ENNReal.toReal_sub_of_le]
    · simp
    · simpa using p.2.2
    · simp
  have hlast :
      ((Fin.last n - k : Fin (n + 1)) : ℕ) = n - (k : ℕ) := by
    rw [Fin.val_sub, Fin.val_last]
    omega
  simp [hq, hlast]

lemma integral_binomialRealMeasure
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (n : ℕ) (p : I) (f : ℝ → E) (hf : Continuous f) :
    (∫ z, f z ∂binomialRealMeasure n p) =
      ∑ k : Fin (n + 1), (binomialPMF n p k).toReal • f (k : ℝ) := by
  rw [binomialRealMeasure,
    integral_map Measurable.of_discrete.aemeasurable hf.aestronglyMeasurable]
  exact PMF.integral_eq_sum _ _

lemma integrable_binomialRealMeasure
    {E : Type*} [NormedAddCommGroup E]
    (n : ℕ) (p : I) (f : ℝ → E) (hf : Continuous f) :
    Integrable f (binomialRealMeasure n p) := by
  rw [binomialRealMeasure,
    integrable_map_measure hf.aestronglyMeasurable Measurable.of_discrete.aemeasurable]
  exact .of_finite

lemma charFun_map_cast_binomial (n : ℕ) (p : I) (t : ℝ) :
    charFun (binomialRealMeasure n p) t =
      (((1 - (p : ℝ) : ℝ) : ℂ) + (p : ℂ) * exp (t * Complex.I)) ^ n := by
  rw [charFun_apply_real,
    integral_binomialRealMeasure n p _ (by fun_prop)]
  rw [Fin.sum_univ_eq_sum_range]
  simp only [RCLike.real_smul_eq_coe_mul]
  conv_rhs => rw [add_comm]
  rw [add_pow]
  apply Finset.sum_congr rfl
  intro k hk
  rw [binomialPMF_apply_toReal]
  have hexp :
      exp ((t : ℂ) * (k : ℂ) * Complex.I) = exp ((t : ℂ) * Complex.I) ^ k := by
    calc
      exp ((t : ℂ) * (k : ℂ) * Complex.I) =
          exp ((k : ℂ) * ((t : ℂ) * Complex.I)) := by congr 1 <;> ring
      _ = exp ((t : ℂ) * Complex.I) ^ k := Complex.exp_nat_mul _ _
  rw [hexp]
  push_cast
  ring

end ProbabilityTheory
