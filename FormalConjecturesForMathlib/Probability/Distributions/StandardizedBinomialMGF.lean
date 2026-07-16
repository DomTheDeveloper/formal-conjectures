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

public import FormalConjecturesForMathlib.Probability.Distributions.StandardizedBinomialTails

/-!
# Moment-generating functions of standardized binomial laws

The standardized binomial MGF is the `n`th power of the standardized Bernoulli MGF evaluated at
`t / sqrt n`.  Combining this exact identity with Hoeffding's lemma gives a sub-Gaussian parameter
which is uniform in the number of trials.
-/

public section

noncomputable section

open MeasureTheory Measure ProbabilityTheory Real unitInterval
open scoped ENNReal NNReal ProbabilityTheory Topology unitInterval

namespace ProbabilityTheory

/-- Exact moment-generating function of the real-valued binomial law. -/
lemma mgf_map_cast_binomial (n : ℕ) (p : I) (t : ℝ) :
    mgf id Bin(ℝ, n, p) t =
      ((1 - (p : ℝ)) + (p : ℝ) * exp t) ^ n := by
  rw [mgf]
  change (∫ x : ℝ, exp (t * x) ∂((binomial n p).map (Nat.cast : ℕ → ℝ))) = _
  have hcast : AEMeasurable (Nat.cast : ℕ → ℝ) (binomial n p) :=
    (.of_discrete : Measurable (Nat.cast : ℕ → ℝ)).aemeasurable
  have hexpNat : AEStronglyMeasurable (fun x : ℝ ↦ exp (t * x))
      ((binomial n p).map (Nat.cast : ℕ → ℝ)) := by fun_prop
  rw [integral_map hcast hexpNat]
  have hval : AEMeasurable (Fin.val : Fin (n + 1) → ℕ) (binomialPMF n p).toMeasure :=
    (.of_discrete : Measurable (Fin.val : Fin (n + 1) → ℕ)).aemeasurable
  have hexpFin : AEStronglyMeasurable (fun x : ℕ ↦ exp (t * (x : ℝ)))
      ((binomialPMF n p).toMeasure.map Fin.val) := by fun_prop
  rw [binomial, integral_map hval hexpFin]
  have hsum :
      (∫ x : Fin (n + 1), exp (t * ((x : ℕ) : ℝ)) ∂(binomialPMF n p).toMeasure) =
        ∑ x : Fin (n + 1), ((binomialPMF n p) x).toReal •
          exp (t * ((x : ℕ) : ℝ)) :=
    PMF.integral_eq_sum (binomialPMF n p) (fun x : Fin (n + 1) ↦
      exp (t * ((x : ℕ) : ℝ)))
  rw [hsum]
  simp only [binomialPMF, PMF.binomial_apply, Finset.sum_fin_eq_sum_range]
  have hq : ((1 : ℝ≥0∞) - (toNNReal p : ℝ≥0∞)).toReal = 1 - (p : ℝ) := by
    rw [ENNReal.toReal_sub_of_le]
    · simp
    · simpa using p.2.2
    · simp
  conv_rhs => rw [add_comm]
  rw [add_pow]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k < n + 1 := Finset.mem_range.mp hk
  simp only [dif_pos hk', Fin.val_last]
  have hexp : exp (t * (k : ℝ)) = exp t ^ k := by
    calc
      exp (t * (k : ℝ)) = exp ((k : ℝ) * t) := by congr 1 <;> ring
      _ = exp t ^ k := Real.exp_nat_mul _ _
  simp [hq, smul_eq_mul, hexp]
  ring

/-- Exact MGF of one standardized Bernoulli variable. -/
lemma mgf_standardizedBernoulli (p : I) (t : ℝ) :
    mgf (standardizedBernoulli p) Ber((1 : ℝ), 0, p) t =
      (p : ℝ) * exp (t * ((1 - (p : ℝ)) / bernoulliStdDev p)) +
        (1 - (p : ℝ)) * exp (t * (-(p : ℝ) / bernoulliStdDev p)) := by
  rw [mgf, integral_bernoulliMeasure]
  simp only [smul_eq_mul, standardizedBernoulli, sub_zero, zero_sub]
  congr 1 <;> ring

/-- The standardized binomial MGF is an `n`th power of the standardized Bernoulli MGF. -/
lemma mgf_standardizedBinomialMeasure (n : ℕ) (p : I) (t : ℝ) :
    mgf id (standardizedBinomialMeasure n p) t =
      (mgf (standardizedBernoulli p) Ber((1 : ℝ), 0, p)
        ((Real.sqrt n)⁻¹ * t)) ^ n := by
  let s : ℝ := (Real.sqrt n)⁻¹ * t
  let a : ℝ := s / bernoulliStdDev p
  rw [standardizedBinomialMeasure, mgf_id_map (continuous_standardizeBinomial n p).aemeasurable]
  rw [mgf]
  have hsplit (z : ℝ) :
      exp (t * standardizeBinomial n p z) =
        exp (a * z) * exp (-(a * (n * (p : ℝ)))) := by
    rw [← exp_add]
    congr 1
    rw [standardizeBinomial]
    dsimp [a, s]
    push_cast
    ring
  simp_rw [hsplit]
  rw [integral_mul_const]
  have hbin := mgf_map_cast_binomial n p a
  rw [mgf] at hbin
  rw [hbin, mgf_standardizedBernoulli]
  have hfactor :
      (p : ℝ) * exp (s * ((1 - (p : ℝ)) / bernoulliStdDev p)) +
          (1 - (p : ℝ)) * exp (s * (-(p : ℝ) / bernoulliStdDev p)) =
        ((1 - (p : ℝ)) + (p : ℝ) * exp a) * exp (-(a * (p : ℝ))) := by
    have hexp :
        exp (s * ((1 - (p : ℝ)) / bernoulliStdDev p)) =
          exp a * exp (-(a * (p : ℝ))) := by
      rw [← exp_add]
      congr 1
      dsimp [a]
      ring
    have hneg :
        exp (s * (-(p : ℝ) / bernoulliStdDev p)) =
          exp (-(a * (p : ℝ))) := by
      congr 1
      dsimp [a]
      ring
    rw [hexp, hneg]
    ring
  rw [hfactor, mul_pow]
  congr 1
  calc
    exp (-(a * (n * (p : ℝ)))) =
        exp ((n : ℝ) * (-(a * (p : ℝ)))) := by
          congr 1
          push_cast
          ring
    _ = exp (-(a * (p : ℝ))) ^ n := Real.exp_nat_mul _ _

private lemma integrable_exp_mul_standardizedBinomialMeasure
    (n : ℕ) (p : I) (t : ℝ) :
    Integrable (fun z : ℝ ↦ exp (t * z)) (standardizedBinomialMeasure n p) := by
  rw [standardizedBinomialMeasure]
  rw [integrable_map_measure (by fun_prop) (continuous_standardizeBinomial n p).aemeasurable]
  change Integrable
    (fun z : ℝ ↦ exp (t * standardizeBinomial n p z))
    ((binomial n p).map (Nat.cast : ℕ → ℝ))
  rw [integrable_map_measure (by fun_prop)
    ((.of_discrete : Measurable (Nat.cast : ℕ → ℝ)).aemeasurable)]
  rw [binomial]
  rw [integrable_map_measure (by fun_prop)
    ((.of_discrete : Measurable (Fin.val : Fin (n + 1) → ℕ)).aemeasurable)]
  exact .of_finite

/-- For positive `n`, standardized binomial laws have a sub-Gaussian parameter independent of
`n`. -/
lemma hasSubgaussianMGF_standardizedBinomialMeasure
    (n : ℕ) (hn : 0 < n) (p : I) (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    HasSubgaussianMGF id (standardizedBernoulliSubgaussianParameter p)
      (standardizedBinomialMeasure n p) := by
  let c := standardizedBernoulliSubgaussianParameter p
  have hB : HasSubgaussianMGF (standardizedBernoulli p) c Ber((1 : ℝ), 0, p) :=
    hasSubgaussianMGF_standardizedBernoulli p hp0 hp1
  constructor
  · exact integrable_exp_mul_standardizedBinomialMeasure n p
  · intro t
    rw [mgf_standardizedBinomialMeasure]
    let s : ℝ := (Real.sqrt n)⁻¹ * t
    have hsqrt : Real.sqrt n ≠ 0 := by
      rw [Real.sqrt_ne_zero']
      exact_mod_cast hn
    have hscale : (n : ℝ) * s ^ 2 = t ^ 2 := by
      dsimp [s]
      rw [inv_mul_eq_div]
      field_simp [hsqrt]
      rw [Real.sq_sqrt]
      · ring
      · positivity
    calc
      (mgf (standardizedBernoulli p) Ber((1 : ℝ), 0, p) s) ^ n ≤
          (exp ((c : ℝ) * s ^ 2 / 2)) ^ n := by
            gcongr
            exact hB.mgf_le s
      _ = exp ((c : ℝ) * t ^ 2 / 2) := by
        rw [← Real.exp_nat_mul]
        congr 1
        push_cast
        rw [← hscale]
        ring

end ProbabilityTheory
