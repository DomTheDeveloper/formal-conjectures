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
    mgf id (binomialRealMeasure n p) t =
      ((1 - (p : ℝ)) + (p : ℝ) * exp t) ^ n := by
  rw [mgf, integral_binomialRealMeasure n p _ (by fun_prop), Finset.sum_fin_eq_sum_range]
  simp only [smul_eq_mul]
  conv_rhs => rw [add_comm]
  rw [add_pow]
  apply Finset.sum_congr rfl
  intro k hk
  rw [dif_pos (Finset.mem_range.mp hk), binomialPMF_apply_toReal]
  have hexp : exp (t * (k : ℝ)) = exp t ^ k := by
    calc
      exp (t * (k : ℝ)) = exp ((k : ℝ) * t) := by congr 1 <;> ring
      _ = exp t ^ k := Real.exp_nat_mul _ _
  change
    (p : ℝ) ^ k * (1 - (p : ℝ)) ^ (n - k) * (n.choose k : ℝ) * exp (t * (k : ℝ)) =
      ((p : ℝ) * exp t) ^ k * (1 - (p : ℝ)) ^ (n - k) * (n.choose k : ℝ)
  rw [hexp, mul_pow]
  ring

/-- Exact MGF of one standardized Bernoulli variable. -/
lemma mgf_standardizedBernoulli (p : I) (t : ℝ) :
    mgf (standardizedBernoulli p) Ber((1 : ℝ), 0, p) t =
      (p : ℝ) * exp (t * ((1 - (p : ℝ)) / bernoulliStdDev p)) +
        (1 - (p : ℝ)) * exp (t * (-(p : ℝ) / bernoulliStdDev p)) := by
  rw [mgf, integral_bernoulliMeasure]
  simp only [smul_eq_mul, standardizedBernoulli]
  congr 1 <;> ring_nf

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
  change mgf id (binomialRealMeasure n p) a * exp (-(a * (n * (p : ℝ)))) =
    (mgf (standardizedBernoulli p) Ber((1 : ℝ), 0, p) s) ^ n
  rw [mgf_map_cast_binomial, mgf_standardizedBernoulli]
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
  exact integrable_binomialRealMeasure n p _ (by fun_prop)

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
            exact pow_le_pow_left₀ mgf_nonneg (hB.mgf_le s) n
      _ = exp ((c : ℝ) * t ^ 2 / 2) := by
        rw [← Real.exp_nat_mul]
        congr 1
        push_cast
        rw [← hscale]
        ring

end ProbabilityTheory
