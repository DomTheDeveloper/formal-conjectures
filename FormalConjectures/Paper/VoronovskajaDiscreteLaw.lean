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

/-!
# The discrete probability law of Bézier--Bernstein weights

This file packages the Bézier coefficients as a finite probability mass function and proves that,
after centering and normalization, their law is exactly the powered-survival transform of the
standardized binomial law. This is the discrete bridge between the operator formula and the
probability-limit infrastructure.
-/

import FormalConjectures.Paper.VoronovskajaProof
import FormalConjecturesForMathlib.Probability.Distributions.PoweredBinomialLimit
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.ProbabilityMassFunction.Integrals

open Topology Filter Real unitInterval Polynomial
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory Topology unitInterval

namespace VoronovskajaTypeFormula

private theorem sum_range_sub_succ (a : ℕ → ℝ) (m : ℕ) :
    ∑ k ∈ Finset.range m, (a k - a (k + 1)) = a 0 - a m := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_range_succ, ih]
      ring

private theorem sum_bezierWeight_range (n m : ℕ) (α x : ℝ) :
    ∑ k ∈ Finset.range m, bezierWeight n k α x =
      1 - (bernsteinTail n m).eval x ^ α := by
  rw [show (∑ k ∈ Finset.range m, bezierWeight n k α x) =
      ∑ k ∈ Finset.range m,
        ((bernsteinTail n k).eval x ^ α -
          (bernsteinTail n (k + 1)).eval x ^ α) by rfl]
  rw [sum_range_sub_succ]
  simp [bernsteinTail_zero]

noncomputable def bezierPMF
    (n : ℕ) (α : ℝ) (hα : 0 < α) (x : I) : PMF (Fin (n + 1)) :=
  PMF.ofFintype
    (fun k => ENNReal.ofReal (bezierWeight n k α (x : ℝ)))
    (by
      have hnonneg : ∀ k : Fin (n + 1),
          0 ≤ bezierWeight n k α (x : ℝ) := by
        intro k
        exact bezierWeight_nonneg n k (Nat.le_of_lt_succ k.isLt) hα x.property
      calc
        ∑ k : Fin (n + 1), ENNReal.ofReal (bezierWeight n k α (x : ℝ)) =
            ENNReal.ofReal (∑ k : Fin (n + 1), bezierWeight n k α (x : ℝ)) := by
          symm
          simpa only [Finset.sum_univ] using
            (ENNReal.ofReal_sum_of_nonneg (s := Finset.univ)
              (f := fun k : Fin (n + 1) => bezierWeight n k α (x : ℝ))
              (fun k _ => hnonneg k))
        _ = ENNReal.ofReal 1 := by
          congr 1
          rw [Fin.sum_univ_eq_sum_range]
          exact sum_bezierWeight n hα (x : ℝ)
        _ = 1 := by simp)

@[simp] theorem bezierPMF_apply
    (n : ℕ) (α : ℝ) (hα : 0 < α) (x : I) (k : Fin (n + 1)) :
    bezierPMF n α hα x k = ENNReal.ofReal (bezierWeight n k α (x : ℝ)) := by
  rfl

noncomputable def standardizedBezierPMF
    (n : ℕ) (α : ℝ) (hα : 0 < α) (x : I) : PMF ℝ :=
  (bezierPMF n α hα x).map
    (fun k => standardizeBinomial n x ((k : ℕ) : ℝ))

noncomputable def standardizedBezierMeasure
    (n : ℕ) (α : ℝ) (hα : 0 < α) (x : I) : Measure ℝ :=
  (standardizedBezierPMF n α hα x).toMeasure

instance (n : ℕ) (α : ℝ) (hα : 0 < α) (x : I) :
    IsProbabilityMeasure (standardizedBezierMeasure n α hα x) := by
  unfold standardizedBezierMeasure
  infer_instance

private theorem monotone_standardizeBinomial_nat (n : ℕ) (x : I) :
    Monotone (fun k : ℕ => standardizeBinomial n x (k : ℝ)) := by
  intro a b hab
  unfold standardizeBinomial
  have hsqrt : 0 ≤ (Real.sqrt (n : ℝ))⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg _)
  have hsd : 0 ≤ (bernoulliStdDev x)⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg _)
  rw [div_eq_mul_inv, div_eq_mul_inv]
  apply mul_le_mul_of_nonneg_left _ hsqrt
  apply mul_le_mul_of_nonneg_right _ hsd
  exact sub_le_sub_right (Nat.cast_le.mpr hab) _

private theorem exists_filter_range_eq_range_of_antitone
    (P : ℕ → Prop) [DecidablePred P]
    (hP : ∀ ⦃i j⦄, i ≤ j → P j → P i) :
    ∀ N : ℕ, ∃ m ≤ N, (Finset.range N).filter P = Finset.range m := by
  intro N
  induction N with
  | zero => exact ⟨0, le_rfl, by simp⟩
  | succ N ih =>
      by_cases hN : P N
      · refine ⟨N + 1, le_rfl, ?_⟩
        apply Finset.filter_eq_self.2
        intro i hi
        exact hP (Nat.le_of_lt_succ (Finset.mem_range.mp hi)) hN
      · obtain ⟨m, hm, hfilter⟩ := ih
        refine ⟨m, hm.trans (Nat.le_succ N), ?_⟩
        simp [Finset.range_succ, hN, hfilter]

private theorem cdf_pmf_map_eq_sum
    {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (p : PMF ι) (g : ι → ℝ) (hg : Measurable g) (t : ℝ) :
    cdf ((p.map g).toMeasure) t =
      ∑ i : ι, if g i ≤ t then (p i).toReal else 0 := by
  rw [cdf_eq_real, measureReal_def]
  rw [PMF.toMeasure_map_apply g p (Set.Iic t) hg measurableSet_Iic]
  rw [PMF.toMeasure_apply_fintype, ENNReal.toReal_sum]
  · apply Finset.sum_congr rfl
    intro i hi
    by_cases hit : g i ≤ t <;> simp [hit]
  · intro i hi
    by_cases hit : g i ≤ t <;> simp [hit, p.apply_ne_top]

private theorem binomialPMF_toReal_eq_bernstein
    (n : ℕ) (x : I) (k : Fin (n + 1)) :
    ((binomialPMF n x) k).toReal =
      (bernsteinPolynomial ℝ n k).eval (x : ℝ) := by
  simp only [binomialPMF, PMF.binomial_apply, bernsteinPolynomial,
    Polynomial.eval_mul, Polynomial.eval_natCast, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_sub, Polynomial.eval_one]
  have hq : ((1 : ℝ≥0∞) - (toNNReal x : ℝ≥0∞)).toReal = 1 - (x : ℝ) := by
    rw [ENNReal.toReal_sub_of_le]
    · simp
    · simpa using x.2.2
    · simp
  simp [hq]
  ring

private theorem standardizedBinomialMeasure_eq_pmf_map
    (n : ℕ) (x : I) :
    standardizedBinomialMeasure n x =
      ((binomialPMF n x).map
        (fun k => standardizeBinomial n x ((k : ℕ) : ℝ))).toMeasure := by
  have hval : Measurable (Fin.val : Fin (n + 1) → ℕ) := .of_discrete
  have hcast : Measurable (Nat.cast : ℕ → ℝ) := .of_discrete
  have hstd : Measurable (standardizeBinomial n x) :=
    (continuous_standardizeBinomial n x).measurable
  rw [standardizedBinomialMeasure]
  change ((Bin(n, x).map (Nat.cast : ℕ → ℝ)).map (standardizeBinomial n x)) = _
  rw [binomial_eq_binomialPMF_toMeasure_map_val]
  rw [Measure.map_map hstd hcast]
  rw [Measure.map_map (hstd.comp hcast) hval]
  simpa [Function.comp_def] using
    (PMF.toMeasure_map (p := binomialPMF n x)
      (f := fun k : Fin (n + 1) =>
        standardizeBinomial n x ((k : ℕ) : ℝ)) (.of_discrete))

private theorem cdf_standardizedBezierMeasure_eq_sum
    (n : ℕ) (α : ℝ) (hα : 0 < α) (x : I) (t : ℝ) :
    cdf (standardizedBezierMeasure n α hα x) t =
      ∑ k : Fin (n + 1),
        if standardizeBinomial n x ((k : ℕ) : ℝ) ≤ t then
          bezierWeight n k α (x : ℝ)
        else 0 := by
  rw [standardizedBezierMeasure, standardizedBezierPMF,
    cdf_pmf_map_eq_sum (bezierPMF n α hα x)
      (fun k => standardizeBinomial n x ((k : ℕ) : ℝ)) Measurable.of_discrete]
  apply Finset.sum_congr rfl
  intro k hk
  by_cases hkt : standardizeBinomial n x ((k : ℕ) : ℝ) ≤ t
  · simp [hkt, bezierPMF_apply, ENNReal.toReal_ofReal,
      bezierWeight_nonneg n k (Nat.le_of_lt_succ k.isLt) hα x.property]
  · simp [hkt]

private theorem cdf_standardizedBinomialMeasure_eq_sum
    (n : ℕ) (x : I) (t : ℝ) :
    cdf (standardizedBinomialMeasure n x) t =
      ∑ k : Fin (n + 1),
        if standardizeBinomial n x ((k : ℕ) : ℝ) ≤ t then
          (bernsteinPolynomial ℝ n k).eval (x : ℝ)
        else 0 := by
  rw [standardizedBinomialMeasure_eq_pmf_map,
    cdf_pmf_map_eq_sum (binomialPMF n x)
      (fun k => standardizeBinomial n x ((k : ℕ) : ℝ)) Measurable.of_discrete]
  apply Finset.sum_congr rfl
  intro k hk
  by_cases hkt : standardizeBinomial n x ((k : ℕ) : ℝ) ≤ t
  · simp [hkt, binomialPMF_toReal_eq_bernstein]
  · simp [hkt]

private theorem sum_bernsteinPolynomial_range
    (n m : ℕ) (hm : m ≤ n + 1) (x : ℝ) :
    ∑ k ∈ Finset.range m, (bernsteinPolynomial ℝ n k).eval x =
      1 - (bernsteinTail n m).eval x := by
  calc
    (∑ k ∈ Finset.range m, (bernsteinPolynomial ℝ n k).eval x) =
        ∑ k ∈ Finset.range m,
          ((bernsteinTail n k).eval x - (bernsteinTail n (k + 1)).eval x) := by
      apply Finset.sum_congr rfl
      intro k hk
      have hkn : k ≤ n := Nat.le_of_lt_succ <| (Finset.mem_range.mp hk).trans_le hm
      rw [bernsteinTail_eval_eq_bernstein_add_succ n k hkn x]
      ring
    _ = 1 - (bernsteinTail n m).eval x := by
      rw [sum_range_sub_succ]
      simp [bernsteinTail_zero]

private theorem exists_common_cdf_cutoff
    (n : ℕ) (x : I) (t : ℝ) :
    ∃ m ≤ n + 1,
      cdf (standardizedBinomialMeasure n x) t =
          1 - (bernsteinTail n m).eval (x : ℝ) ∧
      ∀ (α : ℝ) (hα : 0 < α),
        cdf (standardizedBezierMeasure n α hα x) t =
          1 - (bernsteinTail n m).eval (x : ℝ) ^ α := by
  let P : ℕ → Prop := fun k => standardizeBinomial n x (k : ℝ) ≤ t
  have hP : ∀ ⦃i j⦄, i ≤ j → P j → P i := by
    intro i j hij hj
    exact (monotone_standardizeBinomial_nat n x hij).trans hj
  obtain ⟨m, hm, hfilter⟩ :=
    exists_filter_range_eq_range_of_antitone P hP (n + 1)
  refine ⟨m, hm, ?_, ?_⟩
  · rw [cdf_standardizedBinomialMeasure_eq_sum]
    change (∑ k : Fin (n + 1),
      if P k then (bernsteinPolynomial ℝ n k).eval (x : ℝ) else 0) = _
    rw [Fin.sum_univ_eq_sum_range]
    rw [← Finset.sum_filter]
    rw [hfilter]
    exact sum_bernsteinPolynomial_range n m hm (x : ℝ)
  · intro α hα
    rw [cdf_standardizedBezierMeasure_eq_sum]
    change (∑ k : Fin (n + 1), if P k then bezierWeight n k α (x : ℝ) else 0) = _
    rw [Fin.sum_univ_eq_sum_range]
    rw [← Finset.sum_filter]
    rw [hfilter]
    exact sum_bezierWeight_range n m α (x : ℝ)

@[category API, AMS 26 40 47]
theorem cdf_standardizedBezierMeasure
    (n : ℕ) (α : ℝ) (hα : 0 < α) (x : I) (t : ℝ) :
    cdf (standardizedBezierMeasure n α hα x) t =
      1 - (1 - cdf (standardizedBinomialMeasure n x) t) ^ α := by
  obtain ⟨m, hm, hbase, hbezier⟩ := exists_common_cdf_cutoff n x t
  rw [hbezier α hα, hbase]
  simp

@[category API, AMS 26 40 47]
theorem standardizedBezierMeasure_eq_poweredStandardizedBinomial
    (n : ℕ) (α : ℝ) (hα : 0 < α) (x : I) :
    standardizedBezierMeasure n α hα x =
      (poweredStandardizedBinomialProbability n x α hα : Measure ℝ) := by
  apply Measure.eq_of_cdf
  funext t
  rw [cdf_standardizedBezierMeasure]
  simp only [poweredStandardizedBinomialProbability, poweredProbability,
    ProbabilityMeasure.coe_mk, cdf_poweredMeasure, poweredCDF_apply]

end VoronovskajaTypeFormula
