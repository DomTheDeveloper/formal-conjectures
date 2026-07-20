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

public import FormalConjectures.Paper.VoronovskajaRemainder
public import Mathlib.Analysis.SpecialFunctions.Bernstein

/-!
# Exact moments in the classical Bernstein case

At shape parameter one, the Bézier differences are exactly the ordinary Bernstein basis weights.
The first centered moment vanishes and the second centered moment is `x(1-x)/n`.
-/

public section

noncomputable section

open Topology Filter Real unitInterval Polynomial
open Set
open scoped unitInterval

namespace VoronovskajaTypeFormula

lemma bezierWeight_one_eq_bernsteinPolynomial
    (n k : ℕ) (hk : k ≤ n) (x : ℝ) :
    bezierWeight n k 1 x = (bernsteinPolynomial ℝ n k).eval x := by
  rw [bezierWeight, Real.rpow_one, Real.rpow_one,
    bernsteinTail_eval_eq_bernstein_add_succ n k hk x]
  ring

private lemma sum_cast_mul_bernsteinPolynomial_eval
    (n : ℕ) (x : ℝ) :
    ∑ k ∈ Finset.range (n + 1),
      (k : ℝ) * (bernsteinPolynomial ℝ n k).eval x = (n : ℝ) * x := by
  calc
    (∑ k ∈ Finset.range (n + 1),
        (k : ℝ) * (bernsteinPolynomial ℝ n k).eval x) =
        (∑ k ∈ Finset.range (n + 1),
          k • bernsteinPolynomial ℝ n k).eval x := by
      rw [Polynomial.eval_finset_sum]
      apply Finset.sum_congr rfl
      intro k hk
      simp [nsmul_eq_mul]
    _ = (n • Polynomial.X : Polynomial ℝ).eval x := by
      rw [bernsteinPolynomial.sum_smul]
    _ = (n : ℝ) * x := by
      simp [nsmul_eq_mul]

lemma bezierCenteredMoment_one_eq_zero
    (n : ℕ) (hn : 0 < n) (x : ℝ) :
    bezierCenteredMoment n 1 x = 0 := by
  rw [bezierCenteredMoment]
  simp_rw [sub_mul, div_mul_eq_mul_div]
  rw [Finset.sum_sub_distrib, ← Finset.sum_div, ← Finset.mul_sum,
    sum_bezierWeight n one_pos x, mul_one]
  have hweights :
      ∑ k ∈ Finset.range (n + 1), (k : ℝ) * bezierWeight n k 1 x =
        (n : ℝ) * x := by
    calc
      ∑ k ∈ Finset.range (n + 1), (k : ℝ) * bezierWeight n k 1 x =
          ∑ k ∈ Finset.range (n + 1),
            (k : ℝ) * (bernsteinPolynomial ℝ n k).eval x := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [bezierWeight_one_eq_bernsteinPolynomial n k
          (Nat.le_of_lt_succ (Finset.mem_range.mp hk)) x]
      _ = (n : ℝ) * x := sum_cast_mul_bernsteinPolynomial_eval n x
  rw [hweights]
  field_simp [show (n : ℝ) ≠ 0 by exact_mod_cast hn.ne']
  ring

lemma sum_sq_centered_bezierWeight_one
    (n : ℕ) (hn : 0 < n) (x : I) :
    ∑ k ∈ Finset.range (n + 1),
      ((((k : ℝ) / (n : ℝ)) - (x : ℝ)) ^ 2) *
        bezierWeight n k 1 (x : ℝ) =
      (x : ℝ) * (1 - (x : ℝ)) / (n : ℝ) := by
  have hvar := bernstein.variance hn.ne' x
  have hfin :
      (∑ k : Fin (n + 1),
        ((((k : ℝ) / (n : ℝ)) - (x : ℝ)) ^ 2) *
          bezierWeight n (k : ℕ) 1 (x : ℝ)) =
        (x : ℝ) * (1 - (x : ℝ)) / (n : ℝ) := by
    calc
      (∑ k : Fin (n + 1),
          ((((k : ℝ) / (n : ℝ)) - (x : ℝ)) ^ 2) *
            bezierWeight n (k : ℕ) 1 (x : ℝ)) =
          ∑ k : Fin (n + 1),
            ((x : ℝ) - (bernstein.z k : ℝ)) ^ 2 * bernstein n k x := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [bezierWeight_one_eq_bernsteinPolynomial n (k : ℕ) k.is_le]
        change
          (((k : ℝ) / (n : ℝ) - (x : ℝ)) ^ 2) *
              (bernsteinPolynomial ℝ n (k : ℕ)).eval (x : ℝ) =
            ((x : ℝ) - (bernstein.z k : ℝ)) ^ 2 *
              (bernsteinPolynomial ℝ n (k : ℕ)).eval (x : ℝ)
        simp only [bernstein.z]
        ring
      _ = (x : ℝ) * (1 - (x : ℝ)) / (n : ℝ) := hvar
  rw [Fin.sum_univ_eq_sum_range] at hfin
  simpa using hfin

end VoronovskajaTypeFormula
