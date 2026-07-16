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
# Finite binomial PMFs and their characteristic function

Mathlib already defines the canonical binomial measures `Bin(n, p)` and `Bin(R, n, p)`, together
with their probability-measure instances and finite-sum integral formula.  This file adds the finite
`Fin (n + 1)` PMF alias used by the Bézier-law calculation, proves that its pushforward is the
canonical measure, and records the characteristic function of the real-valued binomial measure.
-/

public section

open MeasureTheory Measure Complex unitInterval
open scoped unitInterval ENNReal ProbabilityTheory

namespace ProbabilityTheory

/-- The finite binomial PMF on `Fin (n + 1)`. -/
@[expose]
noncomputable def binomialPMF (n : ℕ) (p : I) : PMF (Fin (n + 1)) :=
  PMF.binomial (toNNReal p) (by simpa using p.2.2) n

/-- The canonical binomial measure is the pushforward of the finite binomial PMF by `Fin.val`. -/
lemma binomial_eq_binomialPMF_toMeasure_map_val (n : ℕ) (p : I) :
    Bin(n, p) = (binomialPMF n p).toMeasure.map (Fin.val : Fin (n + 1) → ℕ) := by
  refine ext_of_singleton fun k ↦ ?_
  rw [binomial_singleton]
  rw [Measure.map_apply (.of_discrete : Measurable (Fin.val : Fin (n + 1) → ℕ))
    (measurableSet_singleton k)]
  by_cases hk : k ≤ n
  · let i : Fin (n + 1) := ⟨k, Nat.lt_succ_iff.mpr hk⟩
    have hpre : (Fin.val : Fin (n + 1) → ℕ) ⁻¹' ({k} : Set ℕ) = {i} := by
      ext j
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      constructor
      · intro h
        apply Fin.ext
        simpa [i] using h
      · intro h
        subst j
        simp [i]
    rw [hpre, (binomialPMF n p).toMeasure_apply_singleton i (measurableSet_singleton i)]
    have hi : (Fin.ofNat (n + 1) k : Fin (n + 1)) = i := by
      apply Fin.ext
      simp [i, Nat.mod_eq_of_lt (Nat.lt_succ_iff.mpr hk)]
    simpa [binomialPMF, hi] using
      (PMF.binomial_apply_of_le hk (by simpa using p.2.2))
  · have hnk : n < k := Nat.lt_of_not_ge hk
    have hpre : (Fin.val : Fin (n + 1) → ℕ) ⁻¹' ({k} : Set ℕ) = ∅ := by
      ext i
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.not_mem_empty, iff_false]
      intro hi
      apply hk
      have hik : k < n + 1 := by simpa [hi] using i.isLt
      exact Nat.lt_succ_iff.mp hik
    rw [hpre]
    simp [Nat.choose_eq_zero_of_lt hnk]

lemma charFun_map_cast_binomial (n : ℕ) (p : I) (t : ℝ) :
    charFun Bin(ℝ, n, p) t =
      (((1 - (p : ℝ) : ℝ) : ℂ) + (p : ℂ) * exp (t * Complex.I)) ^ n := by
  rw [charFun_apply_real, integral_map_cast_binomial]
  rw [show Finset.Iic n = Finset.range (n + 1) by ext k; simp]
  simp only [RCLike.real_smul_eq_coe_mul]
  conv_rhs => rw [add_comm]
  rw [add_pow]
  apply Finset.sum_congr rfl
  intro k hk
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
