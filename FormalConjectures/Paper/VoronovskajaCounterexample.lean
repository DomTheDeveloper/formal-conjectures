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

import FormalConjectures.Paper.VoronovskajaTypeFormula

/-!
# Counterexample for the formalized Bézier–Bernstein operator

The current definition samples `f (k / n)` using natural-number division. Consequently it is not
an approximation operator: for `0 < n`, the identity function vanishes at every sample except
`k = n`. At `α = 2` and `x = 1 / 2`, the scaled error tends to `-∞`, so it has no finite limit.
-/

open Topology Filter Real unitInterval Polynomial

namespace VoronovskajaTypeFormula

/-- In the current definition, `k / n` is natural-number division, followed by coercion to `ℝ`. -/
theorem bezierBernstein_uses_nat_division
    (n : ℕ) (α : ℝ) (f : ℝ → ℝ) (x : ℝ) :
    bezierBernstein n α f x =
      ∑ k ∈ Finset.range (n + 1),
        f ((k / n : ℕ) : ℝ) *
          ((bernsteinTail n k).eval x ^ α -
            (bernsteinTail n (k + 1)).eval x ^ α) := by
  rfl

/-- The last Bernstein tail is the last Bernstein basis polynomial. -/
theorem bernsteinTail_self_eval (n : ℕ) (x : ℝ) :
    (bernsteinTail n n).eval x = x ^ n := by
  simp [bernsteinTail, bernsteinPolynomial]

/-- The Bernstein tail starting strictly after `n` vanishes. -/
theorem bernsteinTail_succ_self (n : ℕ) : bernsteinTail n (n + 1) = 0 := by
  simp [bernsteinTail]

/-- Exact value of the currently formalized operator on the identity function. -/
theorem bezierBernstein_id_two_half (n : ℕ) (hn : 0 < n) :
    bezierBernstein n (2 : ℝ) id (1 / 2 : ℝ) = ((1 / 2 : ℝ) ^ n) ^ 2 := by
  rw [bezierBernstein]
  rw [Finset.sum_eq_single n]
  · simp [bernsteinTail_self_eval, bernsteinTail_succ_self, Nat.div_self hn.ne']
  · intro k hk hkn
    have hklt : k < n := by
      simp only [Finset.mem_range] at hk
      omega
    simp [Nat.div_eq_of_lt hklt]
  · simp

/-- The operator value on the identity function tends to zero. -/
theorem tendsto_bezierBernstein_id_two_half_zero :
    Tendsto (fun n : ℕ => bezierBernstein n (2 : ℝ) id (1 / 2 : ℝ)) atTop (𝓝 0) := by
  have hpow : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hsq : Tendsto (fun n : ℕ => ((1 / 2 : ℝ) ^ n) ^ 2) atTop (𝓝 0) := by
    simpa using hpow.pow 2
  apply hsq.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  exact bezierBernstein_id_two_half n hn

/-- The scaled error in the current formalization diverges to `-∞`. -/
theorem tendsto_voronovskaja_id_two_half_atBot :
    Tendsto
      (fun n : ℕ => Real.sqrt n *
        (bezierBernstein n (2 : ℝ) id (1 / 2 : ℝ) - id (1 / 2 : ℝ)))
      atTop atBot := by
  have hdiff : Tendsto
      (fun n : ℕ => bezierBernstein n (2 : ℝ) id (1 / 2 : ℝ) - (1 / 2 : ℝ))
      atTop (𝓝 (-1 / 2 : ℝ)) := by
    simpa using tendsto_bezierBernstein_id_two_half_zero.sub
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 / 2 : ℝ)) atTop (𝓝 (1 / 2 : ℝ)))
  have hsqrt : Tendsto (fun n : ℕ => Real.sqrt (n : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  simpa using hsqrt.atTop_mul_neg (by norm_num : (-1 / 2 : ℝ) < 0) hdiff

/-- Hence the sequence in the current formal conjecture has no finite real limit. -/
theorem not_tendsto_voronovskaja_id_two_half (L : ℝ) :
    ¬ Tendsto
      (fun n : ℕ => Real.sqrt n *
        (bezierBernstein n (2 : ℝ) id (1 / 2 : ℝ) - id (1 / 2 : ℝ)))
      atTop (𝓝 L) := by
  intro hL
  have hlt : ∀ᶠ n : ℕ in atTop,
      Real.sqrt n *
        (bezierBernstein n (2 : ℝ) id (1 / 2 : ℝ) - id (1 / 2 : ℝ)) < L - 1 :=
    tendsto_voronovskaja_id_two_half_atBot.eventually_lt_atBot (L - 1)
  have hgt : ∀ᶠ n : ℕ in atTop,
      L - 1 < Real.sqrt n *
        (bezierBernstein n (2 : ℝ) id (1 / 2 : ℝ) - id (1 / 2 : ℝ)) :=
    hL.eventually (Ioi_mem_nhds (by linarith : L - 1 < L))
  filter_upwards [hlt, hgt] with n hnlt hngt
  exact (not_lt_of_ge hngt.le) hnlt

end VoronovskajaTypeFormula
