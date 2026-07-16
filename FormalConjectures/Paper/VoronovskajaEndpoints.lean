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

import FormalConjectures.Paper.VoronovskajaProof

/-!
# Endpoint cases of the Bézier--Bernstein asymptotic

At the two endpoints the operator is exact: at zero every mass is concentrated at the zeroth
sampling point, while at one every positive-degree operator is concentrated at its final sampling
point. Consequently the scaled approximation error vanishes identically there.
-/

open Topology Filter Real unitInterval Polynomial

namespace VoronovskajaTypeFormula

/-- Every Bernstein tail starting at a positive index vanishes at zero. -/
@[category API, AMS 26 40 47]
theorem bernsteinTail_eval_zero_of_pos (n k : ℕ) (hk : 0 < k) :
    (bernsteinTail n k).eval 0 = 0 := by
  rw [bernsteinTail_eval_eq_sum]
  apply Finset.sum_eq_zero
  intro j hj
  have hjpos : 0 < j := hk.trans_le (Finset.mem_Icc.mp hj).1
  simp [hjpos.ne']

/-- A Bernstein tail whose starting index is at most `n` equals one at the right endpoint. -/
@[category API, AMS 26 40 47]
theorem bernsteinTail_eval_one_of_le (n k : ℕ) (hk : k ≤ n) :
    (bernsteinTail n k).eval 1 = 1 := by
  rw [bernsteinTail_eval_eq_sum, Finset.sum_eq_single n]
  · simp
  · intro j hj hjn
    have hjle : j ≤ n := (Finset.mem_Icc.mp hj).2
    have hjlt : j < n := lt_of_le_of_ne hjle hjn
    have hsub : 0 < n - j := Nat.sub_pos_of_lt hjlt
    simp [hsub.ne']
  · simp [hk]

/-- The Bézier--Bernstein operator reproduces the value at zero exactly. -/
@[category API, AMS 26 40 47]
theorem bezierBernstein_zero (n : ℕ) {α : ℝ} (hα : 0 < α) (f : ℝ → ℝ) :
    bezierBernstein n α f 0 = f 0 := by
  rw [bezierBernstein_uses_real_division, Finset.sum_eq_single 0]
  · simp [bernsteinTail_zero, bernsteinTail_eval_zero_of_pos n 1 (by omega), hα.ne']
  · intro k hk hk0
    have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
    have hksucc : 0 < k + 1 := by omega
    simp [bernsteinTail_eval_zero_of_pos n k hkpos,
      bernsteinTail_eval_zero_of_pos n (k + 1) hksucc, hα.ne']
  · simp

/-- Every positive-degree Bézier--Bernstein operator reproduces the value at one exactly. -/
@[category API, AMS 26 40 47]
theorem bezierBernstein_one (n : ℕ) (hn : 0 < n) {α : ℝ} (hα : 0 < α) (f : ℝ → ℝ) :
    bezierBernstein n α f 1 = f 1 := by
  rw [bezierBernstein_uses_real_division, Finset.sum_eq_single n]
  · have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    simp [bernsteinTail_eval_one_of_le n n le_rfl, bernsteinTail_succ_self,
      hα.ne', hn0]
  · intro k hk hkn
    have hkle : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
    have hklt : k < n := lt_of_le_of_ne hkle hkn
    have hksucc : k + 1 ≤ n := Nat.succ_le_iff.mpr hklt
    simp [bernsteinTail_eval_one_of_le n k hklt.le,
      bernsteinTail_eval_one_of_le n (k + 1) hksucc]
  · simp

/-- The scaled approximation error is identically zero at the left endpoint. -/
@[category API, AMS 26 40 47]
theorem tendsto_bezierBernstein_zero
    {α : ℝ} (hα : 0 < α) (f : ℝ → ℝ) :
    Tendsto (fun n : ℕ ↦ Real.sqrt n * (bezierBernstein n α f 0 - f 0)) atTop (𝓝 0) := by
  simp [bezierBernstein_zero _ hα f]

/-- The scaled approximation error tends to zero at the right endpoint. -/
@[category API, AMS 26 40 47]
theorem tendsto_bezierBernstein_one
    {α : ℝ} (hα : 0 < α) (f : ℝ → ℝ) :
    Tendsto (fun n : ℕ ↦ Real.sqrt n * (bezierBernstein n α f 1 - f 1)) atTop (𝓝 0) := by
  apply tendsto_atTop_of_eventually_const (i₀ := 1)
  intro n hn
  have hnpos : 0 < n := by omega
  simp [bezierBernstein_one n hnpos hα f]

end VoronovskajaTypeFormula
