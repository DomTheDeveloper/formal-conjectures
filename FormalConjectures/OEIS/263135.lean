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

import FormalConjecturesUtil

/-!
# Maximum contacts on the honeycomb lattice

This work-in-progress file records the exact arithmetic reduction for the
conjecture associated with OEIS A263135.  The remaining theorem is the
edge-isoperimetric characterization of finite vertex sets in the infinite
honeycomb graph; it is not hidden behind an axiom or a weakened definition.

*References:*
- [A263135](https://oeis.org/A263135)
- [A047932](https://oeis.org/A047932)
- [A216256](https://oeis.org/A216256)
- Berit Grußien, ["Isoperimetric Inequalities on Hexagonal Grids"](https://arxiv.org/abs/1201.0697)
-/

namespace OeisA263135

/-- Integer interval characterizing `ceil (sqrt x)` for positive `x`. -/
def IsCeilSqrt (x r : ℤ) : Prop :=
  0 ≤ r ∧ (r - 1) ^ 2 < x ∧ x ≤ r ^ 2

/-- Integer interval characterizing A216256 at positive index `n`. -/
def IsA216256Index (n k : ℤ) : Prop :=
  0 ≤ k ∧ k ^ 2 - k + 1 < 3 * n ∧ 3 * n ≤ k ^ 2 + k + 1

private lemma isCeilSqrt_unique {x a b : ℤ} (hx : 0 < x)
    (ha : IsCeilSqrt x a) (hb : IsCeilSqrt x b) : a = b := by
  rcases ha with ⟨ha0, haLower, haUpper⟩
  rcases hb with ⟨hb0, hbLower, hbUpper⟩
  by_contra hne
  rcases lt_or_gt_of_ne hne with hab | hba
  · have hb1 : 1 ≤ b := by
      by_contra h
      have hbzero : b = 0 := by omega
      subst b
      norm_num at hbUpper
      linarith
    have h1 : 0 ≤ b - 1 - a := by omega
    have h2 : 0 ≤ b - 1 + a := by omega
    have hsq : a ^ 2 ≤ (b - 1) ^ 2 := by
      nlinarith [mul_nonneg h1 h2]
    nlinarith
  · have ha1 : 1 ≤ a := by
      by_contra h
      have hazero : a = 0 := by omega
      subst a
      norm_num at haUpper
      linarith
    have h1 : 0 ≤ a - 1 - b := by omega
    have h2 : 0 ≤ a - 1 + b := by omega
    have hsq : b ^ 2 ≤ (a - 1) ^ 2 := by
      nlinarith [mul_nonneg h1 h2]
    nlinarith

/-- The exact ceiling subtraction needed for the A263135 conjecture. -/
@[category research solved, AMS 11]
theorem ceiling_difference
    (n k r s : ℤ)
    (hn : 1 ≤ n)
    (hk : IsA216256Index n k)
    (hr : IsCeilSqrt (3 * n) r)
    (hs : IsCeilSqrt (12 * n - 3) s) :
    s - r = k := by
  rcases hk with ⟨hk0, hkLower, hkUpper⟩
  rcases hr with ⟨hr0, hrLower, hrUpper⟩
  have hk1 : 1 ≤ k := by
    by_contra h
    have hkzero : k = 0 := by omega
    subst k
    norm_num at hkUpper
    nlinarith
  have hk_le_r : k ≤ r := by
    by_contra h
    have hrk : r ≤ k - 1 := by omega
    have h1 : 0 ≤ k - 1 - r := by omega
    have h2 : 0 ≤ k - 1 + r := by omega
    have hsq : r ^ 2 ≤ (k - 1) ^ 2 := by
      nlinarith [mul_nonneg h1 h2]
    nlinarith
  have hr_le : r ≤ k + 1 := by
    by_contra h
    have hkr : k + 2 ≤ r := by omega
    have h1 : 0 ≤ r - 1 - (k + 1) := by omega
    have h2 : 0 ≤ r - 1 + (k + 1) := by omega
    have hsq : (k + 1) ^ 2 ≤ (r - 1) ^ 2 := by
      nlinarith [mul_nonneg h1 h2]
    nlinarith
  rcases (show r = k ∨ r = k + 1 by omega) with hrEq | hrEq
  · subst r
    have hx : 0 < 12 * n - 3 := by nlinarith
    have htarget : IsCeilSqrt (12 * n - 3) (2 * k) := by
      refine ⟨by omega, ?_, ?_⟩ <;> nlinarith
    have hsEq : s = 2 * k := isCeilSqrt_unique hx hs htarget
    omega
  · subst r
    have hrLower' : k ^ 2 < 3 * n := by simpa using hrLower
    have hgap : k ^ 2 + 1 ≤ 3 * n := by omega
    have hx : 0 < 12 * n - 3 := by nlinarith
    have htarget : IsCeilSqrt (12 * n - 3) (2 * k + 1) := by
      refine ⟨by omega, ?_, ?_⟩ <;> nlinarith
    have hsEq : s = 2 * k + 1 := isCeilSqrt_unique hx hs htarget
    omega

/-- Incidence bookkeeping in a 3-regular ambient graph. -/
@[category API, AMS 05]
theorem internal_edges_from_boundary
    (vertices internalEdges boundaryEdges : ℤ)
    (hdegree : 3 * vertices = 2 * internalEdges + boundaryEdges) :
    2 * internalEdges = 3 * vertices - boundaryEdges := by
  linarith

/--
The original OEIS conjecture.  A full proof must instantiate `a` with the
maximum induced-edge count on the infinite honeycomb graph and prove its even
closed form.  This declaration intentionally remains open until that geometric
layer is kernel checked.
-/
@[category research open, AMS 05]
theorem conjecture
    (a triangular index : ℕ → ℕ)
    (n : ℕ) (hn : 0 < n)
    (hA263135 : a (2 * n) = 3 * n - ⌈Real.sqrt (3 * n)⌉₊)
    (hA047932 : triangular n = ⌊(3 * n : ℝ) - Real.sqrt (12 * n - 3)⌋₊)
    (hA216256 : index n = ⌈Real.sqrt (3 * n - (3 : ℝ) / 4) - (1 : ℝ) / 2⌉₊) :
    a (2 * n) - triangular n = index n := by
  sorry

end OeisA263135
