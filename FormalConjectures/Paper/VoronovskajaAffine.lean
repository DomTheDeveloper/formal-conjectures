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
# Exact formulas for constant and affine functions

The Taylor remainder in the Bézier--Bernstein decomposition vanishes identically for affine
functions.  Hence the identity function isolates the centered first moment exactly; there is no
analytic approximation hidden in that reduction.
-/

open Topology Filter Real unitInterval Polynomial

namespace VoronovskajaTypeFormula

/-- Bézier--Bernstein operators reproduce constant functions exactly. -/
@[category API, AMS 26 40 47]
theorem bezierBernstein_const
    (n : ℕ) {α : ℝ} (hα : 0 < α) (c x : ℝ) :
    bezierBernstein n α (fun _ ↦ c) x = c := by
  rw [bezierBernstein_uses_real_division]
  change (∑ k ∈ Finset.range (n + 1), c * bezierWeight n k α x) = c
  rw [← Finset.mul_sum, sum_bezierWeight n hα x, mul_one]

/-- The weighted first-order Taylor remainder of an affine function is exactly zero. -/
@[category API, AMS 26 40 47]
theorem bezierTaylorRemainder_affine
    (n : ℕ) (α a b x : ℝ) :
    bezierTaylorRemainder n α (fun z ↦ a * z + b) x a = 0 := by
  rw [bezierTaylorRemainder]
  apply Finset.sum_eq_zero
  intro k hk
  ring

/-- Exact centered-moment formula for an affine function. -/
@[category API, AMS 26 40 47]
theorem bezierBernstein_affine_sub
    (n : ℕ) {α : ℝ} (hα : 0 < α) (a b x : ℝ) :
    bezierBernstein n α (fun z ↦ a * z + b) x - (a * x + b) =
      a * bezierCenteredMoment n α x := by
  rw [bezierBernstein_sub_eq_moment_add_remainder n hα (fun z ↦ a * z + b) x a,
    bezierTaylorRemainder_affine, add_zero]

/-- The identity function reduces the whole approximation error exactly to the centered moment. -/
@[category API, AMS 26 40 47]
theorem bezierBernstein_id_sub
    (n : ℕ) {α : ℝ} (hα : 0 < α) (x : ℝ) :
    bezierBernstein n α id x - x = bezierCenteredMoment n α x := by
  simpa [id] using bezierBernstein_affine_sub n hα 1 0 x

/-- The scaled identity-function error is literally the scaled centered moment. -/
@[category API, AMS 26 40 47]
theorem sqrt_mul_bezierBernstein_id_sub
    (n : ℕ) {α : ℝ} (hα : 0 < α) (x : ℝ) :
    Real.sqrt n * (bezierBernstein n α id x - x) =
      Real.sqrt n * bezierCenteredMoment n α x := by
  rw [bezierBernstein_id_sub n hα x]

end VoronovskajaTypeFormula
