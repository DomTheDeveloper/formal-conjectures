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

public import FormalConjecturesForMathlib.Combinatorics.RestrictedRunTableaux

@[expose] public section

/-!
# Exact reduction for restricted-run tableaux

This file formalizes algebraic consequences of the six-state Markov-additive
model proposed for Kauers--Zeilberger Conjecture 2a. It does not assume or
state the missing fixed-endpoint cone local-limit theorem.
-/

open Filter
open scoped Topology

namespace RestrictedRunTableaux

/-- The bridge mass corresponding to the candidate equal-weight path model. -/
noncomputable def bridgeMass (n : ℕ) : ℝ :=
  (4 * (G n : ℝ)) / (3 * (8 : ℝ) ^ n)

/-- The normalization predicted to have a positive finite bridge limit. -/
noncomputable def bridgeNormalized (n : ℕ) : ℝ :=
  (n : ℝ) ^ 4 * bridgeMass n

/-- Exact rescaling between the tableau and bridge normalizations. -/
theorem normalizedCount_eq_bridgeNormalized (n : ℕ) :
    normalizedCount n = (3 / 4 : ℝ) * bridgeNormalized n := by
  unfold normalizedCount bridgeNormalized bridgeMass
  have h8 : (8 : ℝ) ^ n ≠ 0 := by positivity
  field_simp [h8]
  ring

/-- The inverse exact rescaling. -/
theorem bridgeNormalized_eq_normalizedCount (n : ℕ) :
    bridgeNormalized n = (4 / 3 : ℝ) * normalizedCount n := by
  rw [normalizedCount_eq_bridgeNormalized]
  ring

/-- A bridge limit gives the normalized tableau limit. -/
theorem tendsto_normalizedCount_of_bridge {c : ℝ}
    (h : Tendsto bridgeNormalized atTop (𝓝 c)) :
    Tendsto normalizedCount atTop (𝓝 ((3 / 4 : ℝ) * c)) := by
  simpa only [normalizedCount_eq_bridgeNormalized] using h.const_mul (3 / 4 : ℝ)

/-- The normalized tableau limit determines the bridge limit. -/
theorem tendsto_bridge_of_normalizedCount {C : ℝ}
    (h : Tendsto normalizedCount atTop (𝓝 C)) :
    Tendsto bridgeNormalized atTop (𝓝 ((4 / 3 : ℝ) * C)) := by
  simpa only [bridgeNormalized_eq_normalizedCount] using h.const_mul (4 / 3 : ℝ)

/-- Conjecture 2a is exactly equivalent to convergence of the normalized
bridge mass to a positive constant. -/
theorem conjecture_2a_iff_bridge_limit :
    (∃ C : ℝ, 0 < C ∧ Tendsto normalizedCount atTop (𝓝 C)) ↔
      ∃ c : ℝ, 0 < c ∧ Tendsto bridgeNormalized atTop (𝓝 c) := by
  constructor
  · rintro ⟨C, hC, hlim⟩
    refine ⟨(4 / 3 : ℝ) * C, mul_pos (by norm_num) hC, ?_⟩
    exact tendsto_bridge_of_normalizedCount hlim
  · rintro ⟨c, hc, hlim⟩
    refine ⟨(3 / 4 : ℝ) * c, mul_pos (by norm_num) hc, ?_⟩
    exact tendsto_normalizedCount_of_bridge hlim

/-- The quadratic form of the candidate asymptotic covariance matrix
`(5/9) * [[2,-1],[-1,2]]`. -/
def covarianceQuadratic (x y : ℝ) : ℝ :=
  (5 / 9 : ℝ) * (2 * x ^ 2 - 2 * x * y + 2 * y ^ 2)

/-- A sum-of-squares certificate for the covariance quadratic form. -/
theorem covarianceQuadratic_eq_sumSquares (x y : ℝ) :
    covarianceQuadratic x y =
      (5 / 9 : ℝ) * (x ^ 2 + y ^ 2 + (x - y) ^ 2) := by
  unfold covarianceQuadratic
  ring

/-- The candidate covariance matrix is positive definite. -/
theorem covarianceQuadratic_pos {x y : ℝ} (hxy : x ≠ 0 ∨ y ≠ 0) :
    0 < covarianceQuadratic x y := by
  rw [covarianceQuadratic_eq_sumSquares]
  have hxy2 : 0 < x ^ 2 + y ^ 2 := by
    rcases hxy with hx | hy
    · exact add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero hx) (sq_nonneg y)
    · exact add_pos_of_nonneg_of_pos (sq_nonneg x) (sq_pos_of_ne_zero hy)
  exact mul_pos (by norm_num)
    (add_pos_of_pos_of_nonneg hxy2 (sq_nonneg (x - y)))

/-- The degree-three positive cone polynomial in the Brownian reduction. -/
def coneHarmonic (x y : ℝ) : ℝ :=
  x * y * (x + y)

theorem coneHarmonic_pos {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    0 < coneHarmonic x y := by
  unfold coneHarmonic
  positivity

theorem coneHarmonic_left_boundary (y : ℝ) : coneHarmonic 0 y = 0 := by
  simp [coneHarmonic]

theorem coneHarmonic_right_boundary (x : ℝ) : coneHarmonic x 0 = 0 := by
  simp [coneHarmonic]

/-- The polynomial identity corresponding to
`u_xx - u_xy + u_yy = 0` for `u(x,y)=x*y*(x+y)`. -/
theorem coneHarmonic_generator_identity (x y : ℝ) :
    2 * y - (2 * x + 2 * y) + 2 * x = 0 := by
  ring

end RestrictedRunTableaux
