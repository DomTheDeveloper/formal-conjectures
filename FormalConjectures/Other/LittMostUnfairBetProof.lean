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

import Mathlib

/-!
# Arithmetic core for the most unfair Litt coin-word bet

The complete combinatorial proof is recorded in `LittMostUnfairBetProof.md`.
This file kernelizes the denominator-cleared arithmetic endgame. Its inputs are
exactly the overlap and variance estimates established by the Walsh-shape
argument, so no probabilistic or analytic assumptions remain in this layer.
-/

set_option autoImplicit false

namespace LittMostUnfairBetProof

/-- Constant-word branch: the overlap difference is at most the candidate
numerator, and the variance numerator is at least the power-of-two denominator. -/
theorem constant_branch
    (candidate delta variance denominator : ℕ)
    (hdelta : delta ≤ candidate)
    (hvariance : denominator ≤ variance) :
    delta ^ 2 * denominator ≤ candidate ^ 2 * variance := by
  exact Nat.mul_le_mul (Nat.pow_le_pow_left hdelta 2) hvariance

/-- Nonconstant branch after writing `2^n = 4 * 2^(n-2)`.
The sharp overlap estimate is `2 * delta ≤ candidate`; the Walsh gap is
`2^(n-2) ≤ variance`. -/
theorem nonconstant_branch
    (candidate delta variance quarterDenominator : ℕ)
    (hdelta : 2 * delta ≤ candidate)
    (hvariance : quarterDenominator ≤ variance) :
    delta ^ 2 * (4 * quarterDenominator) ≤ candidate ^ 2 * variance := by
  have hsq : (2 * delta) ^ 2 ≤ candidate ^ 2 := Nat.pow_le_pow_left hdelta 2
  calc
    delta ^ 2 * (4 * quarterDenominator) =
        (2 * delta) ^ 2 * quarterDenominator := by ring
    _ ≤ candidate ^ 2 * variance := Nat.mul_le_mul hsq hvariance

/-- Zero numerator, including the reversal-degenerate pairs, is immediate. -/
theorem zero_difference_branch (candidate variance denominator : ℕ) :
    0 ^ 2 * denominator ≤ candidate ^ 2 * variance := by simp

/-- The three exact branches combine to the cleared-denominator optimizer. -/
theorem cleared_optimizer
    (candidate delta variance denominator quarterDenominator : ℕ)
    (hdenominator : denominator = 4 * quarterDenominator)
    (hcase :
      delta = 0 ∨
      (delta ≤ candidate ∧ denominator ≤ variance) ∨
      (2 * delta ≤ candidate ∧ quarterDenominator ≤ variance)) :
    delta ^ 2 * denominator ≤ candidate ^ 2 * variance := by
  rcases hcase with hzero | hconstant | hnonconstant
  · subst delta
    exact zero_difference_branch candidate variance denominator
  · exact constant_branch candidate delta variance denominator hconstant.1 hconstant.2
  · rw [hdenominator]
    exact nonconstant_branch candidate delta variance quarterDenominator
      hnonconstant.1 hnonconstant.2

#print axioms constant_branch
#print axioms nonconstant_branch
#print axioms cleared_optimizer

end LittMostUnfairBetProof
