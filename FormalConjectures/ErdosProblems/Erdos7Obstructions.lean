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
# Algebraic kernels for the Erdős--Selfridge odd covering campaign

This file formalizes reusable algebraic implications and exact arithmetic
checks from the finite-LCM obstruction campaign. It deliberately does not
claim `Erdos7.erdos_7`.
-/

namespace Erdos7Obstructions

/-- If the unselected classes have total incidence at least the complement of
two selected independent blocks, then the block-overlap lower bound follows. -/
theorem block_excess_two
    (T I₁ I₂ U₁ U₂ : ℚ)
    (hcover : (1 - U₁) * (1 - U₂) ≤ T - I₁ - I₂) :
    I₁ + I₂ - (1 - (1 - U₁) * (1 - U₂)) ≤ T - 1 := by
  linarith

/-- The one-block version of the same excess rearrangement. -/
theorem block_excess_one
    (T I U : ℚ) (hcover : 1 - U ≤ T - I) :
    I - U ≤ T - 1 := by
  linarith

/-- Once the fiber-profile contradiction is true at a lower bound `rA`, it is
true for every larger remainder, provided `rB > IB`. -/
theorem profile_threshold
    (IB rB rA C R : ℚ)
    (hcoef : IB < rB)
    (hR : rA ≤ R)
    (hbase : IB * (rA + C) < rB * rA) :
    IB * (R + C) < rB * R := by
  have hnonneg : 0 ≤ (rB - IB) * (R - rA) :=
    mul_nonneg (sub_nonneg.mpr (le_of_lt hcoef)) (sub_nonneg.mpr hR)
  nlinarith

/-- Arithmetic core of the elementary `U(315) ≤ 241` argument. -/
theorem u315_capacity_arithmetic :
    (195 : ℤ) + ((18 + 12 + 5 + 6 + 4 + 3 + 1) - 3) = 241 := by
  norm_num

/-- The elementary two-prime-power box calculation `U(675) ≤ 487`. -/
theorem u675_box_arithmetic :
    (675 : ℤ) - ((14 * 19) - (13 * 6)) = 487 := by
  norm_num

/-- The strict numerical gap excluding LCM `45045`. -/
theorem lcm_45045_gap :
    ((14742 : ℚ) / 45045) < ((15823 : ℚ) / 45045) := by
  norm_num

/-- Fiber-profile gap for `3^3 * 5^2 * 7^2 * 11`, paired with `13`. -/
theorem lcm_4729725_profile_gap :
    (1 : ℤ) * (28068 + 271710) + 37038 = 12 * 28068 := by
  norm_num

/-- Fiber-profile gap for `3^5 * 5^2 * 7 * 11`, paired with `13`. -/
theorem lcm_6081075_profile_gap :
    (1 : ℤ) * (36947 + 342114) + 64303 = 12 * 36947 := by
  norm_num

/-- Exact two-fiber correction used for the `3^3*5^2*7^2*11` block. -/
theorem two_fiber_correction_363825 :
    (37431 : ℤ) - 9 * 3506 = 5877 := by
  norm_num

/-- Exact two-fiber correction used for the `3^5*5^2*7*11` block. -/
theorem two_fiber_correction_467775 :
    (48924 : ℤ) - 81 * 510 = 7614 := by
  norm_num

end Erdos7Obstructions
