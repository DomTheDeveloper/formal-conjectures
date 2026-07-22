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

public import FormalConjecturesUtil
public import FormalConjecturesForMathlib.Analysis.Equidistribution.UnitAddTorus
public import FormalConjecturesForMathlib.NumberTheory.SquarefreeRadicals

@[expose] public section

/-!
# OEIS A261865 / Peter Kagey's Problem 13

For a positive integer `n`, OEIS A261865 is the least positive integer `k`
for which a positive integer multiple of `√k` lies strictly between `n` and
`n + 1`.

Peter Kagey's Problem 13 asks for the natural density of the indices at which
a fixed squarefree `j ≥ 2` is the least successful radicand.  The predicted
density is

`(1 / √j) * ∏_{2 ≤ s < j, Squarefree s} (1 - 1 / √s)`.
-/

open Filter
open scoped BigOperators Topology

namespace OeisA261865

/-- A positive integer multiple of `√k` lies strictly in `(n, n + 1)`. -/
def Hits (k n : ℕ) : Prop :=
  ∃ m : ℕ, 0 < m ∧
    (n : ℝ) < (m : ℝ) * Real.sqrt (k : ℝ) ∧
      (m : ℝ) * Real.sqrt (k : ℝ) < (n : ℝ) + 1

/-- `k` is the least positive radicand that hits the interval `(n, n + 1)`. -/
def IsValue (n k : ℕ) : Prop :=
  0 < k ∧ Hits k n ∧ ∀ r : ℕ, 0 < r → r < k → ¬ Hits r n

/-- The rotation parameter `1 / √s`. -/
noncomputable def alpha (s : ℕ) : ℝ :=
  1 / Real.sqrt (s : ℝ)

/-- The fractional-part condition corresponding to `Hits s n`. -/
def CoordinateHit (s n : ℕ) : Prop :=
  1 - alpha s < Int.fract ((n : ℝ) * alpha s)

/--
The next positive integer after a nonnegative real `x` lies below `x + a`
exactly when the fractional part of `x` is greater than `1 - a`.
-/
theorem exists_nat_between_iff_fract {x a : ℝ} (hx : 0 ≤ x) :
    (∃ m : ℕ, 0 < m ∧ x < (m : ℝ) ∧ (m : ℝ) < x + a) ↔
      1 - a < Int.fract x := by
  constructor
  · rintro ⟨m, _hmpos, hxm, hmx⟩
    have hfloor_lt : ⌊x⌋ < (m : ℤ) :=
      Int.floor_lt.mpr (by simpa using hxm)
    have hnext_le : ⌊x⌋ + 1 ≤ (m : ℤ) := by omega
    have hnext_le_real : ((⌊x⌋ + 1 : ℤ) : ℝ) ≤ (m : ℝ) := by
      exact_mod_cast hnext_le
    have hnext_lt : (⌊x⌋ : ℝ) + 1 < x + a := by
      exact lt_of_le_of_lt (by simpa using hnext_le_real) hmx
    have hdecomp := Int.floor_add_fract x
    linarith
  · intro hfract
    have hfloor_nonneg : 0 ≤ ⌊x⌋ := Int.floor_nonneg.mpr hx
    let m : ℕ := ⌊x⌋.toNat + 1
    have hmcast : (m : ℝ) = (⌊x⌋ : ℝ) + 1 := by
      simp [m, Int.toNat_of_nonneg hfloor_nonneg]
    refine ⟨m, by simp [m], ?_, ?_⟩
    · rw [hmcast]
      exact Int.lt_floor_add_one x
    · rw [hmcast]
      have hdecomp := Int.floor_add_fract x
      linarith

/--
The interval-hitting predicate is exactly an irrational-rotation interval.
This removes the first axiom from the uploaded proof bundle.
-/
theorem hits_iff_coordinateHit (s n : ℕ) (hs : 2 ≤ s) :
    Hits s n ↔ CoordinateHit s n := by
  have hs_real_pos : (0 : ℝ) < (s : ℝ) := by positivity
  have hsqrt_pos : (0 : ℝ) < Real.sqrt (s : ℝ) := Real.sqrt_pos.2 hs_real_pos
  have hx : 0 ≤ (n : ℝ) / Real.sqrt (s : ℝ) :=
    div_nonneg (by positivity) hsqrt_pos.le
  constructor
  · rintro ⟨m, hmpos, hleft, hright⟩
    have hleft' : (n : ℝ) / Real.sqrt (s : ℝ) < (m : ℝ) :=
      (div_lt_iff₀ hsqrt_pos).2 hleft
    have hright' : (m : ℝ) <
        (n : ℝ) / Real.sqrt (s : ℝ) + 1 / Real.sqrt (s : ℝ) := by
      have := (lt_div_iff₀ hsqrt_pos).2 hright
      convert this using 1 <;> ring
    have hfract := (exists_nat_between_iff_fract hx).mp
      ⟨m, hmpos, hleft', hright'⟩
    simpa [CoordinateHit, alpha, div_eq_mul_inv] using hfract
  · intro hcoord
    have hfract :
        1 - 1 / Real.sqrt (s : ℝ) <
          Int.fract ((n : ℝ) / Real.sqrt (s : ℝ)) := by
      simpa [CoordinateHit, alpha, div_eq_mul_inv] using hcoord
    obtain ⟨m, hmpos, hleft, hright⟩ :=
      (exists_nat_between_iff_fract hx).mpr hfract
    refine ⟨m, hmpos, (div_lt_iff₀ hsqrt_pos).mp hleft, ?_⟩
    apply (lt_div_iff₀ hsqrt_pos).mp
    convert hright using 1 <;> ring

/--
Removing a positive square factor from a radicand preserves the hitting
property.  Hence a nonsquarefree radicand can never be a genuinely new least
value: every hit by `c² s` is already a hit by `s`.
-/
theorem hits_square_mul_imp (c s n : ℕ) (hc : 0 < c) :
    Hits (c ^ 2 * s) n → Hits s n := by
  rintro ⟨m, hm, hleft, hright⟩
  have hsqrt :
      Real.sqrt ((c ^ 2 * s : ℕ) : ℝ) =
        (c : ℝ) * Real.sqrt (s : ℝ) := by
    rw [Nat.cast_mul, Nat.cast_pow, Real.sqrt_mul (sq_nonneg (c : ℝ))]
    rw [Real.sqrt_sq (Nat.cast_nonneg c)]
  refine ⟨m * c, Nat.mul_pos hm hc, ?_, ?_⟩
  · simpa only [hsqrt, Nat.cast_mul, mul_assoc] using hleft
  · simpa only [hsqrt, Nat.cast_mul, mul_assoc] using hright

/-- The squarefree integers in `[2, j)`. -/
noncomputable def squarefreeBelow (j : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Ico 2 j).filter Squarefree

/-- The density predicted for the value `j` in OEIS A261865. -/
noncomputable def predictedDensity (j : ℕ) : ℝ :=
  alpha j * ∏ s ∈ squarefreeBelow j, (1 - alpha s)

/--
**Peter Kagey's Problem 13 / OEIS A261865.**

For every squarefree `j ≥ 2`, the set of positive indices where the least
successful radicand is `j` has the stated natural density.

The mathematical proof and Lean development were produced by
ProofOrchestrator, using OpenAI GPT-5.6 Thinking, under Dominic Dabish's
supervision.
-/
@[category research open, AMS 11]
theorem density_formula (j : ℕ) (hj : 2 ≤ j) (hsq : Squarefree j) :
    {n : ℕ | 0 < n ∧ IsValue n j}.HasDensity (predictedDensity j) := by
  sorry

end OeisA261865
