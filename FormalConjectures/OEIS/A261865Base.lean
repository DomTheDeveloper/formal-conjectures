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

public import Mathlib
public import FormalConjecturesForMathlib.Analysis.Equidistribution.UnitAddTorus
public import FormalConjecturesForMathlib.NumberTheory.SquarefreeRadicals

@[expose] public section

/-!
# OEIS A261865 / Peter Kagey's Problem 13: definitions and reductions
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

/-- The next positive integer after a nonnegative real `x` lies below `x + a`
exactly when the fractional part of `x` is greater than `1 - a`. -/
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
      norm_num [m]
      exact_mod_cast Int.toNat_of_nonneg hfloor_nonneg
    refine ⟨m, by simp [m], ?_, ?_⟩
    · rw [hmcast]
      exact Int.lt_floor_add_one x
    · rw [hmcast]
      have hdecomp := Int.floor_add_fract x
      linarith

/-- The interval-hitting predicate is exactly an irrational-rotation interval. -/
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

/-- The radicand `1` never hits an open unit interval between consecutive integers. -/
theorem not_hits_one (n : ℕ) : ¬ Hits 1 n := by
  rintro ⟨m, _hm, hleft, hright⟩
  have hnm : n < m := by
    exact_mod_cast (by simpa using hleft)
  have hright' : (m : ℝ) < (n : ℝ) + 1 := by simpa using hright
  have hmn : m ≤ n := by
    exact_mod_cast hright'
  omega

/-- Removing a positive square factor from a radicand preserves the hitting property. -/
theorem hits_square_mul_imp (c s n : ℕ) (hc : 0 < c) :
    Hits (c ^ 2 * s) n → Hits s n := by
  rintro ⟨m, hm, hleft, hright⟩
  have hsqrt :
      Real.sqrt ((c ^ 2 * s : ℕ) : ℝ) =
        (c : ℝ) * Real.sqrt (s : ℝ) := by
    rw [Nat.cast_mul, Nat.cast_pow, Real.sqrt_mul (sq_nonneg (c : ℝ))]
    rw [Real.sqrt_sq (Nat.cast_nonneg c)]
  refine ⟨m * c, Nat.mul_pos hm hc, ?_, ?_⟩
  · calc
      (n : ℝ) < (m : ℝ) * ((c : ℝ) * Real.sqrt (s : ℝ)) := by
        rw [← hsqrt]
        exact hleft
      _ = ((m * c : ℕ) : ℝ) * Real.sqrt (s : ℝ) := by
        push_cast
        ring
  · calc
      ((m * c : ℕ) : ℝ) * Real.sqrt (s : ℝ) =
          (m : ℝ) * ((c : ℝ) * Real.sqrt (s : ℝ)) := by
            push_cast
            ring
      _ < (n : ℝ) + 1 := by
        rw [← hsqrt]
        exact hright

/-- Every hit descends to a hit by a positive squarefree radicand no larger than the original. -/
theorem exists_squarefree_hit_le (r n : ℕ) (hr : 0 < r) (hhit : Hits r n) :
    ∃ s : ℕ, 0 < s ∧ s ≤ r ∧ Squarefree s ∧ Hits s n := by
  induction r using Nat.strong_induction_on with
  | h r ih =>
      by_cases hsq : Squarefree r
      · exact ⟨r, hr, le_rfl, hsq, hhit⟩
      · rcases e : r.minSqFac with _ | d
        · exact (hsq (Nat.squarefree_iff_minSqFac.mpr e)).elim
        · have hdprime : d.Prime := Nat.minSqFac_prime e
          obtain ⟨s, hrs⟩ := Nat.minSqFac_dvd e
          have hdpos : 0 < d := hdprime.pos
          have hspos : 0 < s := by
            apply Nat.pos_of_ne_zero
            intro hs0
            subst s
            simp at hr
          have hslt : s < r := by
            rw [hrs]
            have hdd : 1 < d * d := by nlinarith [hdprime.two_le]
            simpa using Nat.mul_lt_mul_of_pos_right hdd hspos
          have hhit_s : Hits s n := by
            apply hits_square_mul_imp d s n hdpos
            simpa [pow_two, hrs] using hhit
          obtain ⟨t, htpos, htle, htsq, hthit⟩ := ih s hslt hspos hhit_s
          exact ⟨t, htpos, htle.trans hslt.le, htsq, hthit⟩

/-- The squarefree integers in `[2, j)`. -/
noncomputable def squarefreeBelow (j : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Ico 2 j).filter Squarefree

@[simp] theorem mem_squarefreeBelow {j s : ℕ} :
    s ∈ squarefreeBelow j ↔ 2 ≤ s ∧ s < j ∧ Squarefree s := by
  classical
  simp [squarefreeBelow, and_assoc]

/-- The squarefree radicands relevant to the value `j`, including `j` itself. -/
noncomputable def relevantRadicands (j : ℕ) : Finset ℕ :=
  insert j (squarefreeBelow j)

@[simp] theorem mem_relevantRadicands {j s : ℕ} :
    s ∈ relevantRadicands j ↔ s = j ∨ (2 ≤ s ∧ s < j ∧ Squarefree s) := by
  classical
  simp [relevantRadicands]

/-- `j` is the least successful radicand exactly when it hits and every smaller squarefree
radicand at least two misses. -/
theorem isValue_iff_squarefree_competitors (n j : ℕ) (hj : 2 ≤ j) :
    IsValue n j ↔
      Hits j n ∧ ∀ s ∈ squarefreeBelow j, ¬ Hits s n := by
  constructor
  · rintro ⟨_hjpos, hjhit, hminimal⟩
    refine ⟨hjhit, ?_⟩
    intro s hs
    have hs' := mem_squarefreeBelow.mp hs
    exact hminimal s (lt_of_lt_of_le Nat.zero_lt_two hs'.1) hs'.2.1
  · rintro ⟨hjhit, hsmall⟩
    refine ⟨lt_of_lt_of_le Nat.zero_lt_two hj, hjhit, ?_⟩
    intro r hrpos hrj hrhit
    obtain ⟨s, hspos, hsr, hssq, hshit⟩ := exists_squarefree_hit_le r n hrpos hrhit
    have hsne : s ≠ 1 := by
      intro hs1
      subst s
      exact not_hits_one n hshit
    have hsge : 2 ≤ s := by omega
    have hslt : s < j := lt_of_le_of_lt hsr hrj
    exact hsmall s (mem_squarefreeBelow.mpr ⟨hsge, hslt, hssq⟩) hshit

/-- Fractional-part version of `isValue_iff_squarefree_competitors`. -/
theorem isValue_iff_coordinateConditions (n j : ℕ) (hj : 2 ≤ j) :
    IsValue n j ↔
      CoordinateHit j n ∧ ∀ s ∈ squarefreeBelow j, ¬ CoordinateHit s n := by
  rw [isValue_iff_squarefree_competitors n j hj, hits_iff_coordinateHit j n hj]
  constructor
  · rintro ⟨hjhit, hsmall⟩
    refine ⟨hjhit, ?_⟩
    intro s hs hscoord
    have hsge := (mem_squarefreeBelow.mp hs).1
    exact hsmall s hs ((hits_iff_coordinateHit s n hsge).mpr hscoord)
  · rintro ⟨hjhit, hsmall⟩
    refine ⟨hjhit, ?_⟩
    intro s hs hshit
    have hsge := (mem_squarefreeBelow.mp hs).1
    exact hsmall s hs ((hits_iff_coordinateHit s n hsge).mp hshit)

/-- Adjoin the rational coordinate `1` to a finite family of radicands. -/
def radicandWithOne {S : Finset ℕ} : Option S → ℕ
  | none => 1
  | some s => s.1

/-- Reciprocal radicals indexed by distinct squarefree integers at least two have no integer
relation modulo `1`. -/
theorem noIntegerRelation_alpha (S : Finset ℕ)
    (hge : ∀ s ∈ S, 2 ≤ s) (hsq : ∀ s ∈ S, Squarefree s) :
    UnitAddTorus.NoIntegerRelation (fun s : S => alpha s.1) := by
  let r : Option S → ℕ := radicandWithOne
  have hr_sq : ∀ o, Squarefree (r o) := by
    intro o
    cases o with
    | none => simp [r, radicandWithOne]
    | some s => simpa [r, radicandWithOne] using hsq s.1 s.2
  have hr_inj : Function.Injective r := by
    intro o₁ o₂ h
    cases o₁ with
    | none =>
        cases o₂ with
        | none => rfl
        | some s =>
            exfalso
            have := hge s.1 s.2
            simp [r, radicandWithOne] at h
            omega
    | some s =>
        cases o₂ with
        | none =>
            exfalso
            have := hge s.1 s.2
            simp [r, radicandWithOne] at h
            omega
        | some t =>
            apply congrArg some
            apply Subtype.ext
            simpa [r, radicandWithOne] using h
  have hli := Real.linearIndependent_inv_sqrt_squarefree r hr_sq hr_inj
  intro k hk
  obtain ⟨z, hz⟩ := hk
  let c : Option S → ℚ
    | none => -(z : ℚ)
    | some s => (k s : ℚ)
  have hsum :
      ∑ o, c o • (1 / Real.sqrt (r o : ℝ)) =
        ∑ o, (0 : ℚ) • (1 / Real.sqrt (r o : ℝ)) := by
    rw [Fintype.sum_option]
    simp only [c, r, radicandWithOne, Nat.cast_one, Real.sqrt_one, div_one,
      Rat.smul_def, Rat.cast_neg, Rat.cast_intCast, neg_mul, mul_one,
      zero_smul, Finset.sum_const_zero]
    change -(z : ℝ) + ∑ s : S, (k s : ℝ) * alpha s.1 = 0
    linarith
  have hc := (Fintype.linearIndependent_iffₛ.mp hli c (fun _ => 0) hsum)
  funext s
  have hs := hc (some s)
  exact_mod_cast (by simpa [c] using hs)

/-- The density predicted for the value `j` in OEIS A261865. -/
noncomputable def predictedDensity (j : ℕ) : ℝ :=
  alpha j * ∏ s ∈ squarefreeBelow j, (1 - alpha s)

end OeisA261865
