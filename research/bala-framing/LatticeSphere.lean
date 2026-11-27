import Mathlib.Data.Nat.Choose.Sum
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Finite formulas for spheres in the cubic lattice (OEIS A035607). -/

open Finset
open scoped BigOperators

namespace LatticeSphere

/-- Choose the nonzero coordinates, their signs, and a positive composition of the distance. -/
def count (h d : ℕ) : ℕ :=
  ∑ j ∈ range (min h d), 2 ^ (j + 1) * h.choose (j + 1) * (d - 1).choose j

private theorem weighted (h d : ℕ) :
    d * count h d = ∑ j ∈ range (min h d),
      2 ^ (j + 1) * (j + 1) * h.choose (j + 1) * d.choose (j + 1) := by
  cases d with
  | zero => simp [count]
  | succ d =>
    rw [count, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    simp only [Nat.succ_sub_one]
    change (d + 1) * _ = _
    calc
      _ = (2 ^ (j + 1) * ((d + 1) * d.choose j)) * h.choose (j + 1) := by ring
      _ = _ := by rw [Nat.add_one_mul_choose_eq]; ring

/-- Reciprocity exchanges the lattice dimension and the distance. -/
theorem reciprocity (h d : ℕ) : d * count h d = h * count d h := by
  rw [weighted, weighted, min_comm d h]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Extracting twice the dimension leaves an integer with the parity of the distance. -/
theorem weighted_parity (h d : ℕ) (hh : 0 < h) (hd : 0 < d) :
    ∃ q : ℕ, d * count h d = 2 * h * (d + 2 * q) := by
  obtain ⟨H, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hh)
  let l := min (H+1) d - 1
  have hl : min (H+1) d = l+1 := by dsimp [l]; omega
  let f (j : ℕ) := 2^j * H.choose j * d.choose (j+1)
  have hf : d * count (H+1) d = (2 * (H+1)) * ∑ j ∈ range (l+1), f j := by
    rw [weighted, ← hl, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    dsimp [f]
    rw [pow_succ]
    calc
      _ = 2 * 2^j * ((H+1).choose (j+1) * (j+1)) * d.choose (j+1) := by ring
      _ = _ := by rw [← Nat.add_one_mul_choose_eq]; ring
  refine ⟨∑ j ∈ range l, 2^j * H.choose (j+1) * d.choose (j+1+1), ?_⟩
  rw [hf, Finset.sum_range_succ', Finset.mul_sum]
  congr 1
  simp only [f, pow_zero, Nat.choose_zero_right, Nat.zero_add, Nat.choose_one_right,
    mul_one, one_mul]
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [pow_succ]
  ring

private theorem valuation_of_odd (a : ℕ) (h : Odd a) : padicValNat 2 a = 0 :=
  padicValNat.eq_zero_of_not_dvd (by obtain ⟨k, hk⟩ := h; omega)

private theorem count_ne_zero (h d : ℕ) (hh : 0 < h) (hd : 0 < d) : count h d ≠ 0 := by
  obtain ⟨q, heq⟩ := weighted_parity h d hh hd
  intro hz
  rw [hz, mul_zero] at heq
  exact (Nat.ne_of_gt (by positivity)) heq.symm

/-- Exact valuation for every positive dimension and odd distance. -/
theorem at_odd_distance (h d : ℕ) (hh : 0 < h) (hd : Odd d) :
    padicValNat 2 (count h d) = 1 + padicValNat 2 h := by
  have hd0 : 0 < d := by obtain ⟨k, hk⟩ := hd; omega
  obtain ⟨q, heq⟩ := weighted_parity h d hh hd0
  have hq : Odd (d + 2 * q) := by obtain ⟨k, hk⟩ := hd; exact ⟨k+q, by omega⟩
  have hv := congrArg (padicValNat 2) heq
  rw [padicValNat.mul (Nat.ne_of_gt hd0) (count_ne_zero h d hh hd0),
    padicValNat.mul (by positivity : 2*h ≠ 0) (by omega),
    padicValNat.mul (by decide : 2 ≠ 0) (Nat.ne_of_gt hh),
    valuation_of_odd _ hd, valuation_of_odd _ hq, padicValNat.self (by decide : 1 < 2)] at hv
  omega

/-- In odd dimension every sphere of positive radius has exactly one factor of two. -/
theorem at_odd_dimension (h d : ℕ) (hh : Odd h) (hd : 0 < d) :
    padicValNat 2 (count h d) = 1 := by
  have hh0 : 0 < h := by obtain ⟨k, hk⟩ := hh; omega
  have hv := congrArg (padicValNat 2) (reciprocity h d)
  rw [padicValNat.mul (Nat.ne_of_gt hd) (count_ne_zero h d hh0 hd),
    padicValNat.mul (Nat.ne_of_gt hh0) (count_ne_zero d h hd hh0),
    valuation_of_odd _ hh, at_odd_distance d h hd hh] at hv
  omega

/-- A division-free identity for the sum of the first m odd squares. -/
theorem odd_squares (m : ℕ) :
    3 * (∑ j ∈ range m, (2*j+1)^2) + m = 4*m^3 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ]
    calc
      _ = (3 * (∑ j ∈ range m, (2*j+1)^2) + m) + (12*m^2+12*m+4) := by ring
      _ = _ := by rw [ih]; ring

/-- The odd-square sum in the binary convolution has exactly the valuation of its length. -/
theorem odd_squares_valuation (m : ℕ) (hm : 0 < m) :
    padicValNat 2 (∑ j ∈ range m, (2*j+1)^2) = padicValNat 2 m := by
  let S := ∑ j ∈ range m, (2*j+1)^2
  have hm2 : 0 < m^2 := by positivity
  have hsub : 4*m^2-1+1 = 4*m^2 := by omega
  have hf : 3*S = m*(4*m^2-1) := by
    have h1 : 3*S+m = 4*m^3 := odd_squares m
    have h2 : m*(4*m^2-1)+m = 4*m^3 := calc
      _ = m*((4*m^2-1)+1) := by ring
      _ = _ := by rw [hsub]; ring
    omega
  have ho : Odd (4*m^2-1) := ⟨2*m^2-1, by omega⟩
  have hk : 0 < 4*m^2-1 := by omega
  have hs : S ≠ 0 := by
    intro hs
    rw [hs, mul_zero] at hf
    exact (Nat.ne_of_gt (Nat.mul_pos hm hk)) hf.symm
  have v := congrArg (padicValNat 2) hf
  rw [padicValNat.mul (by decide : 3 ≠ 0) hs, padicValNat.mul (Nat.ne_of_gt hm)
    (Nat.ne_of_gt hk), valuation_of_odd 3 (by decide), valuation_of_odd _ ho] at v
  simpa [S] using v

#print axioms odd_squares_valuation
#print axioms reciprocity
#print axioms at_odd_distance
#print axioms at_odd_dimension
#print axioms odd_squares

end LatticeSphere
