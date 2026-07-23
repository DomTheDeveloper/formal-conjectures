import Scratch.A263135ChainCount

namespace OeisA263135

private theorem sum_sub_two_mul_eq_staircase (q a : ℕ) (hqa : q ≤ a) :
    Finset.sum (Finset.range a) (fun t => q - 2 * t) = staircase q := by
  unfold staircase
  nth_rewrite 1 [← Nat.add_sub_of_le hqa]
  rw [Finset.sum_range_add]
  have hzero : Finset.sum (Finset.range (a - q)) (fun t => q - 2 * (q + t)) = 0 := by
    apply Finset.sum_eq_zero
    intro t ht
    omega
  rw [hzero, add_zero]

private theorem min_long_add_deficit (a b c t : ℕ) :
    min c (a + b - 2 * t) + (a + b - c - 2 * t) = a + b - 2 * t := by
  by_cases h : c ≤ a + b - 2 * t
  · rw [min_eq_left h]
    omega
  · rw [min_eq_right (Nat.le_of_not_ge h)]
    omega

private theorem min_short_add_deficit (a b c t : ℕ) :
    min c (a + b - 2 - 2 * t) + (a + b - c - 2 - 2 * t) =
      a + b - 2 - 2 * t := by
  by_cases h : c ≤ a + b - 2 - 2 * t
  · rw [min_eq_left h]
    omega
  · rw [min_eq_right (Nat.le_of_not_ge h)]
    omega

private theorem sum_chain_lengths (a b : ℕ) (hab : a ≤ b) :
    Finset.sum (Finset.range a)
      (fun t => (a + b - 2 * t) + (a + b - 2 - 2 * t)) = 2 * a * b := by
  induction a generalizing b with
  | zero => simp
  | succ a ih =>
      rw [Finset.sum_range_succ]
      have hab' : a ≤ b := by omega
      have hshift :
          Finset.sum (Finset.range a)
              (fun t => (a + 1 + b - 2 * t) + (a + 1 + b - 2 - 2 * t)) =
            Finset.sum (Finset.range a)
              (fun t => (a + b - 2 * t) + (a + b - 2 - 2 * t)) + 2 * a := by
        calc
          Finset.sum (Finset.range a)
              (fun t => (a + 1 + b - 2 * t) + (a + 1 + b - 2 - 2 * t)) =
              Finset.sum (Finset.range a)
                (fun t => ((a + b - 2 * t) + (a + b - 2 - 2 * t)) + 2) := by
            apply Finset.sum_congr rfl
            intro t ht
            have hta := Finset.mem_range.mp ht
            omega
          _ = Finset.sum (Finset.range a)
                (fun t => (a + b - 2 * t) + (a + b - 2 - 2 * t)) +
              Finset.sum (Finset.range a) (fun _ => 2) := by
            rw [Finset.sum_add_distrib]
          _ = Finset.sum (Finset.range a)
                (fun t => (a + b - 2 * t) + (a + b - 2 - 2 * t)) + 2 * a := by
            simp [Nat.mul_comm]
      rw [hshift, ih b hab']
      have hlast :
          (a + 1 + b - 2 * a) + (a + 1 + b - 2 - 2 * a) = 2 * (b - a) := by
        omega
      rw [hlast]
      nlinarith

/-- The total unused capacity of the product chains is the staircase deficiency. -/
theorem chainCapSum_add_deficiency (a b c : ℕ)
    (hab : a ≤ b) (hbc : b ≤ c) :
    chainCapSum a b c + staircaseDeficiency (a + b - c) = 2 * a * b := by
  let q := a + b - c
  have hqa : q ≤ a := by
    dsimp [q]
    omega
  have hq2a : q - 2 ≤ a := by omega
  have hdef1 := sum_sub_two_mul_eq_staircase q a hqa
  have hdef2 := sum_sub_two_mul_eq_staircase (q - 2) a hq2a
  have hterm : ∀ t ∈ Finset.range a,
      (min c (a + b - 2 * t) + min c (a + b - 2 - 2 * t)) +
          ((q - 2 * t) + (q - 2 - 2 * t)) =
        (a + b - 2 * t) + (a + b - 2 - 2 * t) := by
    intro t ht
    dsimp [q]
    rw [← min_long_add_deficit a b c t, ← min_short_add_deficit a b c t]
    omega
  have hsum := Finset.sum_congr rfl hterm
  have hlen := sum_chain_lengths a b hab
  simp only [Finset.sum_add_distrib] at hsum hlen
  unfold chainCapSum staircaseDeficiency
  rw [← hdef1, ← hdef2]
  simp only [Finset.sum_add_distrib]
  omega

/-- Sorted row counts imply the required quadratic size bound. -/
theorem six_mul_card_le_row_sum_sq_of_sorted (S : Finset Vertex)
    (hab : (occupiedRows .first S).card ≤ (occupiedRows .second S).card)
    (hbc : (occupiedRows .second S).card ≤ (occupiedRows .diagonal S).card) :
    6 * S.card ≤
      ((occupiedRows .first S).card + (occupiedRows .second S).card +
        (occupiedRows .diagonal S).card) ^ 2 := by
  let a := (occupiedRows .first S).card
  let b := (occupiedRows .second S).card
  let c := (occupiedRows .diagonal S).card
  have hcard : S.card ≤ chainCapSum a b c := by
    simpa [a, b, c] using card_le_chainCapSum S hab
  have hcap : chainCapSum a b c + staircaseDeficiency (a + b - c) = 2 * a * b :=
    chainCapSum_add_deficiency a b c hab hbc
  have hm : S.card + staircaseDeficiency (a + b - c) ≤ 2 * a * b := by
    omega
  change 6 * S.card ≤ (a + b + c) ^ 2
  exact perimeter_square_of_chain_deficiency a b c S.card hab hbc hm

end OeisA263135
