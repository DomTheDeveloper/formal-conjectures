import Scratch.A263135RowBound

namespace OeisA263135

/-- Sum of the positive terms in the arithmetic progression `q, q-2, q-4, ...`. -/
def staircase (q : ℕ) : ℕ :=
  ∑ t ∈ Finset.range q, q - 2 * t

private theorem staircase_add_two (q : ℕ) :
    staircase (q + 2) = staircase q + q + 2 := by
  unfold staircase
  rw [Finset.sum_range_succ']
  simp only [Nat.mul_zero, Nat.sub_zero]
  have hshift :
      (∑ t ∈ Finset.range (q + 1), q + 2 - 2 * (t + 1)) =
        ∑ t ∈ Finset.range (q + 1), q - 2 * t := by
    apply Finset.sum_congr rfl
    intro t ht
    omega
  rw [hshift, Finset.sum_range_succ]
  have hlast : q - 2 * q = 0 := by omega
  simp [hlast]
  omega

private theorem staircase_eq_sub_add : ∀ q : ℕ,
    staircase q = staircase (q - 2) + q
  | 0 => by simp [staircase]
  | 1 => by norm_num [staircase]
  | q + 2 => by
      simpa only [Nat.add_sub_cancel] using staircase_add_two q

/-- Deficiency contributed by the two symmetric chains over one grid-chain family. -/
def staircaseDeficiency (q : ℕ) : ℕ :=
  staircase q + staircase (q - 2)

private theorem staircaseDeficiency_add_two (q : ℕ) :
    staircaseDeficiency (q + 2) = staircaseDeficiency q + 2 * q + 2 := by
  rw [staircaseDeficiency, staircaseDeficiency, Nat.add_sub_cancel,
    staircase_add_two, staircase_eq_sub_add q]
  omega

/-- Twice the staircase deficiency dominates the square of its width. -/
theorem sq_le_two_mul_staircaseDeficiency : ∀ q : ℕ,
    q ^ 2 ≤ 2 * staircaseDeficiency q
  | 0 => by simp [staircaseDeficiency, staircase]
  | 1 => by norm_num [staircaseDeficiency, staircase]
  | q + 2 => by
      have ih := sq_le_two_mul_staircaseDeficiency q
      rw [staircaseDeficiency_add_two]
      nlinarith

/-- The purely arithmetic implication used after the chain count. -/
theorem perimeter_square_of_chain_deficiency
    (a b c m : ℕ)
    (hab : a ≤ b)
    (hbc : b ≤ c)
    (hm : m + staircaseDeficiency (a + b - c) ≤ 2 * a * b) :
    6 * m ≤ (a + b + c) ^ 2 := by
  let q := a + b - c
  have hq : q ≤ a := by
    dsimp [q]
    omega
  have hc : a + b = c + q := by
    dsimp [q]
    omega
  have hsq := sq_le_two_mul_staircaseDeficiency q
  have hm2 : 2 * m + q ^ 2 ≤ 4 * a * b := by
    nlinarith
  nlinarith [sq_nonneg (a - q), sq_nonneg (b - q),
    mul_nonneg (Nat.zero_le (a - q)) (Nat.zero_le (b - q))]

end OeisA263135
