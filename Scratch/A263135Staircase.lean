import Scratch.A263135RowBound

namespace OeisA263135

/-- Sum of the positive terms in the arithmetic progression `q, q-2, q-4, ...`. -/
def staircase (q : ℕ) : ℕ :=
  Finset.sum (Finset.range q) (fun t => q - 2 * t)

private theorem staircase_add_two (q : ℕ) :
    staircase (q + 2) = staircase q + q + 2 := by
  unfold staircase
  rw [Finset.sum_range_succ']
  simp only [Nat.mul_zero, Nat.sub_zero]
  have hshift :
      Finset.sum (Finset.range (q + 1)) (fun t => q + 2 - 2 * (t + 1)) =
        Finset.sum (Finset.range (q + 1)) (fun t => q - 2 * t) := by
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
  have hsq : q ^ 2 ≤ 2 * staircaseDeficiency q :=
    sq_le_two_mul_staircaseDeficiency q
  have hm2 : 2 * m + q ^ 2 ≤ 4 * a * b := by
    calc
      2 * m + q ^ 2 ≤ 2 * m + 2 * staircaseDeficiency q :=
        Nat.add_le_add_left hsq (2 * m)
      _ = 2 * (m + staircaseDeficiency q) := by ring
      _ ≤ 2 * (2 * a * b) := Nat.mul_le_mul_left 2 hm
      _ = 4 * a * b := by ring
  let x := a - q
  let z := b - a
  have haeq : a = q + x := by
    dsimp [x]
    omega
  have hbeq : b = q + x + z := by
    dsimp [x, z]
    omega
  have hceq : c = q + 2 * x + z := by
    omega
  rw [haeq, hbeq] at hm2
  rw [haeq, hbeq, hceq]
  nlinarith [Nat.zero_le (x ^ 2), Nat.zero_le (x * z), Nat.zero_le (z ^ 2)]

end OeisA263135
