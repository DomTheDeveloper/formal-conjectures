import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

/-! # 11. Why a square root appears
In the motivating error budget, sharing a cost X across m lifts costs X/m per
lift, while chain length contributes m. The two terms are equal at m = √X.
This calculation explains the choice. The formal construction rounds the
length and allows a small power loss, as expressed by `GlobalTheory.EX.RankVal`.
The comparison theorem for actual theta lifts is used in file 15. -/

namespace RH17

theorem chainCostLower {X m : ℝ} (hX : 0 ≤ X) (hm : 0 < m) :
    2 * Real.sqrt X ≤ X / m + m := by
  have square : 2 * Real.sqrt X * m ≤ X + m ^ 2 := by
    nlinarith [sq_nonneg (m - Real.sqrt X), Real.sq_sqrt hX]
  calc
    2 * Real.sqrt X ≤ (X + m^2) / m := (le_div_iff₀ hm).2 square
    _ = X / m + m := by field_simp

theorem chainCostAtRoot {X : ℝ} (hX : 0 < X) :
    X / Real.sqrt X + Real.sqrt X = 2 * Real.sqrt X := by
  have h : X / Real.sqrt X = Real.sqrt X :=
    (div_eq_iff (Real.sqrt_pos.2 hX).ne').2 (Real.mul_self_sqrt hX.le).symm
  rw [h, two_mul]

end RH17
