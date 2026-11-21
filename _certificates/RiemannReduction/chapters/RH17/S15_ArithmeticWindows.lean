import RH17.S03_Windows
import RH17.S13_ThetaChains
import RH17.S14_TrivialLevel

/-! # 15. Produce the one-sided bound for the actual prime statistic
The arithmetic comparison gives exponent 1/2+(d+l+7)ε. The constants d,l
are fixed before choosing ε. For a requested θ>1/2, choose ε so the cost fits
inside θ−1/2. Taking the window past both the comparison threshold and 1
allows this exponent change at every real point in the interval. -/

namespace RH17

open Formalism.BasicNotions Formalism.MainNotions Formalism.HC UpperTheory.Top GlobalTheory.EX

theorem primeWindowsOfTied (tied : ZetaTiedWindows) : NearHalf primeError (1/2) := by
  intro θ hθ _
  obtain ⟨d, l, ε₀, hε₀, families⟩ := tied
  obtain ⟨ε, pos, small, budget⟩ := exists_small_eps (d+l+7) (sub_pos.mpr hθ) hε₀
  obtain ⟨F, fits, windows, estimates⟩ := families ε pos small
  obtain ⟨cut, bound⟩ := UpperTheory.Comparison₂.level_gm_le_on_family_scales
    (Level.cyc PChar.one) d l ε pos F fits estimates
  refine ⟨1, ?_⟩
  intro start
  obtain ⟨Y, late, covers⟩ := (windows_iff _ _).mp windows (max start (max cut 1))
  refine ⟨Y, (le_max_left _ _).trans late, ?_⟩
  intro y hy
  have past : max cut 1 ≤ y := (le_max_right _ _).trans (late.trans hy.1)
  have width : (1 : ℝ) + 1/2 = 3/2 := by norm_num
  have mem := covers y hy.1 (by simpa only [width] using hy.2)
  have arith := bound y ((le_max_left _ _).trans past) mem
  rw [trivialLevelSum] at arith
  rw [one_mul]
  exact arith.trans (Real.rpow_le_rpow_of_exponent_le ((le_max_right _ _).trans past) (by linarith))

end RH17
