import RH17.S06_LocalLandau

/-! # 7. How little of the prime error needs control?
At θ = 1/2 the localized theorem can use the positive part of G itself as the
upper envelope. Its weighted mass on a window is the integral of
max(G(y),0)·y^(−3/2). This file specializes the archive's integral criterion.
The statement explicitly records integrability on the selected intervals. -/

namespace RH17

open MeasureTheory Set

noncomputable def positivePart (y : ℝ) := max (primeError y) 0

def SmallPositiveMass (δ : ℝ) : Prop :=
  ∀ η : ℝ, 0 < η → ∀ start : ℝ, ∃ Y ≥ start,
    IntegrableOn (fun y => positivePart y * y ^ (-(3/2) : ℝ)) (Icc Y (Y ^ (1+δ))) ∧
    (∫ y in Icc Y (Y ^ (1+δ)), positivePart y * y ^ (-(3/2) : ℝ)) ≤ Y ^ η

theorem envelopeOfSmallMass {δ : ℝ} (h : SmallPositiveMass δ) :
    Deduction.WindowHyp zetaFamily (1/2) δ := by
  intro η hη start
  obtain ⟨Y, hy, hInt, bound⟩ := h η hη start
  have exponent : -(1/2 : ℝ) - 1 = -(3/2) := by norm_num
  refine ⟨Y, hy, positivePart, ?_, ?_, ?_⟩
  · simpa only [exponent] using hInt
  · intro y _
    exact ⟨le_max_right _ _, (singleSum y).le.trans (le_max_left _ _)⟩
  · simpa only [exponent] using bound

end RH17
