import RH17.S07_PositiveMass
import RH17.S08_PointwiseBounds
import Formalism.GammaFactorNonvanishing.RhOfRight

/-! # 9. Reflect to the critical line
Given a putative zero with real part σ > 1/2, choose θ strictly between 1/2
and min(σ,1). The window estimate at this θ excludes it. The zeta functional
equation rules out a nontrivial zero to the left by reflecting it to the right.
The archive's reflection lemma handles the trivial zeros and the point 1
exactly as Mathlib's definition of RH requires. -/

namespace RH17

theorem rhOfPowerWindows {δ : ℝ} (hδ : 0 < δ) (windows : NearHalf primeError δ) :
    RiemannHypothesis := by
  apply Formalism.VW.rh_of_right
  intro s hs _
  obtain ⟨θ, hθ, small⟩ := exists_between (lt_min hs (by norm_num : (1/2 : ℝ) < 1))
  have belowOne := small.trans_le (min_le_right _ _)
  exact noZeroOfPowerWindows (lt_trans (by norm_num : (0 : ℝ) < 1/2) hθ) belowOne hδ
    (windows θ hθ belowOne) (small.trans_le (min_le_left _ _))

theorem rhOfSmallMass {δ : ℝ} (hδ : 0 < δ) (mass : SmallPositiveMass δ) :
    RiemannHypothesis :=
  Formalism.VW.rh_of_right fun _ hs _ =>
    rightOfEnvelope (by norm_num) (by norm_num) hδ (envelopeOfSmallMass mass) hs

end RH17
