import RH17.S09_Reflection

/-! # 10. What a hypothetical zero would force
For any fixed multiplier C, every sufficiently late window would contain a
point where the upper bound C·y^θ fails. This is the precise obstruction to a
zero. Individual terms can oscillate inside each window. -/

namespace RH17

theorem forcedExcursion {s : ℂ} {θ δ : ℝ} (hθ : 0 < θ) (hθ' : θ < 1)
    (hδ : 0 < δ) (hs : θ < s.re) (hz : riemannZeta s = 0) (C : ℝ) :
    ∃ start : ℝ, ∀ Y ≥ start, ∃ y ∈ Set.Icc Y (Y ^ (1+δ)), C * y ^ θ < primeError y := by
  classical
  have impossible : ¬ OnWindows δ (fun y => primeError y ≤ C * y ^ θ) :=
    fun windows => (noZeroOfPowerWindows hθ hθ' hδ ⟨C, windows⟩ hs) hz
  unfold OnWindows at impossible
  push Not at impossible
  exact impossible

end RH17
