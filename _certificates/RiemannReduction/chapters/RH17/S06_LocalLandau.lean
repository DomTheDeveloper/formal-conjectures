import RH17.S05_ZerosBecomePoles
import Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.landauWindow
import Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.WindowHypUOfWindowHyp

/-! # 6. Detect a pole from one-sided information on long intervals
Write u = log y. The kth derivative of the Laplace transform has weight
u^k exp(−σu)/k!, concentrated near k/σ. Choosing k to place that peak in the
window bounds the derivative. A pole with real part above θ would force larger
derivatives. `landau_window` supplies this analytic implication. -/

namespace RH17

theorem rightOfEnvelope {θ δ : ℝ} (hθ : 0 < θ) (hθ' : θ < 1) (hδ : 0 < δ)
    (henv : Deduction.WindowHyp zetaFamily θ δ) {s : ℂ} (hs : θ < s.re) :
    riemannZeta s ≠ 0 := by
  obtain ⟨Φ, hΦ⟩ := primeTransformExists
  have hlog := Deduction.windowHypU_of_windowHyp zetaFamily hδ henv
  rw [logStatistic] at hlog
  intro hz
  exact (not_le_of_gt hs) (Deduction.landau_window hΦ hθ hθ' hδ hlog s
    (zeroMemPoleSet (hθ.trans hs) hz))

end RH17
