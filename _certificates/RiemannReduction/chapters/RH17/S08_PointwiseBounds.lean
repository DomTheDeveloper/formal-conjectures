import RH17.S03_Windows
import RH17.S06_LocalLandau
import Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.WindowHypOfRpow

/-! # 8. Turn a power bound into an integral bound
If G(y) ≤ C·y^θ, the positive envelope |C|·y^θ contributes at most
|C|·δ·log Y after multiplication by y^(−θ−1) and integration across the
window. Every positive power of Y eventually dominates this logarithm. -/

namespace RH17

theorem noZeroOfPowerWindows {θ δ : ℝ} (hθ : 0 < θ) (hθ' : θ < 1) (hδ : 0 < δ)
    (h : PowerWindows primeError δ θ) {s : ℂ} (hs : θ < s.re) : riemannZeta s ≠ 0 := by
  obtain ⟨C, windows⟩ := h
  apply rightOfEnvelope hθ hθ' hδ _ hs
  apply Deduction.windowHyp_of_rpow zetaFamily (C := C) hδ
  intro start
  obtain ⟨Y, hY, upper⟩ := windows start
  exact ⟨Y, hY, fun y hy => (singleSum y).le.trans (upper y hy)⟩

end RH17
