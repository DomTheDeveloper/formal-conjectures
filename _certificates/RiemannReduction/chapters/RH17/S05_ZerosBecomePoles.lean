import RH17.S04_MellinTransform
import Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.poleData

/-! # 5. A zero survives in the transform
The logarithmic derivative of a function with a zero of multiplicity m has a
simple pole with residue m. At a nontrivial zeta zero ρ this gives the centered
transform a residue −m/(ρ(ρ−1)). Its nonvanishing lets the next step detect the
zero. The archive also tracks the sign when the pole is real. -/

namespace RH17

theorem zeroMemPoleSet {s : ℂ} (hp : 0 < s.re) (hz : riemannZeta s = 0) :
    s ∈ Deduction.zeroSet zetaFamily :=
  ⟨hp, (), Or.inl ((singleL s).trans hz)⟩

theorem logStatistic : Deduction.gm zetaFamily = fun u => primeError (Real.exp u) :=
  funext fun u => singleSum (Real.exp u)

theorem primeTransformExists : ∃ Φ : ℂ → ℂ,
    Deduction.PoleData (fun u => primeError (Real.exp u)) Φ (Deduction.zeroSet zetaFamily) := by
  rw [← logStatistic]
  exact Deduction.poleData zetaFamily

end RH17
