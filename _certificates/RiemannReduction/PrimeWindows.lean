import Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.ZeroFreeOfRpowWindow
import Formalism.GammaFactorNonvanishing.RhOfRight
import Mathlib.Tactic

namespace RiemannReduction

private noncomputable def zetaFamily : Deduction.CharFamily where
  ι := Unit
  fin := inferInstance
  N _ := 1
  nz _ := inferInstance
  χ _ := 1
  a _ := 1
  a_pos _ := one_pos
  adm _ := Or.inl rfl

private theorem trivialPrimeSum (y : ℝ) :
    (Deduction.Gchi (1 : DirichletCharacter ℂ 1) y).re = Deduction.G y := by
  have hχ : (fun n : ℕ => (1 : DirichletCharacter ℂ 1) n) = fun _ => (1 : ℂ) :=
    funext fun _ => MulChar.one_apply (isUnit_of_subsingleton _)
  simp [Deduction.Gchi, Deduction.G, hχ, Complex.add_re, Complex.sub_re]

private theorem zetaPrimeSum (y : ℝ) : Deduction.Gm zetaFamily y = Deduction.G y := by
  simpa [Deduction.Gm, zetaFamily] using trivialPrimeSum y

private theorem zetaL (s : ℂ) : DirichletCharacter.LFunction (zetaFamily.χ ()) s = riemannZeta s :=
  congrFun (DirichletCharacter.LFunction_modOne_eq (χ := zetaFamily.χ ())) s

/-- The arithmetic part must supply one-sided bounds on arbitrarily late windows. -/
theorem rh_of_prime_windows
    (windows : ∀ θ : ℝ, 1/2 < θ → θ < 1 → ∃ C : ℝ, ∀ start : ℝ, ∃ Y ≥ start,
      ∀ y ∈ Set.Icc Y (Y ^ (1 + (1/2 : ℝ))), Deduction.G y ≤ C * y ^ θ) :
    RiemannHypothesis := by
  apply Formalism.VW.rh_of_right
  intro s hs _
  obtain ⟨θ, hhalf, hsmall⟩ := exists_between (lt_min hs (by norm_num : (1/2 : ℝ) < 1))
  have hθ := hsmall.trans_le (min_le_right _ _)
  obtain ⟨C, hC⟩ := windows θ hhalf hθ
  have bound := Deduction.zeroFree_of_rpow_window zetaFamily (C := C)
    ((by norm_num : (0 : ℝ) < 1/2).trans hhalf) hθ (by norm_num : (0 : ℝ) < 1/2)
    (by simpa only [zetaPrimeSum] using hC)
  have hL := bound () s (hsmall.trans_le (min_le_left _ _))
  rwa [zetaL] at hL

#print axioms rh_of_prime_windows

end RiemannReduction
