import Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.ZeroFreeOfRpowWindow
import Formalism.GammaFactorNonvanishing.RhOfRight

namespace RiemannReduction

private noncomputable def zetaFamily : Deduction.CharFamily where
  ι := Unit
  N _ := 1
  χ _ := 1
  a _ := 1
  a_pos _ := one_pos
  adm _ := Or.inl rfl

private theorem primeSum (y : ℝ) : Deduction.Gm zetaFamily y = Deduction.G y := by
  change (∑ _ : Unit, (1 : ℝ) * (Deduction.Gchi (1 : DirichletCharacter ℂ 1) y).re) = _
  have trivial : (fun n : ℕ => (1 : DirichletCharacter ℂ 1) n) = fun _ => (1 : ℂ) :=
    funext fun _ => MulChar.one_apply (isUnit_of_subsingleton _)
  simp [Deduction.Gchi, Deduction.G, trivial, Complex.add_re, Complex.sub_re]

/-- A one-sided estimate on arbitrarily late prime-counting windows suffices for RH. -/
theorem rh_of_prime_windows
    (windows : ∀ θ : ℝ, 1/2 < θ → θ < 1 → ∃ C : ℝ, ∀ start : ℝ, ∃ Y ≥ start,
      ∀ y ∈ Set.Icc Y (Y ^ (1 + (1/2 : ℝ))), Deduction.G y ≤ C * y ^ θ) : RiemannHypothesis := by
  apply Formalism.VW.rh_of_right
  intro s hs _
  obtain ⟨θ, hθ, hsmall⟩ := exists_between (lt_min hs (by norm_num : (1/2 : ℝ) < 1))
  have belowOne := hsmall.trans_le (min_le_right _ _)
  obtain ⟨C, quiet⟩ := windows θ hθ belowOne
  have zeroFree := Deduction.zeroFree_of_rpow_window zetaFamily (C := C) (by linarith : 0 < θ)
    belowOne (by norm_num : (0 : ℝ) < 1/2) (by simpa only [primeSum] using quiet)
  simpa only [zetaFamily, DirichletCharacter.LFunction_modOne_eq] using
    zeroFree () s (hsmall.trans_le (min_le_left _ _))

#print axioms rh_of_prime_windows

end RiemannReduction
