import RH17.S01_PrimeSum

/-! # 2. Keep only zeta
The character modulo one takes the value one at every integer. Taking its
weight to be one makes the archive's family statistic exactly the real prime
error. There is then one L-function to test. -/

namespace RH17

noncomputable def zetaFamily : Deduction.CharFamily where
  ι := Unit
  fin := inferInstance
  N _ := 1
  nz _ := inferInstance
  χ _ := 1
  a _ := 1
  a_pos _ := one_pos
  adm _ := Or.inl rfl

theorem trivialSum (y : ℝ) :
    (Deduction.Gchi (1 : DirichletCharacter ℂ 1) y).re = primeError y := by
  have trivialValue : (fun n : ℕ => (1 : DirichletCharacter ℂ 1) n) = fun _ => (1 : ℂ) :=
    funext fun _ => MulChar.one_apply (isUnit_of_subsingleton _)
  simp [Deduction.Gchi, Deduction.G, trivialValue, Complex.add_re, Complex.sub_re]

@[simp] theorem singleSum (y : ℝ) : Deduction.Gm zetaFamily y = primeError y := by
  change (∑ _ : Unit, (1 : ℝ) * (Deduction.Gchi (1 : DirichletCharacter ℂ 1) y).re) = _
  simpa using trivialSum y

theorem singleL (s : ℂ) : DirichletCharacter.LFunction (1 : DirichletCharacter ℂ 1) s = riemannZeta s :=
  congrFun (DirichletCharacter.LFunction_modOne_eq (χ := (1 : DirichletCharacter ℂ 1))) s

end RH17
