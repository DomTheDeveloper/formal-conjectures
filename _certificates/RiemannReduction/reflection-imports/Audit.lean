import Main

-- Check the five public constants independently of the publisher's statement aliases.
example : RiemannHypothesis := riemannHypothesis
example : ∀ s : ℂ, riemannZeta s = 0 → (¬∃ n : ℕ, s = -2 * ((n : ℂ) + 1)) →
    s ≠ 1 → s.re = 1 / 2 := riemannZeta_eq_zero_re
example : ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ),
    1 / 2 < s.re → (χ ≠ 1 ∨ s ≠ 1) → χ.LFunction s ≠ 0 := LFunction_ne_zero_of_half_lt_re
example : ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ),
    0 < s.re → s.re < 1 → χ.LFunction s = 0 → s.re = 1 / 2 := LFunction_eq_zero_re
example : ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive →
    ∀ s : ℂ, 0 < s.re → s.re < 1 → χ.LFunction s = 0 → s.re = 1 / 2 :=
  LFunction_eq_zero_re_of_isPrimitive

#print axioms riemannHypothesis
#print axioms riemannZeta_eq_zero_re
#print axioms LFunction_ne_zero_of_half_lt_re
#print axioms LFunction_eq_zero_re
#print axioms LFunction_eq_zero_re_of_isPrimitive
