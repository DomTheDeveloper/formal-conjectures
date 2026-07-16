import FormalConjectures.Util.ProblemImports

namespace BeaverMathOlympiad

@[category research solved, AMS 5 11 68]
theorem bmo4_complete_test
    (a : ℕ → ℕ)
    (a_ini : a 0 = 2)
    (a_rec : ∀ n, a (n+1)
      = if a n % 3 = 0 then a n / 3 + 2 ^ n + 1 else (a n - 2) / 3 + 2 ^ n - 1) :
    ¬ (∃ n, a n % 3 = 1) := by
  have hclosed : ∀ n : ℕ,
      (n % 4 = 0 ∧ 5 * a n = 3 * 2 ^ n + 7) ∨
      (n % 4 = 1 ∧ 5 * a n + 6 = 3 * 2 ^ n) ∨
      (n % 4 = 2 ∧ 5 * a n = 3 * 2 ^ n + 3) ∨
      (n % 4 = 3 ∧ 5 * a n = 3 * 2 ^ n + 6) := by
    intro n
    induction n with
    | zero =>
        exact Or.inl ⟨by norm_num, by norm_num [a_ini]⟩
    | succ n ih =>
        rcases ih with h0 | h1 | h2 | h3
        · rcases h0 with ⟨hn4, hform⟩
          have hamod : a n % 3 = 2 := by omega
          have hdiv : a n = 3 * ((a n - 2) / 3) + 2 := by omega
          refine Or.inr (Or.inl ⟨?_, ?_⟩)
          · omega
          · rw [a_rec n]
            simp [hamod, pow_succ]
            omega
        · rcases h1 with ⟨hn4, hform⟩
          have hamod : a n % 3 = 0 := by omega
          have hdiv : a n = 3 * (a n / 3) := by omega
          refine Or.inr (Or.inr (Or.inl ⟨?_, ?_⟩))
          · omega
          · rw [a_rec n]
            simp [hamod, pow_succ]
            omega
        · rcases h2 with ⟨hn4, hform⟩
          have hamod : a n % 3 = 0 := by omega
          have hdiv : a n = 3 * (a n / 3) := by omega
          refine Or.inr (Or.inr (Or.inr ⟨?_, ?_⟩))
          · omega
          · rw [a_rec n]
            simp [hamod, pow_succ]
            omega
        · rcases h3 with ⟨hn4, hform⟩
          have hamod : a n % 3 = 0 := by omega
          have hdiv : a n = 3 * (a n / 3) := by omega
          refine Or.inl ⟨?_, ?_⟩
          · omega
          · rw [a_rec n]
            simp [hamod, pow_succ]
            omega
  rintro ⟨n, hn⟩
  rcases hclosed n with h0 | h1 | h2 | h3
  · omega
  · omega
  · omega
  · omega

#print axioms bmo4_complete_test

end BeaverMathOlympiad
