import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Tactic

def UpperTheory.EveryCharacter : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ), 1 / 2 < s.re → (χ ≠ 1 ∨ s ≠ 1) → DirichletCharacter.LFunction χ s ≠ 0

theorem UpperTheory.zeta_ne_zero_of_everyCharacter (h : UpperTheory.EveryCharacter) : ∀ s : ℂ, 1 / 2 < s.re → s ≠ 1 → riemannZeta s ≠ 0 := fun s hs h1 => by
  have := h 1 1 s hs (Or.inr h1)
  rwa [DirichletCharacter.LFunction_modOne_eq] at this

theorem UpperTheory.riemannHypothesis_of_everyCharacter (h : UpperTheory.EveryCharacter) : RiemannHypothesis := by
  intro s hs hn h1
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hs0 : s ≠ 0 := by rintro rfl; rw [riemannZeta_zero] at hs; norm_num at hs
    have h1s : (1 - s) ≠ 1 := fun e => hs0 (by simpa using e)
    have hz : riemannZeta (1 - s) ≠ 0 := UpperTheory.zeta_ne_zero_of_everyCharacter h (1 - s) (by simp; linarith) h1s
    have hc : completedRiemannZeta s = completedRiemannZeta (1 - s) := (completedRiemannZeta_one_sub s).symm
    have h1s0 : (1 - s) ≠ 0 := fun e => h1 (by linear_combination -e)
    rw [riemannZeta_def_of_ne_zero hs0, div_eq_zero_iff] at hs
    rcases hs with hs | hs
    · exact hz (by rw [riemannZeta_def_of_ne_zero h1s0, ← hc, hs, zero_div])
    · obtain ⟨n, hn'⟩ := Complex.Gammaℝ_eq_zero_iff.1 hs
      rcases n with _ | n
      · exact hs0 (by simpa using hn')
      · exact hn ⟨n, by rw [hn']; push_cast; ring⟩
  · exact UpperTheory.zeta_ne_zero_of_everyCharacter h s hgt h1 hs

#print axioms UpperTheory.riemannHypothesis_of_everyCharacter
