import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Tactic

open Complex ComplexConjugate

namespace RHReflection

/-- A nontrivial zero in the left half-plane gives a zero at its reflected point. -/
private theorem reflected_zero (s : ℂ) (zero : riemannZeta s = 0)
    (nontrivial : ¬∃ n : ℕ, s = -2 * (n + 1)) (ne_one : s ≠ 1) :
    riemannZeta (1 - s) = 0 := by
  have ne_zero : s ≠ 0 := by rintro rfl; norm_num [riemannZeta_zero] at zero
  have gamma_ne : Gammaℝ s ≠ 0 := by
    rw [Ne, Gammaℝ_eq_zero_iff]
    rintro ⟨_ | n, hn⟩
    · exact ne_zero (by simpa using hn)
    · exact nontrivial ⟨n, by rw [hn]; push_cast; ring⟩
  have completed := (div_eq_zero_iff.1 ((riemannZeta_def_of_ne_zero ne_zero).symm.trans zero)).resolve_right gamma_ne
  rw [riemannZeta_def_of_ne_zero (sub_ne_zero.2 ne_one.symm), completedRiemannZeta_one_sub, completed, zero_div]

/-- Ordinary RH is equivalent to nonvanishing in the upper right part of the critical strip. -/
theorem iff_upper_right :
    RiemannHypothesis ↔ ∀ s : ℂ, 1 / 2 < s.re → s.re < 1 → 0 ≤ s.im → riemannZeta s ≠ 0 := by
  constructor
  · intro rh s half _ _ zero
    have nontrivial : ¬∃ n : ℕ, s = -2 * (n + 1) := by
      rintro ⟨n, rfl⟩
      simp at half
      linarith [Nat.cast_nonneg (α := ℝ) n]
    exact half.ne' (rh s zero nontrivial (by rintro rfl; simp_all))
  · intro upper
    have right (s : ℂ) (half : 1 / 2 < s.re) : riemannZeta s ≠ 0 := by
      by_cases one : s.re < 1
      · by_cases im : 0 ≤ s.im
        · exact upper s half one im
        · intro zero
          exact upper (conj s) (by simpa only [conj_re] using half) (by simpa only [conj_re] using one)
            (by simpa only [conj_im, neg_nonneg] using (le_of_not_ge im))
            (by rw [riemannZeta_conj, zero, map_zero])
      · exact riemannZeta_ne_zero_of_one_le_re (le_of_not_gt one)
    intro s zero nontrivial ne_one
    rcases lt_trichotomy s.re (1 / 2) with left | equal | rightHalf
    · exact False.elim (right (1 - s) (by simp; linarith) (reflected_zero s zero nontrivial ne_one))
    · exact equal
    · exact False.elim (right s rightHalf zero)

#print axioms iff_upper_right
end RHReflection
