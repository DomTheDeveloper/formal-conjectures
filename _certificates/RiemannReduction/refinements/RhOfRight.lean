import Mathlib

theorem Formalism.VW.rh_of_right (hz : ∀ s : ℂ, 1 / 2 < s.re → s ≠ 1 → riemannZeta s ≠ 0) :
    RiemannHypothesis := by
  intro s zero nontrivial ne_one
  rcases lt_trichotomy s.re (1 / 2) with left | middle | right
  · have ne_zero : s ≠ 0 := by rintro rfl; rw [riemannZeta_zero] at zero; norm_num at zero
    have gamma_ne : Complex.Gammaℝ s ≠ 0 := by
      rw [Ne, Complex.Gammaℝ_eq_zero_iff]
      rintro ⟨_ | n, hn⟩
      · exact ne_zero (by simpa using hn)
      · exact nontrivial ⟨n, by rw [hn]; push_cast; ring⟩
    have completed := (div_eq_zero_iff.1 ((riemannZeta_def_of_ne_zero ne_zero).symm.trans zero)).resolve_right gamma_ne
    apply False.elim <| hz (1 - s) (by simp; linarith) (fun h => ne_zero (by simpa using h)) ?_
    rw [riemannZeta_def_of_ne_zero (sub_ne_zero.2 ne_one.symm), completedRiemannZeta_one_sub, completed, zero_div]
  · exact middle
  · exact (hz s right ne_one zero).elim
