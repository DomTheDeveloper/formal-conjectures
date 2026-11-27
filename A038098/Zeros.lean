module

public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Shift
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

/-! For a zero on the critical line, bound its contribution to the four-point
integrated explicit formula in each of the three frequency ranges. -/
public section
namespace Sun.CubeAnalytic
open Real

noncomputable def zeroKernel (z : ℂ) (t : ℝ) : ℂ :=
  (t:ℂ)^(z+1)/(z+1)/z

noncomputable def fourKernel (z : ℂ) (a b d : ℝ) : ℂ :=
  (zeroKernel z (b+d)-zeroKernel z b)-(zeroKernel z (a+d)-zeroKernel z a)

private theorem segment {f f' : ℝ → ℂ} {a b C : ℝ} (hab : a ≤ b)
    (hf : ∀ t ∈ Set.Icc a b, HasDerivAt f (f' t) t)
    (hb : ∀ t ∈ Set.Ico a b, ‖f' t‖ ≤ C) : ‖f b-f a‖ ≤ C*(b-a) :=
  norm_image_sub_le_of_norm_deriv_le_segment' (fun t ht => (hf t ht).hasDerivWithinAt)
    hb b ⟨hab,le_rfl⟩

private noncomputable def zeroFirst (z : ℂ) (t : ℝ) : ℂ := (t:ℂ)^z/z

private theorem deriv_kernel {z : ℂ} (hz : z.re=1/2) {t : ℝ} (ht : 0<t) :
    HasDerivAt (zeroKernel z) (zeroFirst z t) t := by
  have he : z ≠ -1 := by
    intro h; rw [h] at hz; norm_num at hz
  exact (hasDerivAt_ofReal_cpow_const' ht.ne' he).div_const z

private theorem deriv_first {z : ℂ} (hz : z.re=1/2) {t : ℝ} (ht : 0<t) :
    HasDerivAt (zeroFirst z) ((t:ℂ)^(z-1)) t := by
  have he : z ≠ 0 := by
    intro h; rw [h] at hz; norm_num at hz
  simpa only [zeroFirst, mul_div_cancel_left₀ _ he] using
    (hasDerivAt_ofReal_cpow_const ht.ne' he).div_const z

/-- Before rounding the numerical cutoffs, the three bounds come respectively
from two derivatives, one derivative, and the four endpoint values. -/
theorem fourKernel_le {z : ℂ} (hz : z.re = 1/2) (hi : 0 < |z.im|)
    {a b d : ℝ} (ha : 0<a) (hab : a≤b) (hd : 0≤d) :
    ‖fourKernel z a b d‖ ≤ min (d*(b-a)/√a)
      (min (2*d*√(b+d)/|z.im|) (4*((b+d)*√(b+d))/|z.im|^2)) := by
  let s := |z.im|
  have hs : 0<s := hi
  have hn : s ≤ ‖z‖ := Complex.abs_im_le_norm _
  have hn1 : s ≤ ‖z+1‖ := by simpa [s] using Complex.abs_im_le_norm (z+1)
  have trunc (t : ℝ) (ht : 0≤t) :
      ‖zeroFirst z (b+t)-zeroFirst z (a+t)‖ ≤ (b-a)/√a := by
    have h := segment (f := zeroFirst z) (f' := fun u : ℝ => (u:ℂ)^(z-1))
      (a := a+t) (b := b+t) (C := 1/√a) (by linarith)
      (fun u hu => deriv_first hz (by linarith [hu.1])) (fun u hu => by
        have hu0 : 0 < u := by linarith [hu.1]
        rw [Complex.norm_cpow_eq_rpow_re_of_pos hu0,Complex.sub_re,hz,Complex.one_re,
          show (1/2:ℝ)-1= -(1/2) by norm_num,Real.rpow_neg hu0.le,← Real.sqrt_eq_rpow,← one_div]
        exact one_div_le_one_div_of_le (sqrt_pos.2 ha) (sqrt_le_sqrt (by linarith [hu.1])))
    convert h using 1 <;> ring
  have low := segment (f := fun t => zeroKernel z (b+t)-zeroKernel z (a+t))
    (f' := fun t => zeroFirst z (b+t)-zeroFirst z (a+t))
    (a := 0) (b := d) (C := (b-a)/√a) hd
    (fun t ht => ((deriv_kernel hz (show 0 < b+t by linarith [ht.1])).comp_const_add b t).sub
      ((deriv_kernel hz (show 0 < a+t by linarith [ht.1])).comp_const_add a t))
    (fun t ht => trunc t ht.1)
  simp only [add_zero,sub_zero] at low
  have reord : fourKernel z a b d = (zeroKernel z (b+d)-zeroKernel z (a+d)) -
      (zeroKernel z b-zeroKernel z a) := by unfold fourKernel; abel
  refine le_min ?_ (le_min ?_ ?_)
  · rw [reord]
    exact low.trans_eq (by ring)
  · have increment (u : ℝ) (hu : a≤u) (hu' : u≤b) :
        ‖zeroKernel z (u+d)-zeroKernel z u‖ ≤ (√(b+d)/s)*d := by
      have h := segment (f := zeroKernel z) (f' := zeroFirst z)
        (a := u) (b := u+d) (C := √(b+d)/s) (by linarith)
        (fun v hv => deriv_kernel hz (by linarith [hv.1])) (fun v hv => by
          have hv0 : 0<v := by linarith [hv.1]
          rw [zeroFirst,norm_div,Complex.norm_cpow_eq_rpow_re_of_pos hv0,hz,← sqrt_eq_rpow]
          exact (div_le_div_of_nonneg_right (sqrt_le_sqrt (by linarith [hv.2])) (norm_nonneg _)).trans
            (div_le_div_of_nonneg_left (sqrt_nonneg _) hs hn))
      simpa only [add_sub_cancel_left] using h
    have ht := norm_sub_le (zeroKernel z (b+d)-zeroKernel z b) (zeroKernel z (a+d)-zeroKernel z a)
    change ‖_ - _‖ ≤ 2*d*√(b+d)/s
    calc _ ≤ (√(b+d)/s)*d+(√(b+d)/s)*d := ht.trans (add_le_add (increment b hab le_rfl) (increment a le_rfl hab))
         _ = _ := by ring
  · let C := (b+d)*√(b+d)/s^2
    have endpoint (t : ℝ) (ht : a≤t) (ht' : t≤b+d) : ‖zeroKernel z t‖ ≤ C := by
      have ht0 : 0<t := by linarith
      rw [zeroKernel,norm_div,norm_div,Complex.norm_cpow_eq_rpow_re_of_pos ht0,Complex.add_re,hz,
        Complex.one_re,show (1/2:ℝ)+1=1+1/2 by norm_num,Real.rpow_add ht0,Real.rpow_one,← sqrt_eq_rpow,div_div]
      have hM : s^2 ≤ ‖z+1‖*‖z‖ := by rw [pow_two]; exact mul_le_mul hn1 hn hs.le (norm_nonneg _)
      exact (div_le_div_of_nonneg_right (mul_le_mul ht' (sqrt_le_sqrt ht') (sqrt_nonneg _) (by linarith))
        (by positivity)).trans (div_le_div_of_nonneg_left (by positivity) (by positivity) hM)
    have h1 := (norm_sub_le (zeroKernel z (b+d)) (zeroKernel z b)).trans
      (add_le_add (endpoint (b+d) (by linarith) le_rfl) (endpoint b hab (by linarith)))
    have h2 := (norm_sub_le (zeroKernel z (a+d)) (zeroKernel z a)).trans
      (add_le_add (endpoint (a+d) (by linarith) (by linarith)) (endpoint a le_rfl (by linarith)))
    have H := (norm_sub_le (zeroKernel z (b+d)-zeroKernel z b) (zeroKernel z (a+d)-zeroKernel z a)).trans (add_le_add h1 h2)
    change ‖_ - _‖ ≤ 4*((b+d)*√(b+d))/s^2
    exact H.trans_eq (by dsimp [C]; ring)

end Sun.CubeAnalytic
#print axioms Sun.CubeAnalytic.fourKernel_le
