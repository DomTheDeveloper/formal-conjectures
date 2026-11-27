import A038098.Assembly
import A038098.IntegralIdentity
import Schoenfeld.PsiSharp

/-! Adapter for senamakel/conjectures-lean, commit f34a54829210, on its
pinned Lean 4.36 toolchain. -/
namespace Sun.CubeBridge
open Sun.CubeAnalytic Schoenfeld Real

private theorem nonzero_height (h : RiemannHypothesis) (ρ : Zeros) : 0 < |(ρ:ℂ).im| := by
  apply abs_pos.2
  intro he
  have hp := im_sq_pos h ρ
  rw [he] at hp
  norm_num at hp

private theorem counted_zeros (h : RiemannHypothesis) (R : RosserZeroCount)
    (S : Finset Zeros) (t : ℝ) (ht : 1000000 ≤ t) :
    counted S (fun ρ : Zeros => |(ρ:ℂ).im|) (fun ρ => mult ρ/2) t ≤ countMajorant t := by
  classical
  have ht0 : 0≤t := by linarith
  have hs := ind_summable h ht0
  have hr : Summable (fun ρ => ind t (reflect ρ)) := reflect.summable_iff.mpr hs
  have point (ρ : Zeros) :
      (if |(ρ:ℂ).im|<t then mult ρ/2 else 0) ≤ (ind t ρ+ind t (reflect ρ))/2 := by
    by_cases hh : |(ρ:ℂ).im|<t
    · rw [if_pos hh]
      by_cases hp : 0<(ρ:ℂ).im
      · have hj : ind t ρ=mult ρ := by
          simp [ind,hp,((le_abs_self _).trans hh.le)]
        rw [hj]
        linarith [ind_nonneg t (reflect ρ)]
      · have hn : (ρ:ℂ).im<0 := lt_of_le_of_ne (le_of_not_gt hp) (abs_pos.1 (nonzero_height h ρ))
        have hf : ind t (reflect ρ)=mult ρ := by
          rw [abs_of_neg hn] at hh
          simp [ind,im_reflect,mult_reflect,neg_pos.2 hn,hh.le]
        rw [hf]
        linarith [ind_nonneg t ρ]
    · rw [if_neg hh]
      linarith [ind_nonneg t (reflect ρ), ind_nonneg t ρ]
  calc counted S (fun ρ : Zeros => |(ρ:ℂ).im|) (fun ρ => mult ρ/2) t ≤
      ∑ ρ∈S, (ind t ρ+ind t (reflect ρ))/2 := Finset.sum_le_sum fun ρ _ => point ρ
    _ = (∑ ρ∈S, (ind t ρ + ind t (reflect ρ)))/2 := (Finset.sum_div ..).symm
    _ ≤ (∑' ρ, (ind t ρ + ind t (reflect ρ)))/2 := div_le_div_of_nonneg_right
      (Summable.sum_le_tsum _ (fun ρ _ => add_nonneg (ind_nonneg t ρ) (ind_nonneg t (reflect ρ)))
        (hs.add hr)) (by norm_num)
    _ = cnt t := by rw [hs.tsum_add hr,reflect.tsum_eq (ind t),cnt_eq]; ring
    _ ≤ Nc t := cnt_le_Nc R (by linarith)
    _ ≤ countMajorant t := by
      have H : exp (4:ℝ) ≤ 1000000 := calc
        exp 4 = exp 1^4 := by rw [← exp_nat_mul]; norm_num
        _ ≤ 3^4 := pow_le_pow_left₀ (exp_pos _).le (by linarith [exp_one_lt_d9]) 4
        _ ≤ _ := by norm_num
      have hlog := (le_log_iff_exp_le (by linarith : 0<t)).2 (H.trans ht)
      unfold countMajorant Nc
      linarith

private theorem term_eq (k : ℕ) (hk : 1≤k) (ρ : Zeros) :
    (mult ρ:ℂ)*zeroKernel (ρ:ℂ) (k:ℝ) = (k:ℂ)*tW k ρ := by
  unfold zeroKernel tW
  rw [← nat_mul_cpow k hk]
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

private theorem smoothing (h : RiemannHypothesis) (R : RosserZeroCount) {n : ℕ}
    (hn : 2000000≤n) : SmoothedBound n := by
  refine smoothed_from_explicit_formula (fun ρ : Zeros => (ρ:ℂ)) mult
    (fun ρ => re_eq_half h ρ) (nonzero_height h) mult_nonneg
    (E := fun k => (k:ℝ)*Efun k) (c₁ := kappa) (c₀ := delta) ?_ ?_ Efun_bounds
    (counted_zeros h R) hn
  · intro k hk
    exact ((summable_tW h k hk).mul_left (k:ℂ)).congr (fun ρ => (term_eq k hk ρ).symm)
  · intro k hk
    have hs : (∑' ρ : Zeros, (mult ρ:ℂ)*zeroKernel (ρ:ℂ) (k:ℝ)) =
        (k:ℂ)*(∑' ρ, tW k ρ) := by
      calc _ = ∑' ρ, (k:ℂ)*tW k ρ := tsum_congr (term_eq k hk)
           _ = _ := tsum_mul_left
    have e : (∫ t in (1:ℝ)..(k:ℝ), Chebyshev.psi t) = psi1 (k:ℝ) := by
      rw [integral_psi_eq_weighted_sum k hk,psi1,Nat.floor_natCast]
    rw [e,psi1_nat_eq h k hk,hs,Complex.mul_re]
    simp

theorem cubes_above_buthe_of_RH_and_Rosser (h : RiemannHypothesis) (R : RosserZeroCount)
    (n : ℕ) (lo : 2154434≤n) (hi : n≤10000000) :
    (((n+1)^3).primeCounting : ℚ) / (((n+1)^3:ℕ):ℚ) <
      ((n^3).primeCounting : ℚ) / ((n^3:ℕ):ℚ) :=
  cubes_above_finite (fun _ hx => psi_explicit h R hx)
    (fun _ hn _ => smoothing h R (by omega)) n lo hi

end Sun.CubeBridge
#print axioms Sun.CubeBridge.cubes_above_buthe_of_RH_and_Rosser
