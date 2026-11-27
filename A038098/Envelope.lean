module

public import A038098.Analytic

/-! Upper part of the missing cube range. The only analytic input is the
explicit Chebyshev estimate proved as Schoenfeld.psi_explicit from RH and
Rosser's zero count in senamakel/conjectures-lean. -/

public section
namespace Sun.CubeAnalytic
open Real

def ExplicitPsi : Prop :=
  ∀ z : ℝ, 10^10 ≤ z →
    |Chebyshev.psi z - z| ≤ √z * (log z ^ 2 / (8 * π) - 0.2985 * log z + 4.62)

private theorem theta_lower (hΨ : ExplicitPsi) {z : ℝ} (hz : 10^16 ≤ z) (hlog : log z ≤ 50) :
    0.99999*z ≤ Chebyshev.theta z := by
  have hz1 : 1 ≤ z := by linarith
  have hs := Real.sqrt_nonneg z
  have hs8 : 100000000 ≤ √z := Real.le_sqrt_of_sq_le (by norm_num1 at hz ⊢; linarith)
  have hL := Real.log_nonneg hz1
  have hL2 := pow_le_pow_left₀ hL hlog 2
  have hterm : log z ^ 2 / (8*π) - 0.2985*log z + 4.62 ≤ 105 := by
    have : log z ^ 2 / (8*π) ≤ 100 := by rw [div_le_iff₀ (by positivity)]; linarith [pi_gt_d6]
    linarith
  have herr := (abs_le.mp (hΨ z (by linarith))).1
  have hb := mul_le_mul_of_nonneg_left hterm hs
  have h4 : log 4 ≤ 2 := by
    rw [log_le_iff_le_exp (by norm_num)]
    rw [show (2:ℝ) = 1+1 by norm_num, exp_add]
    nlinarith [exp_one_gt_two]
  have hpow {q : ℝ} (hq : q ≤ 1/2) :
      Chebyshev.psi (z^q) ≤ 6*√z := by
    have h1 : z^q ≤ √z := by
      rw [Real.sqrt_eq_rpow]
      exact Real.rpow_le_rpow_of_exponent_le hz1 hq
    calc Chebyshev.psi (z^q) ≤ (log 4 + 4) * z^q := Chebyshev.psi_le_const_mul_self (by positivity)
      _ ≤ 6 * √z := mul_le_mul (by linarith) h1 (by positivity) (by norm_num)
  have hgap := Chebyshev.psi_sub_theta_le_psi_add_psi_add_psi z
  have h2 := hpow (q := (2:ℝ)⁻¹) (by norm_num)
  have h3 := hpow (q := (3:ℝ)⁻¹) (by norm_num)
  have h5 := hpow (q := (5:ℝ)⁻¹) (by norm_num)
  have ht := mul_nonneg (show 0 ≤ 0.00001*√z-123 by linarith) hs
  nlinarith only [Real.sq_sqrt (show 0 ≤ z by linarith), herr, hb, hgap, h2, h3, h5, ht]

/-- Abel summation on [x/1024,x] supplies the left-end prime-count lower bound. -/
theorem prime_lower_of_explicit (hΨ : ExplicitPsi) {x : ℝ} (hx : 10^16 ≤ x/1024) (hL : log x ≤ 50) :
    (1+0.998/log x)/log x ≤ (Nat.primeCounting ⌊x⌋₊ : ℝ)/x := by
  let a := x/1024
  have ha : 2 ≤ a := by dsimp [a]; linarith
  have hax : a ≤ x := by dsimp [a] at *; linarith
  have hx0 : 0 < x := by linarith
  have hlx : 0 < log x := Real.log_pos (by linarith)
  let f := fun t : ℝ => Chebyshev.theta t / (t * log t ^ 2)
  have integ (l u : ℝ) (hl : 2 ≤ l) (hlu : l ≤ u) : IntervalIntegrable f MeasureTheory.volume l u := by
    rw [intervalIntegrable_iff, Set.uIoc_of_le hlu]
    exact (Chebyshev.integrableOn_theta_div_id_mul_log_sq u).mono_set
      (fun t ht => ⟨hl.trans ht.1.le,ht.2⟩)
  have h1 : 0 ≤ ∫ t in (2:ℝ)..a, f t := intervalIntegral.integral_nonneg ha
    (fun t ht => div_nonneg (Chebyshev.theta_nonneg _) (mul_nonneg (by linarith [ht.1]) (sq_nonneg _)))
  have h2 : ∫ t in a..x, 0.99999/(log x)^2 ≤ ∫ t in a..x, f t := by
    apply intervalIntegral.integral_mono_on hax intervalIntegrable_const (integ a x ha hax)
    intro t ht
    have ht0 : 0 < t := by linarith [ht.1]
    have hlt : 0 < log t := Real.log_pos (by linarith [ht.1])
    have hle := Real.log_le_log ht0 ht.2
    have hθ := theta_lower hΨ (show 10^16 ≤ t from hx.trans ht.1) (hle.trans hL)
    calc 0.99999/log x ^ 2 ≤ 0.99999/log t ^ 2 :=
        div_le_div_of_nonneg_left (by norm_num) (by positivity) (pow_le_pow_left₀ hlt.le hle 2)
      _ = (0.99999*t) / (t * log t ^ 2) := by field_simp
      _ ≤ f t := div_le_div_of_nonneg_right hθ (by positivity)
  rw [intervalIntegral.integral_const, smul_eq_mul] at h2
  have hθx := theta_lower hΨ (hx.trans hax) hL
  have h3 := div_le_div_of_nonneg_right hθx hlx.le
  have hid := intervalIntegral.integral_add_adjacent_intervals (integ 2 a le_rfl ha) (integ a x ha hax)
  have hπ := Chebyshev.primeCounting_eq_theta_div_log_add_integral (ha.trans hax)
  change (Nat.primeCounting ⌊x⌋₊ : ℝ) = _ + ∫ t in (2:ℝ)..x, f t at hπ
  apply (le_div_iff₀ hx0).2
  calc (1+0.998/log x)/log x*x = x*(log x+0.998)/log x^2 := by field_simp
    _ ≤ x*(0.99999*log x + 0.99999*(1-1/1024))/log x^2 := by
      apply div_le_div_of_nonneg_right _ (sq_nonneg _)
      apply mul_le_mul_of_nonneg_left _ hx0.le
      linarith
    _ = 0.99999*x/log x + (x-a)*(0.99999/log x^2) := by dsimp [a]; field_simp
    _ ≤ (Nat.primeCounting ⌊x⌋₊ : ℝ) := by linarith only [h1,h2,h3,hid,hπ]

private theorem exp_lower (k : ℕ) {f : ℝ} (hf : 0 ≤ f) :
    (2.71828:ℝ)^k*(1+f/32)^32 ≤ exp (k+f) := by
  have h1 := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2.71828)
    (show 2.71828 ≤ exp 1 by linarith [exp_one_gt_d9]) k
  have h2 := pow_le_pow_left₀ (show 0 ≤ 1+f/32 by linarith)
    (show 1+f/32 ≤ exp (f/32) by linarith [add_one_le_exp (f/32)]) 32
  have hh := mul_le_mul h1 h2 (by positivity) (by positivity)
  rw [← exp_nat_mul, ← exp_nat_mul, ← exp_add] at hh
  simpa only [Nat.cast_ofNat, mul_one, show (32:ℝ)*(f/32)=f by ring] using hh

private theorem exp_lower_endpoint : exp (46.75:ℝ) ≤ (6000000:ℝ)^3 := by
  have h := pow_le_pow_left₀ (exp_pos 1).le
    (show exp 1 ≤ 2.719 by linarith [exp_one_lt_d9]) 47
  rw [← exp_nat_mul, show (47:ℕ)*(1:ℝ) = 46.75+0.25 by norm_num, exp_add] at h
  nlinarith only [h, mul_le_mul_of_nonneg_left (add_one_le_exp (0.25:ℝ)) (exp_pos 46.75).le]

private theorem range_bound {n : ℕ} (hn : 6000000 ≤ n) (hΨ : ExplicitPsi) {U r : ℝ}
    (hU : log (((n+1:ℕ)^3:ℕ):ℝ) ≤ U) (hU50 : U ≤ 50) (hr : r^2 ≤ (n:ℝ))
    (hnum : (2.000001*(0.0398*U^2-0.2985*46.75+4.62))*U < 2.994*r) :
    (((n+1)^3).primeCounting : ℚ) / (((n+1)^3:ℕ):ℚ) <
      ((n^3).primeCounting : ℚ) / ((n^3:ℕ):ℚ) := by
  let m : ℝ := n
  let x : ℕ := n^3
  let y : ℕ := (n+1)^3
  have hm : 6000000 ≤ m := by dsimp [m]; exact_mod_cast hn
  have xm : (x:ℝ) = m^3 := by simp [x,m]
  have ym : (y:ℝ) = (m+1)^3 := by simp [y,m]
  have xbig : (6000000:ℝ)^3 ≤ x := xm.symm ▸ pow_le_pow_left₀ (by norm_num) hm 3
  have xy : x < y := Nat.pow_lt_pow_left (Nat.lt_succ_self _) (by decide)
  have xyr : (x:ℝ) ≤ y := by exact_mod_cast xy.le
  have x0 : 0 < (x:ℝ) := by linarith
  have lx : 46.75 ≤ log (x:ℝ) := (Real.le_log_iff_exp_le x0).2 (exp_lower_endpoint.trans xbig)
  have lxy := Real.log_le_log x0 xyr
  have ly : log (y:ℝ) ≤ U := hU
  have lower := prime_lower_of_explicit hΨ (x := (x:ℝ)) (by linarith) (lxy.trans (ly.trans hU50))
  rw [Nat.floor_natCast] at lower
  apply ratio_lt_of_psi (x := x) (y := y) (by exact_mod_cast (show (1:ℝ) < x by linarith)) xy lower
  let C := 0.0398*U^2-0.2985*46.75+4.62
  have hUpos : 46.75 ≤ U := lx.trans (lxy.trans ly)
  have cpos : 0 ≤ C := by
    dsimp [C]
    nlinarith [pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 46.75) hUpos 2]
  have ec (z : ℝ) (hz : 10^10 ≤ z) (hzl : 46.75 ≤ log z) (hzu : log z ≤ U) :
      |Chebyshev.psi z-z| ≤ √z*C := by
    apply (hΨ z hz).trans
    apply mul_le_mul_of_nonneg_left _ (sqrt_nonneg _)
    have hsq := pow_le_pow_left₀ (show 0 ≤ log z by linarith) hzu 2
    have hcoeff : (1:ℝ)/(8*π) ≤ 0.0398 := by rw [div_le_iff₀ (by positivity)]; linarith [pi_gt_d6]
    have hbb := mul_le_mul hcoeff hsq (sq_nonneg _) (by norm_num : (0:ℝ) ≤ 0.0398)
    dsimp [C]
    rw [div_eq_inv_mul]
    simp only [one_div] at hbb
    linarith
  have ex := (abs_le.1 (ec x (by linarith) lx (lxy.trans ly))).1
  have ey := (abs_le.1 (ec y (by linarith) (lx.trans lxy) ly)).2
  have scale : (y:ℝ) ≤ (1.000001:ℝ)^2*x := by
    rw [xm,ym]
    calc (m+1)^3 ≤ (1.0000002*m)^3 := pow_le_pow_left₀ (by linarith) (by linarith) 3
      _ ≤ _ := by rw [mul_pow]; apply mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
  have sr := sqrt_le_sqrt scale
  rw [sqrt_mul (by norm_num), sqrt_sq (by norm_num : (0:ℝ) ≤ 1.000001)] at sr
  have ey' := mul_le_mul_of_nonneg_right sr cpos
  have increment : Chebyshev.psi y-Chebyshev.psi x ≤ (y:ℝ)-x + (2.000001*C)*√(x:ℝ) := by
    linarith
  have hprod : 2.000001*C*log (x:ℝ) < 2.994*√m := calc
    _ ≤ 2.000001*C*U := mul_le_mul_of_nonneg_left (lxy.trans ly) (by positivity)
    _ < 2.994*r := hnum
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.le_sqrt_of_sq_le hr) (by norm_num)
  have sx : √(x:ℝ) = m*√m := by
    rw [xm, show m^3=m^2*m by ring, sqrt_mul (sq_nonneg _), sqrt_sq (by linarith)]
  have id : √m*√(x:ℝ) = m^2 := by rw [sx]; nlinarith only [congrArg (fun z : ℝ => m*z) (Real.sq_sqrt (show 0 ≤ m by linarith))]
  have hp := mul_lt_mul_of_pos_right hprod (Real.sqrt_pos.mpr x0)
  rw [mul_assoc (2.994:ℝ),id] at hp
  have gap : 3*m^2 ≤ (y:ℝ)-x := by rw [xm,ym]; nlinarith
  have gain : 2.000001*C*√(x:ℝ) < ((y:ℝ)-x)*0.998/log (x:ℝ) := by
    apply (lt_div_iff₀ (show 0 < log (x:ℝ) by linarith)).2
    nlinarith only [hp,gap]
  apply lt_of_le_of_lt increment
  calc _ < ((y:ℝ)-x) + ((y:ℝ)-x)*0.998/log (x:ℝ) := by linarith only [gain]
       _ = _ := by ring

/-- The published explicit ψ estimate suffices for four million consecutive cube comparisons.
The inequality is strict and uses inclusive prime counts at both endpoints. -/
theorem cubes_six_million_to_ten_million (hΨ : ExplicitPsi) (n : ℕ)
    (hn : 6000000 ≤ n) (hn' : n ≤ 10000000) :
    (((n+1)^3).primeCounting : ℚ) / (((n+1)^3:ℕ):ℚ) <
      ((n^3).primeCounting : ℚ) / ((n^3:ℕ):ℚ) := by
  have bound {N : ℕ} {U : ℝ} (hnN : n ≤ N) (he : ((N:ℝ)+1)^3 ≤ exp U) :
      log (((n+1:ℕ)^3:ℕ):ℝ) ≤ U := by
    apply (log_le_iff_le_exp (by positivity)).2
    push_cast
    exact (pow_le_pow_left₀ (by positivity) (by exact_mod_cast Nat.succ_le_succ hnN) 3).trans he
  by_cases h0 : n ≤ 6080000
  · apply range_bound hn hΨ (U := 46.875) (r := 2449) _ (by norm_num) _ (by norm_num)
    · apply bound h0
      calc ((6080000:ℝ)+1)^3 ≤ 2.71828^46*(1+0.875/32)^32 := by norm_num
        _ ≤ _ := by convert exp_lower 46 (f := 0.875) (by norm_num) using 1; norm_num
    · norm_num1
      exact_mod_cast (show 5997601 ≤ n by omega)
  by_cases h1 : n ≤ 6280000
  · apply range_bound hn hΨ (U := 46.975) (r := 2465) _ (by norm_num) _ (by norm_num)
    · apply bound h1
      calc ((6280000:ℝ)+1)^3 ≤ 2.71828^46*(1+0.975/32)^32 := by norm_num
        _ ≤ _ := by convert exp_lower 46 (f := 0.975) (by norm_num) using 1; norm_num
    · norm_num1
      exact_mod_cast (show 6076225 ≤ n by omega)
  by_cases h2 : n ≤ 6800000
  · apply range_bound hn hΨ (U := 47.2) (r := 2505) _ (by norm_num) _ (by norm_num)
    · apply bound h2
      calc ((6800000:ℝ)+1)^3 ≤ 2.71828^47*(1+0.2/32)^32 := by norm_num
        _ ≤ _ := by convert exp_lower 47 (f := 0.2) (by norm_num) using 1; norm_num
    · norm_num1
      exact_mod_cast (show 6275025 ≤ n by omega)
  by_cases h3 : n ≤ 8280000
  · apply range_bound hn hΨ (U := 47.8) (r := 2607) _ (by norm_num) _ (by norm_num)
    · apply bound h3
      calc ((8280000:ℝ)+1)^3 ≤ 2.71828^47*(1+0.8/32)^32 := by norm_num
        _ ≤ _ := by convert exp_lower 47 (f := 0.8) (by norm_num) using 1; norm_num
    · norm_num1
      exact_mod_cast (show 6796449 ≤ n by omega)
  apply range_bound hn hΨ (U := 49.275) (r := 2877) _ (by norm_num) _ (by norm_num)
  · apply bound hn'
    calc ((10000000:ℝ)+1)^3 ≤ 2.71828^49*(1+0.275/32)^32 := by norm_num
      _ ≤ _ := by convert exp_lower 49 (f := 0.275) (by norm_num) using 1; norm_num
  · norm_num1
    exact_mod_cast (show 8277129 ≤ n by omega)
end Sun.CubeAnalytic
#print axioms Sun.CubeAnalytic.prime_lower_of_explicit
#print axioms Sun.CubeAnalytic.cubes_six_million_to_ten_million
