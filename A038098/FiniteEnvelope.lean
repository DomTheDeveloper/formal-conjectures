module

public import A038098.Envelope

public section
namespace Sun.CubeAnalytic
open Real

/-- Büthe's finite ψ estimate is needed only at or above 1500. The same
interface is supplied below 10^10 by the stronger four-fifths certificate. -/
def FinitePsi (B : ℝ) : Prop :=
  ∀ z : ℝ, 1500 ≤ z → z ≤ B → |Chebyshev.psi z-z| ≤ 0.94*√z

private theorem log_le_point38_sqrt {m : ℝ} (hm : 200 ≤ m) : log m ≤ 0.38*√m := by
  have hm0 : 0 ≤ m := by linarith
  have hs : 14 ≤ √m := Real.le_sqrt_of_sq_le (by linarith)
  have h14 : log 14 ≤ 2.65 := by
    apply (log_le_iff_le_exp (by norm_num)).2
    calc (14:ℝ) ≤ 2.71828^2*(1+0.65/32)^32 := by norm_num
      _ ≤ _ := by convert exp_lower 2 (f := 0.65) (by norm_num) using 1; norm_num
  have h := log_le_sub_one_of_pos (show 0 < √m/14 by linarith)
  rw [log_div (by linarith) (by norm_num), log_sqrt hm0] at h
  linarith

/-- All cube comparisons above 199 up to the end of a finite-RH-quality
ψ envelope follow directly from that envelope. -/
theorem cubes_of_finite_psi {B : ℝ} (hΨ : FinitePsi B) (n : ℕ) (hn : 200 ≤ n)
    (hB : (((n+1)^3:ℕ):ℝ) ≤ B) :
    (((n+1)^3).primeCounting : ℚ) / (((n+1)^3:ℕ):ℚ) <
      ((n^3).primeCounting : ℚ) / ((n^3:ℕ):ℚ) := by
  let m : ℝ := n
  let x : ℕ := n^3
  let y : ℕ := (n+1)^3
  let a : ℝ := x/16
  have hm : 200 ≤ m := by dsimp [m]; exact_mod_cast hn
  have xm : (x:ℝ) = m^3 := by simp [x,m]
  have ym : (y:ℝ) = (m+1)^3 := by simp [y,m]
  have xbig : (200:ℝ)^3 ≤ x := xm.symm ▸ pow_le_pow_left₀ (by norm_num) hm 3
  have ha : 500000 ≤ a := by dsimp [a]; linarith
  have hax : a ≤ x := by dsimp [a]; linarith
  have xy : x < y := Nat.pow_lt_pow_left (Nat.lt_succ_self _) (by decide)
  have xyr : (x:ℝ) ≤ y := by exact_mod_cast xy.le
  have x0 : 0 < (x:ℝ) := by linarith
  have xB : (x:ℝ) ≤ B := xyr.trans hB
  have sx : √(x:ℝ) = m*√m := by
    rw [xm, show m^3=m^2*m by ring, sqrt_mul (sq_nonneg _), sqrt_sq (by linarith)]
  have Lpos : 0 < log (x:ℝ) := log_pos (by linarith)
  have Lbound : log (x:ℝ) ≤ 1.14*√m := by
    rw [xm,Real.log_pow]; push_cast
    linarith [log_le_point38_sqrt hm]
  have hθ (t : ℝ) (ht : a ≤ t) (htx : t ≤ x) : t-19*√t ≤ Chebyshev.theta t := by
    have h := (abs_le.1 (hΨ t (by linarith) (htx.trans xB))).1
    have hg := psi_sub_theta_eighteen (show 1 ≤ t by linarith)
    linarith [sqrt_nonneg t]
  have hAbel := abel_lower (show 2 ≤ a by linarith) hax (by norm_num : (0:ℝ) ≤ 0.972) (fun t ht => by
    have ht0 : 0 ≤ t := by linarith [ht.1]
    have h700 : 700 ≤ √t := Real.le_sqrt_of_sq_le (by linarith [ht.1])
    have haux := mul_nonneg (show 0 ≤ 0.028*√t-19 by linarith) (sqrt_nonneg t)
    nlinarith only [hθ t ht.1 ht.2, sq_sqrt ht0, haux])
  rw [Nat.floor_natCast] at hAbel
  have cost : 19*√(x:ℝ)*log (x:ℝ) ≤ 0.109*x := by
    have hl : 19*log (x:ℝ) ≤ 0.109*√(x:ℝ) := by
      rw [sx]
      have := mul_nonneg (show 0 ≤ 0.109*m-21.66 by linarith) (sqrt_nonneg m)
      linarith
    calc 19*√(x:ℝ)*log (x:ℝ) = (19*log (x:ℝ))*√(x:ℝ) := by ring
      _ ≤ (0.109*√(x:ℝ))*√(x:ℝ) := mul_le_mul_of_nonneg_right hl (sqrt_nonneg _)
      _ = _ := by rw [mul_assoc,Real.mul_self_sqrt x0.le]
  have lower : (1+0.8/log (x:ℝ))/log (x:ℝ) ≤ (x.primeCounting:ℝ)/x := by
    apply (le_div_iff₀ x0).2
    have hleft := div_le_div_of_nonneg_right (hθ x hax le_rfl) Lpos.le
    calc (1+0.8/log (x:ℝ))/log (x:ℝ)*x ≤ ((x:ℝ)-19*√(x:ℝ))/log (x:ℝ) +
        ((x:ℝ)-a)*(0.972/log (x:ℝ)^2) := by
          dsimp [a]
          field_simp
          nlinarith only [cost,x0.le]
      _ ≤ _ := by linarith only [hleft,hAbel]
  apply ratio_lt_of_psi (x := x) (y := y) (by exact_mod_cast (show (1:ℝ) < x by linarith)) xy lower
  have scale : (y:ℝ) ≤ (1.01:ℝ)^2*x := by
    rw [xm,ym]
    calc (m+1)^3 ≤ (1.005*m)^3 := pow_le_pow_left₀ (by linarith) (by linarith) 3
      _ ≤ _ := by rw [mul_pow]; apply mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
  have sr := sqrt_le_sqrt scale
  rw [sqrt_mul (by norm_num),sqrt_sq (by norm_num : (0:ℝ) ≤ 1.01)] at sr
  have ex := (abs_le.1 (hΨ x (by linarith) xB)).1
  have ey := (abs_le.1 (hΨ y (by linarith) hB)).2
  have inc : Chebyshev.psi y-Chebyshev.psi x ≤ (y:ℝ)-x + 1.9*√(x:ℝ) := by
    linarith [sqrt_nonneg (x:ℝ)]
  have id : √(x:ℝ)*√m = m^2 := by
    rw [sx,mul_assoc,Real.mul_self_sqrt (show 0 ≤ m by linarith)]; ring
  have gap : 3*m^2 ≤ (y:ℝ)-x := by rw [xm,ym]; nlinarith
  have gain : 1.9*√(x:ℝ) < ((y:ℝ)-x)*0.8/log (x:ℝ) := by
    apply (lt_div_iff₀ Lpos).2
    have h1 := mul_le_mul_of_nonneg_left Lbound (show 0 ≤ 1.9*√(x:ℝ) by positivity)
    have h2 : 1.9*√(x:ℝ)*(1.14*√m) = 2.166*m^2 := by rw [← id]; ring
    nlinarith only [h1,h2,gap,sq_pos_of_pos (show 0 < m by linarith)]
  apply lt_of_le_of_lt inc
  calc _ < ((y:ℝ)-x) + ((y:ℝ)-x)*0.8/log (x:ℝ) := by linarith only [gain]
       _ = _ := by ring

theorem cubes_200_to_2153
    (h : ∀ z : ℝ, 1500 ≤ z → z ≤ 10^10 → |Chebyshev.psi z-z| ≤ (4/5)*√z)
    (n : ℕ) (hn : 200 ≤ n) (hn' : n ≤ 2153) :
    (((n+1)^3).primeCounting : ℚ) / (((n+1)^3:ℕ):ℚ) <
      ((n^3).primeCounting : ℚ) / ((n^3:ℕ):ℚ) := by
  apply cubes_of_finite_psi (B := 10^10) _ n hn
  · intro z hz hz'
    exact (h z hz hz').trans (mul_le_mul_of_nonneg_right (by norm_num) (sqrt_nonneg _))
  · push_cast
    have hN : (n:ℝ) ≤ 2153 := by exact_mod_cast hn'
    exact (pow_le_pow_left₀ (by positivity) (show (n:ℝ)+1 ≤ 2154 by linarith) 3).trans (by norm_num)

theorem cubes_200_to_2154433 (h : FinitePsi (10^19))
    (n : ℕ) (hn : 200 ≤ n) (hn' : n ≤ 2154433) :
    (((n+1)^3).primeCounting : ℚ) / (((n+1)^3:ℕ):ℚ) <
      ((n^3).primeCounting : ℚ) / ((n^3:ℕ):ℚ) := by
  apply cubes_of_finite_psi h n hn
  push_cast
  have hN : (n:ℝ) ≤ 2154433 := by exact_mod_cast hn'
  exact (pow_le_pow_left₀ (by positivity) (show (n:ℝ)+1 ≤ 2154434 by linarith) 3).trans (by norm_num)

end Sun.CubeAnalytic
#print axioms Sun.CubeAnalytic.cubes_200_to_2153
#print axioms Sun.CubeAnalytic.cubes_200_to_2154433
