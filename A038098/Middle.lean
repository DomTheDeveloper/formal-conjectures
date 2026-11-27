module

public import A038098.FiniteEnvelope

public section
namespace Sun.CubeAnalytic
open Real

/-- Coefficient of √x in the paper's proposed upper bound for the smoothed increment. -/
@[expose] noncomputable def errorCoeff (t : ℝ) : ℝ :=
  let u := t/3 + log (2.01/(3.01*(2*π)))
  let v := t/2 + log (0.671/(2.01*(2*π)))
  6.01 + 2.01/(2*π)*(v^2-u^2+2*v+2*u)

/-- The remaining analytic estimate for this cube. The smoothing width is free, so it may
be chosen integral when applying the integer integrated explicit formula. -/
@[expose] def SmoothedBound (n : ℕ) : Prop :=
  let x : ℝ := (n:ℝ)^3
  let y : ℝ := ((n:ℝ)+1)^3
  let F := fun z : ℝ => ∫ u in (1:ℝ)..z, Chebyshev.psi u
  ∃ d : ℝ, 0 < d ∧ (F (y+d)-F y-F x+F (x-d))/d ≤ y-x+√x*errorCoeff (log x)

theorem middle_cube_of_smoothed (hΨ : ExplicitPsi) {n : ℕ} (hn : 2 ≤ n)
    (ht : 43.7 ≤ log ((n:ℝ)^3)) (ht' : log ((n:ℝ)^3) ≤ 50) (h : SmoothedBound n) :
    (((n+1)^3).primeCounting : ℚ) / (((n+1)^3:ℕ):ℚ) <
      ((n^3).primeCounting : ℚ) / ((n^3:ℕ):ℚ) := by
  let x : ℕ := n^3
  let y : ℕ := (n+1)^3
  have hx : 1 < x := lt_of_lt_of_le (by decide : 1 < (2:ℕ)^3) (Nat.pow_le_pow_left hn 3)
  have xy : x < y := Nat.pow_lt_pow_left (Nat.lt_succ_self _) (by decide)
  have xpos : 0 < (x:ℝ) := by exact_mod_cast (show 0 < x by omega)
  have npos : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have xc : (x:ℝ) = (n:ℝ)^3 := by simp [x]
  have yc : (y:ℝ) = ((n:ℝ)+1)^3 := by simp [y]
  rw [← xc] at ht ht'
  have hL : 0 < log (x:ℝ) := by linarith
  have hxsize : 10^15 ≤ (x:ℝ)/1024 := by
    have h42 : 1024*(10:ℝ)^15 ≤ exp 42 := calc
      1024*(10:ℝ)^15 ≤ (2.71828:ℝ)^42*(1+0/32)^32 := by norm_num
      _ ≤ exp 42 := by convert exp_lower 42 (f := 0) (by norm_num) using 1; norm_num
    have he := exp_le_exp.mpr (show 42 ≤ log (x:ℝ) by linarith)
    rw [exp_log xpos] at he
    linarith
  have hlo := prime_lower_of_explicit hΨ hxsize ht'
  rw [Nat.floor_natCast] at hlo
  apply ratio_lt_of_psi hx xy hlo
  obtain ⟨d,hd,hD⟩ := h
  rw [← xc, ← yc] at hD
  have hinc := (smoothed_increment (x:ℝ) (y:ℝ) d hd).trans hD
  have hp : errorCoeff (log (x:ℝ)) < 2.994*exp (log (x:ℝ)/6)/log (x:ℝ) :=
    explicit_formula_margin ht (by linarith)
  have he3 : exp (log (x:ℝ)/3) = (n:ℝ) := by
    rw [xc,log_pow]
    push_cast
    rw [show (3:ℝ)*log n/3=log n by ring, exp_log npos]
  have hs : √(x:ℝ)*exp (log (x:ℝ)/6) = (n:ℝ)^2 := calc
    _ = exp (log (x:ℝ)/2)*exp (log (x:ℝ)/6) := by rw [exp_half,exp_log xpos]
    _ = exp (log (x:ℝ)/3)^2 := by
      rw [pow_two,←exp_add,←exp_add]
      congr 1; ring
    _ = _ := by rw [he3]
  have gain : √(x:ℝ)*errorCoeff (log (x:ℝ)) < ((y:ℝ)-x)*0.998/log (x:ℝ) := calc
    _ < √(x:ℝ)*(2.994*exp (log (x:ℝ)/6)/log (x:ℝ)) := mul_lt_mul_of_pos_left hp (sqrt_pos.mpr xpos)
    _ = 2.994*(n:ℝ)^2/log (x:ℝ) := by rw [← hs]; ring
    _ ≤ _ := by
      apply div_le_div_of_nonneg_right _ hL.le
      rw [xc,yc]; nlinarith
  apply lt_of_le_of_lt hinc
  calc _ < ((y:ℝ)-x) + ((y:ℝ)-x)*0.998/log (x:ℝ) := by linarith only [gain]
       _ = _ := by ring

/-- An explicit reduction of the former 200 ≤ n ≤ 10⁷ gap to two estimates. -/
theorem middle_range (hΨ : ExplicitPsi) (hB : FinitePsi (10^19))
    (hS : ∀ n : ℕ, 2154434 ≤ n → n < 6000000 → SmoothedBound n)
    (n : ℕ) (hn : 200 ≤ n) (hn' : n ≤ 10000000) :
    (((n+1)^3).primeCounting : ℚ) / (((n+1)^3:ℕ):ℚ) <
      ((n^3).primeCounting : ℚ) / ((n^3:ℕ):ℚ) := by
  by_cases hsmall : n ≤ 2154433
  · exact cubes_200_to_2154433 hB n hn hsmall
  by_cases hlarge : 6000000 ≤ n
  · exact cubes_six_million_to_ten_million hΨ n hlarge hn'
  apply middle_cube_of_smoothed hΨ (by omega) _ _ (hS n (by omega) (by omega))
  · apply (le_log_iff_exp_le (by positivity : 0 < (n:ℝ)^3)).2
    have h44 := pow_le_pow_left₀ (exp_pos 1).le
      (show exp 1 ≤ 2.7183 by linarith [exp_one_lt_d9]) 44
    rw [← exp_nat_mul, show (44:ℕ)*(1:ℝ) = 43.7+0.3 by norm_num,exp_add] at h44
    have h1 : exp (43.7:ℝ) ≤ (2154434:ℝ)^3 := by
      nlinarith only [h44,mul_le_mul_of_nonneg_left (add_one_le_exp (0.3:ℝ)) (exp_pos 43.7).le]
    exact h1.trans (pow_le_pow_left₀ (by norm_num) (by exact_mod_cast (show 2154434 ≤ n by omega)) 3)
  · apply (log_le_iff_le_exp (by positivity : 0 < (n:ℝ)^3)).2
    calc (n:ℝ)^3 ≤ (6000000:ℝ)^3 := pow_le_pow_left₀ (by positivity) (by exact_mod_cast (show n ≤ 6000000 by omega)) 3
      _ ≤ 2.71828^50*(1+0/32)^32 := by norm_num
      _ ≤ _ := by convert exp_lower 50 (f := 0) (by norm_num) using 1; norm_num
end Sun.CubeAnalytic
#print axioms Sun.CubeAnalytic.middle_cube_of_smoothed
#print axioms Sun.CubeAnalytic.middle_range
