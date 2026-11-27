module

public import A038098.Geometry
public import A038098.Middle

public section
namespace Sun.CubeAnalytic
open Real

/-- Compare the explicit integrated zero-count bound with the budget in the
four-point integer formula, including rounding and all four remainders. -/
theorem rounded_budget {m d : ℝ} (hm : 2000000≤m)
    (hd : 6*√(m^3)≤d) (hd' : d≤6*√(m^3)+1) :
    let s := √(m^3)
    let A := (2.01/3.01)*m
    let B := (0.671/2.01)*s
    let u := log A-log (2*π)
    let v := log B-log (2*π)
    (d*s*4.02)*((v^2-u^2+2*v+2*u)/(4*π)+(log A+1)/A-1/(2*B)) + 3 ≤
      d*(s*errorCoeff (log (m^3))-d) := by
  let s := √(m^3)
  let A := (2.01/3.01)*m
  let B := (0.671/2.01)*s
  let u := log A-log (2*π)
  let v := log B-log (2*π)
  let V := v^2-u^2+2*v+2*u
  have hm0 : 0<m := by linarith
  have ms : (2000000:ℝ)^3 ≤ m^3 := pow_le_pow_left₀ (by norm_num) hm 3
  have hsb : 1000 ≤ s := le_sqrt_of_sq_le (by linarith)
  have hs : 0<s := by linarith
  change 6*s≤d at hd
  change d≤6*s+1 at hd'
  have h1 : 1≤d := by linarith
  have hA : 1000000≤A := by dsimp [A]; linarith
  have ha : 0<A := by linarith
  have hb : 0<B := by dsimp [B]; positivity
  have eu : u = log (m^3)/3 + log (2.01/(3.01*(2*π))) := by
    dsimp [u,A]
    rw [log_mul (by norm_num : (2.01/3.01:ℝ)≠0) hm0.ne',log_pow,
      log_div (by norm_num : (2.01:ℝ)≠0) (by norm_num : (3.01:ℝ)≠0),
      log_div (by norm_num : (2.01:ℝ)≠0) (by positivity : (3.01*(2*π):ℝ)≠0),
      log_mul (by norm_num : (3.01:ℝ)≠0) (by positivity : 2*π≠0)]
    push_cast
    ring
  have ev : v = log (m^3)/2 + log (0.671/(2.01*(2*π))) := by
    dsimp [v,B,s]
    rw [log_mul (by norm_num : (0.671/2.01:ℝ)≠0) (sqrt_pos.2 (pow_pos hm0 3)).ne',
      log_sqrt (pow_nonneg hm0.le 3),
      log_div (by norm_num : (0.671:ℝ)≠0) (by norm_num : (2.01:ℝ)≠0),
      log_div (by norm_num : (0.671:ℝ)≠0) (by positivity : (2.01*(2*π):ℝ)≠0),
      log_mul (by norm_num : (2.01:ℝ)≠0) (by positivity : 2*π≠0)]
    ring
  have hp : errorCoeff (log (m^3)) = 6.01+2.01/(2*π)*V := by
    unfold V
    rw [eu,ev]
    rfl
  have hlog : log (1000000:ℝ) ≤ 20 := by
    apply (log_le_iff_le_exp (by norm_num)).2
    calc (1000000:ℝ) ≤ (2.71828:ℝ)^20*(1+0/32)^32 := by norm_num
         _ ≤ exp 20 := by convert exp_lower 20 (f := 0) (by norm_num) using 1; norm_num
  have hl := log_le_sub_one_of_pos (show 0<A/1000000 by positivity)
  rw [log_div ha.ne' (by norm_num)] at hl
  have hcost : (log A+1)/A ≤ 0.0001 := (div_le_iff₀ ha).2 (by linarith)
  have hrem : 0≤1/(2*B) := by positivity
  let E := V/(4*π)+(log A+1)/A-1/(2*B)
  have hE : 4.02*E ≤ errorCoeff (log (m^3))-6.009 := by
    rw [hp]
    calc 4.02*E = 2.01/(2*π)*V + 4.02*((log A+1)/A-1/(2*B)) := by
          dsimp [E]; field_simp; ring
         _ ≤ _ := by linarith only [hcost,hrem]
  have hmul := mul_le_mul_of_nonneg_left hE (show 0≤d*s by positivity)
  have hrest := mul_le_mul_of_nonneg_left (show 3 ≤ 6.009*s-d by linarith) (show 0≤d by linarith)
  change (d*s*4.02)*E + 3 ≤ d*(s*errorCoeff (log (m^3))-d)
  nlinarith only [hmul,hrest,h1]

end Sun.CubeAnalytic
#print axioms Sun.CubeAnalytic.rounded_budget
