module

public import A038098.Envelope
public import A038098.Zeros

/-! The width of the two smoothing intervals may be rounded upward to an
integer. The following estimates hold throughout the intermediate cube range. -/
public section
namespace Sun.CubeAnalytic
open Real

theorem width_geometry {m d : ℝ} (hm : 2000000 ≤ m)
    (hd : 6*√(m^3)≤d) (hd' : d≤6*√(m^3)+1) :
    0 < m^3-d ∧
    (((m+1)^3-(m^3-d))/(√(m^3-d)*√(m^3)) ≤ 3.01/m) ∧
    (2*√((m+1)^3+d)/√(m^3) ≤ 2.01) ∧
    (4*(((m+1)^3+d)*√((m+1)^3+d))/(d*√(m^3)) ≤ 0.671*√(m^3)) := by
  let x := m^3
  let y := (m+1)^3
  let s := √x
  have hm0 : 0<m := by linarith
  have hx0 : 0<x := pow_pos hm0 _
  have hs0 : 0<s := sqrt_pos.2 hx0
  have hs2 : s^2=x := sq_sqrt hx0.le
  have hs : s=m*√m := by
    dsimp [s,x]
    rw [show m^3 = m^2*m by ring,sqrt_mul (sq_nonneg _),sqrt_sq hm0.le]
  change 6*s ≤ d at hd
  change d ≤ 6*s+1 at hd'
  have hd0 : 0<d := by linarith
  have hr : 1400 ≤ √m := le_sqrt_of_sq_le (by linarith)
  have hh : 6*√m ≤ 0.0045*m := by
    nlinarith only [mul_nonneg (show 0≤0.0045*√m-6 by linarith) (sqrt_nonneg m),sq_sqrt hm0.le]
  have m2 : 2000000*m ≤ m^2 := by nlinarith only [mul_nonneg (sub_nonneg.2 hm) hm0.le]
  have m3 : 2000000*m^2 ≤ x := by
    dsimp [x]
    nlinarith only [mul_nonneg (sub_nonneg.2 hm) (sq_nonneg m)]
  have dsmall : d≤0.005*m^2 := by
    rw [hs] at hd'
    nlinarith only [hd',mul_le_mul_of_nonneg_left hh hm0.le,m2,hm]
  have diff : y-(x-d) ≤ 3.006*m^2 := by
    dsimp [y,x]
    nlinarith only [dsmall,m2,hm]
  have rp : 0<x-d := by nlinarith only [m3,dsmall,sq_pos_of_pos hm0]
  have upper : y+d ≤ 1.000002*x := by linarith only [diff,m3]
  have lroot : 0.99999*s ≤ √(x-d) := le_sqrt_of_sq_le (by
    nlinarith only [hs2,m3,dsmall,hx0.le])
  have uroot : √(y+d) ≤ 1.000001*s := by
    apply (sqrt_le_iff).2
    exact ⟨by positivity, by nlinarith only [upper,hs2,hx0.le]⟩
  change 0<x-d ∧ (y-(x-d))/(√(x-d)*s) ≤ 3.01/m ∧
    2*√(y+d)/s ≤ 2.01 ∧ 4*((y+d)*√(y+d))/(d*s) ≤ 0.671*s
  refine ⟨rp,?_,?_,?_⟩
  · apply (div_le_div_iff₀ (mul_pos (sqrt_pos.2 rp) hs0) hm0).2
    have hy := mul_le_mul_of_nonneg_right diff hm0.le
    have hl := mul_le_mul_of_nonneg_right lroot hs0.le
    have xid : m^2*m = x := by dsimp [x]; ring
    nlinarith only [hy,hl,hs2,xid,hx0.le]
  · apply (div_le_iff₀ hs0).2
    linarith only [uroot,hs0.le]
  · apply (div_le_iff₀ (mul_pos hd0 hs0)).2
    have hu := mul_le_mul upper uroot (sqrt_nonneg _) (show 0≤1.000002*x by positivity)
    have hdx := mul_le_mul_of_nonneg_right hd hx0.le
    have he : 0.671*s*(d*s) = 0.671*d*x := by rw [← hs2]; ring
    rw [he]
    nlinarith only [hu,hdx,mul_nonneg hx0.le hs0.le]

end Sun.CubeAnalytic
#print axioms Sun.CubeAnalytic.width_geometry
