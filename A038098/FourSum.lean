module

public import A038098.Geometry
public import A038098.ZeroWeights

public section
namespace Sun.CubeAnalytic
open Real

/-- Scale the three bounds for one zero to the capped inverse-ordinate weight
with cutoffs A=(2.01/3.01)m and B=(0.671/2.01)√(m³). -/
theorem one_weight {z : ℂ} (hz : z.re=1/2) (hi : 0 < |z.im|) {m d : ℝ}
    (hm : 2000000≤m) (hd : 6*√(m^3)≤d) (hu : d≤6*√(m^3)+1) :
    ‖fourKernel z (m^3-d) ((m+1)^3) d‖ ≤
    (d*√(m^3))*(2.01*ordinateWeight ((2.01/3.01)*m) ((0.671/2.01)*√(m^3)) |z.im|) := by
  let x := m^3
  let y := (m+1)^3
  let s := √x
  let g := |z.im|
  let A := (2.01/3.01)*m
  let B := (0.671/2.01)*s
  have hm0 : 0<m := by linarith
  have hs0 : 0<s := sqrt_pos.2 (pow_pos hm0 _)
  have hg : 0<g := hi
  change 6*s≤d at hd
  have hd0 : 0<d := by linarith
  have sc : 0≤d*s := mul_nonneg hd0.le hs0.le
  obtain ⟨hstart,L,M,H⟩ := width_geometry hm hd hu
  change 0<x-d at hstart
  change (y-(x-d))/(√(x-d)*s) ≤ 3.01/m at L
  change 2*√(y+d)/s≤2.01 at M
  change 4*((y+d)*√(y+d))/(d*s)≤0.671*s at H
  have hxy : x-d≤y := by dsimp [x,y]; nlinarith [sq_nonneg m]
  apply (fourKernel_le hz hi hstart hxy hd0.le).trans
  change min (d*(y-(x-d))/√(x-d)) (min (2*d*√(y+d)/g) (4*((y+d)*√(y+d))/g^2)) ≤
    (d*s)*(2.01*ordinateWeight A B g)
  unfold ordinateWeight
  simp only [mul_min_of_nonneg _ _ (by norm_num : (0:ℝ)≤2.01),mul_min_of_nonneg _ _ sc]
  refine min_le_min ?_ (min_le_min ?_ ?_)
  · calc d*(y-(x-d))/√(x-d) = (d*s)*((y-(x-d))/(√(x-d)*s)) := by
            field_simp
         _ ≤ (d*s)*(3.01/m) := mul_le_mul_of_nonneg_left L sc
         _ = (d*s)*(2.01*(1/A)) := by dsimp [A]; field_simp; ring
  · calc 2*d*√(y+d)/g = (d*s/g)*(2*√(y+d)/s) := by field_simp; ring
         _ ≤ (d*s/g)*2.01 := mul_le_mul_of_nonneg_left M (by positivity)
         _ = (d*s)*(2.01*(1/g)) := by ring
  · calc 4*((y+d)*√(y+d))/g^2 = (d*s/g^2)*(4*((y+d)*√(y+d))/(d*s)) := by field_simp; ring
         _ ≤ (d*s/g^2)*(0.671*s) := mul_le_mul_of_nonneg_left H (by positivity)
         _ = (d*s)*(2.01*(B/g^2)) := by dsimp [B]; ring

/-- The four-point zero contribution is bounded by the integrated counting
majorant. All ordinates and both signs may be supplied together. -/
theorem zero_sum_for_cube {ι : Type*} (z : ι → ℂ) (w : ι → ℝ) {m d : ℝ}
    (hz : ∀ i, (z i).re=1/2) (hi : ∀ i, 0 < |(z i).im|) (hw : ∀ i,0≤w i)
    (hm : 2000000≤m) (hd : 6*√(m^3)≤d) (hu : d≤6*√(m^3)+1)
    (hcount : ∀ (S : Finset ι) (t : ℝ), (2.01/3.01)*m≤t →
      counted S (fun i => |(z i).im|) (fun i => w i/2) t ≤ countMajorant t) :
    let A := (2.01/3.01)*m
    let B := (0.671/2.01)*√(m^3)
    let u := log A-log (2*π)
    let v := log B-log (2*π)
    ‖∑' i, (w i:ℂ)*fourKernel (z i) (m^3-d) ((m+1)^3) d‖ ≤
      (d*√(m^3)*4.02)*((v^2-u^2+2*v+2*u)/(4*π)+(log A+1)/A-1/(2*B)) := by
  let s := √(m^3)
  let A := (2.01/3.01)*m
  let B := (0.671/2.01)*s
  let g := fun i => |(z i).im|
  let W := fun i => w i/2*ordinateWeight A B (g i)
  have hm0 : 0<m := by linarith
  have hs0 : 0<s := sqrt_pos.2 (pow_pos hm0 _)
  change 6*s≤d at hd
  have hd0 : 0<d := by linarith
  have ha : 0<A := by dsimp [A]; positivity
  have s_eq : s=m*√m := by
    dsimp [s]
    rw [show m^3=m^2*m by ring,sqrt_mul (sq_nonneg _),sqrt_sq hm0.le]
  have hr : 1400≤√m := le_sqrt_of_sq_le (by linarith)
  have hab : A≤B := by
    dsimp [A,B]
    rw [s_eq]
    linarith only [mul_le_mul_of_nonneg_left hr hm0.le,hm0.le]
  obtain ⟨hs,hb⟩ := tsum_ordinateWeight_le g (fun i => w i/2) ha hab hi
    (fun i => by have := hw i; positivity) hcount
  let C := d*s*4.02
  have hc : 0≤C := by dsimp [C]; positivity
  have hsum : HasSum (fun i => C*W i) (C*(∑' i,W i)) := hs.hasSum.mul_left C
  have hN (i : ι) : ‖(w i:ℂ)*fourKernel (z i) (m^3-d) ((m+1)^3) d‖ ≤ C*W i := by
    rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (hw i)]
    have H := mul_le_mul_of_nonneg_left (one_weight (hz i) (hi i) hm hd hu) (hw i)
    apply H.trans_eq
    dsimp [C,W,g,A,B,s]
    ring
  apply (tsum_of_norm_bounded hsum hN).trans
  exact mul_le_mul_of_nonneg_left hb hc

end Sun.CubeAnalytic
#print axioms Sun.CubeAnalytic.zero_sum_for_cube
