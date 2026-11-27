module

public import A038098.FourSum
public import A038098.Budget
public import A038098.IntegerSmoothing

public section
namespace Sun.CubeAnalytic
open Real

/-- The standard integer integrated explicit formula and a zero-count bound
imply the smoothing estimate for every intermediate cube. Both signs of the
ordinates occur in z, and w records multiplicity. -/
theorem smoothed_from_explicit_formula {ι : Type*} (z : ι → ℂ) (w : ι → ℝ)
    (hz : ∀ i, (z i).re = 1/2) (hi : ∀ i, 0 < |(z i).im|) (hw : ∀ i,0≤w i)
    (hS : ∀ k : ℕ, 1≤k → Summable (fun i => (w i:ℂ)*zeroKernel (z i) (k:ℝ)))
    {E : ℕ → ℝ} {c₁ c₀ : ℝ}
    (hF : ∀ k : ℕ, 1≤k → (∫ t in (1:ℝ)..(k:ℝ), Chebyshev.psi t) =
      (k:ℝ)^2/2-(∑' i, (w i:ℂ)*zeroKernel (z i) (k:ℝ)).re+c₁*k+E k+c₀)
    (hE : ∀ k : ℕ, 1≤k → (k:ℝ)-3/2 ≤ E k ∧ E k ≤ k)
    (hcount : ∀ (S : Finset ι) (t : ℝ), 1000000≤t →
      counted S (fun i => |(z i).im|) (fun i => w i/2) t ≤ countMajorant t)
    {n : ℕ} (hn : 2000000≤n) : SmoothedBound n := by
  let m : ℝ := n
  let x := n^3
  let y := (n+1)^3
  let s := √(m^3)
  let d := ⌈6*s⌉₊
  have hm : 2000000≤m := by dsimp [m]; exact_mod_cast hn
  have hm0 : 0<m := by linarith
  have s2 : s^2=m^3 := sq_sqrt (pow_nonneg hm0.le _)
  have hs : 1000≤s := le_sqrt_of_sq_le (by
    linarith only [pow_le_pow_left₀ (by norm_num : (0:ℝ)≤2000000) hm 3])
  have dl : 6*s ≤ (d:ℝ) := Nat.le_ceil _
  have du : (d:ℝ) ≤ 6*s+1 := (Nat.ceil_lt_add_one (by positivity : 0≤6*s)).le
  have dp : 1 ≤ d := by exact_mod_cast (show (1:ℝ)≤d by linarith)
  have xc : (x:ℝ)=m^3 := by simp [x,m]
  have yc : (y:ℝ)=(m+1)^3 := by simp [y,m]
  have ds : d<x := by
    have h := mul_nonneg (show 0≤s-7 by linarith) (show 0≤s by linarith)
    exact_mod_cast (show (d:ℝ)<x by nlinarith only [h,s2,hs,du,xc])
  have yp : 1≤y := Nat.succ_le_of_lt (pow_pos (Nat.succ_pos n) _)
  let K := fun (a : ℕ) (i : ι) => (w i:ℂ)*zeroKernel (z i) (a:ℝ)
  let Z := fun a : ℕ => (∑' i, K a i).re
  let D := fun i => (w i:ℂ)*fourKernel (z i) (m^3-(d:ℝ)) ((m+1)^3) d
  change d<n^3 at ds
  apply smoothed_of_integer_zero_sum (Z := Z) (d := d) dp ds hF hE
  have s₁ : Summable (K (y+d)) := hS _ (by omega)
  have s₂ : Summable (K y) := hS _ yp
  have s₃ : Summable (K x) := hS _ (by change 1≤n^3; omega)
  have s₄ : Summable (K (x-d)) := hS _ (by change 1≤n^3-d; omega)
  have H : (∑' i, D i) = ((∑' i,K (y+d) i)-(∑' i,K y i))-
      ((∑' i,K x i)-(∑' i,K (x-d) i)) := by
    rw [← s₁.tsum_sub s₂,← s₃.tsum_sub s₄,← (s₁.sub s₂).tsum_sub (s₃.sub s₄)]
    apply tsum_congr
    intro i
    dsimp [D,K,fourKernel]
    rw [Nat.cast_add,Nat.cast_sub (show d≤x from ds.le),xc,yc,sub_add_cancel]
    ring
  have hR : Z (y+d)-Z y-Z x+Z (x-d) = (∑' i, D i).re := by
    rw [H]
    simp only [Complex.sub_re,Z]
    ring
  have hN := zero_sum_for_cube z w hz hi hw hm dl du (fun S t ht => hcount S t (by linarith))
  have hB := rounded_budget hm dl du
  change |Z (y+d)-Z y-Z x+Z (x-d)|+3 ≤ (d:ℝ)*(s*errorCoeff (log (m^3))-d)
  rw [hR]
  exact (add_le_add_right (Complex.abs_re_le_norm _) 3).trans
    ((add_le_add_right hN 3).trans hB)

end Sun.CubeAnalytic
#print axioms Sun.CubeAnalytic.smoothed_from_explicit_formula
