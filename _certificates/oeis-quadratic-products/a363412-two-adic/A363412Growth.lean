import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Topology.Instances.Rat
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! Turning the residue formulas into the rational-valued limit. -/
namespace A363412Two
open Filter Topology

private theorem square_le_exp (e : ℕ) : e^2 ≤ 2*2^e := by
  induction e with
  | zero => decide
  | succ e ih =>
    by_cases he : e ≤ 2
    · interval_cases e <;> decide
    · have h := Nat.mul_le_mul_left e (show 3 ≤ e by omega)
      rw [pow_succ (2:ℕ)]
      nlinarith

private theorem special_bound (n m v : ℕ) (hm : 0 < m)
    (hl : 8*m ≤ n+1) (hr : n ≤ 8*m) (hv : v = 4*m+2+padicValNat 2 m) :
    (2*(v:ℚ)-(n:ℚ))^2 ≤ 100*((n:ℚ)+1) := by
  let e := padicValNat 2 m
  have hp : 2^e ≤ m := Nat.le_of_dvd hm (pow_padicValNat_dvd (p:=2) (n:=m))
  have hes : e^2 ≤ 2*m := (square_le_exp e).trans (Nat.mul_le_mul_left 2 hp)
  have heq : (e:ℚ)^2 ≤ 2*(m:ℚ) := by exact_mod_cast hes
  have hl' : 8*(m:ℚ) ≤ (n:ℚ)+1 := by exact_mod_cast hl
  have hr' : (n:ℚ) ≤ 8*(m:ℚ) := by exact_mod_cast hr
  have hv' : (v:ℚ) = 4*(m:ℚ)+2+(e:ℚ) := by exact_mod_cast hv
  have he0 : 0 ≤ (e:ℚ) := by positivity
  calc
    _ ≤ (5+2*(e:ℚ))^2 := sq_le_sq' (by linarith) (by linarith)
    _ ≤ 50+8*(e:ℚ)^2 := by nlinarith [sq_nonneg (5-2*(e:ℚ))]
    _ ≤ _ := by linarith

/-- A sequence with the A363412 valuation formulas has the predicted slope. -/
theorem slope_from_classes (f : ℕ → ℕ)
    (low : ∀ m r, 1 ≤ r → r ≤ 2 → f (8*m+r) = 4*m)
    (middle : ∀ m r, 3 ≤ r → r ≤ 6 → f (8*m+r) = 4*m+2)
    (edges : ∀ m, 0 < m → f (8*m-1) = 4*m+2+padicValNat 2 m ∧
                            f (8*m) = 4*m+2+padicValNat 2 m) :
    Tendsto (fun n : ℕ => (2:ℚ)*(f n:ℚ)/(n:ℚ)) atTop (𝓝 1) := by
  have bound (n : ℕ) (hn : 0 < n) :
      (2*(f n:ℚ)-(n:ℚ))^2 ≤ 100*((n:ℚ)+1) := by
    let m := n/8
    let r := n%8
    have rep : n = 8*m+r := by dsimp [m,r]; omega
    have rangeR : r < 8 := Nat.mod_lt _ (by decide)
    by_cases h0 : r=0
    · have h : n=8*m := by omega
      have hm : 0<m := by omega
      exact special_bound n m _ hm (by omega) (by omega) (h ▸ (edges m hm).2)
    by_cases h7 : r=7
    · have h : n=8*(m+1)-1 := by omega
      exact special_bound n (m+1) _ (by omega) (by omega) (by omega)
        (h ▸ (edges (m+1) (by omega)).1)
    have small : n ≤ 2*f n+2 ∧ 2*f n ≤ n+2 := by
      rw [rep]
      by_cases h : r ≤ 2
      · rw [low m r (by omega) h]; omega
      · rw [middle m r (by omega) (by omega)]; omega
    have sl : (n:ℚ) ≤ 2*(f n:ℚ)+2 := by exact_mod_cast small.1
    have sr : 2*(f n:ℚ) ≤ (n:ℚ)+2 := by exact_mod_cast small.2
    calc
      _ ≤ (2:ℚ)^2 := sq_le_sq' (by linarith) (by linarith)
      _ ≤ _ := by
        have hnq : 0 ≤ (n:ℚ) := by positivity
        linarith
  have close (δ : ℚ) (hd : 0 < δ) :
      ∀ᶠ n : ℕ in atTop, 1-δ < (2:ℚ)*(f n:ℚ)/(n:ℚ) ∧
                          (2:ℚ)*(f n:ℚ)/(n:ℚ) < 1+δ := by
    obtain ⟨N,hN⟩ := exists_nat_gt (200/δ^2)
    filter_upwards [eventually_ge_atTop (max 1 N)] with n hn
    have hn1 : 1 ≤ n := (le_max_left _ _).trans hn
    have hnq : (1:ℚ) ≤ n := by exact_mod_cast hn1
    have hn0 : (0:ℚ) < n := by linarith
    have hNn : (N:ℚ) ≤ n := by exact_mod_cast (le_max_right 1 N).trans hn
    have hscale := (div_lt_iff₀ (sq_pos_of_pos hd)).mp (hN.trans_le hNn)
    have hbig : 100*((n:ℚ)+1) < (δ*n)^2 := by
      nlinarith [mul_lt_mul_of_pos_right hscale hn0]
    have hsq := (bound n hn1).trans_lt hbig
    have hab := sq_lt_sq.mp hsq
    rw [abs_of_pos (mul_pos hd hn0)] at hab
    obtain ⟨l,r⟩ := abs_lt.mp hab
    exact ⟨(lt_div_iff₀ hn0).2 (by nlinarith), (div_lt_iff₀ hn0).2 (by nlinarith)⟩
  apply tendsto_order.2
  constructor
  · intro a ha
    filter_upwards [close (1-a) (by linarith)] with n h
    linarith [h.1]
  · intro a ha
    filter_upwards [close (a-1) (by linarith)] with n h
    linarith [h.2]

end A363412Two
#print axioms A363412Two.slope_from_classes
