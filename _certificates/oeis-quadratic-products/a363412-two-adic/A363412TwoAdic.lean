import A363412Dyadic
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! Exact two-adic valuations at every positive index of OEIS A363412. -/
namespace A363412Two

private def W (m : ℕ) : R := chunk normalized 0 m
private def Y (m r : ℕ) : R := chunk factor (8*m) r

private theorem exact_val {e : ℕ} {z : ℤ} (h : ∃ u : ℤ, z=(2:ℤ)^e*(2*u+1)) :
    padicValInt 2 z = e := by
  obtain ⟨u,rfl⟩ := h
  rw [padicValInt.mul (pow_ne_zero _ (by decide)) (by omega),
    padicValInt.eq_zero_of_not_dvd (by omega : ¬ (2:ℤ) ∣ 2*u+1), add_zero]
  change padicValNat 2 (((2:ℤ)^e).natAbs) = e
  rw [Int.natAbs_pow]
  exact padicValNat.prime_pow (p:=2) e

private theorem odd_mul_val (x u : ℤ) (hu : ¬(2:ℤ) ∣ u) :
    padicValInt 2 (u*x) = padicValInt 2 x := by
  by_cases hx : x=0
  · simp [hx]
  have hu' : u ≠ 0 := by rintro rfl; exact hu (dvd_zero _)
  rw [padicValInt.mul hu' hx,padicValInt.eq_zero_of_not_dvd hu,zero_add]

private theorem extract (m : ℕ) : chunk factor 0 (8*m) = ((((2:ℤ)^(4*m)):ℤ):R)*W m := by
  rw [extract_eights]
  change (( (16:ℤ)^m : ℤ):R)*W m = _
  rw [show (16:ℤ)=2^4 by decide,← pow_mul]

private theorem eight_coords (m : ℕ) :
    (chunk factor 0 (8*m)).re = (2:ℤ)^(4*m)*(W m).re ∧
    term (8*m) = (2:ℤ)^(4*m)*(W m).im := by
  unfold term
  rw [extract]
  simp only [Zsqrtd.mul_re, Zsqrtd.mul_im, Zsqrtd.intCast_re, Zsqrtd.intCast_im]
  simp

private theorem tail_im (m r : ℕ) :
    term (8*m+r) = (2:ℤ)^(4*m)*((W m).re*(Y m r).im+(W m).im*(Y m r).re) := by
  unfold term
  rw [chunk_add,zero_add,extract]
  change (((((2:ℤ)^(4*m):ℤ):R)*W m)*Y m r).im = _
  simp only [Zsqrtd.mul_re, Zsqrtd.mul_im, Zsqrtd.intCast_re, Zsqrtd.intCast_im]
  ring

private theorem W_parity (m : ℕ) :
    ∃ u v : ℤ, (W m).re = 2*u+1 ∧ (W m).im = 4*v := by
  obtain ⟨u,v,hr,hi⟩ := collect 0 m
  refine ⟨u,2*v+m,?_,?_⟩
  · simpa [W] using hr
  · simpa [W] using hi

private theorem tail_congr (m r : ℕ) :
    (Y m r).re % 8 = (chunk factor 0 r).re % 8 ∧
    (Y m r).im % 8 = (chunk factor 0 r).im % 8 := by
  have shift (j : ℕ) : ∃ z : R, factor (8*m+j) = factor (0+j)+8*z := by
    refine ⟨⟨0,m⟩,?_⟩
    ext <;> simp [factor]
    ring
  obtain ⟨z,h⟩ := shift_chunk factor (8*m) 0 8 shift r
  change Y m r = _ at h
  rw [h]
  simp

/-- At residues 1 and 2 modulo eight the valuation is the extracted block exponent. -/
theorem small_residues (m r : ℕ) (hlo : 1 ≤ r) (hhi : r ≤ 2) :
    padicValInt 2 (term (8*m+r)) = 4*m := by
  obtain ⟨u,v,hu,hv⟩ := W_parity m
  have c := (tail_congr m r).2
  have b : (chunk factor 0 r).im % 8 = 1 ∨ (chunk factor 0 r).im % 8 = 3 := by
    interval_cases r <;> decide
  obtain ⟨y,hy⟩ : ∃ y : ℤ, (Y m r).im = 2*y+1 := ⟨(Y m r).im/2,by omega⟩
  apply exact_val
  refine ⟨2*u*y+u+y+2*v*(Y m r).re,?_⟩
  rw [tail_im,hu,hv,hy]; ring

/-- Residues 3 through 6 modulo eight gain exactly two additional powers. -/
theorem middle_residues (m r : ℕ) (hlo : 3 ≤ r) (hhi : r ≤ 6) :
    padicValInt 2 (term (8*m+r)) = 4*m+2 := by
  obtain ⟨u,v,hu,hv⟩ := W_parity m
  obtain ⟨cr,ci⟩ := tail_congr m r
  have b : (chunk factor 0 r).im % 8 = 4 ∧
      ((chunk factor 0 r).re % 8 = 0 ∨ (chunk factor 0 r).re % 8 = 4) := by
    interval_cases r <;> decide
  obtain ⟨x,hx⟩ : ∃ x : ℤ, (Y m r).re = 2*x := ⟨(Y m r).re/2,by omega⟩
  obtain ⟨y,hy⟩ : ∃ y : ℤ, (Y m r).im = 8*y+4 := ⟨(Y m r).im/8,by omega⟩
  apply exact_val
  refine ⟨u*(2*y+1)+y+v*x,?_⟩
  rw [tail_im,hu,hv,hx,hy,pow_add]; ring

private theorem inverse_step (n : ℕ) :
    (1+3*((n:ℤ)+1)^2)*term n =
      term (n+1)-((n:ℤ)+1)*(chunk factor 0 (n+1)).re := by
  simp [term,chunk,factor]
  ring

/-- At 8m-1 and 8m the two orders agree and include the order of m. -/
theorem paired_eights (m : ℕ) (hm : 0 < m) :
    padicValInt 2 (term (8*m-1)) = 4*m+2+padicValNat 2 m ∧
    padicValInt 2 (term (8*m)) = 4*m+2+padicValNat 2 m := by
  obtain ⟨e,k,⟨j,hj⟩,hmf⟩ := Nat.exists_eq_two_pow_mul_odd (by omega : m ≠ 0)
  have kj : (k:ℤ) = 2*(j:ℤ)+1 := by exact_mod_cast hj
  have mf : (m:ℤ) = (2:ℤ)^e*(2*(j:ℤ)+1) := by exact_mod_cast hmf.trans (by rw [hj])
  have em : padicValNat 2 m = e := by
    rw [← padicValInt.of_nat]
    exact exact_val ⟨j,mf⟩
  obtain ⟨u,v,hu,hv⟩ := collect e k
  rw [← hmf] at hu hv
  change (W m).re = _ at hu
  change (W m).im = _ at hv
  rw [kj] at hv
  obtain ⟨ar,bi⟩ := eight_coords m
  have power : (2:ℤ)^(4*m+2+e) = (2:ℤ)^(4*m)*4*2^e := by rw [pow_add,pow_add]; ring
  have last : term (8*m) = (2:ℤ)^(4*m+2+e)*(2*(v+j)+1) := by
    rw [bi,hv,power]; ring
  rw [em]
  refine ⟨?_, exact_val ⟨v+j,last⟩⟩
  have step := inverse_step (8*m-1)
  rw [show 8*m-1+1 = 8*m by omega,
    show ((8*m-1:ℕ):ℤ)+1=8*(m:ℤ) by omega] at step
  have odd : ¬(2:ℤ) ∣ 1+3*(8*(m:ℤ))^2 := by ring_nf; omega
  rw [← odd_mul_val _ _ odd,step]
  apply exact_val
  refine ⟨v+j-(2*(j:ℤ)+1)*(2*u+1),?_⟩
  rw [last,ar,hu,power]
  conv_lhs => rhs; lhs; rhs; rw [mf]
  ring

end A363412Two
#print axioms A363412Two.small_residues
#print axioms A363412Two.middle_residues
#print axioms A363412Two.paired_eights
