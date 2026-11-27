import Mathlib.NumberTheory.Zsqrtd.Basic
import Mathlib.Tactic.Ring

/-! Eight-factor blocks for the imaginary coefficient of OEIS A363412. -/
namespace A363412Two
abbrev R := Zsqrtd (-3)

def factor (j : ℕ) : R := ⟨1, (j : ℤ) + 1⟩

/-- The product at zero-based positions i through i+n-1. -/
def chunk (f : ℕ → R) (i : ℕ) : ℕ → R
  | 0 => 1
  | n+1 => chunk f i n * f (i+n)

def term (n : ℕ) : ℤ := (chunk factor 0 n).im

theorem term_eq_product (n : ℕ) :
    term n = (∏ j ∈ Finset.range n, (⟨1, 1+(j:ℤ)⟩ : R)).im := by
  have h : chunk factor 0 n = ∏ j ∈ Finset.range n, (⟨1, 1+(j:ℤ)⟩ : R) := by
    induction n with
    | zero => simp [chunk]
    | succ n ih => simp [chunk, Finset.prod_range_succ, ih, factor, add_comm]
  exact congrArg Zsqrtd.im h

theorem chunk_add (f : ℕ → R) (i n k : ℕ) :
    chunk f i (n+k) = chunk f i n * chunk f (i+n) k := by
  induction k with
  | zero => simp [chunk]
  | succ k ih =>
    change chunk f i (n+k) * f (i+(n+k)) = _
    rw [ih]
    simp [chunk,Nat.add_assoc,mul_assoc]

theorem shift_chunk (f : ℕ → R) (i j : ℕ) (q : R)
    (h : ∀ k, ∃ z : R, f (i+k) = f (j+k)+q*z) (n : ℕ) :
    ∃ z : R, chunk f i n = chunk f j n + q*z := by
  induction n with
  | zero => exact ⟨0, by simp [chunk]⟩
  | succ n ih =>
    obtain ⟨u,hu⟩ := ih
    obtain ⟨v,hv⟩ := h n
    refine ⟨u*f (j+n)+chunk f j n*v+q*u*v, ?_⟩
    simp only [chunk,hu,hv]
    ring

/-- Horner evaluation with coefficients in increasing degree. -/
def eval (x : ℤ) : List ℤ → ℤ
  | [] => 0
  | a::cs => a + x*eval x cs

private theorem eval_shift (x h : ℤ) (cs : List ℤ) :
    ∃ k : ℤ, eval (x+h) cs = eval x cs+h*k := by
  induction cs with
  | nil => exact ⟨0,by simp [eval]⟩
  | cons c cs ih =>
    obtain ⟨k,hk⟩ := ih
    exact ⟨eval x cs+(x+h)*k, by simp only [eval,hk]; ring⟩

/-- Coefficients after extracting the constant term and a factor of 256
    from the original eight-factor product. The identity is checked below. -/
private def realCoeffs : List ℤ :=
  [0,113427,1501233,8473248,25565904,44416512,44513280,23887872,5308416]
private def imagCoeffs : List ℤ :=
  [0,-174386,-1261008,-4652760,-9616320,-11257344,-6967296,-1769472]

def normalized (i : ℕ) : R :=
  ⟨17311+16*eval i realCoeffs, -147924+16*eval i imagCoeffs⟩

set_option maxHeartbeats 1200000 in
theorem eight (i : ℕ) : chunk factor (8*i) 8 = 16 * normalized i := by
  ext <;> norm_num [chunk, factor, normalized, eval, realCoeffs, imagCoeffs] <;> ring

private theorem normalized_shift (i h : ℕ) :
    ∃ z : R, normalized (i+h) = normalized i + (16*(h:R))*z := by
  obtain ⟨a,ha⟩ := eval_shift i h realCoeffs
  obtain ⟨b,hb⟩ := eval_shift i h imagCoeffs
  refine ⟨⟨a,b⟩, ?_⟩
  ext <;> simp [normalized,ha,hb] <;> ring

theorem extract_eights (m : ℕ) :
    chunk factor 0 (8*m) = ((16:ℤ)^m : ℤ) * (chunk normalized 0 m : R) := by
  induction m with
  | zero => simp [chunk]
  | succ m ih =>
    rw [Nat.mul_succ,chunk_add,zero_add,eight,ih]
    simp [chunk,pow_succ]
    ring

/-- A run of 2^e normalized eight-factor blocks, starting anywhere, has
    odd real coordinate and imaginary valuation exactly e+2. -/
theorem dyadic (e i : ℕ) :
    ∃ u v : ℤ, (chunk normalized i (2^e)).re = 2*u+1 ∧
      (chunk normalized i (2^e)).im = (2:ℤ)^e*4*(2*v+1) := by
  induction e generalizing i with
  | zero =>
    refine ⟨8655+8*eval i realCoeffs, -18491+2*eval i imagCoeffs, ?_, ?_⟩ <;>
      simp [chunk,normalized] <;> ring
  | succ e ih =>
    let h : ℕ := 2^e
    let X := chunk normalized i h
    obtain ⟨u,v,hu,hv⟩ := ih i
    change X.re = _ at hu
    change X.im = _ at hv
    have offset (k : ℕ) : ∃ z : R,
        normalized (i+h+k) = normalized (i+k)+(16*(h:R))*z := by
      rw [show i+h+k=i+k+h by omega]
      exact normalized_shift (i+k) h
    obtain ⟨z,hz⟩ := shift_chunk normalized (i+h) i _ offset h
    let K := X*z
    have key : chunk normalized i (2^(e+1)) =
        X*X + (((16:ℤ)*(2:ℤ)^e : ℤ) : R)*K := by
      rw [show 2^(e+1) = h+h by simp [h,pow_succ,Nat.mul_two]]
      rw [chunk_add,hz]
      change X*(X+16*(h:R)*z) = _
      dsimp [K,h]
      push_cast
      ring
    let q := (2:ℤ)^e
    refine ⟨2*u^2+2*u-24*q^2*(2*v+1)^2+8*q*K.re, 2*u*v+u+v+K.im, ?_, ?_⟩ <;>
      rw [key] <;> simp only [Zsqrtd.add_re, Zsqrtd.add_im, Zsqrtd.mul_re, Zsqrtd.mul_im,
        Zsqrtd.intCast_re, Zsqrtd.intCast_im, hu, hv, q, pow_succ] <;> ring

/-- Collecting k runs of length 2^e records the parity of k in the
    coefficient left after division by 4 * 2^e. -/
theorem collect (e k : ℕ) :
    ∃ u v : ℤ, (chunk normalized 0 (2^e*k)).re = 2*u+1 ∧
      (chunk normalized 0 (2^e*k)).im = (2:ℤ)^e*4*(2*v+k) := by
  induction k with
  | zero => exact ⟨0,0,by simp [chunk],by simp [chunk]⟩
  | succ k ih =>
    obtain ⟨u,v,hu,hv⟩ := ih
    obtain ⟨a,b,ha,hb⟩ := dyadic e (2^e*k)
    rw [Nat.mul_succ,chunk_add,zero_add]
    let q := (2:ℤ)^e
    refine ⟨2*u*a+u+a-24*q^2*(2*v+k)*(2*b+1),
      u*(2*b+1)+a*(2*v+k)+b+v, ?_, ?_⟩ <;>
      simp [hu,hv,ha,hb,q] <;> ring

end A363412Two
#print axioms A363412Two.eight
#print axioms A363412Two.dyadic
#print axioms A363412Two.collect
