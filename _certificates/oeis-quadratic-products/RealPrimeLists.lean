import QuadraticDivisors
import Mathlib.Algebra.Field.ZMod

/-!
# Primes that never divide a real coefficient

The recurrence modulo p suffices to decide whether p ever divides a real
coefficient. A block of length 2p acts by a scalar, so the finite calculation
certifies a condition at every natural index.

The final three lists correspond to OEIS A363409, A363413 and A363415.
The last list includes 139 between 137 and 157.
-/

namespace QuadraticDivisors

/-- Real part of the product with indices 1 through n. -/
def A (d : ℤ) (n : ℕ) : ℤ := (block d 1 n).re

structure Residues (p : ℕ) where
  re : ZMod p
  im : ZMod p
  realProduct : ZMod p
  deriving DecidableEq

/-- Keep both coordinates and the product of all real coordinates seen. -/
def step {p : ℕ} (d : ℤ) (k : ZMod p) (s : Residues p) : Residues p :=
  let a := s.re - (d : ZMod p) * k * s.im
  ⟨a, s.im + k * s.re, s.realProduct * a⟩

def residues (d : ℤ) (p : ℕ) : ℕ → Residues p
  | 0 => ⟨1, 0, 1⟩
  | n + 1 => step d ((n : ZMod p) + 1) (residues d p n)

private theorem coordinates (d : ℤ) (p n : ℕ) :
    (residues d p n).re = (A d n : ZMod p) ∧
    (residues d p n).im = (B d n : ZMod p) := by
  unfold A B
  induction n with
  | zero => simp [residues, block]
  | succ n ih =>
    simp only [residues, step, block, Zsqrtd.re_mul, Zsqrtd.im_mul, factor,
      Int.cast_add, Int.cast_mul, Int.cast_neg, Int.cast_one, Int.cast_natCast, ih.1, ih.2]
    constructor <;> ring

private theorem shifted (d : ℤ) (p t : ℕ) (ht : (t : ZMod p) = 0)
    (hi : (residues d p t).im = 0) (n : ℕ) :
    (residues d p (n + t)).re = (residues d p t).re * (residues d p n).re ∧
    (residues d p (n + t)).im = (residues d p t).re * (residues d p n).im := by
  induction n with
  | zero => simp [residues, hi]
  | succ n ih =>
    rw [Nat.succ_add]
    simp only [residues, step, Nat.cast_add, ht, add_zero, ih.1, ih.2]
    constructor <;> ring

private theorem product_nonzero (d : ℤ) (p : ℕ) [Fact p.Prime] (n : ℕ) :
    (residues d p n).realProduct ≠ 0 ↔
      ∀ j ≤ n, (residues d p j).re ≠ 0 := by
  induction n with
  | zero => simp [residues]
  | succ n ih =>
    change (residues d p n).realProduct * (residues d p (n + 1)).re ≠ 0 ↔ _
    rw [mul_ne_zero_iff, ih]
    constructor
    · rintro ⟨prev, last⟩ j hj
      rcases Nat.lt_or_eq_of_le hj with h | rfl
      · exact prev j (by omega)
      · exact last
    · intro h
      exact ⟨fun j hj => h j (by omega), h _ (by omega)⟩

/-- A window ending at a scalar block controls the real coordinate at all
    indices. Including t in the window accounts for a zero scalar as well. -/
private theorem all_indices (d : ℤ) (p t : ℕ) [Fact p.Prime] (hpos : 0 < t)
    (ht : (t : ZMod p) = 0) (hi : (residues d p t).im = 0) :
    (residues d p t).realProduct ≠ 0 ↔ ∀ n, ¬ (p : ℤ) ∣ A d n := by
  have relate (j : ℕ) : (residues d p j).re ≠ 0 ↔ ¬ (p : ℤ) ∣ A d j := by
    rw [(coordinates d p j).1]
    exact not_congr (ZMod.intCast_zmod_eq_zero_iff_dvd (A d j) p)
  rw [product_nonzero]
  constructor
  · intro small n
    apply (relate n).mp
    induction n using Nat.strong_induction_on with
    | h n prev =>
      by_cases hn : n ≤ t
      · exact small n hn
      · have eqn : n - t + t = n := by omega
        have hs := (shifted d p t ht hi (n - t)).1
        rw [eqn] at hs
        rw [hs]
        exact mul_ne_zero (small t (le_refl t)) (prev _ (by omega))
  · intro h j _
    exact (relate j).mpr (h j)

theorem finite_test (d : ℤ) (hd : 2 ≤ d) (p : ℕ) (hp : p.Prime) :
    (residues d p (2 * p)).realProduct ≠ 0 ↔ ∀ n, ¬ (p : ℤ) ∣ A d n := by
  let _ : Fact p.Prime := ⟨hp⟩
  have hi : (residues d p (2 * p)).im = 0 := by
    rw [(coordinates d p (2 * p)).2, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact (nonzero_multiple d hd p hp.pos).1
  exact all_indices d p (2 * p) (by have := hp.pos; omega) (by simp) hi

/-- An equivalent tail-recursive scan for the finite certificates. -/
private def scanFrom (d : ℤ) (p : ℕ) : ℕ → ℕ → Residues p → Residues p
  | 0, _, s => s
  | len + 1, done, s => scanFrom d p len (done + 1) (step d ((done : ZMod p) + 1) s)

private theorem scanFrom_spec (d : ℤ) (p len : ℕ) (n : ℕ) :
    scanFrom d p len n (residues d p n) = residues d p (n + len) := by
  induction len generalizing n with
  | zero => rfl
  | succ len ih =>
    change scanFrom d p len (n + 1) (residues d p (n + 1)) = _
    rw [ih, show n + 1 + len = n + (len + 1) by omega]

def scan (d : ℤ) (p n : ℕ) : Residues p :=
  scanFrom d p n 0 ⟨1, 0, 1⟩

theorem scan_spec (d : ℤ) (p n : ℕ) : scan d p n = residues d p n := by
  simpa [scan, residues] using scanFrom_spec d p n 0

def primePrefix (d : ℤ) (bound : ℕ) : List ℕ :=
  (List.range (bound + 1)).filter fun p =>
    decide (p.Prime ∧ (scan d p (2 * p)).realProduct ≠ 0)

theorem mem_primePrefix_iff (d : ℤ) (hd : 2 ≤ d) (bound p : ℕ) :
    p ∈ primePrefix d bound ↔ p ≤ bound ∧ p.Prime ∧ ∀ n, ¬ (p : ℤ) ∣ A d n := by
  simp only [primePrefix, List.mem_filter, List.mem_range, Nat.lt_succ_iff,
    decide_eq_true_eq, scan_spec]
  constructor
  · rintro ⟨hb, hp, hw⟩
    exact ⟨hb, hp, (finite_test d hd p hp).mp hw⟩
  · rintro ⟨hb, hp, hw⟩
    exact ⟨hb, hp, (finite_test d hd p hp).mpr hw⟩

-- The calculations below use the kernel's decision procedure.
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000

theorem certificate_139 :
    scan 5 139 138 = ⟨2, 0, 20⟩ ∧ scan 5 139 139 = ⟨2, 0, 40⟩ := by
  decide +kernel

private theorem forty_nonzero : (40 : ZMod 139) ≠ 0 := by decide +kernel

/-- The prime 139, omitted from the proposed list in A363415, never divides a term. -/
theorem missing_prime_139 : Nat.Prime 139 ∧ ∀ n, ¬ (139 : ℤ) ∣ A 5 n := by
  have hp : Nat.Prime 139 := by decide
  let _ : Fact (Nat.Prime 139) := ⟨hp⟩
  have c := certificate_139.2
  rw [scan_spec] at c
  apply And.intro hp
  apply (all_indices 5 139 139 (by decide) (ZMod.natCast_self _) (by rw [c])).mp
  rw [c]
  exact forty_nonzero

theorem prefix_A363409 :
    primePrefix 2 101 = [2, 5, 13, 23, 29, 31, 47, 53, 61, 71, 101] := by
  decide +kernel

theorem prefix_A363413 :
    primePrefix 4 79 = [2, 3, 11, 19, 23, 31, 47, 59, 67, 71, 79] := by
  decide +kernel

theorem corrected_prefix_A363415 :
    primePrefix 5 197 = [5, 11, 13, 31, 53, 79, 97, 113, 137, 139, 157, 179, 193, 197] := by
  decide +kernel

end QuadraticDivisors

#print axioms QuadraticDivisors.finite_test
#print axioms QuadraticDivisors.missing_prime_139
#print axioms QuadraticDivisors.prefix_A363409
#print axioms QuadraticDivisors.prefix_A363413
#print axioms QuadraticDivisors.corrected_prefix_A363415
