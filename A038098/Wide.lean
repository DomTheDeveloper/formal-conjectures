module

public import A038098.Sieve

/-! Count bits in parallel using residues modulo 2^r − 1. For a given residue
class of bit positions, shift it to positions divisible by r and mask the word.
Each selected power of 2 is 1 modulo 2^r−1. The block-size hypothesis rules
out any wrap in this residue count. -/

@[expose] public section
namespace Sun.CubeSieve
open Finset

def laneCount (r : ℕ) : ℕ → ℕ → ℕ
  | 0,_ => 0
  | t+1,x => x%2 + laneCount r t (x >>> r)

theorem laneCount_le (r t x : ℕ) : laneCount r t x ≤ t := by
  induction t generalizing x with
  | zero => simp [laneCount]
  | succ t ih => rw [laneCount]; have := ih (x >>> r); omega

theorem stripe_step {r : ℕ} (hr : 0 < r) (t x : ℕ) :
    x &&& progression r (t+1) = x%2 + 2^r*((x>>>r) &&& progression r t) := by
  let y := x &&& progression r (t+1)
  have hB : 1 < 2^r := Nat.one_lt_two_pow (by omega)
  have h2dvd : 2 ∣ 2^r := dvd_pow_self _ (by omega)
  have hlo : y % 2^r = x%2 := by
    dsimp [y]
    rw [Nat.and_mod_two_pow, progression, Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt hB,
      Nat.and_one_is_mod, Nat.mod_mod_of_dvd _ h2dvd]
  have hhi : y / 2^r = (x>>>r) &&& progression r t := by
    rw [← Nat.shiftRight_eq_div_pow]
    dsimp [y]
    rw [Nat.shiftRight_and_distrib, Nat.shiftRight_eq_div_pow (progression r (t+1)),progression,
      Nat.add_comm, Nat.add_mul_div_left _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt hB, Nat.zero_add]
  have h := Nat.mod_add_div y (2^r)
  rw [hlo,hhi] at h
  exact h.symm

def laneFast (r t x : ℕ) : ℕ := (x &&& periodic r t) % ((1 <<< r)-1)

theorem laneFast_eq {r : ℕ} (hr : 0 < r) (t x : ℕ) (ht : t < 2^r-1) :
    laneFast r t x = laneCount r t x := by
  unfold laneFast
  rw [periodic_eq hr, Nat.shiftLeft_eq, one_mul]
  induction t generalizing x with
  | zero => simp [progression,laneCount]
  | succ t ih =>
    rw [stripe_step hr, laneCount]
    let y := (x>>>r) &&& progression r t
    let M := 2^r-1
    have hB : 2^r=M+1 := by dsimp [M]; have := Nat.two_pow_pos r; omega
    have hcount : x%2 + laneCount r t (x>>>r) < M := by
      have := laneCount_le r t (x>>>r)
      dsimp [M]; omega
    change (x%2 + 2^r*y)%M = _
    calc (x%2+2^r*y)%M = (x%2+y+M*y)%M := by congr 1; rw [hB]; ring
      _ = (x%2+y)%M := Nat.add_mul_mod_self_left _ _ _
      _ = (x%2+(y%M))%M := by simp
      _ = _ := by rw [show y%M = laneCount r t (x>>>r) from ih (x>>>r) (by omega), Nat.mod_eq_of_lt hcount]

theorem sum_digits (r x : ℕ) :
    ∑ j ∈ range r, (x>>>j)%2 = Nat.count (fun j => x.testBit j = true) r := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [sum_range_succ, Nat.count_succ, ih]
    by_cases h : (x>>>r)%2 = 0
    · simp [Nat.testBit, Nat.one_and_eq_mod_two,h]
    · have h1 : (x>>>r)%2 = 1 := by omega
      simp [Nat.testBit, Nat.one_and_eq_mod_two,h1]

theorem sum_lanes (r t x : ℕ) :
    ∑ j ∈ range r, laneCount r t (x>>>j) = Nat.count (fun j => x.testBit j = true) (r*t) := by
  induction t generalizing x with
  | zero => simp [laneCount]
  | succ t ih =>
    simp only [laneCount, sum_add_distrib, Nat.mul_succ]
    rw [sum_digits, Nat.add_comm (r*t) r, Nat.count_add]
    have swap (j : ℕ) : (x>>>j)>>>r = (x>>>r)>>>j := by
      rw [← Nat.shiftRight_add,← Nat.shiftRight_add,Nat.add_comm]
    simp_rw [swap]
    rw [ih]
    simp [Nat.testBit_shiftRight]

def wideWeight (r t x : ℕ) : ℕ :=
  ∑ j ∈ range r, laneFast r t (x>>>j)

theorem wideWeight_eq {r t : ℕ} (hr : 0 < r) (ht : t < 2^r-1) (x : ℕ) :
    wideWeight r t x = Nat.count (fun j => x.testBit j = true) (r*t) := by
  simpa only [wideWeight, laneFast_eq hr t _ ht] using sum_lanes r t x

def packedBlockCount (r t b start width : ℕ) : ℕ :=
  width - wideWeight r t (compositeMask start width (primeList b) % (1<<<width))

theorem packedBlockCount_eq {r t b start width : ℕ} (hr : 0 < r) (ht : t < 2^r-1)
    (hw : width ≤ r*t) (hb : b < start) (hstart : 2 ≤ start) (hu : start+width ≤ (b+1)^2) :
    packedBlockCount r t b start width = Nat.count (fun i => (start+i).Prime) width := by
  let m := compositeMask start width (primeList b)
  have hw' : width ≤ 8 <<< width := by
    rw [Nat.shiftLeft_eq]
    have := Nat.lt_two_pow_self (n := width)
    omega
  rw [← blockCount_eq (d := width) hw' hb hstart hu, packedBlockCount, blockCount,
    prefixWeight_eq hw', wideWeight_eq hr ht]
  congr 1
  obtain ⟨u,hu'⟩ := Nat.exists_eq_add_of_le hw
  rw [hu',Nat.count_add]
  change Nat.count (fun j => (m % (1<<<width)).testBit j = true) width +
    Nat.count (fun j => (m % (1<<<width)).testBit (width+j) = true) u = _
  have hzero : Nat.count (fun j => (m % (1<<<width)).testBit (width+j) = true) u = 0 := by
    simp [Nat.count_eq_card_filter_range,Nat.shiftLeft_eq,Nat.testBit_mod_two_pow]
  rw [hzero,Nat.add_zero]
  apply count_congr_below
  intro j hj
  simp [Nat.shiftLeft_eq,Nat.testBit_mod_two_pow,hj,m]

theorem primeCounting_extend_packed {a v width r t b total : ℕ} (ha : a.primeCounting = v)
    (hr : 0 < r) (ht : t < 2^r-1) (hw : width ≤ r*t) (hb : b < a+1) (hs : 2 ≤ a+1)
    (hu : a+1+width ≤ (b+1)^2) (hc : packedBlockCount r t b (a+1) width + v = total) :
    (a+width).primeCounting = total := by
  change Nat.count Nat.Prime (a+width+1) = total
  rw [show a+width+1 = (a+1)+width by omega, Nat.count_add]
  change a.primeCounting + _ = total
  rw [ha,← packedBlockCount_eq hr ht hw hb hs hu,Nat.add_comm,hc]

end Sun.CubeSieve
