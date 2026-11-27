module

public import Mathlib.NumberTheory.PrimeCounting
public import Mathlib.Data.Nat.Bitwise
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Linarith

/-! A segmented bit sieve for kernel-checkable instances of Sun's A038098 (i).
For a block above the sieve bound, each marked integer is composite. Conversely
its least prime factor marks every composite in the block. -/

@[expose] public section
namespace Sun.CubeSieve

/-- A geometric series whose set bits occupy positions 0, p, 2p, .... -/
def progression (p : ℕ) : ℕ → ℕ
  | 0 => 0
  | n+1 => 2^p * progression p n + 1

theorem progression_mul (p n : ℕ) :
    progression p n * (2^p-1) + 1 = 2^(p*n) := by
  induction n with
  | zero => simp [progression]
  | succ n ih =>
    rw [progression, Nat.mul_succ, pow_add, ← ih]
    have hb : 0 < 2^p := Nat.two_pow_pos _
    generalize 2^p = b at *
    obtain ⟨c, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : b ≠ 0)
    simp only [Nat.succ_sub_one, Nat.succ_eq_add_one]
    ring

/-- The quotient computes the mask with two shifts and one division. -/
def periodic (p n : ℕ) : ℕ :=
  ((1 <<< (p*n))-1) / ((1 <<< p)-1)

theorem periodic_eq {p : ℕ} (hp : 0 < p) (n : ℕ) :
    periodic p n = progression p n := by
  have h := progression_mul p n
  simp only [periodic, Nat.shiftLeft_eq, one_mul]
  rw [← h, Nat.add_sub_cancel]
  exact Nat.mul_div_cancel _ (by have := Nat.one_lt_two_pow (by omega : p ≠ 0); omega)

theorem bit_progression {p : ℕ} (hp : 0 < p) (n i : ℕ) :
    (progression p n).testBit i = true ↔ i < p*n ∧ p ∣ i := by
  induction n generalizing i with
  | zero => simp [progression]
  | succ n ih =>
    rw [progression, Nat.testBit_two_pow_mul_add _ (Nat.one_lt_two_pow (by omega : p ≠ 0)), Nat.mul_succ]
    by_cases h : i < p
    · simp only [h, if_true]
      rw [show (1:ℕ) = 2^0 by decide, Nat.testBit_two_pow, decide_eq_true_eq]
      constructor
      · rintro rfl
        exact ⟨by omega, dvd_zero _⟩
      · rintro ⟨_, hd⟩
        by_contra hn
        have := Nat.le_of_dvd (by omega : 0 < i) hd
        omega
    · simp only [h, if_false, ih]
      have hd : p ∣ i-p ↔ p ∣ i := by
        obtain ⟨k,hk⟩ := Nat.exists_eq_add_of_le (le_of_not_gt h)
        subst i
        simp
      rw [hd]
      omega

def divisorMask (p start width : ℕ) : ℕ :=
  periodic p (width/p+2) >>> (start%p)

theorem bit_divisorMask {p width : ℕ} (hp : 0 < p) (start : ℕ) {i : ℕ} (hi : i < width) :
    (divisorMask p start width).testBit i = true ↔ p ∣ start+i := by
  rw [divisorMask, Nat.testBit_shiftRight, periodic_eq hp, bit_progression hp]
  have ha := Nat.mod_lt start hp
  have hb := Nat.mod_lt width hp
  have hc := Nat.div_add_mod width p
  have hsize : start%p+i < p*(width/p+2) := by rw [Nat.mul_add, Nat.mul_two]; omega
  rw [and_iff_right hsize]
  have hrestore := Nat.div_add_mod start p
  conv_rhs => rw [← hrestore]
  rw [Nat.add_assoc]
  exact Nat.dvd_add_iff_right (Nat.dvd_mul_right p _)

def compositeMask (start width : ℕ) (ps : List ℕ) : ℕ :=
  ps.foldr (fun p mask => divisorMask p start width ||| mask) 0

theorem bit_compositeMask {start width i : ℕ} (hi : i < width) (ps : List ℕ)
    (hp : ∀ p ∈ ps, 0 < p) :
    (compositeMask start width ps).testBit i = true ↔ ∃ p ∈ ps, p ∣ start+i := by
  induction ps with
  | nil => simp [compositeMask]
  | cons p ps ih =>
    change (divisorMask p start width ||| compositeMask start width ps).testBit i = true ↔ _
    rw [Nat.testBit_or, Bool.or_eq_true, bit_divisorMask (hp p (by simp)) _ hi,
      ih (fun q hq => hp q (by simp [hq]))]
    simp

def primeList (b : ℕ) : List ℕ := (List.range (b+1)).filter fun p => decide p.Prime

theorem mem_primeList (b p : ℕ) : p ∈ primeList b ↔ p ≤ b ∧ p.Prime := by
  simp [primeList]

theorem mask_prime {b start width i : ℕ} (hb : b < start) (hstart : 2 ≤ start)
    (hu : start+width ≤ (b+1)^2) (hi : i < width) :
    (compositeMask start width (primeList b)).testBit i = false ↔ (start+i).Prime := by
  have key := bit_compositeMask (start := start) hi (primeList b)
    (fun p h => ((mem_primeList _ _).1 h).2.pos)
  constructor
  · intro h
    by_contra hnp
    let q := (start+i).minFac
    have hq : q.Prime := Nat.minFac_prime (by omega)
    have hsq := Nat.minFac_sq_le_self (by omega : 0 < start+i) hnp
    have hsmall : q ≤ b := by
      by_contra! hbig
      have := Nat.pow_le_pow_left (show b+1 ≤ q by omega) 2
      change q^2 ≤ start+i at hsq
      omega
    have ht := key.2 ⟨q, (mem_primeList _ _).2 ⟨hsmall,hq⟩, Nat.minFac_dvd _⟩
    simp [h] at ht
  · intro h
    cases he : (compositeMask start width (primeList b)).testBit i with
    | false => rfl
    | true =>
      obtain ⟨p,hp,hd⟩ := key.1 he
      have hh := (mem_primeList _ _).1 hp
      rcases (Nat.dvd_prime h).1 hd with h1 | h1
      · exact (hh.2.ne_one h1).elim
      · omega

theorem count_congr_below {f g : ℕ → Prop} [DecidablePred f] [DecidablePred g] {w : ℕ}
    (h : ∀ i < w, f i ↔ g i) : Nat.count f w = Nat.count g w := by
  simp only [Nat.count_eq_card_filter_range]
  congr 1
  apply Finset.filter_congr
  simpa using h

/-- Four bits per entry encode all 256 byte weights, checked below. -/
def byteWeight (n : ℕ) : ℕ := (95125173855764218123276304889944061997689682402263585766959741291920687686033329201817409157123347502415384089435969498586180241031507595463600295898153685276653211633572815512294064538494957912327413386667662218713394765509704508661031522276467630197481635010039778342554499416459730172574551513689147646224 >>> (4*(n%256))) % 16

theorem byteWeight_eq (n : ℕ) : byteWeight n = Nat.count (fun i => n.testBit i = true) 8 := by
  have cert : ∀ k : Fin 256, byteWeight k.val = Nat.count (fun i => k.val.testBit i = true) 8 := by
    decide +kernel
  have h := cert ⟨n%256, Nat.mod_lt _ (by decide)⟩
  have he : byteWeight n = byteWeight (n%256) := by simp [byteWeight]
  rw [he,h]
  apply count_congr_below
  intro i hi
  change (n % (2^8)).testBit i = true ↔ _
  rw [Nat.testBit_mod_two_pow]
  simp [hi]

def weight : ℕ → ℕ → ℕ
  | 0,n => byteWeight n
  | d+1,n =>
      let half := 8 <<< d
      weight d (n % (1 <<< half)) + weight d (n >>> half)

theorem weight_eq (d n : ℕ) : weight d n = Nat.count (fun i => n.testBit i = true) (8 <<< d) := by
  induction d generalizing n with
  | zero => exact byteWeight_eq n
  | succ d ih =>
    let half := 8 <<< d
    have hw : 8 <<< (d+1) = half + half := by simp [half, Nat.shiftLeft_eq, pow_succ]; omega
    rw [hw,Nat.count_add,weight,ih,ih]
    congr 1
    · apply count_congr_below
      intro i hi
      change (n % (1 <<< half)).testBit i = true ↔ _
      change i < half at hi
      simp [Nat.shiftLeft_eq, Nat.testBit_mod_two_pow, hi]
    · simp [half,Nat.testBit_shiftRight]

def prefixWeight (d w mask : ℕ) : ℕ := weight d (mask % (1 <<< w))

theorem prefixWeight_eq {d w : ℕ} (hw : w ≤ 8 <<< d) (mask : ℕ) :
    prefixWeight d w mask = Nat.count (fun i => mask.testBit i = true) w := by
  rw [prefixWeight,weight_eq]
  obtain ⟨t, ht⟩ := Nat.exists_eq_add_of_le hw
  rw [ht,Nat.count_add]
  have he : Nat.count (fun k => (mask % (1 <<< w)).testBit (w+k) = true) t = 0 := by
    simp [Nat.count_eq_card_filter_range, Nat.shiftLeft_eq, Nat.testBit_mod_two_pow]
  rw [he,Nat.add_zero]
  apply count_congr_below
  intro i hi
  simp [Nat.shiftLeft_eq, Nat.testBit_mod_two_pow, hi]

def blockCount (d b start width : ℕ) : ℕ :=
  width - prefixWeight d width (compositeMask start width (primeList b))

theorem blockCount_eq {d b start width : ℕ} (hw : width ≤ 8 <<< d) (hb : b < start)
    (hstart : 2 ≤ start) (hu : start+width ≤ (b+1)^2) :
    blockCount d b start width = Nat.count (fun i => (start+i).Prime) width := by
  rw [blockCount,prefixWeight_eq hw]
  have hc := count_congr_below (g := fun i => ¬(start+i).Prime) (w := width)
    (f := fun i => (compositeMask start width (primeList b)).testBit i = true)
    (fun i hi => by
      have hm := mask_prime hb hstart hu hi
      rw [← hm]
      cases (compositeMask start width (primeList b)).testBit i <;> decide)
  rw [hc]
  simp only [Nat.count_eq_card_filter_range]
  have h := Finset.card_filter_add_card_filter_not (s := Finset.range width) (p := fun i => (start+i).Prime)
  rw [Finset.card_range] at h
  omega

/-- Extend an already verified inclusive prime count by one segmented count. -/
theorem primeCounting_extend {a v width d b total : ℕ} (ha : a.primeCounting = v)
    (hw : width ≤ 8 <<< d) (hb : b < a+1) (hstart : 2 ≤ a+1) (hu : a+1+width ≤ (b+1)^2)
    (hc : blockCount d b (a+1) width + v = total) : (a+width).primeCounting = total := by
  change Nat.count Nat.Prime (a+width+1) = total
  rw [show a+width+1 = (a+1)+width by omega, Nat.count_add]
  change a.primeCounting + _ = total
  rw [ha,← blockCount_eq hw hb hstart hu, Nat.add_comm,hc]

end Sun.CubeSieve
