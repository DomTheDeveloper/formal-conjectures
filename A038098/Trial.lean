module

public import A038098.Wide

/-! A kernel-computable primality test for the short list of sieve divisors.
Only trial divisors through the square root of the list bound are needed. -/
@[expose] public section
namespace Sun.CubeSieve

def trialPrime (q n : ℕ) : Bool :=
  decide (2 ≤ n) && (List.range (q+1)).all fun d =>
    decide (d < 2 ∨ n ≤ d ∨ n%d ≠ 0)

theorem trialPrime_iff {q n : ℕ} (hs : n < (q+1)^2) :
    trialPrime q n = true ↔ n.Prime := by
  simp only [trialPrime, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range]
  constructor
  · rintro ⟨hn,hf⟩
    by_contra hnp
    let p := n.minFac
    have hprime : p.Prime := Nat.minFac_prime (by omega)
    have hbound : p^2 ≤ n := Nat.minFac_sq_le_self (by omega) hnp
    have hsmall : p < q+1 := by
      by_contra! hlarge
      have := Nat.pow_le_pow_left hlarge 2
      omega
    have h2 : 2 ≤ p := hprime.two_le
    have hlt : p < n := (Nat.not_prime_iff_minFac_lt hn).1 hnp
    have hmod : n%p = 0 := Nat.mod_eq_zero_of_dvd (Nat.minFac_dvd n)
    rcases hf p hsmall with h | h | h <;> omega
  · intro hn
    refine ⟨hn.two_le, ?_⟩
    intro d _
    by_cases hd1 : d < 2
    · exact Or.inl hd1
    by_cases hd : n ≤ d
    · exact Or.inr (Or.inl hd)
    right; right
    intro he
    rcases (Nat.dvd_prime hn).1 (Nat.dvd_of_mod_eq_zero he) with heq | heq <;> omega

def trialList (q b : ℕ) : List ℕ := (List.range (b+1)).filter (trialPrime q)

theorem primeList_eq_trial {q b : ℕ} (hb : b < (q+1)^2) :
    primeList b = trialList q b := by
  apply List.filter_congr
  intro n hn
  apply Bool.eq_iff_iff.2
  rw [decide_eq_true_eq, trialPrime_iff]
  exact lt_of_le_of_lt (by have := List.mem_range.1 hn; omega) hb

theorem primeCounting_eq_length (b : ℕ) : b.primeCounting = (primeList b).length :=
  List.countP_eq_length_filter

/-- Keep both endpoints explicit when elaborating very large concrete prime counts. -/
theorem extend_to {a v width r t b total stop : ℕ} (he : a+width = stop)
    (ha : a.primeCounting = v) (hr : 0 < r) (ht : t < 2^r-1) (hw : width ≤ r*t)
    (hb : b < a+1) (hs : 2 ≤ a+1) (hu : a+1+width ≤ (b+1)^2)
    (hc : packedBlockCount r t b (a+1) width + v = total) : stop.primeCounting = total := by
  rw [← he]
  exact primeCounting_extend_packed ha hr ht hw hb hs hu hc

/-- Restrict a single verified divisor table to an earlier endpoint. -/
theorem primeList_succ (n : ℕ) :
    primeList (n+1) = primeList n ++ (if (n+1).Prime then [n+1] else []) := by
  unfold primeList
  rw [List.range_succ,List.filter_append]
  split_ifs with h <;> simp [h]

theorem primeCounting_prefix {a b : ℕ} (hab : a≤b) :
    a.primeCounting = ((primeList b).filter (fun i => decide (i≤a))).length := by
  rw [primeCounting_eq_length]
  congr 1
  symm
  induction b, hab using Nat.le_induction with
  | base =>
    apply List.filter_eq_self.2
    intro i hi
    exact decide_eq_true ((mem_primeList _ _).1 hi).1
  | succ b hab ih =>
    rw [primeList_succ,List.filter_append,ih]
    have hn : ¬b+1≤a := by omega
    split_ifs <;> simp [hn]

def addLanes (r t x : ℕ) : ℕ → ℕ
  | 0 => 0
  | j+1 => addLanes r t x j + laneFast r t (x>>>j)

theorem addLanes_eq (r t x n : ℕ) :
    addLanes r t x n = ∑ j ∈ Finset.range n, laneFast r t (x>>>j) := by
  induction n with
  | zero => simp [addLanes]
  | succ j ih => rw [addLanes,Finset.sum_range_succ,ih]

theorem extend_certificate {a v width r t b total stop mask : ℕ} {ps : List ℕ}
    (he : a+width=stop) (ha : a.primeCounting=v) (hp : primeList b=ps)
    (hr : 0<r) (ht : t<2^r-1) (hw : width≤r*t) (hb : b<a+1)
    (hs : 2≤a+1) (hu : a+1+width≤(b+1)^2)
    (hm : compositeMask (a+1) width ps % (1<<<width) = mask)
    (hc : width-addLanes r t mask r+v=total) : stop.primeCounting=total := by
  apply extend_to he ha hr ht hw hb hs hu
  unfold packedBlockCount wideWeight
  rw [hp,hm,← addLanes_eq]
  exact hc

end Sun.CubeSieve
