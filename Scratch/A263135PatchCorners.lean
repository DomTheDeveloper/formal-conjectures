import Scratch.A263135PatchDefs

namespace OeisA263135

def lowerPairs (b : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range b).biUnion Finset.antidiagonal

@[simp]
theorem mem_lowerPairs {b i j : ℕ} :
    (i, j) ∈ lowerPairs b ↔ i + j < b := by
  constructor
  · intro h
    rcases Finset.mem_biUnion.mp h with ⟨n, hn, hij⟩
    have hs : i + j = n := by
      simpa using Finset.mem_antidiagonal.mp hij
    exact hs ▸ Finset.mem_range.mp hn
  · intro h
    apply Finset.mem_biUnion.mpr
    exact ⟨i + j, Finset.mem_range.mpr h, Finset.mem_antidiagonal.mpr rfl⟩

private theorem antidiagonal_pairwise_disjoint (b : ℕ) :
    (Finset.range b : Set ℕ).PairwiseDisjoint Finset.antidiagonal := by
  intro m hm n hn hmn
  change Disjoint (Finset.antidiagonal m) (Finset.antidiagonal n)
  rw [Finset.disjoint_left]
  intro p hpm hpn
  have hm' : p.1 + p.2 = m := Finset.mem_antidiagonal.mp hpm
  have hn' : p.1 + p.2 = n := Finset.mem_antidiagonal.mp hpn
  exact hmn (hm'.symm.trans hn')

theorem card_lowerPairs (b : ℕ) :
    (lowerPairs b).card = ∑ n ∈ Finset.range b, (n + 1) := by
  rw [lowerPairs, Finset.card_biUnion]
  · simp
  · exact antidiagonal_pairwise_disjoint b

private theorem two_mul_sum_range_succ (n : ℕ) :
    2 * (∑ i ∈ Finset.range n, (i + 1)) = n * (n + 1) := by
  cases n with
  | zero => simp
  | succ k =>
      have h := Finset.sum_range_id_mul_two (k + 1)
      simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
        Nat.nsmul_eq_mul, mul_one] at h ⊢
      norm_num [Nat.succ_sub_one] at h ⊢
      nlinarith

def lowerCornerTriples (b : ℕ) : Finset ((ℕ × ℕ) × Bool) :=
  (lowerPairs b ×ˢ {false}) ∪ (lowerPairs (b - 1) ×ˢ {true})

private theorem lower_corner_sides_disjoint (b : ℕ) :
    Disjoint (lowerPairs b ×ˢ {false}) (lowerPairs (b - 1) ×ˢ {true}) := by
  rw [Finset.disjoint_left]
  intro x hx hy
  have hf : x.2 = false := by
    simpa using (Finset.mem_product.mp hx).2
  have ht : x.2 = true := by
    simpa using (Finset.mem_product.mp hy).2
  exact Bool.noConfusion (hf.symm.trans ht)

theorem card_lowerCornerTriples (b : ℕ) :
    (lowerCornerTriples b).card = b ^ 2 := by
  rw [lowerCornerTriples,
    Finset.card_union_of_disjoint (lower_corner_sides_disjoint b)]
  simp only [Finset.card_product, Finset.card_singleton, mul_one,
    card_lowerPairs]
  by_cases hb : b = 0
  · subst b
    simp
  · obtain ⟨k, rfl⟩ : ∃ k, b = k + 1 :=
      ⟨b - 1, by omega⟩
    have h1 := two_mul_sum_range_succ (k + 1)
    have h2 := two_mul_sum_range_succ k
    apply Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 2)
    rw [Nat.mul_add, h1, h2]
    simp
    ring

theorem lowerCornerTriples_eq_filter_rankBox
    (A B b : ℕ) (hbA : b ≤ A) (hbB : b ≤ B) :
    lowerCornerTriples b =
      (rankBox A B).filter fun x => rankLevel (tripleRankPoint x) < b := by
  ext x
  rcases x with ⟨⟨i, j⟩, side⟩
  cases side <;>
    simp [lowerCornerTriples, rankBox, rankLevel, tripleRankPoint, mem_lowerPairs] <;>
    omega

def reflectTriple (A B : ℕ) (x : (ℕ × ℕ) × Bool) : (ℕ × ℕ) × Bool :=
  ((A - 1 - x.1.1, B - 1 - x.1.2), !x.2)

private theorem reflectTriple_involutive_on_box
    {A B : ℕ} {x : (ℕ × ℕ) × Bool} (hx : x ∈ rankBox A B) :
    reflectTriple A B (reflectTriple A B x) = x := by
  rcases x with ⟨⟨i, j⟩, side⟩
  simp [rankBox] at hx
  rcases hx with ⟨hi, hj⟩
  apply Prod.ext
  · apply Prod.ext <;> simp [reflectTriple] <;> omega
  · simp [reflectTriple]

private theorem reflectTriple_mem_box
    {A B : ℕ} {x : (ℕ × ℕ) × Bool} (hx : x ∈ rankBox A B) :
    reflectTriple A B x ∈ rankBox A B := by
  rcases x with ⟨⟨i, j⟩, side⟩
  simp [rankBox, reflectTriple] at hx ⊢
  rcases hx with ⟨hi, hj⟩
  constructor <;> omega

def upperCornerTriples (A B b C : ℕ) : Finset ((ℕ × ℕ) × Bool) :=
  (rankBox A B).filter fun x => b + C ≤ rankLevel (tripleRankPoint x)

theorem card_upperCornerTriples
    (A B b C : ℕ) (hsum : A + B = C + 2 * b) (hbA : b ≤ A) (hbB : b ≤ B) :
    (upperCornerTriples A B b C).card = b ^ 2 := by
  rw [← card_lowerCornerTriples b]
  apply Finset.card_bij (fun x hx => reflectTriple A B x)
  · intro x hx
    have hxbox := (Finset.mem_filter.mp hx).1
    have hxupper := (Finset.mem_filter.mp hx).2
    rw [lowerCornerTriples_eq_filter_rankBox A B b hbA hbB]
    apply Finset.mem_filter.mpr
    refine ⟨reflectTriple_mem_box hxbox, ?_⟩
    rcases x with ⟨⟨i, j⟩, side⟩
    have hij := by
      simpa [rankBox] using hxbox
    have hi : i < A := hij.1
    have hj : j < B := hij.2
    have hAi : A - 1 - i + i + 1 = A := by omega
    have hBj : B - 1 - j + j + 1 = B := by omega
    cases side <;>
      simp [reflectTriple, rankLevel, tripleRankPoint] at hxupper ⊢ <;> omega
  · intro x hx y hy hxy
    have hxbox := (Finset.mem_filter.mp hx).1
    have hybox := (Finset.mem_filter.mp hy).1
    rw [← reflectTriple_involutive_on_box hxbox,
      ← reflectTriple_involutive_on_box hybox, hxy]
  · intro y hy
    rw [lowerCornerTriples_eq_filter_rankBox A B b hbA hbB] at hy
    have hybox := (Finset.mem_filter.mp hy).1
    refine ⟨reflectTriple A B y, ?_, ?_⟩
    · apply Finset.mem_filter.mpr
      refine ⟨reflectTriple_mem_box hybox, ?_⟩
      have hylower := (Finset.mem_filter.mp hy).2
      rcases y with ⟨⟨i, j⟩, side⟩
      have hij := by
        simpa [rankBox] using hybox
      have hi : i < A := hij.1
      have hj : j < B := hij.2
      have hAi : A - 1 - i + i + 1 = A := by omega
      have hBj : B - 1 - j + j + 1 = B := by omega
      cases side <;>
        simp [reflectTriple, rankLevel, tripleRankPoint] at hylower ⊢ <;> omega
    · exact reflectTriple_involutive_on_box hybox

end OeisA263135
