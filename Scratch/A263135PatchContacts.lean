import Scratch.A263135PatchStructure

namespace OeisA263135

/-- B-side ranked point reached from an A point in the same direction. -/
def sameRankNeighbor (p : RankPoint) : RankPoint := ⟨p.first, p.second, true⟩

/-- B-side ranked point reached horizontally, when `p.first > 0`. -/
def horizontalRankNeighbor (p : RankPoint) : RankPoint :=
  ⟨p.first - 1, p.second, true⟩

/-- B-side ranked point reached diagonally, when `p.second > 0`. -/
def diagonalRankNeighbor (p : RankPoint) : RankPoint :=
  ⟨p.first, p.second - 1, true⟩

@[simp]
theorem neighbor_rankPointVertex_same {p : RankPoint} (hside : p.side = false) :
    neighbor (rankPointVertex p) Direction.same = rankPointVertex (sameRankNeighbor p) := by
  rcases p with ⟨i, j, side⟩
  change side = false at hside
  subst side
  rfl

@[simp]
theorem neighbor_rankPointVertex_horizontal {p : RankPoint}
    (hside : p.side = false) (hi : 0 < p.first) :
    neighbor (rankPointVertex p) Direction.horizontal =
      rankPointVertex (horizontalRankNeighbor p) := by
  rcases p with ⟨i, j, side⟩
  change side = false at hside
  change 0 < i at hi
  subst side
  simp [rankPointVertex, horizontalRankNeighbor, neighbor]
  omega

@[simp]
theorem neighbor_rankPointVertex_diagonal {p : RankPoint}
    (hside : p.side = false) (hj : 0 < p.second) :
    neighbor (rankPointVertex p) Direction.diagonal =
      rankPointVertex (diagonalRankNeighbor p) := by
  rcases p with ⟨i, j, side⟩
  change side = false at hside
  change 0 < j at hj
  subst side
  simp [rankPointVertex, diagonalRankNeighbor, neighbor]
  omega

private theorem same_neighbor_mem_iff
    {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    {p : RankPoint} (hp : p ∈ aRankPatch a b c) :
    neighbor (rankPointVertex p) Direction.same ∈ patch a b c ↔
      rankLevel p ≠ a + b + c - 1 := by
  have hpatch := (Finset.mem_filter.mp hp).1
  have hside := (Finset.mem_filter.mp hp).2
  rw [neighbor_rankPointVertex_same hside, rankPointVertex_mem_patch_iff, mem_rankPatch]
  rw [mem_rankPatch] at hpatch
  rcases p with ⟨i, j, side⟩
  change side = false at hside
  subst side
  simp [sameRankNeighbor, rankLevel] at hpatch ⊢
  omega

private theorem horizontal_neighbor_mem_iff
    {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    {p : RankPoint} (hp : p ∈ aRankPatch a b c) :
    neighbor (rankPointVertex p) Direction.horizontal ∈ patch a b c ↔ p.first ≠ 0 := by
  have hpatch := (Finset.mem_filter.mp hp).1
  have hside := (Finset.mem_filter.mp hp).2
  constructor
  · intro hn hzero
    rcases Finset.mem_image.mp hn with ⟨q, hq, heq⟩
    have hi := congrArg (fun v : Vertex => v.i) heq
    rcases p with ⟨i, j, side⟩
    rcases q with ⟨k, l, side'⟩
    change side = false at hside
    change i = 0 at hzero
    simpa [rankPointVertex, neighbor, hside, hzero] using hi
  · intro hzero
    have hi : 0 < p.first := Nat.pos_of_ne_zero hzero
    rw [neighbor_rankPointVertex_horizontal hside hi, rankPointVertex_mem_patch_iff,
      mem_rankPatch]
    rw [mem_rankPatch] at hpatch
    rcases p with ⟨i, j, side⟩
    change side = false at hside
    change 0 < i at hi
    subst side
    simp [horizontalRankNeighbor, rankLevel] at hpatch ⊢
    omega

private theorem diagonal_neighbor_mem_iff
    {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    {p : RankPoint} (hp : p ∈ aRankPatch a b c) :
    neighbor (rankPointVertex p) Direction.diagonal ∈ patch a b c ↔ p.second ≠ 0 := by
  have hpatch := (Finset.mem_filter.mp hp).1
  have hside := (Finset.mem_filter.mp hp).2
  constructor
  · intro hn hzero
    rcases Finset.mem_image.mp hn with ⟨q, hq, heq⟩
    have hj := congrArg (fun v : Vertex => v.j) heq
    rcases p with ⟨i, j, side⟩
    rcases q with ⟨k, l, side'⟩
    change side = false at hside
    change j = 0 at hzero
    have hj' : (l : ℤ) - 1 = -2 := by
      simpa [rankPointVertex, neighbor, hside, hzero] using hj
    omega
  · intro hzero
    have hj : 0 < p.second := Nat.pos_of_ne_zero hzero
    rw [neighbor_rankPointVertex_diagonal hside hj, rankPointVertex_mem_patch_iff,
      mem_rankPatch]
    rw [mem_rankPatch] at hpatch
    rcases p with ⟨i, j, side⟩
    change side = false at hside
    change 0 < j at hj
    subst side
    simp [diagonalRankNeighbor, rankLevel] at hpatch ⊢
    omega

/-- A points contributing a same-direction internal dart. -/
def sameContactPoints (a b c : ℕ) : Finset RankPoint :=
  (aRankPatch a b c).filter fun p => rankLevel p ≠ a + b + c - 1

/-- A points contributing a horizontal internal dart. -/
def horizontalContactPoints (a b c : ℕ) : Finset RankPoint :=
  (aRankPatch a b c).filter fun p => p.first ≠ 0

/-- A points contributing a diagonal internal dart. -/
def diagonalContactPoints (a b c : ℕ) : Finset RankPoint :=
  (aRankPatch a b c).filter fun p => p.second ≠ 0

private theorem card_complementary_filter
    {α : Type*} [DecidableEq α] (S : Finset α) (P : α → Prop) [DecidablePred P] :
    (S.filter fun x => ¬ P x).card + (S.filter P).card = S.card := by
  have hu : (S.filter fun x => ¬ P x) ∪ S.filter P = S := by
    ext x
    by_cases h : P x <;> simp [h]
  have hd : Disjoint (S.filter fun x => ¬ P x) (S.filter P) := by
    rw [Finset.disjoint_left]
    intro x hxN hxP
    exact (Finset.mem_filter.mp hxN).2 (Finset.mem_filter.mp hxP).2
  simpa [Finset.card_union_of_disjoint hd] using congrArg Finset.card hu

private theorem card_sameContactPoints (a b c : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (sameContactPoints a b c).card = a * b + b * c + c * a - b := by
  have h := card_complementary_filter (aRankPatch a b c)
    (fun p => rankLevel p = a + b + c - 1)
  rw [← topARankPatch, card_topARankPatch a b c ha hb hc, card_aRankPatch] at h
  change (sameContactPoints a b c).card + b = a * b + b * c + c * a at h
  omega

private theorem card_horizontalContactPoints (a b c : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (horizontalContactPoints a b c).card = a * b + b * c + c * a - c := by
  have h := card_complementary_filter (aRankPatch a b c) (fun p => p.first = 0)
  rw [← firstZeroARankPatch, card_firstZeroARankPatch a b c ha hb hc,
    card_aRankPatch] at h
  change (horizontalContactPoints a b c).card + c = a * b + b * c + c * a at h
  omega

private theorem card_diagonalContactPoints (a b c : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (diagonalContactPoints a b c).card = a * b + b * c + c * a - a := by
  have h := card_complementary_filter (aRankPatch a b c) (fun p => p.second = 0)
  rw [← secondZeroARankPatch, card_secondZeroARankPatch a b c ha hb hc,
    card_aRankPatch] at h
  change (diagonalContactPoints a b c).card + a = a * b + b * c + c * a at h
  omega

/-- Ranked representatives of all A-based internal darts of the convex patch. -/
def patchContactDarts (a b c : ℕ) : Finset (RankPoint × Direction) :=
  (sameContactPoints a b c ×ˢ {Direction.same}) ∪
    (horizontalContactPoints a b c ×ˢ {Direction.horizontal}) ∪
      (diagonalContactPoints a b c ×ˢ {Direction.diagonal})

private theorem patchContactDarts_pairwise_disjoint (a b c : ℕ) :
    Disjoint (sameContactPoints a b c ×ˢ {Direction.same})
      (horizontalContactPoints a b c ×ˢ {Direction.horizontal}) ∧
    Disjoint ((sameContactPoints a b c ×ˢ {Direction.same}) ∪
      (horizontalContactPoints a b c ×ˢ {Direction.horizontal}))
      (diagonalContactPoints a b c ×ˢ {Direction.diagonal}) := by
  constructor
  · rw [Finset.disjoint_left]
    intro x hs hh
    have hsame := (Finset.mem_product.mp hs).2
    have hhoriz := (Finset.mem_product.mp hh).2
    simp only [Finset.mem_singleton] at hsame hhoriz
    have hbad : Direction.same = Direction.horizontal := hsame.symm.trans hhoriz
    cases hbad
  · rw [Finset.disjoint_left]
    intro x hsh hd
    rcases Finset.mem_union.mp hsh with hs | hh
    · have hsame := (Finset.mem_product.mp hs).2
      have hdiag := (Finset.mem_product.mp hd).2
      simp only [Finset.mem_singleton] at hsame hdiag
      have hbad : Direction.same = Direction.diagonal := hsame.symm.trans hdiag
      cases hbad
    · have hhoriz := (Finset.mem_product.mp hh).2
      have hdiag := (Finset.mem_product.mp hd).2
      simp only [Finset.mem_singleton] at hhoriz hdiag
      have hbad : Direction.horizontal = Direction.diagonal := hhoriz.symm.trans hdiag
      cases hbad

private theorem card_patchContactDarts (a b c : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (patchContactDarts a b c).card =
      3 * (a * b + b * c + c * a) - (a + b + c) := by
  rcases patchContactDarts_pairwise_disjoint a b c with ⟨h12, h123⟩
  rw [patchContactDarts, Finset.card_union_of_disjoint h123,
    Finset.card_union_of_disjoint h12]
  simp only [Finset.card_product, Finset.card_singleton, mul_one,
    card_sameContactPoints a b c ha hb hc,
    card_horizontalContactPoints a b c ha hb hc,
    card_diagonalContactPoints a b c ha hb hc]
  have haM : a ≤ a * b + b * c + c * a := by nlinarith
  have hbM : b ≤ a * b + b * c + c * a := by nlinarith
  have hcM : c ≤ a * b + b * c + c * a := by nlinarith
  omega

private def rankDartVertex (pd : RankPoint × Direction) : Vertex × Direction :=
  (rankPointVertex pd.1, pd.2)

private theorem rankDartVertex_injective : Function.Injective rankDartVertex := by
  intro p q h
  apply Prod.ext
  · have hv := congrArg (fun z : Vertex × Direction => z.1) h
    apply rankPointVertex_injective
    simpa [rankDartVertex] using hv
  · have hd := congrArg (fun z : Vertex × Direction => z.2) h
    simpa [rankDartVertex] using hd

private theorem rankDart_mem_aInternal_iff
    {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    {pd : RankPoint × Direction} :
    pd ∈ patchContactDarts a b c ↔
      rankDartVertex pd ∈ aInternalDarts (patch a b c) := by
  rcases pd with ⟨p, d⟩
  cases d with
  | same =>
      constructor
      · intro hpd
        have hp : p ∈ sameContactPoints a b c := by
          simpa [patchContactDarts] using hpd
        have hpA := (Finset.mem_filter.mp hp).1
        have hnot := (Finset.mem_filter.mp hp).2
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
          ⟨rankPointVertex_mem_patch_iff.mpr (Finset.mem_filter.mp hpA).1,
            Finset.mem_univ _⟩, ?_⟩, ?_⟩
        · exact (same_neighbor_mem_iff ha hb hc hpA).mpr hnot
        · simpa [rankDartVertex, rankPointVertex] using
            (Finset.mem_filter.mp hpA).2
      · intro hint
        rcases Finset.mem_filter.mp hint with ⟨hint, hside⟩
        rcases Finset.mem_filter.mp hint with ⟨hprod, hn⟩
        have hpPatch := rankPointVertex_mem_patch_iff.mp
          (Finset.mem_product.mp hprod).1
        have hpA : p ∈ aRankPatch a b c := Finset.mem_filter.mpr
          ⟨hpPatch, by simpa [rankDartVertex, rankPointVertex] using hside⟩
        have hp : p ∈ sameContactPoints a b c := Finset.mem_filter.mpr
          ⟨hpA, (same_neighbor_mem_iff ha hb hc hpA).mp hn⟩
        simpa [patchContactDarts] using hp
  | horizontal =>
      constructor
      · intro hpd
        have hp : p ∈ horizontalContactPoints a b c := by
          simpa [patchContactDarts] using hpd
        have hpA := (Finset.mem_filter.mp hp).1
        have hnot := (Finset.mem_filter.mp hp).2
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
          ⟨rankPointVertex_mem_patch_iff.mpr (Finset.mem_filter.mp hpA).1,
            Finset.mem_univ _⟩,
          (horizontal_neighbor_mem_iff ha hb hc hpA).mpr hnot⟩, ?_⟩
        simpa [rankDartVertex, rankPointVertex] using
          (Finset.mem_filter.mp hpA).2
      · intro hint
        rcases Finset.mem_filter.mp hint with ⟨hint, hside⟩
        rcases Finset.mem_filter.mp hint with ⟨hprod, hn⟩
        have hpPatch := rankPointVertex_mem_patch_iff.mp
          (Finset.mem_product.mp hprod).1
        have hpA : p ∈ aRankPatch a b c := Finset.mem_filter.mpr
          ⟨hpPatch, by simpa [rankDartVertex, rankPointVertex] using hside⟩
        have hp : p ∈ horizontalContactPoints a b c := Finset.mem_filter.mpr
          ⟨hpA, (horizontal_neighbor_mem_iff ha hb hc hpA).mp hn⟩
        simpa [patchContactDarts] using hp
  | diagonal =>
      constructor
      · intro hpd
        have hp : p ∈ diagonalContactPoints a b c := by
          simpa [patchContactDarts] using hpd
        have hpA := (Finset.mem_filter.mp hp).1
        have hnot := (Finset.mem_filter.mp hp).2
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
          ⟨rankPointVertex_mem_patch_iff.mpr (Finset.mem_filter.mp hpA).1,
            Finset.mem_univ _⟩,
          (diagonal_neighbor_mem_iff ha hb hc hpA).mpr hnot⟩, ?_⟩
        simpa [rankDartVertex, rankPointVertex] using
          (Finset.mem_filter.mp hpA).2
      · intro hint
        rcases Finset.mem_filter.mp hint with ⟨hint, hside⟩
        rcases Finset.mem_filter.mp hint with ⟨hprod, hn⟩
        have hpPatch := rankPointVertex_mem_patch_iff.mp
          (Finset.mem_product.mp hprod).1
        have hpA : p ∈ aRankPatch a b c := Finset.mem_filter.mpr
          ⟨hpPatch, by simpa [rankDartVertex, rankPointVertex] using hside⟩
        have hp : p ∈ diagonalContactPoints a b c := Finset.mem_filter.mpr
          ⟨hpA, (diagonal_neighbor_mem_iff ha hb hc hpA).mp hn⟩
        simpa [patchContactDarts] using hp

/-- Exact contact count of a convex patch. -/
theorem contacts_patch_formula (a b c : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    contacts (patch a b c) =
      3 * (a * b + b * c + c * a) - (a + b + c) := by
  rw [contacts_eq_card_aInternalDarts]
  rw [← card_patchContactDarts a b c ha hb hc]
  symm
  apply Finset.card_bij (fun pd hpd => rankDartVertex pd)
  · exact fun pd hpd => (rankDart_mem_aInternal_iff ha hb hc).mp hpd
  · intro p hp q hq h
    exact rankDartVertex_injective h
  · intro vd hvd
    rcases vd with ⟨v, d⟩
    rcases Finset.mem_filter.mp hvd with ⟨hint, hside⟩
    rcases Finset.mem_filter.mp hint with ⟨hprod, hn⟩
    rcases Finset.mem_image.mp (Finset.mem_product.mp hprod).1 with ⟨p, hp, rfl⟩
    refine ⟨(p, d), (rankDart_mem_aInternal_iff ha hb hc).mpr ?_, rfl⟩
    exact Finset.mem_filter.mpr ⟨hint, hside⟩

end OeisA263135
