import Scratch.A263135ClippingGeometry

namespace OeisA263135

/-- Convert a ranked A-based dart to the concrete honeycomb coordinates. -/
def clippingRankDartVertex (pd : RankPoint × Direction) : Vertex × Direction :=
  (rankPointVertex pd.1, pd.2)

@[simp]
theorem clippingRankDartVertex_fst (pd : RankPoint × Direction) :
    (clippingRankDartVertex pd).1 = rankPointVertex pd.1 := rfl

@[simp]
theorem clippingRankDartVertex_snd (pd : RankPoint × Direction) :
    (clippingRankDartVertex pd).2 = pd.2 := rfl

/-- The ranked-dart conversion is injective. -/
theorem clippingRankDartVertex_injective : Function.Injective clippingRankDartVertex := by
  intro p q h
  apply Prod.ext
  · have hv := congrArg (fun z : Vertex × Direction => z.1) h
    apply rankPointVertex_injective
    simpa [clippingRankDartVertex] using hv
  · have hd := congrArg (fun z : Vertex × Direction => z.2) h
    simpa [clippingRankDartVertex] using hd

private theorem clipping_same_neighbor_mem_iff
    {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    {p : RankPoint} (hp : p ∈ aRankPatch a b c) :
    neighbor (rankPointVertex p) .same ∈ patch a b c ↔
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

private theorem clipping_horizontal_neighbor_mem_iff
    {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    {p : RankPoint} (hp : p ∈ aRankPatch a b c) :
    neighbor (rankPointVertex p) .horizontal ∈ patch a b c ↔ p.first ≠ 0 := by
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

private theorem clipping_diagonal_neighbor_mem_iff
    {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    {p : RankPoint} (hp : p ∈ aRankPatch a b c) :
    neighbor (rankPointVertex p) .diagonal ∈ patch a b c ↔ p.second ≠ 0 := by
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

/-- A ranked dart is a listed patch contact exactly when its concrete dart is
an A-based internal dart of the patch. -/
theorem clippingRankDart_mem_aInternal_iff
    {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    {pd : RankPoint × Direction} :
    pd ∈ patchContactDarts a b c ↔
      clippingRankDartVertex pd ∈ aInternalDarts (patch a b c) := by
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
        · exact (clipping_same_neighbor_mem_iff ha hb hc hpA).mpr hnot
        · simpa [clippingRankDartVertex, rankPointVertex] using
            (Finset.mem_filter.mp hpA).2
      · intro hint
        rcases Finset.mem_filter.mp hint with ⟨hint, hside⟩
        rcases Finset.mem_filter.mp hint with ⟨hprod, hn⟩
        have hpPatch := rankPointVertex_mem_patch_iff.mp
          (Finset.mem_product.mp hprod).1
        have hpA : p ∈ aRankPatch a b c := Finset.mem_filter.mpr
          ⟨hpPatch, by simpa [clippingRankDartVertex, rankPointVertex] using hside⟩
        have hp : p ∈ sameContactPoints a b c := Finset.mem_filter.mpr
          ⟨hpA, (clipping_same_neighbor_mem_iff ha hb hc hpA).mp hn⟩
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
          (clipping_horizontal_neighbor_mem_iff ha hb hc hpA).mpr hnot⟩, ?_⟩
        simpa [clippingRankDartVertex, rankPointVertex] using
          (Finset.mem_filter.mp hpA).2
      · intro hint
        rcases Finset.mem_filter.mp hint with ⟨hint, hside⟩
        rcases Finset.mem_filter.mp hint with ⟨hprod, hn⟩
        have hpPatch := rankPointVertex_mem_patch_iff.mp
          (Finset.mem_product.mp hprod).1
        have hpA : p ∈ aRankPatch a b c := Finset.mem_filter.mpr
          ⟨hpPatch, by simpa [clippingRankDartVertex, rankPointVertex] using hside⟩
        have hp : p ∈ horizontalContactPoints a b c := Finset.mem_filter.mpr
          ⟨hpA, (clipping_horizontal_neighbor_mem_iff ha hb hc hpA).mp hn⟩
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
          (clipping_diagonal_neighbor_mem_iff ha hb hc hpA).mpr hnot⟩, ?_⟩
        simpa [clippingRankDartVertex, rankPointVertex] using
          (Finset.mem_filter.mp hpA).2
      · intro hint
        rcases Finset.mem_filter.mp hint with ⟨hint, hside⟩
        rcases Finset.mem_filter.mp hint with ⟨hprod, hn⟩
        have hpPatch := rankPointVertex_mem_patch_iff.mp
          (Finset.mem_product.mp hprod).1
        have hpA : p ∈ aRankPatch a b c := Finset.mem_filter.mpr
          ⟨hpPatch, by simpa [clippingRankDartVertex, rankPointVertex] using hside⟩
        have hp : p ∈ diagonalContactPoints a b c := Finset.mem_filter.mpr
          ⟨hpA, (clipping_diagonal_neighbor_mem_iff ha hb hc hpA).mp hn⟩
        simpa [patchContactDarts] using hp

/-- The concrete neighbor of a listed ranked contact is its ranked B endpoint. -/
theorem neighbor_clippingRankDart_eq
    {a b c : ℕ} {pd : RankPoint × Direction}
    (hpd : pd ∈ patchContactDarts a b c) :
    neighbor (rankPointVertex pd.1) pd.2 = rankPointVertex (rankDartNeighbor pd) := by
  rcases pd with ⟨p, d⟩
  cases d with
  | same =>
      have hp : p ∈ sameContactPoints a b c := by
        simpa [patchContactDarts] using hpd
      exact neighbor_rankPointVertex_same
        (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2
  | horizontal =>
      have hp : p ∈ horizontalContactPoints a b c := by
        simpa [patchContactDarts] using hpd
      have hA := (Finset.mem_filter.mp hp).1
      exact neighbor_rankPointVertex_horizontal
        (Finset.mem_filter.mp hA).2
        (Nat.pos_of_ne_zero (Finset.mem_filter.mp hp).2)
  | diagonal =>
      have hp : p ∈ diagonalContactPoints a b c := by
        simpa [patchContactDarts] using hpd
      have hA := (Finset.mem_filter.mp hp).1
      exact neighbor_rankPointVertex_diagonal
        (Finset.mem_filter.mp hA).2
        (Nat.pos_of_ne_zero (Finset.mem_filter.mp hp).2)

end OeisA263135
