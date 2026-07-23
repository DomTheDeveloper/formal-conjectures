import Scratch.A263135BoxChains

namespace OeisA263135

/-- Pair of the first two occupied-row ranks. -/
noncomputable def rectangleRankPair (S : Finset Vertex) (v : ↥S) :
    Fin (occupiedRows .first S).card × Fin (occupiedRows .second S).card :=
  (rowRank .first S v, rowRank .second S v)

/-- Ranked point corresponding to a honeycomb vertex. -/
noncomputable def vertexRankPoint (S : Finset Vertex) (v : ↥S) : RankPoint :=
  ⟨(rowRank .first S v).val, (rowRank .second S v).val, v.val.side⟩

/-- Rectangle-chain index of a honeycomb vertex. -/
noncomputable def vertexChainIndex (S : Finset Vertex) (v : ↥S) : ℕ :=
  rectangleChainIndex (rectangleRankPair S v)

/-- Product-chain choice of a honeycomb vertex. -/
noncomputable def vertexSubchain (S : Finset Vertex) (v : ↥S) : Bool :=
  boxSubchain (rectangleRankPair S v) v.val.side

/-- A vertex's rectangle-chain index lies in the first-row range. -/
theorem vertexChainIndex_lt_firstRows (S : Finset Vertex) (v : ↥S) :
    vertexChainIndex S v < (occupiedRows .first S).card := by
  unfold vertexChainIndex rectangleChainIndex rectangleRankPair
  exact lt_of_le_of_lt (Nat.min_le_left _ _) (rowRank .first S v).isLt

private theorem complement_complement {b j : ℕ} (hj : j < b) :
    b - 1 - (b - 1 - j) = j := by
  omega

private theorem rankPoint_mem_baseBoxChain (S : Finset Vertex) (v : ↥S)
    (hab : (occupiedRows .first S).card ≤ (occupiedRows .second S).card) :
    vertexRankPoint S v ∈
      baseBoxChain (occupiedRows .first S).card (occupiedRows .second S).card
        (vertexChainIndex S v) v.val.side := by
  let a := (occupiedRows .first S).card
  let b := (occupiedRows .second S).card
  let p := rectangleRankPair S v
  let t := vertexChainIndex S v
  change vertexRankPoint S v ∈ baseBoxChain a b t v.val.side
  rw [baseBoxChain]
  have hi : p.1.val < a := p.1.isLt
  have hj : p.2.val < b := p.2.isLt
  have ht : t = min p.1.val (b - 1 - p.2.val) := rfl
  by_cases hvertical : p.1.val ≤ b - 1 - p.2.val
  · apply Finset.mem_union_left
    apply Finset.mem_map.mpr
    refine ⟨p.2.val, ?_, ?_⟩
    · simp only [Finset.mem_range]
      rw [ht, Nat.min_eq_left hvertical]
      omega
    · apply RankPoint.ext
      · change t = (rowRank .first S v).val
        rw [ht, Nat.min_eq_left hvertical]
        rfl
      · rfl
      · rfl
  · apply Finset.mem_union_right
    apply Finset.mem_map.mpr
    let h := p.1.val - (t + 1)
    have htp : t < p.1.val := by
      rw [ht, Nat.min_eq_right (Nat.le_of_not_ge hvertical)]
      exact Nat.lt_of_not_ge hvertical
    refine ⟨h, ?_, ?_⟩
    · simp only [Finset.mem_range]
      dsimp [h]
      omega
    · apply RankPoint.ext
      · change t + 1 + h = (rowRank .first S v).val
        change t + 1 + h = p.1.val
        dsimp [h]
        omega
      · change b - 1 - t = p.2.val
        rw [ht, Nat.min_eq_right (Nat.le_of_not_ge hvertical)]
        exact complement_complement hj
      · rfl

private theorem vertexRankPoint_last_iff (S : Finset Vertex) (v : ↥S) :
    vertexRankPoint S v =
        lastRankPoint (occupiedRows .first S).card (occupiedRows .second S).card
          (vertexChainIndex S v) v.val.side ↔
      isRectangleChainLast (rectangleRankPair S v) := by
  constructor
  · intro h
    constructor
    · simpa [vertexRankPoint, lastRankPoint, rectangleRankPair] using
        congrArg RankPoint.first h
    · simpa [vertexRankPoint, lastRankPoint, vertexChainIndex, rectangleRankPair] using
        congrArg RankPoint.second h
  · rintro ⟨hi, hj⟩
    apply RankPoint.ext
    · simpa [vertexRankPoint, lastRankPoint, rectangleRankPair] using hi
    · simpa [vertexRankPoint, lastRankPoint, vertexChainIndex, rectangleRankPair] using hj
    · rfl

/-- Every ranked vertex belongs to its chosen long or short product chain. -/
theorem vertexRankPoint_mem_chosenChain (S : Finset Vertex) (v : ↥S)
    (hab : (occupiedRows .first S).card ≤ (occupiedRows .second S).card) :
    if vertexSubchain S v then
      vertexRankPoint S v ∈
        shortBoxChain (occupiedRows .first S).card (occupiedRows .second S).card
          (vertexChainIndex S v)
    else
      vertexRankPoint S v ∈
        longBoxChain (occupiedRows .first S).card (occupiedRows .second S).card
          (vertexChainIndex S v) := by
  have hbase := rankPoint_mem_baseBoxChain S v hab
  by_cases hside : v.val.side = true
  · have hbaseTrue : vertexRankPoint S v ∈
        baseBoxChain (occupiedRows .first S).card (occupiedRows .second S).card
          (vertexChainIndex S v) true := by
      simpa [hside] using hbase
    by_cases hlast : isRectangleChainLast (rectangleRankPair S v)
    · have hchoice : vertexSubchain S v = false := by
        simp [vertexSubchain, boxSubchain, hside, hlast]
      rw [hchoice]
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [longBoxChain]
      apply Finset.mem_union_right
      apply Finset.mem_singleton.mpr
      simpa [hside] using (vertexRankPoint_last_iff S v).2 hlast
    · have hchoice : vertexSubchain S v = true := by
        simp [vertexSubchain, boxSubchain, hside, hlast]
      rw [hchoice]
      simp only [↓reduceIte]
      rw [shortBoxChain]
      apply Finset.mem_erase.mpr
      refine ⟨?_, hbaseTrue⟩
      intro heq
      apply hlast
      apply (vertexRankPoint_last_iff S v).1
      simpa [hside] using heq
  · have hfalse : v.val.side = false := Bool.eq_false_of_not_eq_true hside
    have hchoice : vertexSubchain S v = false := by
      simp [vertexSubchain, boxSubchain, hfalse]
    have hbaseFalse : vertexRankPoint S v ∈
        baseBoxChain (occupiedRows .first S).card (occupiedRows .second S).card
          (vertexChainIndex S v) false := by
      simpa [hfalse] using hbase
    rw [hchoice]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [longBoxChain]
    exact Finset.mem_union_left _ hbaseFalse

private theorem vertex_eq_of_fields {v w : Vertex}
    (hi : v.i = w.i) (hj : v.j = w.j) (hs : v.side = w.side) : v = w := by
  rcases v with ⟨vi, vj, vs⟩
  rcases w with ⟨wi, wj, ws⟩
  simp_all

/-- The ranked-point map is injective. -/
theorem vertexRankPoint_injective (S : Finset Vertex) :
    Function.Injective (vertexRankPoint S) := by
  intro v w h
  have hfirst : rowRank .first S v = rowRank .first S w := by
    apply Fin.ext
    exact congrArg RankPoint.first h
  have hsecond : rowRank .second S v = rowRank .second S w := by
    apply Fin.ext
    exact congrArg RankPoint.second h
  have hside : v.val.side = w.val.side := congrArg RankPoint.side h
  have hi : v.val.i = w.val.i := by
    simpa [rowCoord] using (rowRank_eq_iff_rowCoord_eq .first S v w).mp hfirst
  have hj : v.val.j = w.val.j := by
    simpa [rowCoord] using (rowRank_eq_iff_rowCoord_eq .second S v w).mp hsecond
  apply Subtype.ext
  exact vertex_eq_of_fields hi hj hside

end OeisA263135
