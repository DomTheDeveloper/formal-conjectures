import Scratch.A263135ChainMembership

namespace OeisA263135

private theorem baseBoxChain_side {a b t : ℕ} {side : Bool} {p : RankPoint}
    (hp : p ∈ baseBoxChain a b t side) : p.side = side := by
  rcases Finset.mem_union.mp hp with hp | hp
  · rcases Finset.mem_map.mp hp with ⟨j, hj, rfl⟩
    rfl
  · rcases Finset.mem_map.mp hp with ⟨h, hh, rfl⟩
    rfl

/-- Any two points on one base rectangle chain are comparable coordinatewise. -/
theorem baseBoxChain_comparable {a b t : ℕ} {side : Bool} {p q : RankPoint}
    (hp : p ∈ baseBoxChain a b t side)
    (hq : q ∈ baseBoxChain a b t side) :
    (p.first ≤ q.first ∧ p.second ≤ q.second) ∨
      (q.first ≤ p.first ∧ q.second ≤ p.second) := by
  rcases Finset.mem_union.mp hp with hp | hp <;>
    rcases Finset.mem_union.mp hq with hq | hq
  · rcases Finset.mem_map.mp hp with ⟨j, hj, rfl⟩
    rcases Finset.mem_map.mp hq with ⟨k, hk, rfl⟩
    rcases le_total j k with h | h
    · exact Or.inl ⟨le_rfl, h⟩
    · exact Or.inr ⟨le_rfl, h⟩
  · rcases Finset.mem_map.mp hp with ⟨j, hj, rfl⟩
    rcases Finset.mem_map.mp hq with ⟨h, hh, rfl⟩
    simp only [Finset.mem_range] at hj hh
    left
    constructor
    · change t ≤ t + 1 + h
      omega
    · change j ≤ b - 1 - t
      omega
  · rcases Finset.mem_map.mp hp with ⟨h, hh, rfl⟩
    rcases Finset.mem_map.mp hq with ⟨j, hj, rfl⟩
    simp only [Finset.mem_range] at hh hj
    right
    constructor
    · change t ≤ t + 1 + h
      omega
    · change j ≤ b - 1 - t
      omega
  · rcases Finset.mem_map.mp hp with ⟨h, hh, rfl⟩
    rcases Finset.mem_map.mp hq with ⟨k, hk, rfl⟩
    rcases le_total h k with hle | hle
    · left
      constructor
      · change t + 1 + h ≤ t + 1 + k
        omega
      · rfl
    · right
      constructor
      · change t + 1 + k ≤ t + 1 + h
        omega
      · rfl

private theorem baseBoxChain_le_last {a b t : ℕ} {side : Bool} {p : RankPoint}
    (ht : t < a) (hab : a ≤ b)
    (hp : p ∈ baseBoxChain a b t side) :
    p.first ≤ (lastRankPoint a b t side).first ∧
      p.second ≤ (lastRankPoint a b t side).second := by
  rcases Finset.mem_union.mp hp with hp | hp
  · rcases Finset.mem_map.mp hp with ⟨j, hj, rfl⟩
    simp only [Finset.mem_range] at hj
    constructor
    · change t ≤ a - 1
      omega
    · change j ≤ b - 1 - t
      omega
  · rcases Finset.mem_map.mp hp with ⟨h, hh, rfl⟩
    simp only [Finset.mem_range] at hh
    constructor
    · change t + 1 + h ≤ a - 1
      omega
    · rfl

private theorem longBoxChain_true_eq_last {a b t : ℕ} {p : RankPoint}
    (hp : p ∈ longBoxChain a b t) (hside : p.side = true) :
    p = lastRankPoint a b t true := by
  rcases Finset.mem_union.mp hp with hp | hp
  · have := baseBoxChain_side hp
    simp [hside] at this
  · simpa using Finset.mem_singleton.mp hp

private theorem shortBoxChain_side_true {a b t : ℕ} {p : RankPoint}
    (hp : p ∈ shortBoxChain a b t) : p.side = true := by
  exact baseBoxChain_side (Finset.mem_of_mem_erase hp)

private theorem vertex_eq_of_fields {v w : Vertex}
    (hi : v.i = w.i) (hj : v.j = w.j) (hs : v.side = w.side) : v = w := by
  rcases v with ⟨vi, vj, vs⟩
  rcases w with ⟨wi, wj, ws⟩
  simp_all

private theorem vertex_eq_of_rankPoint_le_same_side
    (S : Finset Vertex) (v w : ↥S)
    (hside : v.val.side = w.val.side)
    (hdiag : rowCoord .diagonal v = rowCoord .diagonal w)
    (hfirst : (vertexRankPoint S v).first ≤ (vertexRankPoint S w).first)
    (hsecond : (vertexRankPoint S v).second ≤ (vertexRankPoint S w).second) :
    v = w := by
  have hfirst' : rowRank .first S v ≤ rowRank .first S w := by
    simpa [vertexRankPoint] using hfirst
  have hsecond' : rowRank .second S v ≤ rowRank .second S w := by
    simpa [vertexRankPoint] using hsecond
  have hi := rowCoord_le_of_rowRank_le .first S v w hfirst'
  have hj := rowCoord_le_of_rowRank_le .second S v w hsecond'
  have hieq : rowCoord .first v = rowCoord .first w := by
    rcases v with ⟨⟨iv, jv, sv⟩, hv⟩
    rcases w with ⟨⟨iw, jw, sw⟩, hw⟩
    cases sv <;> cases sw <;> simp [rowCoord] at hi hj hdiag hside ⊢ <;> omega
  have hjeq : rowCoord .second v = rowCoord .second w := by
    rcases v with ⟨⟨iv, jv, sv⟩, hv⟩
    rcases w with ⟨⟨iw, jw, sw⟩, hw⟩
    cases sv <;> cases sw <;> simp [rowCoord] at hi hj hdiag hside ⊢ <;> omega
  apply Subtype.ext
  exact vertex_eq_of_fields
    (by simpa [rowCoord] using hieq)
    (by simpa [rowCoord] using hjeq)
    hside

private theorem vertex_eq_of_rankPoint_comparable_same_side
    (S : Finset Vertex) (v w : ↥S)
    (hside : v.val.side = w.val.side)
    (hdiag : rowCoord .diagonal v = rowCoord .diagonal w)
    (hcomp :
      ((vertexRankPoint S v).first ≤ (vertexRankPoint S w).first ∧
        (vertexRankPoint S v).second ≤ (vertexRankPoint S w).second) ∨
      ((vertexRankPoint S w).first ≤ (vertexRankPoint S v).first ∧
        (vertexRankPoint S w).second ≤ (vertexRankPoint S v).second)) :
    v = w := by
  rcases hcomp with h | h
  · exact vertex_eq_of_rankPoint_le_same_side S v w hside hdiag h.1 h.2
  · exact (vertex_eq_of_rankPoint_le_same_side S w v hside.symm hdiag.symm h.1 h.2).symm

/-- Third-direction row labels are injective on each long product chain. -/
theorem diagonal_injective_on_longChain
    (S : Finset Vertex) (v w : ↥S)
    (hab : (occupiedRows .first S).card ≤ (occupiedRows .second S).card)
    (ht : vertexChainIndex S v = vertexChainIndex S w)
    (hv : vertexRankPoint S v ∈
      longBoxChain (occupiedRows .first S).card (occupiedRows .second S).card
        (vertexChainIndex S v))
    (hw : vertexRankPoint S w ∈
      longBoxChain (occupiedRows .first S).card (occupiedRows .second S).card
        (vertexChainIndex S w))
    (hdiag : rowCoord .diagonal v = rowCoord .diagonal w) :
    v = w := by
  by_cases hsv : v.val.side = true <;> by_cases hsw : w.val.side = true
  · have hvlast := longBoxChain_true_eq_last hv hsv
    have hwlast := longBoxChain_true_eq_last (ht ▸ hw) hsw
    apply vertexRankPoint_injective S
    rw [hvlast, hwlast]
  · have hvlast := longBoxChain_true_eq_last hv hsv
    have hwbase : vertexRankPoint S w ∈
        baseBoxChain (occupiedRows .first S).card (occupiedRows .second S).card
          (vertexChainIndex S v) false := by
      rcases Finset.mem_union.mp (ht ▸ hw) with h | h
      · exact h
      · have hlast := Finset.mem_singleton.mp h
        have htrue : w.val.side = true := by
          simpa [vertexRankPoint, lastRankPoint] using congrArg RankPoint.side hlast
        exact (hsw htrue).elim
    have hle := baseBoxChain_le_last
      (vertexChainIndex_lt_firstRows S v) hab hwbase
    have hfirst : (vertexRankPoint S w).first ≤ (vertexRankPoint S v).first := by
      rw [congrArg RankPoint.first hvlast]
      exact hle.1
    have hsecond : (vertexRankPoint S w).second ≤ (vertexRankPoint S v).second := by
      rw [congrArg RankPoint.second hvlast]
      exact hle.2
    have hi := rowCoord_le_of_rowRank_le .first S w v
      (by simpa [vertexRankPoint] using hfirst)
    have hj := rowCoord_le_of_rowRank_le .second S w v
      (by simpa [vertexRankPoint] using hsecond)
    have hswf : w.val.side = false := Bool.eq_false_of_not_eq_true hsw
    have hdiag' : v.val.i + v.val.j + 1 = w.val.i + w.val.j := by
      simpa [rowCoord, hsv, hswf] using hdiag
    have hi' : w.val.i ≤ v.val.i := by simpa [rowCoord] using hi
    have hj' : w.val.j ≤ v.val.j := by simpa [rowCoord] using hj
    omega
  · have hwlast := longBoxChain_true_eq_last (ht ▸ hw) hsw
    have hvbase : vertexRankPoint S v ∈
        baseBoxChain (occupiedRows .first S).card (occupiedRows .second S).card
          (vertexChainIndex S v) false := by
      rcases Finset.mem_union.mp hv with h | h
      · exact h
      · have hlast := Finset.mem_singleton.mp h
        have htrue : v.val.side = true := by
          simpa [vertexRankPoint, lastRankPoint] using congrArg RankPoint.side hlast
        exact (hsv htrue).elim
    have hle := baseBoxChain_le_last
      (vertexChainIndex_lt_firstRows S v) hab hvbase
    have hfirst : (vertexRankPoint S v).first ≤ (vertexRankPoint S w).first := by
      rw [congrArg RankPoint.first hwlast]
      exact hle.1
    have hsecond : (vertexRankPoint S v).second ≤ (vertexRankPoint S w).second := by
      rw [congrArg RankPoint.second hwlast]
      exact hle.2
    have hi := rowCoord_le_of_rowRank_le .first S v w
      (by simpa [vertexRankPoint] using hfirst)
    have hj := rowCoord_le_of_rowRank_le .second S v w
      (by simpa [vertexRankPoint] using hsecond)
    have hsvf : v.val.side = false := Bool.eq_false_of_not_eq_true hsv
    have hdiag' : v.val.i + v.val.j = w.val.i + w.val.j + 1 := by
      simpa [rowCoord, hsvf, hsw] using hdiag
    have hi' : v.val.i ≤ w.val.i := by simpa [rowCoord] using hi
    have hj' : v.val.j ≤ w.val.j := by simpa [rowCoord] using hj
    omega
  · have hvbase : vertexRankPoint S v ∈
        baseBoxChain (occupiedRows .first S).card (occupiedRows .second S).card
          (vertexChainIndex S v) false := by
      rcases Finset.mem_union.mp hv with h | h
      · exact h
      · have hlast := Finset.mem_singleton.mp h
        have htrue : v.val.side = true := by
          simpa [vertexRankPoint, lastRankPoint] using congrArg RankPoint.side hlast
        exact (hsv htrue).elim
    have hwbase : vertexRankPoint S w ∈
        baseBoxChain (occupiedRows .first S).card (occupiedRows .second S).card
          (vertexChainIndex S v) false := by
      rcases Finset.mem_union.mp (ht ▸ hw) with h | h
      · exact h
      · have hlast := Finset.mem_singleton.mp h
        have htrue : w.val.side = true := by
          simpa [vertexRankPoint, lastRankPoint] using congrArg RankPoint.side hlast
        exact (hsw htrue).elim
    have hcomp := baseBoxChain_comparable hvbase hwbase
    exact vertex_eq_of_rankPoint_comparable_same_side S v w
      ((Bool.eq_false_of_not_eq_true hsv).trans
        (Bool.eq_false_of_not_eq_true hsw).symm) hdiag hcomp

/-- Third-direction row labels are injective on each short product chain. -/
theorem diagonal_injective_on_shortChain
    (S : Finset Vertex) (v w : ↥S)
    (ht : vertexChainIndex S v = vertexChainIndex S w)
    (hv : vertexRankPoint S v ∈
      shortBoxChain (occupiedRows .first S).card (occupiedRows .second S).card
        (vertexChainIndex S v))
    (hw : vertexRankPoint S w ∈
      shortBoxChain (occupiedRows .first S).card (occupiedRows .second S).card
        (vertexChainIndex S w))
    (hdiag : rowCoord .diagonal v = rowCoord .diagonal w) :
    v = w := by
  have hcomp := baseBoxChain_comparable
    (Finset.mem_of_mem_erase hv)
    (Finset.mem_of_mem_erase (ht ▸ hw))
  exact vertex_eq_of_rankPoint_comparable_same_side S v w
    ((shortBoxChain_side_true hv).trans (shortBoxChain_side_true (ht ▸ hw)).symm)
    hdiag hcomp

end OeisA263135
