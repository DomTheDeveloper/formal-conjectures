module

public import Graffiti318
public import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.VertexDistance
public import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.WellTotallyDominated

/-!
# Written on the Wall II - Conjecture 318

This file expresses the certificate in `Graffiti318` using the graph predicates from
Formal Conjectures. [Ermelinda DeLaViña, *Written on the Wall II*, Conjecture 318](https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/index.html).
-/

@[expose] public section

namespace WrittenOnTheWallII.GraphConjecture318

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Every minimal total dominating set in a graph satisfying Conjecture 318 has size two. -/
theorem minimalTotal_card_eq_two [Nontrivial V] (hG : G.Connected)
    (h : Gᶜ.edgeFinset.card ≤ Finset.univ.sup G.distEven)
    {D : Finset V} (hD : G.IsMinimalTotalDominatingSet D) : D.card = 2 := by
  have hmin : Graffiti318.MinimalTotal G D := by
    refine ⟨hD.1, ?_⟩
    intro E hED hE
    exact hED.eq_of_not_ssubset fun hlt ↦ hD.2 E hlt hE
  have hEdges : Graffiti318.missingCount G = Gᶜ.edgeFinset.card := by
    unfold Graffiti318.missingCount
    apply congrArg Finset.card
    ext e
    simp only [SimpleGraph.mem_edgeFinset]
  have hEven : Graffiti318.maxEvenCount G = Finset.univ.sup G.distEven := by rfl
  have hCount := hEdges.trans_le (h.trans_eq hEven.symm)
  exact (Graffiti318.writtenOnTheWallII_318 G hG Fintype.one_lt_card hCount).2.2 D hmin

/-- If the number of missing edges is at most the maximum even-distance vertex count,
a finite connected simple graph on at least two vertices is well totally dominated. -/
theorem conjecture318 [Nontrivial V] (hG : G.Connected)
    (h : Gᶜ.edgeFinset.card ≤ Finset.univ.sup G.distEven) : G.IsWellTotallyDominated := by
  intro S T hS hT
  rw [minimalTotal_card_eq_two G hG h hS, minimalTotal_card_eq_two G hG h hT]

end WrittenOnTheWallII.GraphConjecture318
