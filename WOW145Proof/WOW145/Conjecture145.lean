import WOW146.GraphConjecture146Proof
import FormalConjectures.WrittenOnTheWallII.GraphConjecture145

open Classical
open SimpleGraph
open WrittenOnTheWallII.GraphConjecture145

namespace WOW145

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

private lemma eccent_ne_top_of_connected {G : SimpleGraph α}
    (hG : G.Connected) (u : α) : G.eccent u ≠ ⊤ := by
  have hed : G.ediam ≠ ⊤ := connected_iff_ediam_ne_top.mp hG
  intro hu
  apply hed
  exact top_unique (hu ▸ (eccent_le_ediam (G := G) (u := u)))

private lemma exists_local_independence_one (H : SimpleGraph α)
    [DecidableRel H.Adj]
    (hmin : localIndependenceMin H = 1) :
    ∃ v, indepNeighborsCard H v = 1 := by
  by_contra hnone
  push_neg at hnone
  have htwo : 2 ≤ localIndependenceMin H := by
    unfold localIndependenceMin
    rw [Finset.le_inf'_iff]
    intro v hv
    have hle : localIndependenceMin H ≤ indepNeighborsCard H v := by
      unfold localIndependenceMin
      apply Finset.inf'_le
      exact Finset.mem_univ v
    have hpos : 0 < indepNeighborsCard H v := by omega
    omega
  omega

private lemma dist_le_two_of_compl_local_independence_one
    (G : SimpleGraph α) [DecidableRel G.Adj]
    (hG : G.Connected) {v : α}
    (hv : indepNeighborsCard Gᶜ v = 1) (w : α) :
    G.dist v w ≤ 2 := by
  by_contra hle
  have hdist : 2 < G.dist v w := by omega
  obtain ⟨p, _hpPath, hpLen⟩ := hG.exists_path_of_dist v w
  let b : α := p.getVert 2
  let c : α := p.getVert 3
  have hdistb : G.dist v b = 2 := by
    have hsub := length_eq_dist_of_subwalk hpLen (Walk.isSubwalk_take p 2)
    dsimp [b]
    rw [← hsub]
    simp [Walk.take_length, hpLen, Nat.min_eq_left (by omega)]
  have hdistc : G.dist v c = 3 := by
    have hsub := length_eq_dist_of_subwalk hpLen (Walk.isSubwalk_take p 3)
    dsimp [c]
    rw [← hsub]
    simp [Walk.take_length, hpLen, Nat.min_eq_left (by omega)]
  have hvb : ¬G.Adj v b := by
    intro hadj
    have hone := G.dist_eq_one_iff_adj.mpr hadj
    omega
  have hvc : ¬G.Adj v c := by
    intro hadj
    have hone := G.dist_eq_one_iff_adj.mpr hadj
    omega
  have hbc : G.Adj b c := by
    dsimp [b, c]
    simpa using p.adj_getVert_succ (i := 2) (by rw [hpLen]; omega)
  have hvbne : v ≠ b := by
    intro hEq
    subst b
    simpa using hdistb
  have hvcne : v ≠ c := by
    intro hEq
    subst c
    simpa using hdistc
  have hbmem : b ∈ (Gᶜ).neighborSet v := by
    simpa [SimpleGraph.compl_adj] using And.intro hvbne hvb
  have hcmem : c ∈ (Gᶜ).neighborSet v := by
    simpa [SimpleGraph.compl_adj] using And.intro hvcne hvc
  let b' : ↥((Gᶜ).neighborSet v) := ⟨b, hbmem⟩
  let c' : ↥((Gᶜ).neighborSet v) := ⟨c, hcmem⟩
  have hb'c' : b' ≠ c' := by
    intro hEq
    apply hbc.ne
    exact congrArg Subtype.val hEq
  have hnotadj :
      ¬((Gᶜ).induce ((Gᶜ).neighborSet v)).Adj b' c' := by
    intro hadj
    have hcomp : (Gᶜ).Adj b c := by simpa [b', c'] using hadj
    simpa [SimpleGraph.compl_adj, hbc.ne, hbc] using hcomp
  have hind :
      ((Gᶜ).induce ((Gᶜ).neighborSet v)).IsIndepSet
        ({b', c'} : Set ↥((Gᶜ).neighborSet v)) := by
    rw [← SimpleGraph.isClique_compl, SimpleGraph.isClique_pair]
    intro hne
    simpa [SimpleGraph.compl_adj] using And.intro hne hnotadj
  have hcard := hind.card_le_indepNum (t := ({b', c'} : Finset ↥((Gᶜ).neighborSet v)))
  have htwo : 2 ≤ indepNeighborsCard Gᶜ v := by
    unfold indepNeighborsCard
    simpa [hb'c'] using hcard
  omega

private lemma radius_toNat_le_two_of_local_min_one
    (G : SimpleGraph α) [DecidableRel G.Adj]
    (hG : G.Connected)
    (hmin : localIndependenceMin Gᶜ = 1) :
    G.radius.toNat ≤ 2 := by
  obtain ⟨v, hv⟩ := exists_local_independence_one Gᶜ hmin
  have hdist : ∀ w, G.dist v w ≤ 2 :=
    dist_le_two_of_compl_local_independence_one G hG hv
  obtain ⟨w, hw⟩ := G.exists_edist_eq_eccent_of_finite v
  have hdist_eq : G.dist v w = (G.eccent v).toNat := by
    unfold dist
    rw [hw]
  have hecc : (G.eccent v).toNat ≤ 2 := by
    rw [← hdist_eq]
    exact hdist w
  have hrle : G.radius.toNat ≤ (G.eccent v).toNat :=
    ENat.toNat_le_toNat
      (radius_le_eccent (G := G) (u := v))
      (eccent_ne_top_of_connected hG v)
  omega

/-- Written on the Wall II, Conjecture 145, with the exact upstream signature. -/
theorem conjecture145 (G : SimpleGraph α) [DecidableRel G.Adj]
    (hG : G.Connected)
    (hlMin : 0 < localIndependenceMin Gᶜ) :
    2 * eccSet G (maxEccentricityVertices G : Set α) ≤
      largestInducedTreeSize G * localIndependenceMin Gᶜ := by
  have hperTree :
      eccSet G (maxEccentricityVertices G : Set α) ≤
        largestInducedTreeSize G := by
    have hper := G.eccSet_periphery_add_one_le_diam hG
    have htree := G.diam_succ_le_largestInducedTreeSize hG
    omega
  by_cases htwo : 2 ≤ localIndependenceMin Gᶜ
  · calc
      2 * eccSet G (maxEccentricityVertices G : Set α) ≤
          2 * largestInducedTreeSize G := Nat.mul_le_mul_left 2 hperTree
      _ = largestInducedTreeSize G * 2 := Nat.mul_comm _ _
      _ ≤ largestInducedTreeSize G * localIndependenceMin Gᶜ :=
        Nat.mul_le_mul_left _ htwo
  · have hone : localIndependenceMin Gᶜ = 1 := by omega
    have hrle : G.radius.toNat ≤ 2 :=
      radius_toNat_le_two_of_local_min_one G hG hone
    have hrho : graphSquareRadius G = 1 := by
      rw [SimpleGraph.graphSquareRadius_eq hG]
      omega
    have h146 := WOW146.conjecture146 G hG (by omega : 0 < graphSquareRadius G)
    simpa [hrho, hone] using h146

#print axioms WOW145.conjecture145

end WOW145
