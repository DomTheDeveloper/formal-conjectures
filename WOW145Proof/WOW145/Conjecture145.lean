import WOW146.GraphConjecture146Proof
import FormalConjectures.WrittenOnTheWallII.GraphConjecture145

/-!
# Written on the Wall II — Conjecture 145

This file proves the exact current Formal Conjectures statement. The proof splits on the
minimum local independence number of the complement. The exceptional value one forces a
radius-two center and reduces to the kernel-checked proof of WOWII Conjecture 146.
-/

open Classical
open SimpleGraph
open WrittenOnTheWallII.GraphConjecture145
open WrittenOnTheWallII.GraphConjecture146

namespace WOW145

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

omit [DecidableEq α] in
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
    intro v _hv
    have hle : localIndependenceMin H ≤ indepNeighborsCard H v := by
      unfold localIndependenceMin
      apply Finset.inf'_le
      exact Finset.mem_univ v
    rw [hmin] at hle
    have hne := hnone v
    omega
  rw [hmin] at htwo
  omega

private lemma dist_le_two_of_compl_local_independence_one
    (G : SimpleGraph α) [DecidableRel G.Adj]
    (hG : G.Connected) {v : α}
    (hv : indepNeighborsCard Gᶜ v = 1) (w : α) :
    G.dist v w ≤ 2 := by
  by_contra hle
  have hdist : 2 < G.dist v w := by omega
  obtain ⟨p, _hpPath, hpLen⟩ := hG.exists_path_of_dist v w
  have htwoLen : 2 ≤ p.length := by
    rw [hpLen]
    omega
  have hthreeLen : 3 ≤ p.length := by
    rw [hpLen]
    omega
  let b : α := p.getVert 2
  let c : α := p.getVert 3
  have hdistb : G.dist v b = 2 := by
    have hsub := length_eq_dist_of_subwalk hpLen (Walk.isSubwalk_take p 2)
    calc
      G.dist v b = (p.take 2).length := by simpa [b] using hsub.symm
      _ = 2 := by simp [Walk.take_length, Nat.min_eq_left htwoLen]
  have hdistc : G.dist v c = 3 := by
    have hsub := length_eq_dist_of_subwalk hpLen (Walk.isSubwalk_take p 3)
    calc
      G.dist v c = (p.take 3).length := by simpa [c] using hsub.symm
      _ = 3 := by simp [Walk.take_length, Nat.min_eq_left hthreeLen]
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
    simpa using p.adj_getVert_succ (i := 2) (by omega)
  have hvbne : v ≠ b := by
    intro hEq
    have hzero : G.dist v b = 0 := by simp [hEq]
    omega
  have hvcne : v ≠ c := by
    intro hEq
    have hzero : G.dist v c = 0 := by simp [hEq]
    omega
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
    simp [SimpleGraph.compl_adj] at hcomp
    exact hcomp.2 hbc
  have hind :
      ((Gᶜ).induce ((Gᶜ).neighborSet v)).IsIndepSet
        ({b', c'} : Set ↥((Gᶜ).neighborSet v)) := by
    rw [← SimpleGraph.isClique_compl, SimpleGraph.isClique_pair]
    intro hne
    simpa [SimpleGraph.compl_adj] using And.intro hne hnotadj
  have hindFin :
      ((Gᶜ).induce ((Gᶜ).neighborSet v)).IsIndepSet
        (↑({b', c'} : Finset ↥((Gᶜ).neighborSet v)) : Set ↥((Gᶜ).neighborSet v)) := by
    simpa using hind
  have hcard :
      ({b', c'} : Finset ↥((Gᶜ).neighborSet v)).card ≤
        ((Gᶜ).induce ((Gᶜ).neighborSet v)).indepNum :=
    hindFin.card_le_indepNum
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
  have hdist : ∀ w : α, SimpleGraph.dist G v w ≤ 2 :=
    dist_le_two_of_compl_local_independence_one G hG hv
  obtain ⟨w, hw⟩ := G.exists_edist_eq_eccent_of_finite v
  have hdist_eq : SimpleGraph.dist G v w = (G.eccent v).toNat := by
    unfold SimpleGraph.dist
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
