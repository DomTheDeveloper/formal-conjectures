/-
Candidate solution for WOWII Graph Conjecture 65.

Mathematical status: complete proof.
Lean status: audit copy.
-/

import FormalConjectures.Util.ProblemImports

namespace WrittenOnTheWallII.GraphConjecture65

open Classical SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

/-- In a connected graph, every nontrivial vertex cut has a crossing edge. -/
private lemma exists_adj_crossing
    (G : SimpleGraph α) (hG : G.Connected) (S : Set α)
    (hS : S.Nonempty) (hSc : Sᶜ.Nonempty) :
    ∃ u, u ∈ S ∧ ∃ v, v ∉ S ∧ G.Adj u v := by
  rcases hS with ⟨u, hu⟩
  rcases hSc with ⟨v, hv⟩
  by_contra hn
  push_neg at hn
  let H : G.Subgraph := (⊤ : G.Subgraph).induce S
  have hvH : v ∈ H.verts :=
    (hG u v).mem_subgraphVerts (H := H) (by
      intro x hx y hxy
      have hxS : x ∈ S := by simpa [H] using hx
      have hyS : y ∈ S := by
        by_contra hyS
        exact hn x hxS y hyS hxy
      simpa [H, hxS, hyS] using hxy) (by
        simpa [H] using hu)
  exact hv (by simpa [H] using hvH)

/-- An outside vertex adjacent to `S` has distance to `S` at most one. -/
private lemma distToSet_le_one_of_adj
    (G : SimpleGraph α) (S : Set α) {u v : α}
    (hu : u ∈ S) (hvu : G.Adj v u) :
    distToSet G v S ≤ 1 := by
  have hS : S.toFinset.Nonempty := ⟨u, by simpa using hu⟩
  rw [distToSet, dif_pos hS]
  calc
    _ ≤ G.dist v u := Finset.min'_le _ _ (by
      apply Finset.mem_image.mpr
      exact ⟨u, by simpa using hu, rfl⟩)
    _ = 1 := (G.dist_eq_one_iff_adj).2 hvu

/-- For every set `S` in a connected finite graph, the repository's `distMin`
    is at most one. -/
private lemma distMin_le_one
    (G : SimpleGraph α) (hG : G.Connected) (S : Set α) :
    distMin G S ≤ 1 := by
  classical
  unfold distMin
  dsimp only
  split_ifs with hout
  · rcases hout with ⟨v, hv⟩
    have hvout : v ∉ S := by simpa using hv
    by_cases hS : S.Nonempty
    · have hSc : Sᶜ.Nonempty := ⟨v, by simpa using hvout⟩
      rcases exists_adj_crossing G hG S hS hSc with
        ⟨u, hu, w, hw, huw⟩
      calc
        _ ≤ distToSet G w S := Finset.min'_le _ _ (by
          apply Finset.mem_image.mpr
          exact ⟨w, by simp [hw], rfl⟩)
        _ ≤ 1 := distToSet_le_one_of_adj G S hu huw.symm
    · have hS0 : S = ∅ := Set.not_nonempty_iff_eq_empty.mp hS
      subst S
      calc
        _ ≤ distToSet G v ∅ := Finset.min'_le _ _ (by
          apply Finset.mem_image.mpr
          exact ⟨v, by simp, rfl⟩)
        _ = 0 := by simp [distToSet]
        _ ≤ 1 := by omega
  · omega

/-- Every graph on a nontrivial finite vertex type has a two-vertex induced
    forest, so its largest induced forest has size at least two. -/
private lemma two_le_largestInducedForestSize (G : SimpleGraph α) :
    2 ≤ G.largestInducedForestSize := by
  classical
  unfold largestInducedForestSize
  apply le_csSup
  · refine ⟨Fintype.card α, ?_⟩
    rintro n ⟨s, _hs, rfl⟩
    exact Finset.card_le_univ s
  · obtain ⟨u, v, huv⟩ := exists_pair_ne α
    refine ⟨{u, v}, ?_, by simp [huv]⟩
    intro x c hc
    have hle : c.support.tail.length ≤
        Fintype.card {z // z ∈ ({u, v} : Finset α)} :=
      hc.support_nodup.length_le_card
    have hlen : c.support.tail.length = c.length := by
      simp [Walk.length_support]
    have hcard : Fintype.card {z // z ∈ ({u, v} : Finset α)} = 2 := by
      calc
        Fintype.card {z // z ∈ ({u, v} : Finset α)} =
            ({u, v} : Finset α).card := by
          apply Fintype.card_of_subtype
          intro z
          rfl
        _ = 2 := by simp [huv]
    have hthree : 3 ≤ c.length := hc.three_le_length
    omega

/-- WOWII Conjecture 65. -/
@[category research solved, AMS 5]
theorem conjecture65 (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) :
    let A : Set α := {v | G.degree v = G.minDegree}
    let M : Set α := {v | G.degree v = G.maxDegree}
    (distMin G A : ℝ) + ⌈(distMin G M : ℝ) / 3⌉ ≤
      (G.largestInducedForestSize : ℝ) := by
  let A : Set α := {v | G.degree v = G.minDegree}
  let M : Set α := {v | G.degree v = G.maxDegree}
  change (distMin G A : ℝ) + ⌈(distMin G M : ℝ) / 3⌉ ≤
    (G.largestInducedForestSize : ℝ)

  have hA : distMin G A ≤ 1 := distMin_le_one G h A
  have hM : distMin G M ≤ 1 := distMin_le_one G h M
  have hf : 2 ≤ G.largestInducedForestSize :=
    two_le_largestInducedForestSize G

  have hAcases : distMin G A = 0 ∨ distMin G A = 1 := by omega
  have hMcases : distMin G M = 0 ∨ distMin G M = 1 := by omega
  rcases hAcases with hA0 | hA1
  · rcases hMcases with hM0 | hM1
    · norm_num [hA0, hM0]
    · norm_num [hA0, hM1]
      omega
  · rcases hMcases with hM0 | hM1
    · norm_num [hA1, hM0]
      omega
    · norm_num [hA1, hM1]
      exact hf

#print axioms conjecture65

end WrittenOnTheWallII.GraphConjecture65
