/-
Copyright 2026 The WOW-146 Authors.
Licensed under the Apache License, Version 2.0.
-/

import WOW146.GlobalBounds

open Classical
open SimpleGraph
open WrittenOnTheWallII.GraphConjecture146

namespace WOW146

set_option linter.unusedSectionVars false

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

lemma connected_graphSquare (G : SimpleGraph α) (hG : G.Connected) :
    (graphSquare G).Connected := by
  refine hG.mono ?_
  intro u v huv
  refine ⟨G.ne_of_adj huv, ?_⟩
  exact (G.dist_le (.cons huv .nil)).trans (by norm_num)

lemma dist_le_two_of_graphSquare_dist_le_one (G : SimpleGraph α) (hG : G.Connected)
    {u v : α} (h : (graphSquare G).dist u v ≤ 1) : G.dist u v ≤ 2 := by
  by_cases huv : u = v
  · subst v
    simp
  · have hsconn : (graphSquare G).Connected := connected_graphSquare G hG
    have hpos : 0 < (graphSquare G).dist u v := hsconn.pos_dist_of_ne huv
    have hdist : (graphSquare G).dist u v = 1 := by omega
    exact (dist_eq_one_iff_adj.mp hdist).2

lemma exists_square_center_original_dist_le_two (G : SimpleGraph α) [DecidableRel G.Adj]
    (hG : G.Connected) (hrho : graphSquareRadius G = 1) :
    ∃ c : α, ∀ v : α, G.dist c v ≤ 2 := by
  have hsconn : (graphSquare G).Connected := connected_graphSquare G hG
  obtain ⟨c, hc⟩ := (graphSquare G).exists_eccent_eq_radius
  have hrfin : (graphSquare G).radius ≠ ⊤ := radius_ne_top_iff.mpr hsconn
  have hefin : (graphSquare G).eccent c ≠ ⊤ := by
    rw [hc]
    exact hrfin
  refine ⟨c, fun v => ?_⟩
  apply dist_le_two_of_graphSquare_dist_le_one G hG
  change ((graphSquare G).edist c v).toNat ≤ 1
  calc
    ((graphSquare G).edist c v).toNat ≤ ((graphSquare G).eccent c).toNat :=
      ENat.toNat_le_toNat edist_le_eccent hefin
    _ = ((graphSquare G).radius).toNat := congrArg ENat.toNat hc
    _ = graphSquareRadius G := rfl
    _ = 1 := hrho

lemma diam_le_four_of_graphSquareRadius_eq_one (G : SimpleGraph α) [DecidableRel G.Adj]
    (hG : G.Connected) (hrho : graphSquareRadius G = 1) : G.diam ≤ 4 := by
  obtain ⟨c, hc⟩ := exists_square_center_original_dist_le_two G hG hrho
  obtain ⟨u, v, huv⟩ := G.exists_dist_eq_diam
  rw [← huv]
  calc
    G.dist u v ≤ G.dist u c + G.dist c v := hG.dist_triangle
    _ ≤ 2 + 2 := Nat.add_le_add (by simpa [dist_comm] using hc u) (hc v)
    _ = 4 := by norm_num

lemma exists_middle_of_dist_eq_two (G : SimpleGraph α) (hG : G.Connected)
    {u v : α} (huv : G.dist u v = 2) :
    ∃ w : α, G.Adj u w ∧ G.Adj w v := by
  obtain ⟨p, hp⟩ := hG.exists_walk_length_eq_dist u v
  have hlen : p.length = 2 := hp.trans huv
  let w := p.getVert 1
  refine ⟨w, ?_, ?_⟩
  · have h := p.adj_getVert_succ (show 0 < p.length by omega)
    simpa [w] using h
  · have h := p.adj_getVert_succ (show 1 < p.length by omega)
    have hlast : p.getVert 2 = v := by simpa [hlen] using p.getVert_length
    rw [hlast] at h
    simpa [w] using h

lemma exists_two_middle_of_dist_eq_three (G : SimpleGraph α) (hG : G.Connected)
    {u v : α} (huv : G.dist u v = 3) :
    ∃ b a : α, G.Adj u b ∧ G.Adj b a ∧ G.Adj a v := by
  obtain ⟨p, hp⟩ := hG.exists_walk_length_eq_dist u v
  have hlen : p.length = 3 := hp.trans huv
  let b := p.getVert 1
  let a := p.getVert 2
  refine ⟨b, a, ?_, ?_, ?_⟩
  · have h := p.adj_getVert_succ (show 0 < p.length by omega)
    simpa [b] using h
  · have h := p.adj_getVert_succ (show 1 < p.length by omega)
    simpa [b, a] using h
  · have h := p.adj_getVert_succ (show 2 < p.length by omega)
    have hlast : p.getVert 3 = v := by simpa [hlen] using p.getVert_length
    rw [hlast] at h
    simpa [a] using h

lemma dist_le_two_of_adj_adj (G : SimpleGraph α) {a b c : α}
    (hab : G.Adj a b) (hbc : G.Adj b c) : G.dist a c ≤ 2 := by
  simpa using G.dist_le (.cons hab (.cons hbc .nil))

lemma dist_le_three_of_adj_adj_adj (G : SimpleGraph α) {a b c d : α}
    (hab : G.Adj a b) (hbc : G.Adj b c) (hcd : G.Adj c d) : G.dist a d ≤ 3 := by
  simpa using G.dist_le (.cons hab (.cons hbc (.cons hcd .nil)))

lemma not_adj_of_two_le_dist (G : SimpleGraph α) {u v : α} (h : 2 ≤ G.dist u v) :
    ¬G.Adj u v := by
  intro huv
  have hdist : G.dist u v = 1 := dist_eq_one_iff_adj.mpr huv
  omega

end WOW146
