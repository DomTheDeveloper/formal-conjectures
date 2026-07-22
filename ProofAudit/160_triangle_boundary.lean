/-
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0.
-/

import ProofAudit.«160_triangle_two»

namespace WrittenOnTheWallII.GraphConjecture160Audit

open Classical SimpleGraph Finset
open WrittenOnTheWallII.GraphConjecture160Petals

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

lemma numTrianglesAtVertex_le_triangleMax160
    (G : SimpleGraph α) [DecidableRel G.Adj] (v : α) :
    numTrianglesAtVertex G v ≤ triangleMax160 G := by
  unfold triangleMax160 maxTrianglesAtVertex
  exact Finset.le_max' (Finset.univ.image (numTrianglesAtVertex G)) _
    (Finset.mem_image.mpr ⟨v, Finset.mem_univ v, rfl⟩)

/-- A triangle that omits some vertex in a connected graph has a triangle
vertex of degree at least three: follow a path from the triangle to the outside
and take its first boundary dart. -/
lemma exists_triangle_vertex_degree_ge_three
    (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected)
    {t : Finset α} (ht : G.IsNClique 3 t)
    {x : α} (hx : x ∉ t) :
    ∃ a ∈ t, 3 ≤ G.degree a := by
  have htNon : t.Nonempty := by
    rw [← Finset.card_pos, ht.card_eq]
    decide
  obtain ⟨y, hyt⟩ := htNon
  obtain ⟨p⟩ := hG y x
  obtain ⟨d, _hd, hdin, hdout⟩ :=
    p.exists_boundary_dart (t : Set α) (by simpa using hyt) (by simpa using hx)
  let a : α := d.fst
  let w : α := d.snd
  have hat : a ∈ t := by simpa [a] using hdin
  have hwt : w ∉ t := by simpa [w] using hdout
  have haw : G.Adj a w := by simpa [a, w] using d.adj
  let R : Finset α := insert w (t.erase a)
  have hRsub : R ⊆ G.neighborFinset a := by
    intro q hq
    simp only [R, Finset.mem_insert, Finset.mem_erase] at hq
    rcases hq with rfl | ⟨hqa, hqt⟩
    · simpa using haw
    · have haq : G.Adj a q := ht.isClique hat hqt hqa
      simpa using haq
  have hErase : #(t.erase a) = 2 := by
    rw [Finset.card_erase_of_mem hat, ht.card_eq]
  have hwErase : w ∉ t.erase a := by
    simp [hwt]
  have hRcard : #R = 3 := by
    simp [R, Finset.card_insert_of_notMem hwErase, hErase]
  refine ⟨a, hat, ?_⟩
  rw [← G.card_neighborFinset_eq_degree, ← hRcard]
  exact Finset.card_le_card hRsub

#print axioms numTrianglesAtVertex_le_triangleMax160
#print axioms exists_triangle_vertex_degree_ge_three

end WrittenOnTheWallII.GraphConjecture160Audit
