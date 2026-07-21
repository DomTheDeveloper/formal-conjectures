/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import FormalConjectures.WrittenOnTheWallII.GraphConjecture146

/-!
# A proof of Written on the Wall II, Conjecture 146

The proof uses three universal bounds. If `D = diam G`, `T` is the largest
induced-tree order, `e` is the eccentricity of the periphery, and
`q = rad (G^2)`, then

* `T ≥ D + 1`, from a diametral geodesic;
* `e ≤ D - 1`, because a nonperipheral vertex has eccentricity below `D`;
* `D ≤ 4 q`, since a square-graph edge spans at most two original edges and
  `diam (G^2) ≤ 2 rad (G^2)`.

These inequalities settle every case except `D = 4`, `q = 1`, `e = 3`.
For that case, a vertex at distance three from the periphery and a diametral
pair have mutual distances `3, 3, 4`. Two length-three geodesics then contain
an induced tree on at least six vertices.
-/

namespace SimpleGraph

open Classical

variable {α : Type*} [Fintype α] [DecidableEq α]
variable {G : SimpleGraph α}

/- The following four generic induced-tree helpers are adapted from the
Apache-2.0 proof infrastructure in AlperTheKing/formal-conjectures PR #4457.
They are graph-library lemmas, not a proof of Conjecture 146. -/

omit [Fintype α] in
/-- Attaching a new vertex along its unique neighbor in an induced tree gives a
larger induced tree. -/
lemma IsTree.induce_insert_of_unique_adj_146 {s : Finset α} {z a : α}
    (hT : (G.induce (s : Set α)).IsTree)
    (_hz : z ∉ s) (ha : a ∈ s) (hza : G.Adj z a)
    (huniq : ∀ ⦃b : α⦄, b ∈ s → G.Adj z b → b = a) :
    (G.induce ((insert z s : Finset α) : Set α)).IsTree := by
  classical
  constructor
  · have hsconn : (G.induce (s : Set α)).Preconnected := hT.isConnected.preconnected
    have hzconn : (G.induce ({z} : Set α)).Preconnected := .of_subsingleton
    have hconn := connected_induce_union (v := z) (w := a) (s := ({z} : Set α))
      (t := (s : Set α)) hzconn hsconn (by simp) (by simpa using ha) hza
    rw [Finset.coe_insert]
    simpa only [Set.singleton_union] using hconn
  · intro v c hc
    let e : G.induce ((insert z s : Finset α) : Set α) ↪g G :=
      SimpleGraph.Embedding.induce _
    let q : G.Walk (e v) (e v) := c.map e.toHom
    have hq : q.IsCycle := by
      dsimp [q]
      exact (Walk.map_isCycle_iff_of_injective e.injective).2 hc
    have hq_mem (w : α) (hw : w ∈ q.support) : w ∈ insert z s := by
      dsimp [q] at hw
      rw [Walk.support_map] at hw
      obtain ⟨w', hw', rfl⟩ := List.mem_map.mp hw
      change (w' : α) ∈ insert z s
      exact w'.property
    by_cases hzq : z ∈ q.support
    · let r : G.Walk z z := q.rotate hzq
      have hr : r.IsCycle := by
        dsimp [r]
        exact hq.rotate hzq
      have hrsnd : r.snd ∈ q.support := by
        apply (q.mem_support_rotate_iff hzq).mp
        simpa only [r] using r.getVert_mem_support 1
      have hrpenultimate : r.penultimate ∈ q.support := by
        apply (q.mem_support_rotate_iff hzq).mp
        simpa only [r] using r.getVert_mem_support (r.length - 1)
      have hadj_snd : G.Adj z r.snd := r.adj_snd hr.not_nil
      have hadj_penultimate : G.Adj z r.penultimate :=
        (r.adj_penultimate hr.not_nil).symm
      have hsnd : r.snd ∈ s := by
        rcases Finset.mem_insert.mp (hq_mem _ hrsnd) with heq | hmem
        · exact (hadj_snd.ne heq.symm).elim
        · exact hmem
      have hpenultimate : r.penultimate ∈ s := by
        rcases Finset.mem_insert.mp (hq_mem _ hrpenultimate) with heq | hmem
        · exact (hadj_penultimate.ne heq.symm).elim
        · exact hmem
      exact hr.snd_ne_penultimate <|
        (huniq hsnd hadj_snd).trans (huniq hpenultimate hadj_penultimate).symm
    · have hqs : ∀ w ∈ q.support, w ∈ (s : Set α) := by
        intro w hw
        rcases Finset.mem_insert.mp (hq_mem w hw) with heq | hmem
        · subst w
          exact (hzq hw).elim
        · simpa using hmem
      let qi := q.induce (s : Set α) hqs
      have hqi : qi.IsCycle := by
        apply (Walk.map_isCycle_iff_of_injective
          (f := (SimpleGraph.Embedding.induce (G := G) (s : Set α)).toHom)
          (SimpleGraph.Embedding.induce (G := G) (s : Set α)).injective).mp
        rw [show qi.map (SimpleGraph.Embedding.induce (G := G) (s : Set α)).toHom = q by
          dsimp [qi]
          exact Walk.map_induce q hqs]
        exact hq
      exact hT.IsAcyclic qi hqi

omit [Fintype α] [DecidableEq α] in
/-- Every distance-realizing walk is chordless in the ambient graph. -/
lemma Walk.chordless_of_length_eq_dist_146 {u v x y : α} (p : G.Walk u v)
    (hp : p.length = G.dist u v) (hx : x ∈ p.support) (hy : y ∈ p.support)
    (hxy : G.Adj x y) : s(x, y) ∈ p.edges := by
  induction p with
  | @nil u =>
      simp only [Walk.support_nil, List.mem_singleton] at hx hy
      subst x
      subst y
      exact (hxy.ne rfl).elim
  | @cons u v w huv p ih =>
      have hptail : p.length = G.dist v w :=
        length_eq_dist_of_subwalk hp (Walk.isSubwalk_cons p huv)
      have huniq : ∀ ⦃b : α⦄, b ∈ p.support → G.Adj u b → b = v := by
        intro b hb hub
        obtain ⟨i, hi, hib⟩ := List.mem_iff_getElem.mp hb
        have hget : p.getVert i = b := by
          rw [← p.support_getElem_eq_getVert hi, hib]
        have hiLe : i ≤ p.length := by
          have hlen := p.length_support
          omega
        have hub' : G.Adj u (p.getVert i) := by simpa [hget] using hub
        let r : G.Walk u w := (p.drop i).cons hub'
        have hdistLe : G.dist u w ≤ r.length := G.dist_le r
        have hlen : (p.cons huv).length ≤ r.length := by simpa [hp] using hdistLe
        have hi0 : i = 0 := by
          simp only [Walk.length_cons, r, Walk.drop_length] at hlen
          omega
        subst i
        simpa using hget.symm
      simp only [Walk.support_cons, List.mem_cons] at hx hy
      rw [Walk.edges_cons]
      rcases hx with rfl | hx <;> rcases hy with rfl | hy
      · exact (hxy.ne rfl).elim
      · have hyv : y = v := huniq hy hxy
        simp [hyv]
      · have hxv : x = v := huniq hx hxy.symm
        simp [hxv, Sym2.eq_swap]
      · exact List.mem_cons_of_mem _ (ih hptail hx hy)

omit [Fintype α] in
/-- A distance-realizing walk induces a tree on its support. -/
lemma Walk.induce_support_isTree_of_length_eq_dist_146 {u v : α} (p : G.Walk u v)
    (hp : p.length = G.dist u v) :
    (G.induce (p.support.toFinset : Set α)).IsTree := by
  induction p with
  | @nil u =>
      have hset : (↑(Walk.nil : G.Walk u u).support.toFinset : Set α) = {u} := by
        ext
        simp
      rw [hset]
      letI : Nonempty ↥({u} : Set α) := ⟨⟨u, by simp⟩⟩
      letI : Subsingleton ↥({u} : Set α) := ⟨fun a b => by
        apply Subtype.ext
        simpa only [Set.mem_singleton_iff] using a.property.trans b.property.symm⟩
      exact IsTree.of_subsingleton
  | @cons u v w huv p ih =>
      have hptail : p.length = G.dist v w :=
        length_eq_dist_of_subwalk hp (Walk.isSubwalk_cons p huv)
      have htree := ih hptail
      have hpath : (p.cons huv).IsPath := (p.cons huv).isPath_of_length_eq_dist hp
      have huNot : u ∉ p.support.toFinset := by
        simpa using (List.nodup_cons.mp hpath.support_nodup).1
      have huniq : ∀ ⦃b : α⦄, b ∈ p.support.toFinset → G.Adj u b → b = v := by
        intro b hb hub
        have hbmem : b ∈ p.support := by simpa using hb
        have hedge := (p.cons huv).chordless_of_length_eq_dist_146 hp
          (by simp) (by simp [hbmem]) hub
        simpa using hpath.eq_snd_of_mem_edges hedge
      have hsupp : (Walk.cons huv p).support.toFinset = insert u p.support.toFinset := by simp
      rw [hsupp]
      exact htree.induce_insert_of_unique_adj_146 huNot (by simp) huv huniq

omit [Fintype α] in
/-- A chordless path with exactly one edge to an induced tree can be spliced
onto it. -/
lemma Walk.IsPath.induce_union_isTree_of_unique_attachment_146
    {s : Finset α} {a b r : α} (q : G.Walk a b)
    (hq : q.IsPath)
    (hsTree : (G.induce (s : Set α)).IsTree)
    (hdisj : ∀ ⦃x : α⦄, x ∈ q.support → x ∉ s)
    (hchordless : ∀ ⦃x y : α⦄, x ∈ q.support → y ∈ q.support →
      G.Adj x y → s(x, y) ∈ q.edges)
    (hr : r ∈ s) (har : G.Adj a r)
    (hcross : ∀ ⦃x y : α⦄, x ∈ q.support → y ∈ s → G.Adj x y →
      x = a ∧ y = r) :
    (G.induce (((s ∪ q.support.toFinset : Finset α) : Finset α) : Set α)).IsTree := by
  induction q generalizing s r with
  | @nil u0 =>
      have htree := hsTree.induce_insert_of_unique_adj_146 (hdisj (by simp)) hr har
        (fun _ hy hay => (hcross (by simp) hy hay).2)
      have hset : s ∪ (Walk.nil : G.Walk u0 u0).support.toFinset = insert u0 s := by
        ext x
        simp
      rwa [hset]
  | @cons u0 v0 w0 hu0v0 p ih =>
      have hqFull := hq
      rw [Walk.cons_isPath_iff] at hq
      have hu0_not_p : u0 ∉ p.support := hq.2
      have hu0_not_s : u0 ∉ s := hdisj (by simp)
      have hsU : (G.induce ((insert u0 s : Finset α) : Set α)).IsTree :=
        hsTree.induce_insert_of_unique_adj_146 hu0_not_s hr har
          (fun _ hy hay => (hcross (by simp) hy hay).2)
      have hpdisj : ∀ ⦃x : α⦄, x ∈ p.support → x ∉ insert u0 s := by
        intro x hx hxin
        rcases Finset.mem_insert.mp hxin with rfl | hxs
        · exact hu0_not_p hx
        · exact hdisj (by simp [hx]) hxs
      have hpchordless : ∀ ⦃x y : α⦄, x ∈ p.support → y ∈ p.support →
          G.Adj x y → s(x, y) ∈ p.edges := by
        intro x y hx hy hxy
        have he := hchordless (by simp [hx]) (by simp [hy]) hxy
        rw [Walk.edges_cons] at he
        rcases List.mem_cons.mp he with he | he
        · rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact (hu0_not_p hx).elim
          · exact (hu0_not_p hy).elim
        · exact he
      have hpcross : ∀ ⦃x y : α⦄, x ∈ p.support → y ∈ insert u0 s →
          G.Adj x y → x = v0 ∧ y = u0 := by
        intro x y hx hy hxy
        rcases Finset.mem_insert.mp hy with hyu | hys
        · subst y
          have he : s(u0, x) ∈ (p.cons hu0v0).edges := by
            exact hchordless (by simp) (by simp [hx]) hxy.symm
          have hxv : x = v0 := by simpa using hqFull.eq_snd_of_mem_edges he
          exact ⟨hxv, rfl⟩
        · have hc := hcross (by simp [hx]) hys hxy
          exact (hu0_not_p (hc.1 ▸ hx)).elim
      have hrec := ih hq.1 hsU hpdisj hpchordless (by simp) hu0v0.symm
        (fun x y hx hy hxy => hpcross hx hy hxy)
      have hset : s ∪ (p.cons hu0v0).support.toFinset =
          insert u0 s ∪ p.support.toFinset := by
        ext x
        simp
      rwa [hset]

omit [Fintype α] in
/-- The union cardinality of a finite set and a disjoint path support. -/
lemma Walk.IsPath.card_union_support_of_disjoint_146
    {s : Finset α} {a b : α} (q : G.Walk a b) (hq : q.IsPath)
    (hdisj : ∀ ⦃x : α⦄, x ∈ q.support → x ∉ s) :
    (s ∪ q.support.toFinset).card = s.card + q.length + 1 := by
  have hd : Disjoint s q.support.toFinset := by
    rw [Finset.disjoint_left]
    intro x hxs hxq
    exact hdisj (by simpa using hxq) hxs
  rw [Finset.card_union_of_disjoint hd]
  rw [List.toFinset_card_of_nodup hq.support_nodup, q.length_support]
  omega

omit [DecidableEq α] in
/-- Every concrete induced tree is bounded by `largestInducedTreeSize`. -/
lemma IsTree.card_le_largestInducedTreeSize_146 {s : Finset α}
    (hs : (G.induce (s : Set α)).IsTree) :
    s.card ≤ largestInducedTreeSize G := by
  unfold largestInducedTreeSize
  apply le_csSup
  · exact ⟨Fintype.card α, by
      rintro n ⟨t, rfl, -⟩
      exact t.card_le_univ⟩
  · exact ⟨s, rfl, hs⟩

/-- A diametral geodesic is an induced tree of order `diam + 1`. -/
lemma Connected.diam_add_one_le_largestInducedTreeSize_146
    (h : G.Connected) : G.diam + 1 ≤ largestInducedTreeSize G := by
  have hD0 : G.diam ≠ 0 := (connected_iff_diam_ne_zero).mp h
  obtain ⟨u, v, huv⟩ := G.exists_dist_eq_diam
  have huv0 : G.dist u v ≠ 0 := by simpa [huv] using hD0
  obtain ⟨p, hp⟩ := exists_walk_of_dist_ne_zero huv0
  have htree := p.induce_support_isTree_of_length_eq_dist_146 hp
  have hle := htree.card_le_largestInducedTreeSize_146
  have hpath := p.isPath_of_length_eq_dist hp
  have hcard : p.support.toFinset.card = p.length + 1 := by
    rw [List.toFinset_card_of_nodup hpath.support_nodup, p.length_support]
  rw [hcard, hp, huv] at hle
  exact hle

/-- Membership in a nonempty target set forces distance to that set to be zero. -/
lemma distToSet_eq_zero_of_mem_146 {S : Set α} {v : α} (hv : v ∈ S) :
    G.distToSet v S = 0 := by
  unfold distToSet
  have hS : S.toFinset.Nonempty := Set.toFinset_nonempty.mpr ⟨v, hv⟩
  rw [dif_pos hS]
  apply Nat.eq_zero_of_le_zero
  apply Finset.min'_le
  exact Finset.mem_image.mpr ⟨v, Set.mem_toFinset.mpr hv, by simp⟩

/-- A member of a finite target set bounds distance to that set. -/
lemma distToSet_le_dist_of_mem_146 {S : Set α} (x : α) {s : α} (hs : s ∈ S) :
    G.distToSet x S ≤ G.dist x s := by
  unfold distToSet
  split_ifs with h
  · exact Finset.min'_le _ _ (Finset.mem_image_of_mem _ (Set.mem_toFinset.mpr hs))
  · exact Nat.zero_le _

/-- The periphery of a finite graph is nonempty. -/
lemma maxEccentricityVertices_nonempty_146 (G : SimpleGraph α) :
    (maxEccentricityVertices G).Nonempty := by
  obtain ⟨u, hu⟩ := G.exists_eccent_eq_ediam_of_finite
  exact ⟨u, hu⟩

/-- A pair at distance `diam` consists of peripheral vertices. -/
lemma Connected.mem_maxEccentricityVertices_of_dist_eq_diam_146
    (h : G.Connected) {u v : α} (huv : G.dist u v = G.diam) :
    u ∈ maxEccentricityVertices G := by
  have htop : G.ediam ≠ ⊤ := (connected_iff_ediam_ne_top).mp h
  have hed : G.edist u v = G.ediam := by
    rw [← (h.preconnected u v).coe_dist_eq_edist, huv, diam,
      ENat.natCast_toNat htop]
  change G.eccent u = G.ediam
  exact le_antisymm eccent_le_ediam (hed ▸ edist_le_eccent)

/-- The eccentricity of the periphery is at most `diam - 1`. -/
lemma Connected.eccSet_maxEccentricityVertices_le_diam_sub_one_146
    (h : G.Connected) :
    eccSet G (maxEccentricityVertices G) ≤ G.diam - 1 := by
  let B : Set α := maxEccentricityVertices G
  let dists := Finset.univ.image (fun v => G.distToSet v B)
  have hdists : dists.Nonempty := Finset.univ_nonempty.image _
  unfold eccSet
  change (if hd : dists.Nonempty then dists.max' hd else 0) ≤ G.diam - 1
  rw [dif_pos hdists, Finset.max'_le_iff]
  intro d hd
  rcases Finset.mem_image.mp hd with ⟨v, -, rfl⟩
  have hD0 : G.diam ≠ 0 := (connected_iff_diam_ne_zero).mp h
  by_cases hv : v ∈ B
  · rw [distToSet_eq_zero_of_mem_146 hv]
    omega
  · obtain ⟨b, hb⟩ := maxEccentricityVertices_nonempty_146 G
    have hset : G.distToSet v B ≤ G.dist v b :=
      distToSet_le_dist_of_mem_146 v hb
    have htop : G.ediam ≠ ⊤ := (connected_iff_ediam_ne_top).mp h
    have hdist_le : G.dist v b ≤ G.diam := dist_le_diam htop
    have hdist_lt : G.dist v b < G.diam := by
      by_contra hnlt
      have heq : G.dist v b = G.diam := by omega
      exact hv (h.mem_maxEccentricityVertices_of_dist_eq_diam_146 heq)
    omega

/-- Original edges remain edges in the graph square. -/
lemma le_graphSquare_146 (G : SimpleGraph α) : G ≤ graphSquare G := by
  intro u v huv
  exact ⟨huv.ne, by rw [dist_eq_one_iff_adj.mpr huv]; omega⟩

/-- A square-graph walk of length `m` spans original distance at most `2m`. -/
omit [Fintype α] [DecidableEq α] in
lemma Connected.dist_le_two_mul_length_of_graphSquare_walk_146
    (h : G.Connected) {u v : α} (p : (graphSquare G).Walk u v) :
    G.dist u v ≤ 2 * p.length := by
  induction p with
  | nil => simp
  | @cons u v w huv p ih =>
      have htri := h.dist_triangle (u := u) (v := v) (w := w)
      have huv2 : G.dist u v ≤ 2 := huv.2
      simp only [Walk.length_cons]
      omega

/-- Squaring a graph can shrink its diameter by at most a factor of two. -/
lemma Connected.diam_le_two_mul_graphSquare_diam_146 (h : G.Connected) :
    G.diam ≤ 2 * (graphSquare G).diam := by
  let H := graphSquare G
  have hH : H.Connected := h.mono (le_graphSquare_146 G)
  have hHtop : H.ediam ≠ ⊤ := (connected_iff_ediam_ne_top).mp hH
  obtain ⟨u, v, huv⟩ := G.exists_dist_eq_diam
  obtain ⟨p, hp⟩ := hH.exists_walk_length_eq_dist u v
  have hspan := h.dist_le_two_mul_length_of_graphSquare_walk_146 p
  have hHd : H.dist u v ≤ H.diam := dist_le_diam hHtop
  dsimp [H] at hp hHd ⊢
  rw [hp] at hspan
  omega

/-- For a connected graph, `diam G ≤ 4 * rad (G²)`. -/
lemma Connected.diam_le_four_mul_graphSquareRadius_146 (h : G.Connected) :
    G.diam ≤ 4 * WrittenOnTheWallII.GraphConjecture146.graphSquareRadius G := by
  let H := graphSquare G
  have hH : H.Connected := h.mono (le_graphSquare_146 G)
  have hrTop : H.radius ≠ ⊤ := (radius_ne_top_iff).mpr hH
  have htworTop : 2 * H.radius ≠ ⊤ := by simp [hrTop]
  have hrad : H.diam ≤ 2 * H.radius.toNat := by
    have hnat := ENat.toNat_le_toNat H.ediam_le_two_mul_radius htworTop
    simpa [diam, ENat.toNat_mul] using hnat
  have hdiam := h.diam_le_two_mul_graphSquare_diam_146
  unfold WrittenOnTheWallII.GraphConjecture146.graphSquareRadius
  dsimp [H] at hrad
  omega

/-- The maximum in `eccSet` is attained. -/
lemma exists_distToSet_eq_eccSet_146 (G : SimpleGraph α) (S : Set α) :
    ∃ x : α, G.distToSet x S = eccSet G S := by
  let dists := Finset.univ.image (fun v => G.distToSet v S)
  have hdists : dists.Nonempty := Finset.univ_nonempty.image _
  unfold eccSet
  change ∃ x : α, G.distToSet x S = if hd : dists.Nonempty then dists.max' hd else 0
  rw [dif_pos hdists]
  have hm := Finset.max'_mem dists hdists
  rcases Finset.mem_image.mp hm with ⟨x, -, hx⟩
  exact ⟨x, hx⟩

end SimpleGraph

namespace WrittenOnTheWallII.GraphConjecture146

open Classical SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

/-- Metric core of the exceptional case: distances `3, 3, 4` force an induced
subtree on at least six vertices. -/
lemma six_le_largestInducedTreeSize_of_dist_three_three_four
    (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected)
    {x u v : α} (hxu : G.dist x u = 3) (hxv : G.dist x v = 3)
    (huv : G.dist u v = 4) :
    6 ≤ largestInducedTreeSize G := by
  obtain ⟨p, hpPath, hp⟩ := h.exists_path_of_dist x u
  obtain ⟨q, hqPath, hq⟩ := h.exists_path_of_dist x v
  have hp3 : p.length = 3 := by omega
  have hq3 : q.length = 3 := by omega
  let a := p.getVert 1
  let b := p.getVert 2
  let c := q.getVert 1
  let d := q.getVert 2
  have hxa : G.Adj x a := by
    simpa [a] using p.adj_getVert_succ (show 0 < p.length by omega)
  have hab : G.Adj a b := by
    simpa [a, b] using p.adj_getVert_succ (show 1 < p.length by omega)
  have hbu : G.Adj b u := by
    simpa [b, hp3] using p.adj_getVert_succ (show 2 < p.length by omega)
  have hxc : G.Adj x c := by
    simpa [c] using q.adj_getVert_succ (show 0 < q.length by omega)
  have hcd : G.Adj c d := by
    simpa [c, d] using q.adj_getVert_succ (show 1 < q.length by omega)
  have hdv : G.Adj d v := by
    simpa [d, hq3] using q.adj_getVert_succ (show 2 < q.length by omega)
  let P : G.Walk x u := .cons hxa (.cons hab (.cons hbu .nil))
  let Q : G.Walk x v := .cons hxc (.cons hcd (.cons hdv .nil))
  have hP : P.length = G.dist x u := by simp [P, hxu]
  have hQ : Q.length = G.dist x v := by simp [Q, hxv]
  have hxb : G.dist x b = 2 := by
    have hs := length_eq_dist_of_subwalk hP (Walk.isSubwalk_take P 2)
    simpa [P] using hs.symm
  have hxd : G.dist x d = 2 := by
    have hs := length_eq_dist_of_subwalk hQ (Walk.isSubwalk_take Q 2)
    simpa [Q] using hs.symm
  have hxu_ne : ¬G.Adj x u := by
    intro hxuAdj
    have := dist_eq_one_iff_adj.mpr hxuAdj
    omega
  have hxv_ne : ¬G.Adj x v := by
    intro hxvAdj
    have := dist_eq_one_iff_adj.mpr hxvAdj
    omega
  have hxb_ne : ¬G.Adj x b := by
    intro hxbAdj
    have := dist_eq_one_iff_adj.mpr hxbAdj
    omega
  have hxd_ne : ¬G.Adj x d := by
    intro hxdAdj
    have := dist_eq_one_iff_adj.mpr hxdAdj
    omega
  have huv_ne : ¬G.Adj u v := by
    intro huvAdj
    have := dist_eq_one_iff_adj.mpr huvAdj
    omega
  have huc : ¬G.Adj u c := by
    intro huc
    let r : G.Walk u v := .cons huc (.cons hcd (.cons hdv .nil))
    have := G.dist_le r
    simp [r, huv] at this
  have hud : ¬G.Adj u d := by
    intro hud
    let r : G.Walk u v := .cons hud (.cons hdv .nil)
    have := G.dist_le r
    simp [r, huv] at this
  have hav : ¬G.Adj a v := by
    intro hav
    let r : G.Walk u v := .cons hbu.symm (.cons hab.symm (.cons hav .nil))
    have := G.dist_le r
    simp [r, huv] at this
  have hbv : ¬G.Adj b v := by
    intro hbv
    let r : G.Walk u v := .cons hbu.symm (.cons hbv .nil)
    have := G.dist_le r
    simp [r, huv] at this
  have hbd : ¬G.Adj b d := by
    intro hbd
    let r : G.Walk u v := .cons hbu.symm (.cons hbd (.cons hdv .nil))
    have := G.dist_le r
    simp [r, huv] at this
  have hxa_ne : x ≠ a := hxa.ne
  have hab_ne : a ≠ b := hab.ne
  have hbu_ne : b ≠ u := hbu.ne
  have hxc_ne : x ≠ c := hxc.ne
  have hcd_ne : c ≠ d := hcd.ne
  have hdv_ne : d ≠ v := hdv.ne
  have hxb_eq_ne : x ≠ b := by
    intro hEq
    rw [← hEq] at hxb
    simp at hxb
  have hxd_eq_ne : x ≠ d := by
    intro hEq
    rw [← hEq] at hxd
    simp at hxd
  have hxu_eq_ne : x ≠ u := by
    intro hEq
    rw [← hEq] at hxu
    simp at hxu
  have hxv_eq_ne : x ≠ v := by
    intro hEq
    rw [← hEq] at hxv
    simp at hxv
  by_cases had : G.Adj a d
  · let r : G.Walk u v := .cons hbu.symm (.cons hab.symm (.cons had (.cons hdv .nil)))
    have hr : r.length = G.dist u v := by simp [r, huv]
    have hrTree := r.induce_support_isTree_of_length_eq_dist_146 hr
    have hrPath := r.isPath_of_length_eq_dist hr
    have hxnot : x ∉ r.support.toFinset := by
      simp [r, hxu_eq_ne, hxb_eq_ne, hxa_ne, hxd_eq_ne, hxv_eq_ne]
    have huniq : ∀ ⦃y : α⦄, y ∈ r.support.toFinset → G.Adj x y → y = a := by
      intro y hy hxy
      simp [r] at hy
      rcases hy with rfl | rfl | rfl | rfl | rfl
      · exact (hxu_ne hxy).elim
      · exact (hxb_ne hxy).elim
      · rfl
      · exact (hxd_ne hxy).elim
      · exact (hxv_ne hxy).elim
    have htree := hrTree.induce_insert_of_unique_adj_146 hxnot (by simp [r]) hxa huniq
    have hcardr : r.support.toFinset.card = 5 := by
      rw [List.toFinset_card_of_nodup hrPath.support_nodup, r.length_support]
      simp [r]
    have hcard : (insert x r.support.toFinset).card = 6 := by
      rw [Finset.card_insert_of_notMem hxnot, hcardr]
    have hle := htree.card_le_largestInducedTreeSize_146
    omega
  · by_cases hcb : G.Adj c b
    · let r : G.Walk v u := .cons hdv.symm (.cons hcd.symm (.cons hcb (.cons hbu .nil)))
      have hr : r.length = G.dist v u := by simp [r, dist_comm, huv]
      have hrTree := r.induce_support_isTree_of_length_eq_dist_146 hr
      have hrPath := r.isPath_of_length_eq_dist hr
      have hxnot : x ∉ r.support.toFinset := by
        simp [r, hxv_eq_ne, hxd_eq_ne, hxc_ne, hxb_eq_ne, hxu_eq_ne]
      have huniq : ∀ ⦃y : α⦄, y ∈ r.support.toFinset → G.Adj x y → y = c := by
        intro y hy hxy
        simp [r] at hy
        rcases hy with rfl | rfl | rfl | rfl | rfl
        · exact (hxv_ne hxy).elim
        · exact (hxd_ne hxy).elim
        · rfl
        · exact (hxb_ne hxy).elim
        · exact (hxu_ne hxy).elim
      have htree := hrTree.induce_insert_of_unique_adj_146 hxnot (by simp [r]) hxc huniq
      have hcardr : r.support.toFinset.card = 5 := by
        rw [List.toFinset_card_of_nodup hrPath.support_nodup, r.length_support]
        simp [r]
      have hcard : (insert x r.support.toFinset).card = 6 := by
        rw [Finset.card_insert_of_notMem hxnot, hcardr]
      have hle := htree.card_le_largestInducedTreeSize_146
      omega
    · by_cases hac : G.Adj a c
      · let A : Finset α := P.tail.support.toFinset
        let R : G.Walk c v := .cons hcd (.cons hdv .nil)
        have hAtree : (G.induce (A : Set α)).IsTree := by
          have htail : P.tail.length = G.dist a u :=
            length_eq_dist_of_subwalk hP (Walk.isSubwalk_cons P.tail hxa)
          exact P.tail.induce_support_isTree_of_length_eq_dist_146 htail
        have hR : R.length = G.dist c v :=
          length_eq_dist_of_subwalk hQ (Walk.isSubwalk_cons R hxc)
        have hRPath := R.isPath_of_length_eq_dist hR
        have hRchord : ∀ ⦃z y : α⦄, z ∈ R.support → y ∈ R.support →
            G.Adj z y → s(z, y) ∈ R.edges := by
          intro z y hz hy hzy
          exact R.chordless_of_length_eq_dist_146 hR hz hy hzy
        have hdisj : ∀ ⦃z : α⦄, z ∈ R.support → z ∉ A := by
          intro z hz hzA
          simp [R] at hz
          simp [A, P] at hzA
          rcases hz with rfl | rfl | rfl <;> rcases hzA with rfl | rfl | rfl
          all_goals simp_all
        have hcross : ∀ ⦃z y : α⦄, z ∈ R.support → y ∈ A → G.Adj z y →
            z = c ∧ y = a := by
          intro z y hz hy hzy
          simp [R] at hz
          simp [A, P] at hy
          rcases hz with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
          all_goals simp_all [adj_comm]
        have htree := hRPath.induce_union_isTree_of_unique_attachment_146 R hAtree hdisj
          hRchord (by simp [A, P]) hac.symm hcross
        have hcardA : A.card = 3 := by
          have htailPath := P.tail.isPath_of_length_eq_dist
            (length_eq_dist_of_subwalk hP (Walk.isSubwalk_cons P.tail hxa))
          rw [List.toFinset_card_of_nodup htailPath.support_nodup, P.tail.length_support]
          simp [A, P]
        have hcard := hRPath.card_union_support_of_disjoint_146 R hdisj
        have hle := htree.card_le_largestInducedTreeSize_146
        rw [hcard, hcardA] at hle
        simp [R] at hle
        exact hle
      · let A : Finset α := P.support.toFinset
        let R : G.Walk c v := .cons hcd (.cons hdv .nil)
        have hAtree : (G.induce (A : Set α)).IsTree :=
          P.induce_support_isTree_of_length_eq_dist_146 hP
        have hR : R.length = G.dist c v :=
          length_eq_dist_of_subwalk hQ (Walk.isSubwalk_cons R hxc)
        have hRPath := R.isPath_of_length_eq_dist hR
        have hRchord : ∀ ⦃z y : α⦄, z ∈ R.support → y ∈ R.support →
            G.Adj z y → s(z, y) ∈ R.edges := by
          intro z y hz hy hzy
          exact R.chordless_of_length_eq_dist_146 hR hz hy hzy
        have hdisj : ∀ ⦃z : α⦄, z ∈ R.support → z ∉ A := by
          intro z hz hzA
          simp [R] at hz
          simp [A, P] at hzA
          rcases hz with rfl | rfl | rfl <;> rcases hzA with rfl | rfl | rfl | rfl
          all_goals simp_all
        have hcross : ∀ ⦃z y : α⦄, z ∈ R.support → y ∈ A → G.Adj z y →
            z = c ∧ y = x := by
          intro z y hz hy hzy
          simp [R] at hz
          simp [A, P] at hy
          rcases hz with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl
          all_goals simp_all [adj_comm]
        have htree := hRPath.induce_union_isTree_of_unique_attachment_146 R hAtree hdisj
          hRchord (by simp [A, P]) hxc.symm hcross
        have hcardA : A.card = 4 := by
          have hPPath := P.isPath_of_length_eq_dist hP
          rw [List.toFinset_card_of_nodup hPPath.support_nodup, P.length_support]
          simp [A, P]
        have hcard := hRPath.card_union_support_of_disjoint_146 R hdisj
        have hle := htree.card_le_largestInducedTreeSize_146
        rw [hcard, hcardA] at hle
        simp [R] at hle
        omega

/-- Exact theorem, with the statement from `GraphConjecture146.lean` unchanged. -/
@[category API, AMS 5]
theorem conjecture146_proved (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected)
    (hrad : 0 < graphSquareRadius G) :
    2 * eccSet G (maxEccentricityVertices G : Set α) ≤
    largestInducedTreeSize G * graphSquareRadius G := by
  let e := eccSet G (maxEccentricityVertices G : Set α)
  let T := largestInducedTreeSize G
  let D := G.diam
  let q := graphSquareRadius G
  have hT : D + 1 ≤ T := by
    simpa [D, T] using h.diam_add_one_le_largestInducedTreeSize_146
  have he : e ≤ D - 1 := by
    simpa [e, D] using h.eccSet_maxEccentricityVertices_le_diam_sub_one_146
  have hDq : D ≤ 4 * q := by
    simpa [D, q] using h.diam_le_four_mul_graphSquareRadius_146
  have hD0 : D ≠ 0 := by
    simpa [D] using (connected_iff_diam_ne_zero.mp h)
  have hq : 0 < q := by simpa [q] using hrad
  change 2 * e ≤ T * q
  by_cases hq1 : q = 1
  · have hD4 : D ≤ 4 := by omega
    by_cases hD_eq : D = 4
    · by_cases he2 : e ≤ 2
      · subst q
        omega
      · have he3 : e = 3 := by omega
        obtain ⟨x, hx⟩ := exists_distToSet_eq_eccSet_146 G
          (maxEccentricityVertices G : Set α)
        have hx3 : G.distToSet x (maxEccentricityVertices G : Set α) = 3 := by
          simpa [e, he3] using hx
        obtain ⟨u, v, huvD⟩ := G.exists_dist_eq_diam
        have huv4 : G.dist u v = 4 := by omega
        have huB : u ∈ maxEccentricityVertices G :=
          h.mem_maxEccentricityVertices_of_dist_eq_diam_146 huvD
        have hvB : v ∈ maxEccentricityVertices G := by
          apply h.mem_maxEccentricityVertices_of_dist_eq_diam_146
          rw [dist_comm, huvD]
        have hxuSet := distToSet_le_dist_of_mem_146 (G := G) x huB
        have hxvSet := distToSet_le_dist_of_mem_146 (G := G) x hvB
        have htop : G.ediam ≠ ⊤ := (connected_iff_ediam_ne_top).mp h
        have hxuLe : G.dist x u ≤ 4 := by
          have := dist_le_diam (G := G) (u := x) (v := u) htop
          omega
        have hxvLe : G.dist x v ≤ 4 := by
          have := dist_le_diam (G := G) (u := x) (v := v) htop
          omega
        have hxu4ne : G.dist x u ≠ 4 := by
          intro hxu4
          have hxB : x ∈ maxEccentricityVertices G := by
            apply h.mem_maxEccentricityVertices_of_dist_eq_diam_146
            omega
          have hx0 := distToSet_eq_zero_of_mem_146 (G := G) hxB
          omega
        have hxv4ne : G.dist x v ≠ 4 := by
          intro hxv4
          have hxB : x ∈ maxEccentricityVertices G := by
            apply h.mem_maxEccentricityVertices_of_dist_eq_diam_146
            omega
          have hx0 := distToSet_eq_zero_of_mem_146 (G := G) hxB
          omega
        have hxu3 : G.dist x u = 3 := by omega
        have hxv3 : G.dist x v = 3 := by omega
        have h6 := six_le_largestInducedTreeSize_of_dist_three_three_four G h hxu3 hxv3 huv4
        subst q
        simpa [T, he3] using h6
    · have hD3 : D ≤ 3 := by omega
      subst q
      omega
  · have hq2 : 2 ≤ q := by omega
    have heT : e ≤ T := by omega
    calc
      2 * e ≤ 2 * T := Nat.mul_le_mul_left 2 heT
      _ = T * 2 := by omega
      _ ≤ T * q := Nat.mul_le_mul_left T hq2

#print axioms conjecture146_proved

end WrittenOnTheWallII.GraphConjecture146
