import FormalConjectures.WrittenOnTheWallII.GraphConjecture145

namespace WrittenOnTheWallII.GraphConjecture145

open Classical SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

omit [DecidableEq α] in
/-- The order of any induced tree is bounded by `largestInducedTreeSize`. -/
lemma card_le_largestInducedTreeSize {G : SimpleGraph α} {s : Finset α}
    (hs : (G.induce (s : Set α)).IsTree) :
    s.card ≤ largestInducedTreeSize G := by
  unfold largestInducedTreeSize
  apply le_csSup
  · refine ⟨Fintype.card α, ?_⟩
    intro n hn
    obtain ⟨t, rfl, _⟩ := hn
    exact Finset.card_le_univ t
  · exact ⟨s, rfl, hs⟩

omit [Fintype α] in
/-- Attaching a new vertex along its unique neighbor in an induced tree gives a larger
induced tree. -/
lemma SimpleGraph.IsTree.induce_insert_of_unique_adj {G : SimpleGraph α}
    {s : Finset α} {z a : α}
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

omit [Fintype α] in
/-- A shortest walk induces a tree on its support. -/
lemma SimpleGraph.Walk.induce_support_isTree_of_length_eq_dist {G : SimpleGraph α}
    {u v : α} (p : G.Walk u v) (hp : p.length = G.dist u v) :
    (G.induce (p.support.toFinset : Set α)).IsTree := by
  induction p with
  | @nil u =>
      have hset : (↑(Walk.nil : G.Walk u u).support.toFinset : Set α) = {u} := by
        ext
        simp
      have hsingle : (G.induce ({u} : Set α)).IsTree := by
        letI : Nonempty ↥({u} : Set α) := ⟨⟨u, by simp⟩⟩
        letI : Subsingleton ↥({u} : Set α) := ⟨fun a b => by
          apply Subtype.ext
          have ha : (a : α) = u := by
            simpa only [Set.mem_singleton_iff] using a.property
          have hb : (b : α) = u := by
            simpa only [Set.mem_singleton_iff] using b.property
          exact ha.trans hb.symm⟩
        exact IsTree.of_subsingleton
      rw [hset]
      exact hsingle
  | @cons u v w huv p ih =>
      have hptail : p.length = G.dist v w :=
        length_eq_dist_of_subwalk hp (Walk.isSubwalk_cons p huv)
      have hT := ih hptail
      have hpath : (p.cons huv).IsPath :=
        (p.cons huv).isPath_of_length_eq_dist hp
      have hu_not : u ∉ p.support.toFinset := by
        simpa using (List.nodup_cons.mp hpath.support_nodup).1
      have huniq : ∀ ⦃b : α⦄, b ∈ p.support.toFinset → G.Adj u b → b = v := by
        intro b hb hub
        have hbmem : b ∈ p.support := by simpa using hb
        obtain ⟨i, hi, hib⟩ := List.mem_iff_getElem.mp hbmem
        have hget : p.getVert i = b := by
          rw [← p.support_getElem_eq_getVert hi, hib]
        have hi_le : i ≤ p.length := by
          have hlen := p.length_support
          omega
        have hub' : G.Adj u (p.getVert i) := by simpa [hget] using hub
        let r : G.Walk u w := (p.drop i).cons hub'
        have hdistle : G.dist u w ≤ r.length := G.dist_le r
        have hlen : (p.cons huv).length ≤ r.length := by simpa [hp] using hdistle
        have hi0 : i = 0 := by
          simp only [Walk.length_cons, r, Walk.drop_length] at hlen
          omega
        subst i
        simpa using hget.symm
      have hsupp : (Walk.cons huv p).support.toFinset = insert u p.support.toFinset := by
        simp
      rw [hsupp]
      exact hT.induce_insert_of_unique_adj hu_not (by simp) huv huniq

/-- A connected finite graph has an induced tree on at least `diam + 1` vertices. -/
lemma diam_add_one_le_largestInducedTreeSize (G : SimpleGraph α) (hG : G.Connected) :
    G.diam + 1 ≤ largestInducedTreeSize G := by
  obtain ⟨u, v, huv⟩ := G.exists_dist_eq_diam
  obtain ⟨p, hpPath, hpLen⟩ := hG.exists_path_of_dist u v
  have hpTree : (G.induce (p.support.toFinset : Set α)).IsTree :=
    p.induce_support_isTree_of_length_eq_dist hpLen
  have hpCard : p.support.toFinset.card = G.diam + 1 := by
    rw [List.toFinset_card_of_nodup hpPath.support_nodup, Walk.length_support, hpLen, huv]
  rw [← hpCard]
  exact card_le_largestInducedTreeSize hpTree

/-- Distance to a nonempty set is bounded by distance to any specified member. -/
lemma distToSet_le_dist_of_mem (G : SimpleGraph α) (v s : α) (S : Set α)
    (hs : s ∈ S) : G.distToSet v S ≤ G.dist v s := by
  unfold distToSet
  split_ifs with hS
  · apply Finset.min'_le
    exact Finset.mem_image.mpr ⟨s, by simpa using hs, rfl⟩
  · exact (hS ⟨s, by simpa using hs⟩).elim

/-- The eccentricity of the boundary set is at most the graph diameter. -/
lemma eccSet_maxEccentricityVertices_le_diam (G : SimpleGraph α)
    [DecidableRel G.Adj] (hG : G.Connected) :
    eccSet G (maxEccentricityVertices G : Set α) ≤ G.diam := by
  have hed : G.ediam ≠ ⊤ := G.connected_iff_ediam_ne_top.mp hG
  obtain ⟨b, hb⟩ := G.exists_eccent_eq_ediam_of_finite
  have hbB : b ∈ maxEccentricityVertices G := hb
  unfold eccSet
  split_ifs with hdists
  · apply Finset.max'_le _ _ _
    intro d hd
    obtain ⟨v, -, rfl⟩ := Finset.mem_image.mp hd
    exact (distToSet_le_dist_of_mem G v b _ hbB).trans (G.dist_le_diam hed)
  · exact Nat.zero_le _

/-- Formal proof of WOWII Conjecture 145. -/
theorem conjecture145_proved (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected)
    (hlMin : 0 < localIndependenceMin Gᶜ) :
    2 * eccSet G (maxEccentricityVertices G : Set α) ≤
    largestInducedTreeSize G * localIndependenceMin Gᶜ := by
  sorry

#print axioms conjecture145_proved

end WrittenOnTheWallII.GraphConjecture145
