module

public import Mathlib.Combinatorics.SimpleGraph.Metric
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Data.Finset.Lattice.Fold

/-!
# Written on the Wall II, Conjecture 318

Ermelinda DeLaViña's Graffiti.pc catalogue, 4 March 2007.
https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/index.html

For a finite connected simple graph on at least two vertices, suppose some vertex
sees at least as many vertices at even distance as the graph has missing edges.
Every inclusion-minimal total dominating set then has exactly two vertices.

Choose a vertex v attaining the maximum. Every even-distance vertex other than v
is a nonneighbor of v. Therefore at most one missing edge has both ends outside
v, and every adjacent pair outside v dominates the graph induced there.
In a total dominating set D, choose a neighbor a of v. If a has a neighbor b in
D other than v, the pair {a,b} dominates the whole graph. Otherwise v belongs
to D. Any vertex outside v missed by a must be adjacent to v: a neighbor in D
different from v would give an edge outside v that fails to dominate a.
Thus {v,a} is a total dominating pair in the second case.

The catalogue marked item 318 open when consulted on 24 November 2026.
Its current machine-readable record is available at
https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/files/conjectures.json
The source of the graph metric and unordered edge types is Mathlib.
Lean and Mathlib v4.33.1. From a project with that Mathlib version, run
`lake env lean Graffiti318.lean`.
-/

@[expose] public section
namespace Graffiti318

open Finset
open scoped Classical
noncomputable section

variable {V : Type*} (G : SimpleGraph V)

/-- Every vertex, including each member of D, has a neighbor in D. -/
def TotalDominates (D : Finset V) : Prop :=
  ∀ x, ∃ y ∈ D, G.Adj x y

/-- Inclusion-minimality among total dominating sets. -/
def MinimalTotal (D : Finset V) : Prop :=
  TotalDominates G D ∧ ∀ E ⊆ D, TotalDominates G E → E = D

/-- Every inclusion-minimal total dominating set has minimum cardinality. -/
def WellTotallyDominated : Prop :=
  ∀ D, MinimalTotal G D → ∀ E, TotalDominates G E → D.card ≤ E.card

variable [Fintype V]

def evenCount (v : V) : ℕ :=
  (univ.filter fun w => Even (G.dist v w)).card

def maxEvenCount : ℕ := univ.sup (evenCount G)

def missingCount : ℕ := Gᶜ.edgeFinset.card

/-- Each even-distance vertex other than v supplies a distinct missing edge at v. -/
private theorem evenCount_le (v : V) : evenCount G v ≤ Gᶜ.degree v + 1 := by
  let S := univ.filter fun w => Even (G.dist v w)
  have hv : v ∈ S := by simp [S]
  have hsub : S.erase v ⊆ Gᶜ.neighborFinset v := by
    intro w hw
    obtain ⟨hwv, hwS⟩ := mem_erase.mp hw
    have he : Even (G.dist v w) := (mem_filter.mp hwS).2
    apply (Gᶜ.mem_neighborFinset v w).mpr
    refine (G.compl_adj v w).mpr ⟨Ne.symm hwv, ?_⟩
    intro hadj
    rw [SimpleGraph.dist_eq_one_iff_adj.mpr hadj] at he
    simp at he
  have hs := card_le_card hsub
  have heq := card_erase_add_one hv
  change S.card ≤ (Gᶜ.neighborFinset v).card + 1
  omega

/-- Every edge among the remaining vertices dominates all remaining vertices. -/
def EdgesDominateAway (v : V) : Prop :=
  ∀ ⦃a b⦄, a ≠ v → b ≠ v → G.Adj a b →
    ∀ x, x ≠ v → G.Adj x a ∨ G.Adj x b

private theorem edgesDominateAway_of_count (v : V)
    (h : missingCount G ≤ evenCount G v) : EdgesDominateAway G v := by
  let A := Gᶜ.edgeFinset \ Gᶜ.incidenceFinset v
  have hcard : A.card ≤ 1 := by
    have heq := card_sdiff_add_card_eq_card (Gᶜ.incidenceFinset_subset v)
    rw [Gᶜ.card_incidenceFinset_eq_degree v] at heq
    have he := evenCount_le G v
    change Gᶜ.edgeFinset.card ≤ evenCount G v at h
    change (Gᶜ.edgeFinset \ Gᶜ.incidenceFinset v).card ≤ 1
    omega
  have missing {x y : V} (hx : x ≠ v) (hy : y ≠ v) (hne : x ≠ y)
      (hn : ¬ G.Adj x y) : s(x, y) ∈ A := by
    apply mem_sdiff.mpr
    constructor
    · exact SimpleGraph.mem_edgeFinset.mpr ((G.compl_adj x y).mpr ⟨hne, hn⟩)
    · rw [SimpleGraph.mem_incidenceFinset, SimpleGraph.mk'_mem_incidenceSet_iff]
      exact fun hi => hi.2.elim (Ne.symm hx) (Ne.symm hy)
  intro a b ha hb hab x hx
  by_contra! hnone
  obtain ⟨hxa, hxb⟩ := hnone
  have h1 : x ≠ a := fun e => hxb (e ▸ hab)
  have h2 : x ≠ b := fun e => hxa (e ▸ hab.symm)
  have heq := card_le_one.mp hcard _ (missing hx ha h1 hxa) _ (missing hx hb h2 hxb)
  rcases Sym2.eq_iff.mp heq with hh | hh
  · exact hab.ne hh.2
  · exact h2 hh.1

omit [Fintype V] in
/-- If deleting one vertex leaves a complete multipartite graph, every total dominating
set contains a total dominating pair. -/
theorem contains_dominating_pair (v : V) (hcore : EdgesDominateAway G v)
    {D : Finset V} (hD : TotalDominates G D) :
    ∃ P ⊆ D, P.card = 2 ∧ TotalDominates G P := by
  obtain ⟨a, haD, hva⟩ := hD v
  have makePair {p q : V} (hp : p ∈ D) (hq : q ∈ D) (hne : p ≠ q)
      (covers : ∀ x, G.Adj x p ∨ G.Adj x q) :
      ∃ P ⊆ D, P.card = 2 ∧ TotalDominates G P := by
    refine ⟨{p, q}, insert_subset hp (singleton_subset_iff.mpr hq), card_pair hne, ?_⟩
    intro x
    rcases covers x with h | h
    · exact ⟨p, by simp, h⟩
    · exact ⟨q, by simp, h⟩
  by_cases hex : ∃ b ∈ D, b ≠ v ∧ G.Adj a b
  · obtain ⟨b, hbD, hbv, hab⟩ := hex
    apply makePair haD hbD hab.ne
    intro x
    by_cases hx : x = v
    · exact Or.inl (hx ▸ hva)
    · exact hcore hva.ne' hbv hab x hx
  · obtain ⟨b, hbD, hab⟩ := hD a
    have hbv : b = v := by
      by_contra hne
      exact hex ⟨b, hbD, hne, hab⟩
    subst b
    apply makePair hbD haD hva.ne
    intro x
    by_cases hxa : G.Adj x a
    · exact Or.inr hxa
    · have hxv : x ≠ v := fun h => hxa (h ▸ hva)
      obtain ⟨y, hyD, hxy⟩ := hD x
      by_cases hyv : y = v
      · exact Or.inl (hyv ▸ hxy)
      · rcases hcore hxv hyv hxy a hva.ne' with hax | hay
        · exact (hxa hax.symm).elim
        · exact (hex ⟨y, hyD, hyv, hay⟩).elim

/-- The exact catalogue implication, together with the stronger cardinality conclusion. -/
theorem writtenOnTheWallII_318 (connected : G.Connected) (horder : 1 < Fintype.card V)
    (h : missingCount G ≤ maxEvenCount G) :
    WellTotallyDominated G ∧ (∃ D, TotalDominates G D ∧ D.card = 2) ∧
      ∀ D, MinimalTotal G D → D.card = 2 := by
  let _ : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp horder
  obtain ⟨v, _, hv⟩ := exists_mem_eq_sup univ univ_nonempty (evenCount G)
  have hcore := edgesDominateAway_of_count G v (h.trans_eq hv)
  have hmin : ∀ D, MinimalTotal G D → D.card = 2 := by
    intro D hD
    obtain ⟨P, hPD, htwo, hP⟩ := contains_dominating_pair G v hcore hD.1
    simpa only [hD.2 P hPD hP] using htwo
  have allVerts : TotalDominates G univ := by
    intro x
    obtain ⟨y, hxy⟩ := connected.preconnected.exists_adj_of_nontrivial x
    exact ⟨y, mem_univ _, hxy⟩
  obtain ⟨pair, _, htwo, hp⟩ := contains_dominating_pair G v hcore allVerts
  refine ⟨?_, ⟨pair, hp, htwo⟩, hmin⟩
  intro D hD E hE
  obtain ⟨P, hPE, htwo, _⟩ := contains_dominating_pair G v hcore hE
  rw [hmin D hD, ← htwo]
  exact card_le_card hPE

#print axioms writtenOnTheWallII_318

/-! ### Optimality of the integer threshold

The bowtie is two triangles sharing vertex 0. Its four missing edges exceed
the maximum even-distance count by one. It has minimal total dominating sets
of sizes two and four. This graph occurs in the exceptional family of Theorem 4.3
in [J. J. Gebendorfer, *Three Well-Total-Domination Conjectures*](https://www.researchgate.net/publication/411012117).
-/

def bowtieAdj (x y : Fin 5) : Prop :=
  x ≠ y ∧ (x = 0 ∨ y = 0 ∨ (x.val ≤ 2 ↔ y.val ≤ 2))

private instance : DecidableRel bowtieAdj :=
  fun x y => inferInstanceAs (Decidable
    (x ≠ y ∧ (x = 0 ∨ y = 0 ∨ (x.val ≤ 2 ↔ y.val ≤ 2))))

def bowtie : SimpleGraph (Fin 5) where
  Adj := bowtieAdj
  symm := ⟨by decide⟩
  loopless := ⟨by decide⟩

private instance : DecidableRel bowtie.Adj := inferInstanceAs (DecidableRel bowtieAdj)

private theorem center_adj : ∀ x : Fin 5, x ≠ 0 → bowtie.Adj x 0 := by decide

private theorem bowtie_connected : bowtie.Connected := by
  apply bowtie.connected_iff_exists_forall_reachable.mpr
  refine ⟨0, fun x => ?_⟩
  by_cases hx : x = 0
  · subst x
    exact SimpleGraph.Reachable.rfl
  · exact (center_adj x hx).symm.reachable

private def tableDist (x y : Fin 5) : ℕ :=
  if x = y then 0 else if bowtie.Adj x y then 1 else 2

private theorem bowtie_dist (x y : Fin 5) : bowtie.dist x y = tableDist x y := by
  by_cases h : x = y
  · subst y
    simp [tableDist]
  by_cases hxy : bowtie.Adj x y
  · simp [tableDist, h, hxy]
  have hx : x ≠ 0 := by
    rintro rfl
    exact hxy (center_adj y (Ne.symm h)).symm
  have hy : y ≠ 0 := by
    rintro rfl
    exact hxy (center_adj x h)
  have hd : bowtie.edist x y = 2 := SimpleGraph.edist_eq_two_iff.mpr
    ⟨h, hxy, 0, (bowtie.mem_commonNeighbors).mpr ⟨center_adj x hx, center_adj y hy⟩⟩
  rw [SimpleGraph.dist, hd]
  simp [tableDist, h, hxy]

private theorem bowtie_evenCount : maxEvenCount bowtie = 3 := by
  let row := fun x : Fin 5 => (univ.filter fun y => tableDist x y % 2 = 0).card
  calc
    maxEvenCount bowtie = univ.sup row := by
      apply sup_congr rfl
      intro x _
      unfold evenCount row
      congr 1
      ext y
      simp [bowtie_dist, Nat.even_iff]
    _ = 3 := by decide

private theorem bowtie_missing : missingCount bowtie = 4 := by
  let cross : Finset (Sym2 (Fin 5)) := {s(1, 3), s(1, 4), s(2, 3), s(2, 4)}
  unfold missingCount
  trans cross.card
  · apply congrArg Finset.card
    ext e
    induction e using Sym2.ind with
    | _ a b =>
      simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet,
        SimpleGraph.compl_adj, cross, mem_insert, mem_singleton, Sym2.eq_iff]
      decide +revert
  · decide

/-- The conjecture fails if the allowed number of missing edges is increased by one. -/
theorem sharpness : bowtie.Connected ∧ missingCount bowtie = 4 ∧ maxEvenCount bowtie = 3 ∧
    ¬ WellTotallyDominated bowtie := by
  refine ⟨bowtie_connected, bowtie_missing, bowtie_evenCount, ?_⟩
  let rim : Finset (Fin 5) := {1, 2, 3, 4}
  let pair : Finset (Fin 5) := {0, 1}
  have hr : MinimalTotal bowtie rim := by
    unfold MinimalTotal TotalDominates
    decide
  have hp : TotalDominates bowtie pair := by
    unfold TotalDominates
    decide
  intro hw
  have hle := hw rim hr pair hp
  have hbad : ¬ rim.card ≤ pair.card := by decide
  exact hbad hle

#print axioms sharpness

end
end Graffiti318
