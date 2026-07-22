/-
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0.
-/
import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.C217BitVecGraph
import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.C217BooleanGraph
import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.C217HamiltonDP
import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.C217RowFacts
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Maps
import Mathlib.Data.Fintype.EquivFin

/-!
# Soundness bridge for the regular C217 LRAT certificates
-/

namespace SimpleGraph.C217RegularCertificate

open Classical
open SimpleGraph
open SimpleGraph.C217BitVecGraph
open SimpleGraph.C217BooleanGraph
open SimpleGraph.C217HamiltonDP
open SimpleGraph.C217OrderBound
open SimpleGraph.C217RowFacts

variable {V W : Type*} [Fintype V] [DecidableEq V]

/-- Boolean certificate statement for a connected `k`-regular graph on `n`
vertices. -/
def RegularCertificate (n k : ℕ) : Prop :=
  ∀ bits : BitVec (n * n),
    connectedCutBool (graphOfBitVec bits) = true →
    degreeProfileBool (graphOfBitVec bits) (List.replicate n k) = true →
    hasHamiltonPathBool (graphOfBitVec bits) = true

/-- Relabel a graph along an equivalence. -/
def relabelIso (G : SimpleGraph V) (e : V ≃ W) :
    G ≃g e.simpleGraph G where
  __ := e
  map_rel_iff' := by
    simp [Equiv.simpleGraph]

/-- An equivalence gives a bijection between corresponding neighbor subtypes. -/
def neighborEquiv (G : SimpleGraph V) (e : V ≃ W) (v : V) :
    G.neighborSet v ≃ (e.simpleGraph G).neighborSet (e v) where
  toFun x := ⟨e x.1, by simpa [Equiv.simpleGraph] using x.2⟩
  invFun y := ⟨e.symm y.1, by simpa [Equiv.simpleGraph] using y.2⟩
  left_inv x := by ext; simp
  right_inv y := by ext; simp

/-- Relabeling preserves degree. -/
theorem degree_simpleGraph_apply
    (G : SimpleGraph V) (e : V ≃ W) (v : V) :
    (e.simpleGraph G).degree (e v) = G.degree v := by
  unfold SimpleGraph.degree
  exact Nat.card_congr (neighborEquiv G e v)

/-- A regular graph on `Fin n` passes the exact Boolean degree-profile test. -/
theorem degreeProfileBool_of_regular_fin
    {n k : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hreg : ∀ v, G.degree v = k) :
    degreeProfileBool G (List.replicate n k) = true := by
  apply Bool.and_eq_true.mpr
  constructor
  · simp
  · apply List.all_eq_true.mpr
    intro d hd
    simp [degreeMultiplicity, hreg]

/-- A valid finite Boolean certificate proves traceability on `Fin n`. -/
theorem isTraceable_fin_of_certificate
    {n k : ℕ} (cert : RegularCertificate n k)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : G.Connected) (hreg : ∀ v, G.degree v = k) :
    IsTraceable G := by
  let bits := bitVecOfGraph G
  have hrecover : graphOfBitVec bits = G := by
    simpa [bits] using graphOfBitVec_bitVecOfGraph_eq G
  have hconn : connectedCutBool (graphOfBitVec bits) = true := by
    rw [hrecover]
    exact connectedCutBool_of_connected hG
  have hprofile :
      degreeProfileBool (graphOfBitVec bits) (List.replicate n k) = true := by
    rw [hrecover]
    exact degreeProfileBool_of_regular_fin G hreg
  have hbool := cert bits hconn hprofile
  have htrace := isTraceable_of_hasHamiltonPathBool (graphOfBitVec bits) hbool
  simpa [hrecover] using htrace

/-- A finite regular certificate applies to an arbitrary finite vertex type
whose exact degree row is `k` repeated `n` times. -/
theorem isTraceable_of_regular_row_certificate
    {n k : ℕ} (hnpos : 0 < n) (cert : RegularCertificate n k)
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.Connected)
    (hrow : degreeSequence G = List.replicate n k) :
    IsTraceable G := by
  have hcard : Fintype.card V = n := by
    have h := card_eq_length_of_degreeSequence_eq G hrow
    simpa using h
  have hreg : ∀ v, G.degree v = k := by
    intro v
    have hmem := degree_mem_degreeSequence G v
    rw [hrow] at hmem
    simpa [hnpos.ne'] using hmem
  let e : V ≃ Fin n := Fintype.equivFinOfCardEq hcard
  let GF : SimpleGraph (Fin n) := e.simpleGraph G
  let iso : G ≃g GF := relabelIso G e
  have hGFconn : GF.Connected := by
    exact hG.map iso.toHom iso.surjective
  have hGFreg : ∀ i, GF.degree i = k := by
    intro i
    obtain ⟨v, rfl⟩ := e.surjective i
    rw [show GF = e.simpleGraph G by rfl, degree_simpleGraph_apply G e v]
    exact hreg v
  obtain ⟨a, b, p, hp⟩ :=
    isTraceable_fin_of_certificate cert GF hGFconn hGFreg
  let q := p.map iso.symm.toHom
  exact ⟨iso.symm a, iso.symm b, q, hp.map iso.symm.bijective⟩

#print axioms SimpleGraph.C217RegularCertificate.degree_simpleGraph_apply
#print axioms SimpleGraph.C217RegularCertificate.isTraceable_fin_of_certificate
#print axioms SimpleGraph.C217RegularCertificate.isTraceable_of_regular_row_certificate

end SimpleGraph.C217RegularCertificate
