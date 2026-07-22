/-
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0.
-/
import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.C217FiniteCertificate
import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.C217OrderBound
import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.ChvatalPath
import Lean.Elab.Tactic.Omega

/-!
# Graph bridge for the C217 finite degree certificate

This module translates between the graph's sorted degree sequence and the
count-form Chvátal predicate used by the exhaustive finite certificate.
-/

namespace SimpleGraph.C217DegreeBridge

open Classical
open C217FiniteCertificate
open C217OrderBound
open C217OrderCertificate

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- A connected graph on a nontrivial vertex type has no zero-degree vertex. -/
lemma degree_pos_of_connected {G : SimpleGraph α} [DecidableRel G.Adj]
    [Nontrivial α] (hG : G.Connected) (v : α) : 0 < G.degree v := by
  obtain ⟨w, hw⟩ := exists_ne v
  exact (hG.preconnected v w).degree_pos_left hw

/-- Counting entries of the sorted degree sequence below a threshold is the
same as counting graph vertices below that threshold. -/
lemma degreeSequence_countP_lt (G : SimpleGraph α) [DecidableRel G.Adj] (k : ℕ) :
    (degreeSequence G).countP (fun d => decide (d < k)) =
      (lowDegreeFinset G k).card := by
  have hperm : degreeSequence G ~
      (Finset.univ.toList.map fun v => G.degree v) := by
    rw [← Multiset.coe_eq_coe]
    simp [degreeSequence]
  calc
    (degreeSequence G).countP (fun d => decide (d < k)) =
        (Finset.univ.toList.map fun v => G.degree v).countP
          (fun d => decide (d < k)) := hperm.countP_eq _
    _ = (Finset.univ.toList.filter fun v => decide (G.degree v < k)).length := by
      rw [List.countP_eq_length_filter, List.filter_map, List.length_map]
    _ = (lowDegreeFinset G k).card := by
      rw [← List.toFinset_card_of_nodup ((Finset.nodup_toList _).filter _)]
      simp [lowDegreeFinset]

/-- Decode the Boolean count-form certificate into the graph-theoretic
Chvátal path condition. -/
theorem chvatalPathCondition_of_countHolds
    (G : SimpleGraph α) [DecidableRel G.Adj]
    (hcount : chvatalCountHolds (degreeSequence G) = true) :
    ChvatalPathCondition G := by
  intro i hi hmid
  have hiRange : i ∈ List.range ((degreeSequence G).length + 1) := by
    simp only [List.mem_range]
    rw [degreeSequence_length]
    omega
  have hall :
      (List.range ((degreeSequence G).length + 1)).all (fun i =>
        if 1 ≤ i ∧ 2 * i < (degreeSequence G).length + 1 then
          decide (((degreeSequence G).countP fun d => d < i) < i ∨
            ((degreeSequence G).countP fun d => d <
              (degreeSequence G).length - i) ≤ (degreeSequence G).length - i)
        else true) = true := by
    simpa [chvatalCountHolds] using hcount
  have hitem := List.all_eq_true.mp hall i hiRange
  rw [degreeSequence_length] at hitem
  simp only [hi, hmid, and_self, if_true, decide_eq_true_eq] at hitem
  simpa [degreeSequence_countP_lt] using hitem

/-- Under the C217 exceptional hypotheses, the finite certificate yields either
Chvátal's condition or membership in the exact forty-row remainder. -/
theorem chvatal_or_exceptional
    (G : SimpleGraph α) [DecidableRel G.Adj] [Nontrivial α]
    (hG : G.Connected) (hres : residue G = 2)
    (hdeg : ∀ v, G.degree v ≤ 6) :
    ChvatalPathCondition G ∨ degreeSequence G ∈ exceptionalSequences := by
  let s := degreeSequence G
  have hsres : residueAux s = 2 := by
    simpa [s, degreeSequence, residue] using hres
  have hsbound : ∀ d ∈ s, d ≤ 6 := degreeSequence_bound G 6 hdeg
  have hssorted : s.Pairwise (· ≥ ·) := degreeSequence_pairwise G
  have hspos : ∀ d ∈ s, 1 ≤ d := by
    intro d hd
    have hd' : d ∈ Finset.univ.val.map (fun v => G.degree v) := by
      simpa [s, degreeSequence] using hd
    obtain ⟨v, _, rfl⟩ := Multiset.mem_map.mp hd'
    exact degree_pos_of_connected hG v
  have hlen14 : s.length ≤ 14 := by
    simpa [s] using card_le_fourteen_of_residue_eq_two_of_degree_le_six G hres hdeg
  have hlen2 : 2 ≤ s.length := by
    have htwo : 2 ≤ Fintype.card α := by
      have hone := Fintype.one_lt_card (α := α)
      omega
    simpa [s] using htwo
  let m := cappedSym s
  have hm : degreeList m = s := degreeList_cappedSym_eq s hsbound hssorted
  have hclass : classified s = true := by
    have h := classify_order_two_to_fourteen hlen2 hlen14 m
    simpa [hm] using h
  have hpositive : s.all (fun d => decide (1 ≤ d)) = true :=
    List.all_eq_true.mpr fun d hd => by simpa using hspos d hd
  have hor : chvatalCountHolds s = true ∨ s ∈ exceptionalSequences := by
    have h := hclass
    simp [classified, hpositive, hsres] at h
    exact h
  rcases hor with hch | hex
  · left
    exact chvatalPathCondition_of_countHolds G (by simpa [s] using hch)
  · exact Or.inr (by simpa [s] using hex)

#print axioms SimpleGraph.C217DegreeBridge.degreeSequence_countP_lt
#print axioms SimpleGraph.C217DegreeBridge.chvatalPathCondition_of_countHolds
#print axioms SimpleGraph.C217DegreeBridge.chvatal_or_exceptional

end SimpleGraph.C217DegreeBridge
