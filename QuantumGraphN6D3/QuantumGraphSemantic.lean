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

import FormalConjectures.Paper.MonochromaticQuantumGraph
import Mathlib.Data.ZMod.Basic
import Std.Sat.CNF.Relabel
import Std.Tactic.BVDecide.Reflect
import QuantumGraphCompactLRAT

/-!
# Semantic SAT certificate for the `N = 6`, `D = 3` quantum-graph obstruction

This file gives the SAT variables semantic types, checks that their numerical
encoding is exactly the independently generated DIMACS instance, and checks
the corresponding LRAT certificate with Lean's proved reflected checker.
-/

open Std Sat
open Std.Tactic.BVDecide
open MonochromaticQuantumGraph

namespace QuantumGraphSemantic

open QuantumGraphCompactLRAT

abbrev Clause := CNF.Clause Nat

def endpoints : Array (Nat × Nat) := #[
  (0, 1), (0, 2), (0, 3), (0, 4), (0, 5),
  (1, 2), (1, 3), (1, 4), (1, 5),
  (2, 3), (2, 4), (2, 5),
  (3, 4), (3, 5), (4, 5)
]

def matchingEdges : Array (Array Nat) := #[
  #[0, 9, 14], #[0, 10, 13], #[0, 11, 12],
  #[1, 6, 14], #[1, 7, 13], #[1, 8, 12],
  #[2, 5, 14], #[2, 7, 11], #[2, 8, 10],
  #[3, 5, 13], #[3, 6, 11], #[3, 8, 9],
  #[4, 5, 12], #[4, 6, 10], #[4, 7, 9]
]

def colour (colouring vertex : Nat) : Nat :=
  colouring / (3 ^ (5 - vertex)) % 3

def supportVar (edge left right : Nat) : Nat :=
  9 * edge + 3 * left + right

def natPos (varId : Nat) : Literal Nat := (varId, true)
def natNeg (varId : Nat) : Literal Nat := (varId, false)

/-- The exact procedural encoder used to generate the DIMACS files. -/
def buildCaseCNF (mask : Nat) : CNF Nat := Id.run do
  let mut cnf : Array Clause := #[]
  let mut nextVariable := 135
  for colouringIndex in [:729] do
    let mut monomials : Array Nat := #[]
    for matchingIndex in [:15] do
      let matching := matchingEdges[matchingIndex]!
      let mut factors : Array Nat := #[]
      for factorIndex in [:3] do
        let edge := matching[factorIndex]!
        let pair := endpoints[edge]!
        factors := factors.push <|
          supportVar edge (colour colouringIndex pair.1) (colour colouringIndex pair.2)
      let output := nextVariable
      nextVariable := nextVariable + 1
      cnf := cnf.push [natNeg output, natPos factors[0]!]
      cnf := cnf.push [natNeg output, natPos factors[1]!]
      cnf := cnf.push [natNeg output, natPos factors[2]!]
      cnf := cnf.push [natPos output, natNeg factors[0]!, natNeg factors[1]!, natNeg factors[2]!]
      monomials := monomials.push output
    let mut parity := monomials[0]!
    for position in [1:15] do
      let monomial := monomials[position]!
      let output := nextVariable
      nextVariable := nextVariable + 1
      cnf := cnf.push [natNeg parity, natNeg monomial, natNeg output]
      cnf := cnf.push [natPos parity, natPos monomial, natNeg output]
      cnf := cnf.push [natPos parity, natNeg monomial, natPos output]
      cnf := cnf.push [natNeg parity, natPos monomial, natPos output]
      parity := output
    let target := colouringIndex == 0 || colouringIndex == 364 || colouringIndex == 728
    cnf := cnf.push [if target then natPos parity else natNeg parity]
  for edge in [:15] do
    let varId := supportVar edge 0 0
    cnf := cnf.push [if mask.testBit edge then natPos varId else natNeg varId]
  if nextVariable != 21276 then panic! "unexpected variable count"
  return cnf.toList

inductive Var where
  | support (edge : Fin 15) (left right : Fin 3)
  | monomial (colouring : Fin 729) (matching : Fin 15)
  /-- `position = k` is the xor of monomials `0, ..., k + 1`. -/
  | parity (colouring : Fin 729) (position : Fin 14)
deriving DecidableEq, Fintype

def varPos (v : Var) : Literal Var := (v, true)
def varNeg (v : Var) : Literal Var := (v, false)

def encodeVar : Var → Nat
  | .support edge left right => supportVar edge left right
  | .monomial colouring matching => 135 + colouring * 29 + matching
  | .parity colouring position => 135 + colouring * 29 + 15 + position

theorem encodeVar_injective : Function.Injective encodeVar := by
  native_decide

def endpointsFin : Array (Fin 6 × Fin 6) := #[
  (0, 1), (0, 2), (0, 3), (0, 4), (0, 5),
  (1, 2), (1, 3), (1, 4), (1, 5),
  (2, 3), (2, 4), (2, 5),
  (3, 4), (3, 5), (4, 5)
]

def matchingEdgesFin : Array (Array (Fin 15)) := #[
  #[0, 9, 14], #[0, 10, 13], #[0, 11, 12],
  #[1, 6, 14], #[1, 7, 13], #[1, 8, 12],
  #[2, 5, 14], #[2, 7, 11], #[2, 8, 10],
  #[3, 5, 13], #[3, 6, 11], #[3, 8, 9],
  #[4, 5, 12], #[4, 6, 10], #[4, 7, 9]
]

def decodedColour (colouring : Fin 729) (vertex : Fin 6) : Fin 3 :=
  ⟨colour colouring vertex, Nat.mod_lt _ (by decide)⟩

def factorVar (colouring : Fin 729) (matching : Fin 15) (factor : Fin 3) : Var :=
  let matchingData := matchingEdgesFin[matching]!
  let edge := matchingData[factor]!
  let pair := endpointsFin[edge]!
  .support edge (decodedColour colouring pair.1) (decodedColour colouring pair.2)

def and3CNF (output a b c : Var) : CNF Var := [
  [varNeg output, varPos a],
  [varNeg output, varPos b],
  [varNeg output, varPos c],
  [varPos output, varNeg a, varNeg b, varNeg c]
]

def monomialCNF (colouring : Fin 729) (matching : Fin 15) : CNF Var :=
  and3CNF (.monomial colouring matching)
    (factorVar colouring matching 0)
    (factorVar colouring matching 1)
    (factorVar colouring matching 2)

def xor2CNF (output a b : Var) : CNF Var := [
  [varNeg a, varNeg b, varNeg output],
  [varPos a, varPos b, varNeg output],
  [varPos a, varNeg b, varPos output],
  [varNeg a, varPos b, varPos output]
]

def parityCNF (colouring : Fin 729) (position : Fin 14) : CNF Var :=
  let previous := if h : position = 0 then
      Var.monomial colouring 0
    else
      Var.parity colouring ⟨position - 1, by omega⟩
  let nextMonomial : Fin 15 := ⟨position + 1, by omega⟩
  xor2CNF (.parity colouring position) previous (.monomial colouring nextMonomial)

def target (colouring : Fin 729) : Bool :=
  colouring = 0 || colouring = 364 || colouring = 728

def targetCNF (colouring : Fin 729) : CNF Var :=
  [[if target colouring then varPos (.parity colouring 13)
    else varNeg (.parity colouring 13)]]

def equationCNF (colouring : Fin 729) : CNF Var :=
  (List.ofFn (monomialCNF colouring)).flatten ++
  (List.ofFn (parityCNF colouring)).flatten ++
  targetCNF colouring

def fixedSupportCNF (mask : Nat) : CNF Var :=
  List.ofFn fun edge : Fin 15 =>
    [if mask.testBit edge then varPos (.support edge 0 0)
      else varNeg (.support edge 0 0)]

def semanticCaseCNF (mask : Nat) : CNF Var :=
  (List.ofFn equationCNF).flatten ++ fixedSupportCNF mask

def case00CNF : CNF Nat := buildCaseCNF 0x4024
def semanticCase00CNF : CNF Var := semanticCaseCNF 0x4024

theorem semantic_encoding_case00 :
    CNF.relabel encodeVar semanticCase00CNF = case00CNF := by
  native_decide

def case00Certificate : String :=
  include_str "certificates" / "case_00.clrat"

theorem case00_unsat : case00CNF.Unsat := by
  apply verifyCompactCert_correct case00CNF case00Certificate
  native_decide

theorem semantic_case00_unsat : semanticCase00CNF.Unsat := by
  rw [← CNF.unsat_relabel_iff (fun _ _ h => encodeVar_injective h)]
  rw [semantic_encoding_case00]
  exact case00_unsat

/-! ## Meaning of the Tseitin variables and clauses -/

def bit (x : ZMod 2) : Bool := decide (x = 1)

def supportValue (weights : WeightsN 6 3 (ZMod 2))
    (edge : Fin 15) (left right : Fin 3) : Bool :=
  let pair := endpointsFin[edge]!
  bit (weights (mkEdge pair.1 pair.2 left right))

def factorValue (weights : WeightsN 6 3 (ZMod 2))
    (colouring : Fin 729) (matching : Fin 15) (factor : Fin 3) : Bool :=
  let matchingData := matchingEdgesFin[matching]!
  let edge := matchingData[factor]!
  let pair := endpointsFin[edge]!
  supportValue weights edge (decodedColour colouring pair.1) (decodedColour colouring pair.2)

def monomialValue (weights : WeightsN 6 3 (ZMod 2))
    (colouring : Fin 729) (matching : Fin 15) : Bool :=
  factorValue weights colouring matching 0 &&
  factorValue weights colouring matching 1 &&
  factorValue weights colouring matching 2

def fin15 (n : Nat) : Fin 15 := ⟨n % 15, Nat.mod_lt _ (by decide)⟩

/-- Xor of monomials `0, ..., position`; only positions through `14` are used. -/
def parityValueNat (weights : WeightsN 6 3 (ZMod 2))
    (colouring : Fin 729) : Nat → Bool
  | 0 => monomialValue weights colouring 0
  | position + 1 =>
      Bool.xor (parityValueNat weights colouring position)
        (monomialValue weights colouring (fin15 (position + 1)))

def semanticAssignment (weights : WeightsN 6 3 (ZMod 2)) : Var → Bool
  | .support edge left right => supportValue weights edge left right
  | .monomial colouring matching => monomialValue weights colouring matching
  | .parity colouring position => parityValueNat weights colouring (position + 1)

theorem assignment_factorVar (weights : WeightsN 6 3 (ZMod 2))
    (colouring : Fin 729) (matching : Fin 15) (factor : Fin 3) :
    semanticAssignment weights (factorVar colouring matching factor) =
      factorValue weights colouring matching factor := by
  simp [factorVar, factorValue, semanticAssignment]

theorem and3CNF_eval (assignment : Var → Bool) (output a b c : Var)
    (h : assignment output = (assignment a && assignment b && assignment c)) :
    CNF.eval assignment (and3CNF output a b c) = true := by
  simp only [and3CNF, CNF.eval_cons, CNF.eval_nil, CNF.Clause.eval_cons,
    CNF.Clause.eval_nil, Bool.or_false, Bool.and_true, varNeg, varPos]
  rw [h]
  cases assignment a <;> cases assignment b <;> cases assignment c <;> decide

theorem xor2CNF_eval (assignment : Var → Bool) (output a b : Var)
    (h : assignment output = Bool.xor (assignment a) (assignment b)) :
    CNF.eval assignment (xor2CNF output a b) = true := by
  simp only [xor2CNF, CNF.eval_cons, CNF.eval_nil, CNF.Clause.eval_cons,
    CNF.Clause.eval_nil, Bool.or_false, Bool.and_true, varNeg, varPos]
  rw [h]
  cases assignment a <;> cases assignment b <;> decide

theorem monomialCNF_eval (weights : WeightsN 6 3 (ZMod 2))
    (colouring : Fin 729) (matching : Fin 15) :
    CNF.eval (semanticAssignment weights) (monomialCNF colouring matching) = true := by
  apply and3CNF_eval
  change monomialValue weights colouring matching = _
  rw [assignment_factorVar weights colouring matching 0,
    assignment_factorVar weights colouring matching 1,
    assignment_factorVar weights colouring matching 2]
  rfl

theorem parityCNF_eval (weights : WeightsN 6 3 (ZMod 2))
    (colouring : Fin 729) (position : Fin 14) :
    CNF.eval (semanticAssignment weights) (parityCNF colouring position) = true := by
  apply xor2CNF_eval
  change parityValueNat weights colouring (position + 1) = Bool.xor
    (semanticAssignment weights
      (if h : position = 0 then Var.monomial colouring 0
       else Var.parity colouring ⟨position - 1, by omega⟩))
    (monomialValue weights colouring ⟨position + 1, by omega⟩)
  split
  · rename_i hzero
    rw [hzero]
    rfl
  · rename_i hne
    have hprevious :
        semanticAssignment weights
            (Var.parity colouring ⟨position - 1, by omega⟩) =
          parityValueNat weights colouring position := by
      simp only [semanticAssignment]
      congr 1
      omega
    rw [hprevious, parityValueNat]
    congr 1
    apply congrArg (monomialValue weights colouring)
    apply Fin.ext
    simp [fin15]
    omega

theorem eval_flatten_of_forall (assignment : α → Bool) (formulas : List (CNF α))
    (h : ∀ formula ∈ formulas, CNF.eval assignment formula = true) :
    CNF.eval assignment formulas.flatten = true := by
  induction formulas with
  | nil => rfl
  | cons formula formulas ih =>
      rw [List.flatten_cons, CNF.eval_append, h formula (by simp), ih]
      · rfl
      · intro other hother
        exact h other (by simp [hother])

theorem equationCNF_eval (weights : WeightsN 6 3 (ZMod 2))
    (colouring : Fin 729)
    (equation : parityValueNat weights colouring 14 = target colouring) :
    CNF.eval (semanticAssignment weights) (equationCNF colouring) = true := by
  rw [equationCNF, CNF.eval_append, CNF.eval_append]
  simp only [Bool.and_eq_true]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · apply eval_flatten_of_forall
    intro formula hformula
    rw [List.mem_ofFn] at hformula
    obtain ⟨matching, rfl⟩ := hformula
    exact monomialCNF_eval weights colouring matching
  · apply eval_flatten_of_forall
    intro formula hformula
    rw [List.mem_ofFn] at hformula
    obtain ⟨position, rfl⟩ := hformula
    exact parityCNF_eval weights colouring position
  · cases htarget : target colouring <;>
      simp [targetCNF, htarget, semanticAssignment, varPos, varNeg] at equation ⊢ <;>
      assumption

def BooleanEquationSystem (weights : WeightsN 6 3 (ZMod 2)) : Prop :=
  ∀ colouring : Fin 729, parityValueNat weights colouring 14 = target colouring

def HasDiagonalMask (weights : WeightsN 6 3 (ZMod 2)) (mask : Nat) : Prop :=
  ∀ edge : Fin 15, supportValue weights edge 0 0 = mask.testBit edge

theorem fixedSupportCNF_eval (weights : WeightsN 6 3 (ZMod 2)) (mask : Nat)
    (hmask : HasDiagonalMask weights mask) :
    CNF.eval (semanticAssignment weights) (fixedSupportCNF mask) = true := by
  simp only [CNF.eval, fixedSupportCNF, List.all_eq_true, List.mem_ofFn]
  intro clause
  rintro ⟨edge, rfl⟩
  specialize hmask edge
  cases hbit : mask.testBit edge <;>
    simp [hbit, semanticAssignment, varPos, varNeg] at hmask ⊢ <;>
    assumption

theorem semanticCaseCNF_sat (weights : WeightsN 6 3 (ZMod 2)) (mask : Nat)
    (equations : BooleanEquationSystem weights) (hmask : HasDiagonalMask weights mask) :
    CNF.eval (semanticAssignment weights) (semanticCaseCNF mask) = true := by
  rw [semanticCaseCNF, CNF.eval_append, Bool.and_eq_true]
  constructor
  · apply eval_flatten_of_forall
    intro formula hformula
    rw [List.mem_ofFn] at hformula
    obtain ⟨colouring, rfl⟩ := hformula
    exact equationCNF_eval weights colouring (equations colouring)
  · exact fixedSupportCNF_eval weights mask hmask

theorem no_boolean_solution_case00 :
    ¬ ∃ weights : WeightsN 6 3 (ZMod 2),
      BooleanEquationSystem weights ∧ HasDiagonalMask weights 0x4024 := by
  rintro ⟨weights, equations, hmask⟩
  have := semantic_case00_unsat (semanticAssignment weights)
  change CNF.eval (semanticAssignment weights) (semanticCaseCNF 0x4024) = false at this
  rw [semanticCaseCNF_sat weights 0x4024 equations hmask] at this
  contradiction

/-! ## Arithmetic interpretation over `ZMod 2` -/

@[simp] theorem bit_zero : bit (0 : ZMod 2) = false := by native_decide
@[simp] theorem bit_one : bit (1 : ZMod 2) = true := by native_decide

theorem bit_mul (x y : ZMod 2) : bit (x * y) = (bit x && bit y) := by
  fin_cases x <;> fin_cases y <;> native_decide

theorem bit_add (x y : ZMod 2) : bit (x + y) = Bool.xor (bit x) (bit y) := by
  fin_cases x <;> fin_cases y <;> native_decide

def factorWeight (weights : WeightsN 6 3 (ZMod 2))
    (colouring : Fin 729) (matching : Fin 15) (factor : Fin 3) : ZMod 2 :=
  let matchingData := matchingEdgesFin[matching]!
  let edge := matchingData[factor]!
  let pair := endpointsFin[edge]!
  weights (mkEdge pair.1 pair.2
    (decodedColour colouring pair.1) (decodedColour colouring pair.2))

def monomialWeight (weights : WeightsN 6 3 (ZMod 2))
    (colouring : Fin 729) (matching : Fin 15) : ZMod 2 :=
  factorWeight weights colouring matching 0 *
  factorWeight weights colouring matching 1 *
  factorWeight weights colouring matching 2

def partialSumNat (weights : WeightsN 6 3 (ZMod 2))
    (colouring : Fin 729) : Nat → ZMod 2
  | 0 => monomialWeight weights colouring 0
  | position + 1 =>
      partialSumNat weights colouring position +
        monomialWeight weights colouring (fin15 (position + 1))

theorem monomialValue_eq_bit (weights : WeightsN 6 3 (ZMod 2))
    (colouring : Fin 729) (matching : Fin 15) :
    monomialValue weights colouring matching = bit (monomialWeight weights colouring matching) := by
  simp only [monomialValue, factorValue, supportValue, factorWeight, monomialWeight]
  rw [bit_mul, bit_mul]

theorem parityValueNat_eq_bit_partialSumNat (weights : WeightsN 6 3 (ZMod 2))
    (colouring : Fin 729) : ∀ position,
    parityValueNat weights colouring position = bit (partialSumNat weights colouring position) := by
  intro position
  induction position with
  | zero => exact monomialValue_eq_bit weights colouring 0
  | succ position ih =>
      rw [parityValueNat, partialSumNat, bit_add, ← ih,
        ← monomialValue_eq_bit weights colouring]

def explicitPmSum6 (weights : WeightsN 6 3 (ZMod 2))
    (colouring : V 6 → Fin 3) : ZMod 2 :=
  let w (u v : V 6) := weights (mkEdge u v (colouring u) (colouring v))
  w 0 1 * w 2 3 * w 4 5 +
  w 0 1 * w 2 4 * w 3 5 +
  w 0 1 * w 2 5 * w 3 4 +
  w 0 2 * w 1 3 * w 4 5 +
  w 0 2 * w 1 4 * w 3 5 +
  w 0 2 * w 1 5 * w 3 4 +
  w 0 3 * w 1 2 * w 4 5 +
  w 0 3 * w 1 4 * w 2 5 +
  w 0 3 * w 1 5 * w 2 4 +
  w 0 4 * w 1 2 * w 3 5 +
  w 0 4 * w 1 3 * w 2 5 +
  w 0 4 * w 1 5 * w 2 3 +
  w 0 5 * w 1 2 * w 3 4 +
  w 0 5 * w 1 3 * w 2 4 +
  w 0 5 * w 1 4 * w 2 3

theorem pmSumN_six_eq_explicit (weights : WeightsN 6 3 (ZMod 2))
    (colouring : V 6 → Fin 3) :
    pmSumN 6 3 weights colouring = explicitPmSum6 weights colouring := by
  simp [pmSumN, pmSumList, pmSumListAux, vertices, explicitPmSum6, mkEdge, mul_assoc]
  noncomm_ring

theorem partialSumNat_fourteen_eq_explicit (weights : WeightsN 6 3 (ZMod 2))
    (colouring : Fin 729) :
    partialSumNat weights colouring 14 = explicitPmSum6 weights (decodedColour colouring) := by
  simp [partialSumNat, fin15, monomialWeight, factorWeight, matchingEdgesFin,
    endpointsFin, explicitPmSum6]

theorem decodedColour_allEqual_iff_target :
    ∀ colouring : Fin 729,
      allEqual (decodedColour colouring) ↔ target colouring = true := by
  native_decide

theorem eqSystem_zmod2_to_boolean (weights : WeightsN 6 3 (ZMod 2))
    (equations : EqSystemN 6 3 weights) : BooleanEquationSystem weights := by
  intro colouring
  rw [parityValueNat_eq_bit_partialSumNat,
    partialSumNat_fourteen_eq_explicit]
  have h := equations (decodedColour colouring)
  rw [pmSumN_six_eq_explicit] at h
  have hbit := congrArg bit h
  split at h <;> simp_all [decodedColour_allEqual_iff_target]

theorem no_eqSystem_zmod2_case00 :
    ¬ ∃ weights : WeightsN 6 3 (ZMod 2),
      EqSystemN 6 3 weights ∧ HasDiagonalMask weights 0x4024 := by
  rintro ⟨weights, equations, hmask⟩
  exact no_boolean_solution_case00
    ⟨weights, eqSystem_zmod2_to_boolean weights equations, hmask⟩

end QuantumGraphSemantic
