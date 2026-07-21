import QuantumGraphOrbitData
import Mathlib.Data.BitVec

/-!
# Vertex-permutation and orbit bridge for the quantum-graph obstruction
-/

open MonochromaticQuantumGraph
open scoped BigOperators

namespace QuantumGraphOrbitBridge

open QuantumGraphSemantic QuantumGraphOrbitData

abbrev Mask := BitVec 15

def tableEntry (table : Array (Array Nat)) (row column : Nat) : Nat :=
  let data := table[row]!
  data[column]!

def forwardVertex (permutation : Fin 720) (vertex : Fin 6) : Fin 6 :=
  Fin.ofNat 6 (tableEntry permutationTable permutation vertex)

def inverseVertex (permutation : Fin 720) (vertex : Fin 6) : Fin 6 :=
  Fin.ofNat 6 (tableEntry inversePermutationTable permutation vertex)

def edgeAction (permutation : Fin 720) (edge : Fin 15) : Fin 15 :=
  Fin.ofNat 15 (tableEntry edgeActionTable permutation edge)

def matchingAction (permutation : Fin 720) (matching : Fin 15) : Fin 15 :=
  Fin.ofNat 15 (tableEntry matchingActionTable permutation matching)

def sortedPair (u v : Fin 6) : Fin 6 × Fin 6 :=
  if u < v then (u, v) else (v, u)

theorem inverse_forward : ∀ permutation vertex,
    inverseVertex permutation (forwardVertex permutation vertex) = vertex := by
  native_decide

theorem forward_inverse : ∀ permutation vertex,
    forwardVertex permutation (inverseVertex permutation vertex) = vertex := by
  native_decide

theorem edgeAction_endpoints : ∀ permutation edge,
    endpointsFin[(edgeAction permutation edge).val]! =
      let pair := endpointsFin[edge.val]!
      sortedPair (forwardVertex permutation pair.1) (forwardVertex permutation pair.2) := by
  native_decide

theorem edgeAction_injective : ∀ permutation,
    Function.Injective (edgeAction permutation) := by
  native_decide

theorem matchingAction_injective : ∀ permutation,
    Function.Injective (matchingAction permutation) := by
  native_decide

def matchingSet (matching : Fin 15) : Finset (Fin 15) :=
  matchingEdgesFin[matching.val]!.toList.toFinset

theorem matchingSet_action : ∀ permutation matching,
    matchingSet (matchingAction permutation matching) =
      (matchingSet matching).image (edgeAction permutation) := by
  native_decide

def packBits (bits : Fin 15 → Bool) : Mask :=
  BitVec.ofNat 15 <| ∑ edge : Fin 15, if bits edge then 2 ^ edge.val else 0

theorem packBits_get : ∀ bits : Fin 15 → Bool, ∀ edge : Fin 15,
    (packBits bits).getLsbD edge.val = bits edge := by
  native_decide

def pullMask (permutation : Fin 720) (mask : Mask) : Mask :=
  packBits fun edge => mask.getLsbD (edgeAction permutation edge).val

@[simp] theorem pullMask_get (permutation : Fin 720) (mask : Mask) (edge : Fin 15) :
    (pullMask permutation mask).getLsbD edge.val =
      mask.getLsbD (edgeAction permutation edge).val := by
  exact packBits_get _ _

def representativeMask (caseIndex : Fin 47) : Mask :=
  BitVec.ofNat 15 (representativeTable[caseIndex.val]!)

def classificationCode (mask : Mask) : Nat :=
  let row := classificationTable[mask.toNat / 128]!
  row[mask.toNat % 128]!

def classificationCase (mask : Mask) : Fin 47 :=
  Fin.ofNat 47 (classificationCode mask / 720)

def classificationPermutation (mask : Mask) : Fin 720 :=
  Fin.ofNat 720 (classificationCode mask % 720)

def matchingPresent (mask : Mask) (matching : Fin 15) : Bool :=
  matchingEdgesFin[matching.val]!.all fun edge => mask.getLsbD edge.val

def oddPerfectMatchingParity (mask : Mask) : Bool :=
  (List.ofFn (matchingPresent mask)).foldl Bool.xor false

theorem classification_correct : ∀ mask : Mask,
    oddPerfectMatchingParity mask = true →
      pullMask (classificationPermutation mask) mask =
        representativeMask (classificationCase mask) := by
  native_decide

/- ## Relabeling weights and the perfect-matching sum -/

def pullWeights (permutation : Fin 720) (weights : WeightsN 6 3 (ZMod 2)) :
    WeightsN 6 3 (ZMod 2) := fun edge =>
  let u := forwardVertex permutation edge.u
  let v := forwardVertex permutation edge.v
  if u < v then
    weights (mkEdge u v edge.i edge.j)
  else
    weights (mkEdge v u edge.j edge.i)

def reindexColouring (permutation : Fin 720) (colouring : V 6 → Fin 3) :
    V 6 → Fin 3 := fun vertex => colouring (inverseVertex permutation vertex)

def edgeWeight (weights : WeightsN 6 3 (ZMod 2))
    (colouring : V 6 → Fin 3) (edge : Fin 15) : ZMod 2 :=
  let pair := endpointsFin[edge.val]!
  weights (mkEdge pair.1 pair.2 (colouring pair.1) (colouring pair.2))

def matchingProduct (weights : WeightsN 6 3 (ZMod 2))
    (colouring : V 6 → Fin 3) (matching : Fin 15) : ZMod 2 :=
  ∏ edge ∈ matchingSet matching, edgeWeight weights colouring edge

def enumeratedPmSum (weights : WeightsN 6 3 (ZMod 2))
    (colouring : V 6 → Fin 3) : ZMod 2 :=
  ∑ matching : Fin 15, matchingProduct weights colouring matching

theorem forwardVertex_injective (permutation : Fin 720) :
    Function.Injective (forwardVertex permutation) := by
  intro u v h
  have := congrArg (inverseVertex permutation) h
  simpa [inverse_forward] using this

theorem matchingAction_bijective : ∀ permutation,
    Function.Bijective (matchingAction permutation) := by
  native_decide

theorem edgeWeight_pull (permutation : Fin 720)
    (weights : WeightsN 6 3 (ZMod 2)) (colouring : V 6 → Fin 3)
    (edge : Fin 15) :
    edgeWeight (pullWeights permutation weights) colouring edge =
      edgeWeight weights (reindexColouring permutation colouring)
        (edgeAction permutation edge) := by
  simp only [edgeWeight, pullWeights, reindexColouring]
  rw [edgeAction_endpoints]
  simp only [sortedPair, mkEdge]
  split_ifs with h
  · simp [h, inverse_forward]
  · simp [h, inverse_forward]

theorem matchingProduct_pull (permutation : Fin 720)
    (weights : WeightsN 6 3 (ZMod 2)) (colouring : V 6 → Fin 3)
    (matching : Fin 15) :
    matchingProduct (pullWeights permutation weights) colouring matching =
      matchingProduct weights (reindexColouring permutation colouring)
        (matchingAction permutation matching) := by
  unfold matchingProduct
  rw [matchingSet_action]
  rw [Finset.prod_image]
  · simp_rw [edgeWeight_pull]
  · exact (edgeAction_injective permutation).injOn

theorem enumeratedPmSum_pull (permutation : Fin 720)
    (weights : WeightsN 6 3 (ZMod 2)) (colouring : V 6 → Fin 3) :
    enumeratedPmSum (pullWeights permutation weights) colouring =
      enumeratedPmSum weights (reindexColouring permutation colouring) := by
  simp only [enumeratedPmSum]
  simp_rw [matchingProduct_pull]
  exact (matchingAction_bijective permutation).sum_comp
    (matchingProduct weights (reindexColouring permutation colouring))

theorem enumeratedPmSum_eq_explicit (weights : WeightsN 6 3 (ZMod 2))
    (colouring : V 6 → Fin 3) :
    enumeratedPmSum weights colouring = explicitPmSum6 weights colouring := by
  simp [enumeratedPmSum, matchingProduct, matchingSet, edgeWeight,
    matchingEdgesFin, endpointsFin, explicitPmSum6, Fin.sum_univ_succ]
  ring

theorem explicitPmSum6_pull (permutation : Fin 720)
    (weights : WeightsN 6 3 (ZMod 2)) (colouring : V 6 → Fin 3) :
    explicitPmSum6 (pullWeights permutation weights) colouring =
      explicitPmSum6 weights (reindexColouring permutation colouring) := by
  rw [← enumeratedPmSum_eq_explicit, ← enumeratedPmSum_eq_explicit]
  exact enumeratedPmSum_pull permutation weights colouring

theorem pmSumN_pull (permutation : Fin 720)
    (weights : WeightsN 6 3 (ZMod 2)) (colouring : V 6 → Fin 3) :
    pmSumN 6 3 (pullWeights permutation weights) colouring =
      pmSumN 6 3 weights (reindexColouring permutation colouring) := by
  rw [pmSumN_six_eq_explicit, pmSumN_six_eq_explicit]
  exact explicitPmSum6_pull permutation weights colouring

theorem allEqual_iff_constant (colouring : V 6 → Fin 3) :
    allEqual colouring ↔ ∀ u v, colouring u = colouring v := by
  constructor
  · intro h
    simp [allEqual, allEqualList, vertices] at h
    intro u v
    fin_cases u <;> fin_cases v <;> simp_all
  · intro h
    simp [allEqual, allEqualList, vertices]
    exact ⟨h 0 1, h 1 2, h 2 3, h 3 4, h 4 5⟩

theorem allEqual_reindex (permutation : Fin 720) (colouring : V 6 → Fin 3) :
    allEqual (reindexColouring permutation colouring) ↔ allEqual colouring := by
  rw [allEqual_iff_constant, allEqual_iff_constant]
  constructor
  · intro h u v
    have huv := h (forwardVertex permutation u) (forwardVertex permutation v)
    simpa [reindexColouring, inverse_forward] using huv
  · intro h u v
    exact h _ _

theorem eqSystem_pullWeights (permutation : Fin 720)
    (weights : WeightsN 6 3 (ZMod 2)) (equations : EqSystemN 6 3 weights) :
    EqSystemN 6 3 (pullWeights permutation weights) := by
  intro colouring
  rw [pmSumN_pull, equations]
  simp only [allEqual_reindex]

/- ## The monochromatic support mask -/

def diagonalMask (weights : WeightsN 6 3 (ZMod 2)) : Mask :=
  packBits fun edge => supportValue weights edge 0 0

@[simp] theorem diagonalMask_get (weights : WeightsN 6 3 (ZMod 2))
    (edge : Fin 15) :
    (diagonalMask weights).getLsbD edge.val = supportValue weights edge 0 0 := by
  exact packBits_get _ _

@[simp] theorem diagonalMask_getLsbD_of_lt
    (weights : WeightsN 6 3 (ZMod 2)) (index : Nat) (hindex : index < 15) :
    (diagonalMask weights).getLsbD index =
      supportValue weights ⟨index, hindex⟩ 0 0 := by
  exact diagonalMask_get weights ⟨index, hindex⟩

theorem supportValue_pull_zero (permutation : Fin 720)
    (weights : WeightsN 6 3 (ZMod 2)) (edge : Fin 15) :
    supportValue (pullWeights permutation weights) edge 0 0 =
      supportValue weights (edgeAction permutation edge) 0 0 := by
  have h := congrArg bit
    (edgeWeight_pull permutation weights (fun _ => 0) edge)
  simpa [edgeWeight, supportValue, reindexColouring] using h

theorem diagonalMask_pull (permutation : Fin 720)
    (weights : WeightsN 6 3 (ZMod 2)) :
    diagonalMask (pullWeights permutation weights) =
      pullMask permutation (diagonalMask weights) := by
  apply BitVec.eq_of_getLsbD_eq
  intro index hindex
  let edge : Fin 15 := ⟨index, hindex⟩
  change (diagonalMask (pullWeights permutation weights)).getLsbD edge.val =
    (pullMask permutation (diagonalMask weights)).getLsbD edge.val
  rw [diagonalMask_get, pullMask_get, diagonalMask_get,
    supportValue_pull_zero]

theorem matchingPresent_packBits (bits : Fin 15 → Bool) (matching : Fin 15) :
    matchingPresent (packBits bits) matching =
      matchingEdgesFin[matching.val]!.all bits := by
  simp only [matchingPresent]
  have hfun :
      (fun edge : Fin 15 => (packBits bits).getLsbD edge.val) = bits := by
    funext edge
    exact packBits_get bits edge
  rw [hfun]

theorem matchingPresent_diagonal_eq_monomial_zero
    (weights : WeightsN 6 3 (ZMod 2)) (matching : Fin 15) :
    matchingPresent (diagonalMask weights) matching =
      monomialValue weights 0 matching := by
  rw [diagonalMask, matchingPresent_packBits]
  fin_cases matching <;>
    simp [monomialValue, factorValue,
      supportValue, matchingEdgesFin, endpointsFin, decodedColour, colour,
      mkEdge, Bool.and_assoc]

theorem oddPerfectMatchingParity_diagonal
    (weights : WeightsN 6 3 (ZMod 2)) :
    oddPerfectMatchingParity (diagonalMask weights) =
      parityValueNat weights 0 14 := by
  simp only [oddPerfectMatchingParity]
  letI : Std.Commutative Bool.xor := ⟨Bool.xor_comm⟩
  letI : Std.Associative Bool.xor := ⟨Bool.xor_assoc⟩
  rw [List.foldl_eq_foldr]
  simp [parityValueNat, fin15,
    matchingPresent_diagonal_eq_monomial_zero, List.ofFn, Fin.foldr_succ]

theorem diagonalMask_has_odd_parity (weights : WeightsN 6 3 (ZMod 2))
    (equations : EqSystemN 6 3 weights) :
    oddPerfectMatchingParity (diagonalMask weights) = true := by
  rw [oddPerfectMatchingParity_diagonal,
    eqSystem_zmod2_to_boolean weights equations 0]
  native_decide

end QuantumGraphOrbitBridge
