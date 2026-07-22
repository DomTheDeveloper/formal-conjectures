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

/-!
# Integer-to-characteristic-two bridge for the N=6 equation system

These lemmas are symbolic: they do not depend on the SAT search.  They show
that an integer solution would cast to a solution over `ZMod 2`, after first
expanding the repository's recursive perfect-matching sum into its fifteen
products.
-/

open MonochromaticQuantumGraph

namespace QuantumGraphParityBridge

def explicitPmSum6 {D : Nat} {α : Type} [Semiring α]
    (weights : WeightsN 6 D α) (colouring : V 6 → Fin D) : α :=
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

theorem pmSumN_six_eq_explicit {D : Nat} {α : Type} [Semiring α]
    (weights : WeightsN 6 D α) (colouring : V 6 → Fin D) :
    pmSumN 6 D weights colouring = explicitPmSum6 weights colouring := by
  simp [pmSumN, pmSumList, pmSumListAux, vertices, explicitPmSum6, mkEdge, mul_assoc]
  noncomm_ring

def castWeights (weights : WeightsN 6 3 ℤ) : WeightsN 6 3 (ZMod 2) :=
  fun edge ↦ (weights edge : ZMod 2)

theorem cast_pmSumN_six (weights : WeightsN 6 3 ℤ) (colouring : V 6 → Fin 3) :
    ((pmSumN 6 3 weights colouring : ℤ) : ZMod 2) =
      pmSumN 6 3 (castWeights weights) colouring := by
  rw [pmSumN_six_eq_explicit, pmSumN_six_eq_explicit]
  simp [explicitPmSum6, castWeights]

theorem eqSystem_int_to_zmod2 (weights : WeightsN 6 3 ℤ)
    (equations : EqSystemN 6 3 weights) :
    EqSystemN 6 3 (castWeights weights) := by
  intro colouring
  rw [← cast_pmSumN_six, equations colouring]
  split <;> simp

end QuantumGraphParityBridge
