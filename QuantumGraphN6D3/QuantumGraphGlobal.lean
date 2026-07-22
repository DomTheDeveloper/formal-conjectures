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

import QuantumGraphAllCases
import QuantumGraphParityBridge

/-!
# The global `N = 6`, `D = 3` integer obstruction

The 47 reflected LRAT certificates cover every odd perfect-matching support
orbit under the vertex action.  The characteristic-two obstruction then rules
out integer solutions, and therefore also trinary integer solutions.
-/

open Std Sat MonochromaticQuantumGraph

namespace QuantumGraphGlobal

open QuantumGraphSemantic QuantumGraphOrbitBridge QuantumGraphAllCases
open QuantumGraphParityBridge

theorem no_eqSystem_zmod2 :
    ¬ ∃ weights : WeightsN 6 3 (ZMod 2), EqSystemN 6 3 weights := by
  rintro ⟨weights, equations⟩
  let mask := diagonalMask weights
  have hodd : oddPerfectMatchingParity mask = true := by
    simpa [mask] using diagonalMask_has_odd_parity weights equations
  let caseIndex := classificationCase mask
  let permutation := classificationPermutation mask
  let pulledWeights := pullWeights permutation weights
  have hpulledEquations : EqSystemN 6 3 pulledWeights := by
    exact eqSystem_pullWeights permutation weights equations
  have hclassification :
      pullMask permutation mask = representativeMask caseIndex := by
    exact classification_correct mask hodd
  have hpulledMask :
      diagonalMask pulledWeights = representativeMask caseIndex := by
    calc
      diagonalMask pulledWeights = pullMask permutation mask := by
        exact diagonalMask_pull permutation weights
      _ = representativeMask caseIndex := hclassification
  have hmask :
      HasDiagonalMask pulledWeights (representativeMask caseIndex).toNat := by
    intro edge
    rw [← diagonalMask_get pulledWeights edge, hpulledMask]
    rfl
  have hboolean : BooleanEquationSystem pulledWeights :=
    eqSystem_zmod2_to_boolean pulledWeights hpulledEquations
  have hsat := semanticCaseCNF_sat pulledWeights
    (representativeMask caseIndex).toNat hboolean hmask
  have hfalse := representative_semantic_unsat caseIndex
    (semanticAssignment pulledWeights)
  rw [hsat] at hfalse
  exact Bool.noConfusion hfalse

theorem no_eqSystem_int :
    ¬ ∃ weights : WeightsN 6 3 ℤ, EqSystemN 6 3 weights := by
  rintro ⟨weights, equations⟩
  exact no_eqSystem_zmod2
    ⟨castWeights weights, eqSystem_int_to_zmod2 weights equations⟩

theorem no_eqSystem_trinary_int :
    ¬ ∃ weights : WeightsN 6 3 ℤ,
      (∀ edge, weights edge = (-1 : ℤ) ∨ weights edge = 0 ∨ weights edge = 1) ∧
        EqSystemN 6 3 weights := by
  rintro ⟨weights, _, equations⟩
  exact no_eqSystem_int ⟨weights, equations⟩

end QuantumGraphGlobal
