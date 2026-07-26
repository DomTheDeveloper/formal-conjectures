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

import FormalConjectures.OpenQuantumProblems.«23»

namespace OpenQuantumProblem23

@[category test, AMS 15 47 81]
lemma qubitSICFamily_pairwise_audit :
    HasConstantOverlapSq (sicOverlapSq 2) qubitSICFamily := by
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h13 : Real.sqrt (1 / 3 : ℝ) ^ 2 = 1 / 3 := Real.sq_sqrt (by norm_num)
  have h23 : Real.sqrt (2 / 3 : ℝ) ^ 2 = 2 / 3 := Real.sq_sqrt (by norm_num)
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp_all [overlapSq, qubitSICFamily, vec2, mkStateVector, Fin.sum_univ_two,
      sicOverlapSq, tetraA, tetraB, ω, Complex.normSq_apply] <;>
    ring_nf at * <;>
    nlinarith

@[category test, AMS 15 47 81]
theorem hasSICPOVM_two_audit : HasSICPOVM 2 := by
  exact ⟨qubitSICFamily, qubitSICFamily_normalized, qubitSICFamily_pairwise_audit⟩

end OpenQuantumProblem23
