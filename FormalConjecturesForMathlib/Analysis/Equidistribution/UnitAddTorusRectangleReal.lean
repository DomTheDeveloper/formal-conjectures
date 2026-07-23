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
module

public import FormalConjecturesForMathlib.Analysis.Equidistribution.UnitAddTorusRectangle
public import Mathlib.MeasureTheory.Measure.Real

@[expose] public section

noncomputable section

open MeasureTheory Set Topology
open scoped BigOperators ENNReal NNReal Topology

namespace UnitAddTorus

variable {d : Type*} [Fintype d]

/-- Real Haar measure of a finite torus rectangle is the product of the real
Haar measures of its sides. -/
theorem volumeReal_rectangle (B : d → Set UnitAddCircle) :
    (volume : Measure (UnitAddTorus d)).real (rectangle B) =
      ∏ i, (volume : Measure UnitAddCircle).real (B i) := by
  rw [Measure.real, volume_rectangle]
  rw [ENNReal.toReal_prod]
  rfl

end UnitAddTorus
