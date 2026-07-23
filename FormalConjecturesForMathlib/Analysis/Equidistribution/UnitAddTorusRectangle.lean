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

public import FormalConjecturesForMathlib.Analysis.Equidistribution.UnitAddCircleArc
public import Mathlib.MeasureTheory.Constructions.Pi

@[expose] public section

/-!
# Rectangles in a finite unit torus

A coordinate rectangle in a finite product is open or closed when every side
is, and its product Haar measure is the product of the side measures.
-/

noncomputable section

open MeasureTheory Set Topology
open scoped BigOperators ENNReal NNReal Topology

namespace UnitAddTorus

variable {d : Type*} [Fintype d]

/-- The coordinate rectangle with side `B i` in coordinate `i`. -/
def rectangle (B : d → Set UnitAddCircle) : Set (UnitAddTorus d) :=
  Set.pi Set.univ B

private theorem rectangle_eq_iInter (B : d → Set UnitAddCircle) :
    rectangle B = ⋂ i, (fun x : UnitAddTorus d => x i) ⁻¹' B i := by
  ext x
  simp [rectangle]

/-- A finite product of open sides is open. -/
theorem isOpen_rectangle {B : d → Set UnitAddCircle} (hB : ∀ i, IsOpen (B i)) :
    IsOpen (rectangle B) := by
  rw [rectangle_eq_iInter]
  exact isOpen_iInter_of_finite fun i => (hB i).preimage (continuous_apply i)

/-- A finite product of closed sides is closed. -/
theorem isClosed_rectangle {B : d → Set UnitAddCircle} (hB : ∀ i, IsClosed (B i)) :
    IsClosed (rectangle B) := by
  rw [rectangle_eq_iInter]
  exact isClosed_iInter fun i => (hB i).preimage (continuous_apply i)

/-- Coordinatewise inclusion gives inclusion of rectangles. -/
theorem rectangle_mono {A B : d → Set UnitAddCircle} (h : ∀ i, A i ⊆ B i) :
    rectangle A ⊆ rectangle B :=
  Set.pi_mono fun i _ => h i

/-- Haar measure of a finite torus rectangle is the product of the side measures. -/
theorem volume_rectangle (B : d → Set UnitAddCircle) :
    volume (rectangle B) = ∏ i, volume (B i) := by
  simpa [rectangle] using
    (Measure.pi_pi (fun _ : d => (volume : Measure UnitAddCircle)) B)

end UnitAddTorus
