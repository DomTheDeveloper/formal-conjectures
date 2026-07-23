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
public import Mathlib.MeasureTheory.Measure.Real

@[expose] public section

noncomputable section

open MeasureTheory Set Topology
open scoped ENNReal NNReal Topology

namespace UnitAddCircle

/-- Real Haar measure of the open terminal arc. -/
theorem volumeReal_openArc {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) :
    (volume : Measure UnitAddCircle).real (openArc a) = a := by
  rw [Measure.real, volume_openArc ha0 ha1, ENNReal.toReal_ofReal ha0]

/-- Real Haar measure of the closed terminal arc. -/
theorem volumeReal_closedArc {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) :
    (volume : Measure UnitAddCircle).real (closedArc a) = a := by
  rw [Measure.real, volume_closedArc ha0 ha1, ENNReal.toReal_ofReal ha0]

/-- Real Haar measure of the complement of the open terminal arc. -/
theorem volumeReal_compl_openArc {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) :
    (volume : Measure UnitAddCircle).real (openArc a)ᶜ = 1 - a := by
  have h := measureReal_add_measureReal_compl
    (μ := (volume : Measure UnitAddCircle)) (isOpen_openArc a).measurableSet
  rw [volumeReal_openArc ha0 ha1, probReal_univ] at h
  linarith

/-- Real Haar measure of the complement of the closed terminal arc. -/
theorem volumeReal_compl_closedArc {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) :
    (volume : Measure UnitAddCircle).real (closedArc a)ᶜ = 1 - a := by
  have h := measureReal_add_measureReal_compl
    (μ := (volume : Measure UnitAddCircle)) (isClosed_closedArc a).measurableSet
  rw [volumeReal_closedArc ha0 ha1, probReal_univ] at h
  linarith

end UnitAddCircle
