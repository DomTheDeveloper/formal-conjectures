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

public import Mathlib.MeasureTheory.Measure.FiniteMeasurePi

@[expose] public section

open Set Topology MeasureTheory
open scoped Topology BigOperators

noncomputable section

namespace Set

variable {ι : Type*} [Fintype ι]
variable {α : ι → Type*} [∀ i, TopologicalSpace (α i)]

/-- The frontier of a finite product rectangle is contained in the union of the coordinate
frontiers. -/
theorem frontier_pi_subset_iUnion (A : ∀ i, Set (α i)) :
    frontier (Set.pi univ A) ⊆
      ⋃ i, (fun x : ∀ i, α i => x i) ⁻¹' frontier (A i) := by
  classical
  intro x hx
  by_contra hnot
  have hcoord : ∀ i, x i ∉ frontier (A i) := by
    simpa only [Set.mem_iUnion, Set.mem_preimage, not_exists] using hnot
  by_cases hxA : x ∈ Set.pi univ A
  · have hxint : x ∈ interior (Set.pi univ A) := by
      let U : Set (∀ i, α i) := Set.pi univ (fun i => interior (A i))
      have hUopen : IsOpen U := isOpen_set_pi finite_univ (fun i _ => isOpen_interior)
      have hxU : x ∈ U := by
        intro i _
        exact (mem_interior_iff_notMem_frontier (hxA i trivial)).2 (hcoord i)
      have hUsub : U ⊆ Set.pi univ A := by
        intro y hy i _
        exact interior_subset (hy i trivial)
      exact hUopen.mem_nhds hxU |> interior_maximal hUsub
    exact (mem_frontier_iff_notMem_interior hxA).1 hx hxint
  · have hex : ∃ i, x i ∉ A i := by
      simpa only [Set.mem_pi, Set.mem_univ, forall_true_left, not_forall] using hxA
    obtain ⟨i, hi⟩ := hex
    let V : Set (∀ i, α i) := (fun y => y i) ⁻¹' interior (A i)ᶜ
    have hVopen : IsOpen V := isOpen_interior.preimage (continuous_apply i)
    have hxV : x ∈ V := by
      exact (mem_interior_iff_notMem_frontier (show x i ∈ (A i)ᶜ by simpa)).2 (by simpa using hcoord i)
    have hVsub : V ⊆ (Set.pi univ A)ᶜ := by
      intro y hy hyA
      exact hy (hyA i trivial)
    have hxcompint : x ∈ interior (Set.pi univ A)ᶜ :=
      hVopen.mem_nhds hxV |> interior_maximal hVsub
    have hxcomp : x ∈ (Set.pi univ A)ᶜ := interior_subset hxcompint
    have : x ∉ frontier (Set.pi univ A)ᶜ :=
      (mem_interior_iff_notMem_frontier hxcomp).1 hxcompint
    exact this (by simpa using hx)

end Set

namespace MeasureTheory

variable {ι : Type*} [Fintype ι]
variable {α : ι → Type*} [∀ i, MeasurableSpace (α i)] [∀ i, TopologicalSpace (α i)]

/-- A finite product of coordinate continuity sets is a continuity set for the product measure. -/
theorem measure_frontier_pi_eq_zero
    (μ : ∀ i, Measure (α i)) [∀ i, IsProbabilityMeasure (μ i)]
    (A : ∀ i, Set (α i)) (hnull : ∀ i, μ i (frontier (A i)) = 0) :
    Measure.pi μ (frontier (Set.pi univ A)) = 0 := by
  classical
  apply measure_mono_null (Set.frontier_pi_subset_iUnion A)
  apply measure_iUnion_null
  intro i
  have heq :
      (fun x : ∀ i, α i => x i) ⁻¹' frontier (A i) =
        Set.pi univ (fun j => if j = i then frontier (A i) else univ) := by
    ext x
    simp [Set.mem_pi]
  rw [heq, Measure.pi_pi]
  simp [hnull i]

end MeasureTheory
