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

import FormalConjectures.Wikipedia.EulerBrick

/-!
# Explicit Euler brick witness

The classical cuboid with edges `44`, `117`, and `240` has integral face
diagonals `125`, `244`, and `267`.
-/

namespace EulerBrick

private def side44 : ℕ+ := ⟨44, by norm_num⟩
private def side117 : ℕ+ := ⟨117, by norm_num⟩
private def side240 : ℕ+ := ⟨240, by norm_num⟩

/-- The classical integer cuboid `(44,117,240)` is an Euler brick. -/
@[category test, AMS 11]
theorem isEulerBrick_44_117_240_kernel : IsEulerBrick side44 side117 side240 := by
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨125, ?_⟩
    apply Subtype.ext
    norm_num [side44, side117, pow_two]
  · refine ⟨244, ?_⟩
    apply Subtype.ext
    norm_num [side44, side240, pow_two]
  · refine ⟨267, ?_⟩
    apply Subtype.ext
    norm_num [side117, side240, pow_two]

/-- Euler bricks exist in three dimensions. -/
@[category test, AMS 11]
theorem exists_euler_brick_kernel : ∃ a b c : ℕ+, IsEulerBrick a b c := by
  exact ⟨side44, side117, side240, isEulerBrick_44_117_240_kernel⟩

#print axioms isEulerBrick_44_117_240_kernel
#print axioms exists_euler_brick_kernel

end EulerBrick
