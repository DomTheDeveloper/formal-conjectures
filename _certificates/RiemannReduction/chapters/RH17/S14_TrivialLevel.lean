import RH17.S02_SingleCharacter
import Development.AutomorphicArithmetic.CharacterBoxes.ZeroFreeAllOfTopG
import Development.AutomorphicArithmetic.PrimitiveCosets.GzEq

/-! # 14. Remove every nontrivial term in the final character average
Every Dirichlet character of modulus one is the identity. The cyclic family
therefore contains precisely the trivial primitive character. Erasing it leaves
an empty sum and the level statistic becomes G exactly. Auxiliary characters
still occur inside the arithmetic construction used to produce the estimate. -/

namespace RH17

open Formalism.HC

theorem trivialKept : (Level.cyc PChar.one).KEPT = {PChar.one} := by
  classical
  ext ψ
  rw [Finset.mem_singleton]
  constructor
  · intro h
    obtain ⟨χ, _, eq⟩ := (Level.mem_ofSub _ _).mp h
    have hχ : χ = 1 := DirichletCharacter.level_one χ
    rw [hχ, PChar.of_one] at eq
    exact eq.symm
  · rintro rfl
    exact Level.mem_cyc _

theorem trivialLevelSum (y : ℝ) : (Level.cyc PChar.one).Gm y = primeError y := by
  classical
  rw [Level.Gm, Level.Nt, trivialKept]
  simp only [Finset.erase_singleton, Finset.sum_empty, add_zero]
  obtain ⟨h₁, h₂⟩ := UpperTheory.Comparison₂.Gz_eq y
  exact h₁.trans h₂

end RH17
