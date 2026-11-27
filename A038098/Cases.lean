module

public import A038098.PackedCases

/-! Run generate_packed.py before compiling the generated certificate modules.
The conclusion uses the same rational proportions as OeisA38098.conjecture1. -/
public section
namespace Sun.CubeSieve

theorem cubes_two_to_two_hundred (n : ℕ) (lo : 2≤n) (hi : n≤200) :
    (((n+1)^3).primeCounting : ℚ) / (((n+1)^3:ℕ):ℚ) <
      ((n^3).primeCounting : ℚ) / ((n^3:ℕ):ℚ) :=
  Sun.PackedCases.checked_cubes n lo hi

end Sun.CubeSieve
#print axioms Sun.CubeSieve.cubes_two_to_two_hundred
