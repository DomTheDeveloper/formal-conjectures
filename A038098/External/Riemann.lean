import A038098.External.Schoenfeld
import RSBounds.Rosser1941

namespace Sun.CubeBridge
open Sun.CubeAnalytic

/-- Every cube above the endpoint of Büthe's finite estimate, up through the
start of the earlier large-cube theorem, under the ordinary Riemann hypothesis. -/
theorem cubes_2154434_to_ten_million_of_RH (h : RiemannHypothesis)
    (n : ℕ) (lo : 2154434≤n) (hi : n≤10000000) :
    (((n+1)^3).primeCounting : ℚ) / (((n+1)^3:ℕ):ℚ) <
      ((n^3).primeCounting : ℚ) / ((n^3:ℕ):ℚ) :=
  cubes_above_buthe_of_RH_and_Rosser h
    (fun t ht => TernaryGoldbach.RSBounds.Rosser1941.zero_count_bounds t ht) n lo hi

/-- A single finite ψ estimate suffices for all remaining cubes above 199. -/
theorem cubes_200_to_ten_million (h : RiemannHypothesis) (hB : FinitePsi (10^19))
    (n : ℕ) (lo : 200≤n) (hi : n≤10000000) :
    (((n+1)^3).primeCounting : ℚ) / (((n+1)^3:ℕ):ℚ) <
      ((n^3).primeCounting : ℚ) / ((n^3:ℕ):ℚ) := by
  by_cases hn : n≤2154433
  · exact cubes_200_to_2154433 hB n lo hn
  exact cubes_2154434_to_ten_million_of_RH h n (by omega) hi

end Sun.CubeBridge
#print axioms Sun.CubeBridge.cubes_2154434_to_ten_million_of_RH
#print axioms Sun.CubeBridge.cubes_200_to_ten_million
