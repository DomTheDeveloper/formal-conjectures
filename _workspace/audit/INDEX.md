# Master audit index

**408** `research open` declarations audited (of 1163 in inventory).
Coverage gaps: 755 missing, 0 duplicated.
See [README.md](./README.md) for methodology and category definitions; per-directory detail reports carry the full 13 audit fields per problem.

## Category histogram

| Cat | Meaning | Count |
|---|---|---|
| 0 | Already solved internally | 26 |
| 1 | Already solved externally | 5 |
| 2 | Trivially or easily solvable | 4 |
| 3 | False / refutable as stated | 1 |
| 4 | Vacuously true / accidentally weakened | 40 |
| 5 | Solved mathematically, not yet formalized | 8 |
| 6 | Computationally solvable with certificate | 2 |
| 7 | Plausibly solvable with moderate formal work | 0 |
| 8 | Deep but approachable research problem | 247 |
| 9 | Major open problem / currently infeasible | 72 |
| 10 | Cannot classify without correction/clarification | 3 |

## All problems

Columns: **Cat** = primary category, **Cat2** = secondary, **Match** = does the Lean statement match the intended problem (yes/suspect/no),
**M/L** = mathematical / Lean difficulty (1-10), **Compute** = compute requirement, **Conf** = confidence.

| File | Declaration | Cat | Cat2 | Match | M/L | Compute | Conf | Next action |
|---|---|---|---|---|---|---|---|---|
| `Arxiv/0912.2382/CurlingNumberConjecture.lean` | `curling_number_conjecture` | 8 |  | yes | 8/9 | none | high | Keep open; no viable attack. Could formalize the known reduction facts (k(S)>=1 for nonempty S) as API only. |
| `Arxiv/1601.03081/UniqueCrystalComponents.lean` | `crystals_components_unique` | 8 |  | yes | 6/7 | small | medium | Elementary-number-theory attack plausible: note (a+b)^2+(ab+1)^2 = (a^2+1)(b^2+1)+4ab and study the divisibili |
| `Arxiv/1609.08688/sIncreasingrTuples.lean` | `maximalLength_le_strong` | 8 |  | suspect | 8/9 | none | medium | Verify the exact wording of Conjecture 1.8 against the published paper and weaken to the asymptotic form if ne |
| `Arxiv/2107.00295/IndependentDomination.lean` | `independentDominationEven` | 1 | 5 | yes | 3/9 | none | high | Reclassify to research solved and port the Cho-Kim-Kim-Oum discharging proof plus the easy D=2 case; large eff |
| `Arxiv/2107.00295/IndependentDomination.lean` | `independentDominationOdd` | 8 |  | yes | 6/9 | none | medium | Track the Delta=5 case in the literature (active area: e.g. the 2025 proof of the 3/8-conjecture for cubic gra |
| `Arxiv/2107.12475/CollatzLike.lean` | `CollatzLike` | 9 |  | yes | 9/10 | none | high | None; no known approach (would require ternary-digit equidistribution for 2^n). Note the weaker finiteness for |
| `Arxiv/2208.14736/ZariskiCancellation.lean` | `zariski_cancellation_problem` | 9 |  | yes | 10/10 | none | high | None; keep open. If ever attacked formally, the n<=2 solved variants in this file are the realistic targets. |
| `Arxiv/2303.01089/FurstenbergTimesPTimesQ.lean` | `conjecture_1_3` | 9 |  | yes | 10/10 | none | high | None; keep open. |
| `Arxiv/2501.03234/ArithmeticSumS.lean` | `conjecture_1_1` | 8 |  | yes | 7/8 | none | medium | Investigate the paper's connection between S(p) and class numbers h(-p) (Dedekind-sum-style reciprocity); a pr |
| `Arxiv/2501.03234/ArithmeticSumS.lean` | `conjecture_4_1` | 8 |  | yes | 7/8 | none | medium | Same class-number/L-function route as Conjecture 1.1; numerically extend verification if useful. |
| `Arxiv/2501.03234/ArithmeticSumS.lean` | `conjecture_4_2` | 8 |  | yes | 7/8 | none | medium | As for 4.1; the explicit thresholds (233, 3119) come from the authors' computations. |
| `Arxiv/2501.03234/ArithmeticSumS.lean` | `conjecture_4_3` | 8 |  | yes | 7/8 | none | medium | As for 4.1/4.2. |
| `Arxiv/2501.03234/ArithmeticSumS.lean` | `conjecture_4_4` | 8 |  | yes | 8/9 | none | medium | This superlinearity likely hinges on lower bounds for L(1,chi) (Siegel-type, possibly ineffective); treat as r |
| `Arxiv/2504.17644/Margulis.lean` | `conjecture_1_1` | 9 |  | yes | 10/10 | none | high | None; keep open. |
| `Arxiv/RestrictedRunTableaux.lean` | `conjecture_2a` | 8 |  | yes | 8/10 | none | medium | Genuine research: prove a local limit theorem for the associated cone-constrained Markov-additive walk, or fin |
| `Arxiv/math.0110202/BanachMazurRotation.lean` | `banach_mazur_rotation_problem` | 9 |  | yes | 10/10 | none | high | None; keep open. |
| `Books/BugeaudDistributionModuloOne/IntDistanceDistribution.lean` | `problem_10_1` | 9 |  | yes | 9/9 | none | high | Leave open; no known avenue. No repo PR targets it (pr_register has no Bugeaud entries). |
| `Books/BugeaudDistributionModuloOne/IntDistanceDistribution.lean` | `problem_10_2` | 9 |  | yes | 9/9 | none | high | Leave open. |
| `Books/BugeaudDistributionModuloOne/IntDistanceDistribution.lean` | `problem_10_3` | 9 |  | yes | 9/9 | none | high | Leave open. Note the in-file test lemma correctly derives it from the Waldschmidt statement. |
| `Books/BugeaudDistributionModuloOne/IntDistanceDistribution.lean` | `waldschmidt` | 9 |  | yes | 9/9 | none | high | Leave open. |
| `Books/BugeaudDistributionModuloOne/Problem10_4.lean` | `spectrum_xi_alpha_pow_countable` | 8 |  | yes | 8/8 | none | medium | Leave open; verify the book's exact spectrum definition against [Bug12] Ch. 10 if the file is ever revised. |
| `Books/BugeaudDistributionModuloOne/Problem10_5.lean` | `problem_10_5` | 8 |  | yes | 8/8 | none | medium | Leave open. |
| `Books/BugeaudDistributionModuloOne/Problem10_5.lean` | `problem_10_5_moreover` | 8 |  | yes | 8/8 | none | medium | Leave open. |
| `Books/BugeaudDistributionModuloOne/Problem10_6.lean` | `problem_10_6_variant_1` | 8 |  | yes | 9/9 | none | high | Leave open; avenues are measure rigidity (Furstenberg/Einsiedler-Katok-Lindenstrauss school). |
| `Books/BugeaudDistributionModuloOne/Problem10_6.lean` | `problem_10_6_variant_2` | 4 | 5 | no | 3/9 | none | high | Either restrict to alpha > 1/2 (which restores openness) or reclassify as a corollary of Furstenberg. Closing  |
| `Books/BugeaudDistributionModuloOne/Problem10_7.lean` | `problem_10_7` | 8 |  | yes | 8/8 | none | medium | Leave open; optionally document the fixed-eps vs all-eps reading in the file. |
| `Books/BugeaudDistributionModuloOne/Problem10_8.lean` | `problem_10_8` | 9 |  | yes | 9/9 | none | high | Leave open. Note duplicate liminf formulation padic_littlewood_conjecture in FormalConjectures/Wikipedia/Littl |
| `Books/UniformDistributionOfSequences/Equidistribution.lean` | `isAccumulationPoint_three_halves_pow` | 4 | 7 | suspect | 9/5 | none | medium | Close the formal statement via answer := Filter.limsup (fun n => Int.fract ((3/2)^n)) atTop: prove fract((3/2) |
| `Books/UniformDistributionOfSequences/Equidistribution.lean` | `isEquidistributedModuloOne_three_halves_pow` | 9 |  | yes | 9/9 | none | high | Leave open. |
| `Books/UniformDistributionOfSequences/Equidistribution.lean` | `isEquidistributedModuloOne_transcendental_three_halves_pow` | 3 |  | no | 4/9 | none | medium | Flag for correction upstream: weaken to 'for almost every x' (Koksma/Weyl metric theorem, provable but nontriv |
| `ErdosProblems/1.lean` | `erdos_1` | 9 |  | yes | 9/9 | none | high | Keep open. No formal action; monitor literature for improvements past 2^n/sqrt(n). |
| `ErdosProblems/1.lean` | `erdos_1.variants.real` | 9 |  | yes | 9/9 | none | high | Keep open; any resolution of erdos_1 in the negative would need checking here; a proof of this implies erdos_1 |
| `ErdosProblems/10.lean` | `erdos_10` | 8 |  | yes | 9/9 | none | high | Keep open. A negative answer might come from covering-system constructions; monitor. |
| `ErdosProblems/10.lean` | `erdos_10.variants.granville_soundararajan_odd` | 8 |  | yes | 9/9 | none | medium | Keep open. Disproof would require a large computational search for an odd counterexample; no certificate path  |
| `ErdosProblems/10.lean` | `erdos_10.variants.grechuk` | 8 |  | yes | 8/9 | none | medium | Keep open. Plausible avenue: Crocker/covering-congruence style arguments extended to three powers; monitor erd |
| `ErdosProblems/100.lean` | `erdos_100` | 8 |  | yes | 8/9 | none | high | Keep open. Closing the log n gap requires strengthening distinct-distance counts under the separation hypothes |
| `ErdosProblems/100.lean` | `erdos_100.variants.strong` | 8 |  | yes | 9/9 | none | high | Keep open. |
| `ErdosProblems/1002.lean` | `erdos_1002` | 8 |  | yes | 8/9 | none | medium | Keep open; a proof would likely adapt Kesten's method (substantial analytic work). |
| `ErdosProblems/1003.lean` | `erdos_1003` | 8 |  | yes | 9/9 | none | high | Keep open. |
| `ErdosProblems/1003.lean` | `erdos_1003.variants.Icc` | 8 |  | yes | 9/9 | none | high | Keep open; small-case searches for k = 3 could add value but are not certificates for the conjecture. |
| `ErdosProblems/1004.lean` | `erdos_1004` | 8 |  | yes | 8/9 | none | medium | Keep open. |
| `ErdosProblems/101.lean` | `erdos_101` | 8 |  | yes | 9/9 | none | high | Keep open; formalizing known lower-bound constructions (file TODO) is the only near-term formal work. |
| `ErdosProblems/1038.lean` | `erdos_1038.parts.i` | 8 |  | yes | 8/9 | none | medium | Keep open; the exact constant is a live research question with recent activity (Tao 2025). |
| `ErdosProblems/1041.lean` | `erdos_1041` | 8 |  | yes | 8/9 | none | medium | Keep open; a counterexample would be an explicit polynomial with a certified length lower bound (hard to certi |
| `ErdosProblems/1049.lean` | `erdos_1049` | 9 |  | yes | 9/9 | none | medium | Keep open; needs a genuinely new irrationality technique for rational non-integer bases. |
| `ErdosProblems/1052.lean` | `erdos_1052` | 8 |  | yes | 9/9 | none | high | Keep open. |
| `ErdosProblems/1054.lean` | `erdos_1054.parts.i` | 8 |  | yes | 8/9 | none | medium | Keep open. |
| `ErdosProblems/1054.lean` | `erdos_1054.parts.ii` | 8 |  | yes | 8/9 | none | medium | Keep open. |
| `ErdosProblems/1054.lean` | `erdos_1054.parts.iii` | 8 |  | suspect | 8/9 | none | medium | Suggest upstream cleanup: drop the dead 'exists A, HasDensity 1' conjunct. Mathematically keep open. |
| `ErdosProblems/1055.lean` | `erdos_1055` | 9 | 4 | suspect | 9/9 | none | medium | Report spec defect upstream: fix the r = 2 clause (e.g. require IsOfClass n q for the witness and non-membersh |
| `ErdosProblems/1055.lean` | `erdos_1055.variants.erdos_limit` | 8 |  | yes | 9/9 | none | medium | Keep open; note the def p depends on the sorried existence theorem exists_p (every class nonempty), itself non |
| `ErdosProblems/1055.lean` | `erdos_1055.variants.selfridge_limit` | 8 |  | yes | 9/9 | none | medium | Keep open. |
| `ErdosProblems/1056.lean` | `erdos_1056` | 8 |  | yes | 8/9 | none | high | Keep open. Searching for k = 4 witnesses is a natural computational contribution (a found witness certifies th |
| `ErdosProblems/1056.lean` | `erdos_1056.variants.noll_simmons` | 8 |  | yes | 8/9 | none | medium | Keep open; computational search for large-k witnesses is possible but only certifies individual k. |
| `ErdosProblems/1057.lean` | `erdos_1057` | 9 |  | yes | 9/10 | none | high | Leave open. answer is believed True but proving it needs a breakthrough in analytic number theory; no formal p |
| `ErdosProblems/1057.lean` | `erdos_1057.variants.pomerance` | 9 |  | yes | 9/10 | none | high | Leave open; at least as hard as erdos_1057. |
| `ErdosProblems/1059.lean` | `erdos_1059` | 8 |  | yes | 8/9 | none | high | Leave open. Any progress would come from covering-system / sieve constructions; no formal shortcut. |
| `ErdosProblems/1060.lean` | `erdos_1060.parts.i` | 8 |  | yes | 7/9 | none | medium | Leave open; would need multiplicative-structure arguments beyond the divisor bound. |
| `ErdosProblems/1060.lean` | `erdos_1060.parts.ii` | 8 |  | yes | 8/9 | none | medium | Leave open. |
| `ErdosProblems/1061.lean` | `erdos_1061` | 8 |  | yes | 8/9 | none | medium | Leave open. A first milestone would be positive lower density of solutions. |
| `ErdosProblems/1062.lean` | `erdos_1062.parts.ii` | 8 |  | yes | 9/9 | none | high | Leave open; note the compound answer-encoding in any upstream review. |
| `ErdosProblems/1063.lean` | `erdos_1063.better_upper` | 8 |  | yes | 7/9 | none | medium | Leave open. The cheapest legitimate route would be proving n_k = o(k*lcm(1..k-1)) directly (then answer := n i |
| `ErdosProblems/1065.lean` | `erdos_1065.parts.i` | 8 |  | yes | 8/8 | none | high | Leave open. |
| `ErdosProblems/1065.lean` | `erdos_1065.parts.ii` | 8 |  | yes | 7/8 | none | high | Leave open. |
| `ErdosProblems/1068.lean` | `erdos_1068` | 8 |  | yes | 9/9 | none | medium | Leave open; set-theoretic methods (elementary submodels, consistency results) are the plausible avenue. |
| `ErdosProblems/107.lean` | `erdos_107` | 9 |  | yes | 9/10 | none | high | Leave open. A negative answer for some specific n would in principle be a (gigantic) finite computation; no fe |
| `ErdosProblems/1072.lean` | `erdos_1072.parts.i` | 8 |  | yes | 8/8 | none | high | Leave open. |
| `ErdosProblems/1072.lean` | `erdos_1072.parts.ii` | 8 |  | yes | 8/9 | none | high | Leave open. |
| `ErdosProblems/1072.lean` | `erdos_1072.variants.littleo` | 8 |  | yes | 8/9 | none | high | Leave open. |
| `ErdosProblems/1073.lean` | `erdos_1073` | 8 |  | yes | 8/9 | none | medium | Leave open. |
| `ErdosProblems/1074.lean` | `erdos_1074.parts.i` | 8 |  | yes | 8/9 | none | high | Leave open. |
| `ErdosProblems/1074.lean` | `erdos_1074.parts.ii` | 8 |  | yes | 8/9 | none | medium | Leave open; consider guarding the value question on parts.i in an upstream cleanup. |
| `ErdosProblems/1074.lean` | `erdos_1074.parts.iii` | 8 |  | yes | 8/9 | none | high | Leave open. |
| `ErdosProblems/1074.lean` | `erdos_1074.parts.iv` | 8 |  | yes | 8/9 | none | medium | Leave open. |
| `ErdosProblems/1074.lean` | `erdos_1074.variants.EHSNumbers_one_half` | 8 |  | suspect | 9/9 | none | low | Recommend demoting or annotating this variant upstream (e.g. as a heuristic target, or an interval claim), rat |
| `ErdosProblems/108.lean` | `erdos_108` | 8 |  | yes | 9/9 | none | high | Leave open. Formalizing the solved r = 4 case (Rodl) would be a meaningful standalone project (noted as TODO i |
| `ErdosProblems/1082.lean` | `erdos_1082.parts.i` | 8 |  | yes | 9/9 | none | high | Leave open. Any counterexample search would target small general-position multi-distance sets; none known. |
| `ErdosProblems/1084.lean` | `erdos_1084.variants.triangular_optimal_d2` | 5 |  | yes | 5/9 | none | high | Relabel as research solved citing Harborth 1974 and attempt formalization: lower bound from the explicit hexag |
| `ErdosProblems/1085.lean` | `erdos_1085.variants.upper_d3` | 9 |  | yes | 9/10 | none | high | Leave open. Any progress requires new incidence geometry in R^3; the Lean side additionally needs an entire th |
| `ErdosProblems/1093.lean` | `erdos_1093.parts.i` | 8 |  | suspect | 8/9 | none | medium | Confirm the intended smoothness threshold against erdosproblems.com/1093 / [EES74]; if it is 'primes ≤ k', cha |
| `ErdosProblems/1093.lean` | `erdos_1093.parts.ii` | 8 |  | suspect | 8/9 | none | medium | Fix the smoothness threshold jointly with parts.i, then leave open. |
| `ErdosProblems/1094.lean` | `erdos_1094` | 8 |  | yes | 8/9 | none | medium | Verify the exact ELS93 constant against the source; otherwise leave open. Progress would need effective bounds |
| `ErdosProblems/1095.lean` | `erdos_1095.variants.log_equivalent` | 8 | 3 | no | 9/9 | none | medium | Replace `(fun k ↦ log (g k)) ~[atTop] (fun k ↦ k / log k)` with `(fun k ↦ log (g k)) =Θ[atTop] (fun k ↦ (k : ℝ |
| `ErdosProblems/1095.lean` | `erdos_1095.variants.lower_conjecture` | 8 |  | yes | 9/9 | none | high | Leave open. The gap between exp(c(log k)^2) and exp(ck/log k) is enormous; no strategy known. |
| `ErdosProblems/1095.lean` | `erdos_1095.variants.upper_conjecture` | 8 |  | yes | 8/9 | none | high | Leave open. Would need genuinely new analytic number theory. |
| `ErdosProblems/11.lean` | `erdos_11` | 9 |  | yes | 9/10 | none | high | Leave open (category 9). Do not attempt: a proof would resolve an open Wieferich-type question. |
| `ErdosProblems/11.lean` | `erdos_11.variants.not_four_dvd` | 9 |  | yes | 9/10 | none | high | Leave open. If anything is ever proved here it should be derived from erdos_11 plus the even case, not attacke |
| `ErdosProblems/11.lean` | `erdos_11.variants.two_pow_two` | 8 |  | yes | 8/9 | none | medium | Leave open, but this is the most approachable of the three: a sieve/covering argument over n mod small powers  |
| `ErdosProblems/1101.lean` | `erdos_1101.parts.i` | 8 |  | yes | 9/9 | none | high | Leave open. Key obstruction: lower-bounding the largest gap in the u-sieved set for slowly growing u; a first  |
| `ErdosProblems/1101.lean` | `erdos_1101.parts.ii` | 8 |  | yes | 8/9 | none | high | Leave open. Natural approach: refine Erdos's prime construction to control growth; first milestone is to forma |
| `ErdosProblems/1106.lean` | `erdos_1106.parts.i` | 1 | 5 | yes | 5/9 | none | high | Retag as @[category research solved] with answer(True) and cite Schinzel-Wirsing / Erdos-Ivic. Formalizing the |
| `ErdosProblems/1106.lean` | `erdos_1106.parts.ii` | 8 |  | yes | 9/9 | none | high | Leave open. Key obstruction: converting divisibility results for individual primes into a count of ≥ n distinc |
| `ErdosProblems/1107.lean` | `erdos_1107` | 8 |  | yes | 8/9 | none | high | Leave open. The r = 2 case already required deep work on ternary quadratic forms; general r has no known appro |
| `ErdosProblems/1108.lean` | `erdos_1108.parts.i` | 8 |  | yes | 8/9 | small | medium | Leave open. First milestone: a computational search for k-th powers in A up to a large bound would sharpen the |
| `ErdosProblems/1108.lean` | `erdos_1108.parts.ii` | 8 |  | yes | 8/9 | small | medium | Leave open. Same obstruction as parts.i. |
| `ErdosProblems/1113.lean` | `erdos_1113` | 8 |  | yes | 9/9 | small | high | Leave open. A plausible partial Lean target is formalizing that Izotov's m is a Sierpinski number (algebraic q |
| `ErdosProblems/1113.lean` | `erdos_1113.variants.filaseta_finch_kozek` | 9 |  | yes | 9/10 | none | high | Leave open (category 9). No meaningful strategy exists; the statement quantifies over an infinite family with  |
| `ErdosProblems/1133.lean` | `erdos_1133` | 8 |  | yes | 8/9 | none | medium | Leave open. Progress requires new extremal results on Chebyshev-type polynomials with a linear number of allow |
| `ErdosProblems/1135.lean` | `erdos_1135` | 9 |  | yes | 10/10 | none | high | Leave open. If the Wikipedia file is ever closed, erdos_1135 closes by `exact CollatzConjecture.collatz_conjec |
| `ErdosProblems/1137.lean` | `erdos_1137` | 8 |  | yes | 9/9 | none | high | Leave open. Key obstruction: no upper bound on max_{n<x} d_n is known that is anywhere near the Erdos-Rankin l |
| `ErdosProblems/1139.lean` | `erdos_1139` | 8 |  | yes | 8/9 | none | medium | Leave open. Key obstruction: constructing long intervals free of primes AND semiprimes; Erdos-Rankin handles p |
| `ErdosProblems/1142.lean` | `erdos_1142` | 9 |  | yes | 9/10 | none | high | Leave open. Neither direction is approachable: proving finiteness needs, for every large n, a k with n - 2^k c |
| `ErdosProblems/357.lean` | `erdos_357.parts.i` | 8 |  | yes | 8/9 | none | high | Keep open; monitor erdosproblems.com/357 and follow-ups to Beker 2024 for progress on the o(n) question. |
| `ErdosProblems/357.lean` | `erdos_357.parts.ii.bigO_version` | 4 | 2 | suspect | 8/1 | none | high | Tighten the encoding (e.g. require an explicit elementary function with a stated exponent) or accept as conven |
| `ErdosProblems/357.lean` | `erdos_357.parts.ii.bigO_version_symm` | 4 | 2 | suspect | 8/1 | none | high | Same as bigO_version: tighten encoding or treat as convention-guarded. |
| `ErdosProblems/357.lean` | `erdos_357.parts.ii.bigTheta_version` | 4 | 2 | suspect | 9/1 | none | high | Same as bigO_version. |
| `ErdosProblems/357.lean` | `erdos_357.parts.ii.littleO_version` | 4 | 2 | suspect | 8/1 | none | high | Same as bigO_version. |
| `ErdosProblems/357.lean` | `erdos_357.parts.ii.littleO_version_symm` | 4 | 2 | suspect | 8/3 | none | high | Same as bigO_version; note a non-degenerate answer o(n) would resolve parts.i. |
| `ErdosProblems/357.lean` | `erdos_357.variants.hegyvari` | 5 |  | yes | 5/7 | none | high | Relabel to research solved and formalize Hegyvari's proof; effort medium-large (combinatorial construction for |
| `ErdosProblems/357.lean` | `erdos_357.variants.infinite_set_density` | 8 |  | yes | 7/8 | none | high | Keep open; a first step would be formalizing the known lower-density-0 result. |
| `ErdosProblems/357.lean` | `erdos_357.variants.infinite_set_sum` | 8 |  | yes | 8/9 | none | high | Keep open. |
| `ErdosProblems/357.lean` | `erdos_357.variants.monotone.parts.i` | 8 |  | yes | 8/9 | none | high | Optionally prove h = f as an API lemma to expose the equivalence; otherwise keep open alongside parts.i. |
| `ErdosProblems/357.lean` | `erdos_357.variants.monotone.parts.ii.bigO_version` | 4 | 2 | suspect | 8/1 | none | high | Tighten encoding or treat as convention-guarded. |
| `ErdosProblems/357.lean` | `erdos_357.variants.monotone.parts.ii.bigO_version_symm` | 4 | 2 | suspect | 8/1 | none | high | Tighten encoding or treat as convention-guarded. |
| `ErdosProblems/357.lean` | `erdos_357.variants.monotone.parts.ii.bigTheta_version` | 4 | 2 | suspect | 9/1 | none | high | Tighten encoding or treat as convention-guarded. |
| `ErdosProblems/357.lean` | `erdos_357.variants.monotone.parts.ii.littleO_version` | 4 | 2 | suspect | 8/1 | none | high | Tighten encoding or treat as convention-guarded. |
| `ErdosProblems/357.lean` | `erdos_357.variants.monotone.parts.ii.littleO_version_symm` | 4 | 2 | suspect | 8/3 | none | high | Tighten encoding or treat as convention-guarded. |
| `ErdosProblems/359.lean` | `erdos_359.parts.i` | 8 |  | yes | 8/9 | none | high | Keep open; small-scale computation of A002048 growth could inform but not resolve. |
| `ErdosProblems/359.lean` | `erdos_359.parts.ii` | 8 |  | yes | 8/9 | none | high | Keep open. |
| `ErdosProblems/359.lean` | `erdos_359.variants.isGoodFor_1_asymptotic` | 8 |  | yes | 9/9 | none | high | Keep open. |
| `ErdosProblems/36.lean` | `erdos_36` | 4 | 5 | suspect | 9/9 | none | medium | Tighten encoding (e.g. require a closed-form or high-precision decimal with matching Tendsto proof), or treat  |
| `ErdosProblems/36.lean` | `erdos_36.variants.lower` | 4 | 5 | suspect | 9/9 | none | high | Either tighten the encoding to demand an explicit decimal strictly above 0.379005, or treat closure as 'formal |
| `ErdosProblems/36.lean` | `erdos_36.variants.upper` | 8 |  | yes | 9/10 | none | high | Keep open. Caution: if Haugland's construction-based bound is essentially sharp (the limit is conjectured nume |
| `ErdosProblems/361.lean` | `erdos_361.bigO` | 4 | 2 | no | 8/2 | none | high | Fix the statement: remove the inner 'forall c' (use the outer c) and change the filter to exclude all B having |
| `ErdosProblems/361.lean` | `erdos_361.bigTheta` | 4 | 2 | no | 8/2 | none | high | Fix statement as for bigO; current version closable by contradiction from hA 0 1 and hA 2 1. |
| `ErdosProblems/361.lean` | `erdos_361.smallO` | 4 | 2 | no | 8/2 | none | high | Fix statement as for bigO; current version closable by contradiction from hA 0 1 and hA 2 1. |
| `ErdosProblems/364.lean` | `erdos_364` | 9 |  | yes | 9/10 | none | high | Leave open; no viable attack. Any claimed counterexample would be checkable via the Decidable instance for Pow |
| `ErdosProblems/364.lean` | `erdos_364.variants.strong` | 9 |  | yes | 9/10 | none | high | Leave open. |
| `ErdosProblems/366.lean` | `erdos_366` | 8 | 6 | yes | 8/9 | large | high | Leave open; a witness n would close the answer(sorry) side instantly via the Decidable instance for Nat.Full p |
| `ErdosProblems/366.lean` | `erdos_366.variants.three_two` | 8 |  | yes | 8/9 | none | high | Leave open. |
| `ErdosProblems/366.lean` | `erdos_366.variants.weaker` | 8 | 6 | yes | 8/9 | large | high | Leave open; a witness would be kernel-checkable via Decidable Full. |
| `ErdosProblems/371.lean` | `erdos_371` | 8 |  | yes | 9/10 | none | high | Leave open. |
| `ErdosProblems/373.lean` | `erdos_373` | 8 |  | yes | 8/9 | none | high | Leave open. |
| `ErdosProblems/373.lean` | `erdos_373.variants.maximal_solution` | 8 |  | yes | 8/9 | none | high | Leave open; the membership conjunct (16,[14,5,2]) in S alone is provable by decide/norm_num (16! = 240*14! = 1 |
| `ErdosProblems/373.lean` | `erdos_373.variants.suranyi` | 8 |  | yes | 8/9 | none | high | Leave open. |
| `ErdosProblems/375.lean` | `erdos_375` | 9 |  | yes | 9/10 | none | high | Leave open. Note duplicate open formalizations of the same conjecture at FormalConjectures/Wikipedia/Grimm.lea |
| `ErdosProblems/376.lean` | `erdos_376` | 8 |  | yes | 8/9 | none | high | Leave open. |
| `ErdosProblems/377.lean` | `erdos_377` | 8 |  | yes | 8/9 | none | high | Leave open. |
| `ErdosProblems/383.lean` | `erdos_383` | 8 |  | yes | 8/9 | none | medium | Leave open. |
| `ErdosProblems/385.lean` | `erdos_385.parts.i` | 8 |  | yes | 8/9 | none | high | Leave open. |
| `ErdosProblems/385.lean` | `erdos_385.parts.ii` | 8 |  | yes | 8/9 | none | high | Leave open. |
| `ErdosProblems/385.lean` | `erdos_385.variants.lb` | 8 |  | yes | 8/9 | none | medium | Leave open. |
| `ErdosProblems/386.lean` | `erdos_386` | 8 |  | yes | 8/9 | none | medium | Leave open. |
| `ErdosProblems/386.lean` | `erdos_386.variants.forall` | 8 |  | yes | 8/9 | none | medium | Leave open. |
| `ErdosProblems/386.lean` | `erdos_386.variants.two` | 8 |  | yes | 8/9 | none | medium | Leave open. |
| `ErdosProblems/387.lean` | `erdos_387.variants.schinzel` | 8 |  | yes | 8/9 | none | medium | Check the BNPZ26 paper and recent literature for whether the full Schinzel characterization was settled; other |
| `ErdosProblems/389.lean` | `erdos_389` | 8 |  | yes | 8/9 | none | high | Leave open; individual n are decidable but the universal statement needs a proof idea. |
| `ErdosProblems/39.lean` | `erdos_39` | 8 |  | yes | 9/10 | none | high | Leave open. |
| `ErdosProblems/390.lean` | `erdos_390` | 8 |  | yes | 8/9 | none | high | Leave open. |
| `ErdosProblems/394.lean` | `erdos_394.parts.i` | 8 |  | yes | 8/9 | none | high | Leave open; monitor erdosproblems.com. The t definition (sInf over {m>0 : n \| m(m+1)}) is sound for n>=1 and  |
| `ErdosProblems/394.lean` | `erdos_394.parts.ii` | 8 |  | yes | 8/9 | none | high | Leave open. Even the k=2 case (sum t_3 = o(sum t_2)) appears unresolved. |
| `ErdosProblems/394.lean` | `erdos_394.variants.factorial_gap_conjecture` | 8 |  | suspect | 8/9 | none | medium | Confirm the exact k-range against the erdosproblems.com prose and fix the boundary if needed; otherwise leave  |
| `ErdosProblems/394.lean` | `erdos_394.variants.hall_conjecture` | 8 |  | yes | 8/9 | none | medium | Leave open; a literature check on recent work on A344005/t_2 sums (de la Breteche/Tenenbaum school) would be w |
| `ErdosProblems/396.lean` | `erdos_396` | 8 |  | yes | 8/9 | none | high | Leave open; individual k are searchable but the universal statement is the open content. |
| `ErdosProblems/398.lean` | `erdos_398` | 9 |  | yes | 9/10 | none | high | None; recognized hard open problem. Any unconditional resolution needs a breakthrough. |
| `ErdosProblems/40.lean` | `erdos_40` | 4 | 9 | no | 9/1 | none | high | Report the trivialization upstream: the encoding needs a nontriviality constraint (e.g. require some divergent |
| `ErdosProblems/400.lean` | `erdos_400.parts.i` | 8 |  | yes | 8/9 | none | high | Leave open. |
| `ErdosProblems/400.lean` | `erdos_400.parts.ii` | 8 |  | yes | 8/9 | none | high | Leave open. |
| `ErdosProblems/406.lean` | `erdos_406` | 8 |  | yes | 9/9 | none | high | None; genuinely open with no known attack beyond heuristics and Lagarias-style partial structure results. |
| `ErdosProblems/406.lean` | `erdos_406.variants.one_two` | 8 |  | yes | 9/9 | small | high | The mem half (2^15 in the set) is decidable/by decide; the upper-bound half is the open content. Could split i |
| `ErdosProblems/409.lean` | `erdos_409.parts.i` | 4 | 8 | suspect | 8/2 | none | high | Flag upstream that the encoding admits the sInf non-answer; a faithful version should demand a closed form or  |
| `ErdosProblems/409.lean` | `erdos_409.parts.i.isBigO` | 4 | 8 | suspect | 8/1 | none | high | Same as isTheta variant: accept as design-acknowledged placeholder or add a nontriviality spec. |
| `ErdosProblems/409.lean` | `erdos_409.parts.i.isLittleO` | 4 | 8 | suspect | 8/2 | none | high | Same as the other asymptotic variants. |
| `ErdosProblems/409.lean` | `erdos_409.parts.i.isTheta` | 4 | 8 | suspect | 8/1 | none | high | Acknowledge as design-accepted loophole; a real contribution would prove nontrivial bounds (e.g. c(n) << log n |
| `ErdosProblems/409.lean` | `erdos_409.parts.ii` | 8 |  | yes | 8/9 | none | high | Leave open; small-case basin computation (A039651) could inform but not settle it. |
| `ErdosProblems/409.lean` | `erdos_409.parts.iii` | 4 | 8 | no | 8/1 | none | high | Report upstream: answer must be stated as a function of p only (move alpha out of scope, e.g. 'HasDensity (ans |
| `ErdosProblems/409.lean` | `erdos_409.variants.sigma` | 8 |  | suspect | 8/9 | none | high | Treat jointly with sigma_termination; the extra IsLeast/answer layer adds nothing once the sInf loophole is no |
| `ErdosProblems/409.lean` | `erdos_409.variants.sigma_isBigO` | 4 | 8 | suspect | 8/1 | none | high | Design-acknowledged placeholder. |
| `ErdosProblems/409.lean` | `erdos_409.variants.sigma_isLittleO` | 4 | 8 | suspect | 8/2 | none | high | Design-acknowledged placeholder. |
| `ErdosProblems/409.lean` | `erdos_409.variants.sigma_isTheta` | 4 | 8 | suspect | 8/1 | none | high | Design-acknowledged placeholder; treat as spec-weak. |
| `ErdosProblems/409.lean` | `erdos_409.variants.sigma_prime_termination` | 8 |  | yes | 8/9 | none | high | Deduplicate with sigma_termination upstream (one bare form, one answer form of the identical proposition); mat |
| `ErdosProblems/409.lean` | `erdos_409.variants.sigma_termination` | 8 |  | yes | 8/9 | none | high | Leave open; extending OEIS-style verification for small n is possible but cannot settle it. |
| `ErdosProblems/41.lean` | `erdos_41` | 8 |  | suspect | 9/9 | none | medium | Suggest upstream switching NtupleCondition to a multiset/tuple formulation (sorted tuples a1<=a2<=a3) to match |
| `ErdosProblems/410.lean` | `erdos_410` | 8 |  | yes | 8/9 | none | high | Leave open. |
| `ErdosProblems/412.lean` | `erdos_412` | 8 |  | yes | 9/9 | none | high | Leave open; no viable proof strategy known for trajectory-merging problems of iterated sigma. |
| `ErdosProblems/413.lean` | `erdos_413.parts.i` | 8 |  | yes | 8/9 | none | high | Leave open; computational exploration of barriers is possible but a proof of infinitude is out of reach. |
| `ErdosProblems/413.lean` | `erdos_413.parts.ii` | 8 |  | yes | 8/9 | none | high | Leave open; requires control of omega on all of n-1, n-2, ... simultaneously, related to unproven equidistribu |
| `ErdosProblems/413.lean` | `erdos_413.variants.bigOmega` | 8 |  | yes | 8/9 | none | high | Leave open. |
| `ErdosProblems/414.lean` | `erdos_414` | 8 |  | yes | 9/9 | none | high | Leave open; same trajectory-merging obstruction as problem 412. |
| `ErdosProblems/416.lean` | `erdos_416.parts.i` | 8 |  | yes | 9/9 | none | high | Leave open; any progress would come from refining Ford's machinery. |
| `ErdosProblems/416.lean` | `erdos_416.parts.ii` | 2 | 4 | no | 9/2 | none | high | Close with answer f := V: for x >= 1, V x >= 1 (1 = phi(1) is counted), so V x / V x is eventually 1 and Tends |
| `ErdosProblems/417.lean` | `erdos_417.parts.i` | 8 |  | yes | 9/9 | none | medium | Leave open; connected to Ford's totient distribution machinery. |
| `ErdosProblems/417.lean` | `erdos_417.parts.ii` | 8 |  | yes | 9/9 | none | medium | Leave open. |
| `ErdosProblems/418.lean` | `erdos_418.variants.density` | 8 |  | yes | 8/9 | none | high | Leave open; a proof would likely need to show even numbers avoid p+q-1-type representations with positive dens |
| `ErdosProblems/42.lean` | `erdos_42.variants.constructive` | 1 | 2 | yes | 2/5 | none | medium | Port/import the external Lean proof of erdos_42, set answer(True), and derive f from the atTop-eventually thre |
| `ErdosProblems/421.lean` | `erdos_421` | 8 |  | yes | 8/9 | none | high | Leave open. |
| `ErdosProblems/422.lean` | `erdos_422` | 10 |  | no | 9/10 | none | high | Redefine f before any proof attempt: e.g. an Option-valued/fuel-based total function or an inductively defined |
| `ErdosProblems/422.lean` | `erdos_422.variants.eventually_const` | 10 |  | no | 9/10 | none | high | Same fix as erdos_422: redefine f, then re-state. |
| `ErdosProblems/422.lean` | `erdos_422.variants.growth_rate` | 2 | 4 | no | 9/1 | none | high | Either close formally with answer g := (fun n => (f n : R)) via Asymptotics.isBigO_refl, or (better) flag upst |
| `ErdosProblems/422.lean` | `erdos_422.variants.surjective` | 10 |  | no | 9/10 | none | high | Same fix as erdos_422: redefine f, then re-state. |
| `ErdosProblems/424.lean` | `erdos_424` | 8 |  | yes | 8/9 | none | high | Leave open; numerical exploration of A005244's density is possible but no proof route is known. |
| `ErdosProblems/428.lean` | `erdos_428` | 8 |  | yes | 9/9 | none | medium | Leave open; related to prime tuple/Goldbach-type barriers. |
| `ErdosProblems/44.lean` | `erdos_44` | 8 |  | yes | 8/9 | none | high | Leave open; the difficulty is completing an arbitrary (possibly adversarial) Sidon set to near-maximal density |
| `ErdosProblems/44.lean` | `erdos_44.variants.empty_start` | 5 |  | yes | 4/8 | none | high | Formalize (large effort): Bose-Chowla Sidon construction over F_{q^2} (discrete logs in the cyclic unit group, |
| `ErdosProblems/445.lean` | `erdos_445` | 9 |  | yes | 9/10 | none | high | Leave open; going below the 3/4 exponent means beating the Weil square-root barrier for Kloosterman-type sums  |
| `ErdosProblems/454.lean` | `erdos_454` | 8 |  | yes | 9/9 | none | high | Leave open; progress would come from quantitative convexity results for the prime sequence. |
| `ErdosProblems/455.lean` | `erdos_455` | 8 |  | yes | 8/9 | none | high | Leave open; improving Richter's method toward divergence is the identifiable avenue. |
| `ErdosProblems/458.lean` | `erdos_458` | 9 |  | yes | 9/9 | none | high | Leave open. Note the conjecture implies no prime gap (p_k, p_{k+1}) contains two prime squares q^2 < r^2 (thei |
| `GreensOpenProblems/1.lean` | `green_1` | 9 |  | yes | 9/10 | none | high | No action; keep as open. IsSumFree = Disjoint (A+A) A matches the classical definition (a+b=c forbidden, a=b a |
| `GreensOpenProblems/12.lean` | `green_12` | 8 |  | yes | 9/9 | none | medium | Keep open; monitor Sidorenko-conjecture literature (entropy/Fourier-positivity methods are the identifiable av |
| `GreensOpenProblems/14.lean` | `W_3_20_lower` | 0 | 1 | yes | 2/2 | small | high | Close the catalog statement: set answer(True) in 14.lean and prove with Iff.intro/iff_of_true using Green14.Fa |
| `GreensOpenProblems/14.lean` | `W_3_21_lower` | 0 | 1 | yes | 2/4 | small | medium | Port zeros21 into the merged FunctionCertificateBridge bitmask pattern (as done for t=20), run kernel decide,  |
| `GreensOpenProblems/14.lean` | `W_3_22_lower` | 0 | 1 | yes | 2/4 | small | medium | Port certificate to merged kernel bridge, set answer(True), prove via W_ge_succ_of_checks; verify build. |
| `GreensOpenProblems/14.lean` | `W_3_23_lower` | 0 | 1 | yes | 2/4 | small | medium | Port certificate to merged kernel bridge, set answer(True), prove via W_ge_succ_of_checks; verify build. |
| `GreensOpenProblems/14.lean` | `W_3_24_lower` | 0 | 1 | yes | 2/4 | small | medium | Port certificate to merged kernel bridge, set answer(True), prove via W_ge_succ_of_checks; verify build. |
| `GreensOpenProblems/14.lean` | `W_3_25_lower` | 0 | 1 | yes | 2/4 | small | medium | Port certificate to merged kernel bridge, set answer(True), prove via W_ge_succ_of_checks; verify build. |
| `GreensOpenProblems/14.lean` | `W_3_26_lower` | 0 | 1 | yes | 2/4 | small | medium | Port certificate to merged kernel bridge, set answer(True), prove via W_ge_succ_of_checks; verify build. |
| `GreensOpenProblems/14.lean` | `W_3_27_lower` | 0 | 1 | yes | 2/4 | small | medium | Port certificate to merged kernel bridge, set answer(True), prove via W_ge_succ_of_checks; verify build. |
| `GreensOpenProblems/14.lean` | `W_3_28_lower` | 0 | 1 | yes | 2/4 | small | medium | Port certificate to merged kernel bridge, set answer(True), prove via W_ge_succ_of_checks; verify build. |
| `GreensOpenProblems/14.lean` | `W_3_29_lower` | 0 | 1 | yes | 2/4 | small | medium | Port certificate to merged kernel bridge, set answer(True), prove via W_ge_succ_of_checks; verify build. |
| `GreensOpenProblems/14.lean` | `W_3_30_lower` | 0 | 1 | yes | 2/4 | small | medium | Port certificate to merged kernel bridge, set answer(True), prove via W_ge_succ_of_checks; verify build. |
| `GreensOpenProblems/14.lean` | `W_3_31_lower` | 0 | 1 | yes | 2/4 | medium | medium | Port certificate to merged kernel bridge, set answer(True), prove via W_ge_succ_of_checks (N+1 = 931 > 930); v |
| `GreensOpenProblems/14.lean` | `W_3_32_lower` | 0 | 1 | yes | 2/4 | medium | medium | Port certificate to merged kernel bridge, set answer(True); verify build. |
| `GreensOpenProblems/14.lean` | `W_3_33_lower` | 0 | 1 | yes | 2/4 | medium | medium | Port certificate to merged kernel bridge, set answer(True); verify build. |
| `GreensOpenProblems/14.lean` | `W_3_34_lower` | 0 | 1 | yes | 2/4 | medium | medium | Port certificate to merged kernel bridge, set answer(True); verify build. |
| `GreensOpenProblems/14.lean` | `W_3_35_lower` | 0 | 1 | yes | 2/4 | medium | medium | Port certificate to merged kernel bridge, set answer(True); verify build. |
| `GreensOpenProblems/14.lean` | `W_3_36_lower` | 0 | 1 | yes | 2/4 | medium | medium | Port certificate to merged kernel bridge, set answer(True); verify build. |
| `GreensOpenProblems/14.lean` | `W_3_37_lower` | 0 | 1 | yes | 2/4 | medium | medium | Port certificate to merged kernel bridge, set answer(True); verify build. |
| `GreensOpenProblems/14.lean` | `W_3_38_lower` | 0 | 1 | yes | 2/4 | medium | medium | Port certificate to merged kernel bridge, set answer(True); verify build. |
| `GreensOpenProblems/14.lean` | `W_3_39_lower` | 0 | 1 | yes | 2/5 | medium | medium | Port certificate to merged kernel bridge (bitmask form), set answer(True); verify build. If kernel decide is t |
| `GreensOpenProblems/14.lean` | `green_14_polynomial` | 1 | 4 | suspect | 9/10 | none | high | Report upstream: label should not be 'research open' as stated, and the statement likely misrenders Problem 14 |
| `GreensOpenProblems/14.lean` | `green_14_variant_2r2` | 8 | 6 | yes | 8/9 | large | high | In principle SAT-searchable per candidate r (certificate = the colouring, kernel-checkable via the merged Func |
| `GreensOpenProblems/15.lean` | `green_15` | 9 |  | yes | 9/9 | none | high | Leave as open; no internal or external resolution. Any progress would be a breakthrough in combinatorics on wo |
| `GreensOpenProblems/16.lean` | `green_16` | 4 | 8 | suspect | 9/3 | none | high | Tighten the spec (e.g. ask for asymptotics of f, or forbid self-referential answers by convention); the echo c |
| `GreensOpenProblems/16.lean` | `green_16_conjectured_lower_bound` | 8 |  | yes | 9/9 | none | medium | Leave open; progress = any lower bound N^(1/2+eps). Attribution of this exact conjectured shape to Green's tex |
| `GreensOpenProblems/16.lean` | `green_16_lower_bound` | 5 |  | yes | 5/7 | none | medium | Retag research solved; formalize Ruzsa's Sidon-type construction for this invariant equation - medium effort ( |
| `GreensOpenProblems/16.lean` | `green_16_upper_bound` | 5 |  | yes | 8/9 | none | medium | Retag research solved; formalization is research-scale (almost-periodicity machinery, Fourier analysis on Z). |
| `GreensOpenProblems/16.lean` | `zhao_question` | 8 |  | suspect | 8/9 | none | medium | Rewrite as answer(sorry) iff exists-form, and align the nontriviality convention with the source before invest |
| `GreensOpenProblems/18.lean` | `green_18` | 8 |  | yes | 9/9 | none | medium | Leave open. Key obstruction: no nonabelian analog of the Ajtai-Szemeredi argument for the gx-side action; prog |
| `GreensOpenProblems/19.lean` | `green_19.lower` | 5 |  | yes | 7/9 | none | medium | Retag research solved; formalize Mandache's (or directly FSSZ's) lower-bound construction plus the sInf bookke |
| `GreensOpenProblems/19.lean` | `green_19.upper` | 5 |  | yes | 7/9 | none | medium | Retag research solved; formalizing Mandache's positive result needs heavy regularity/analytic machinery - rese |
| `GreensOpenProblems/2.lean` | `green_2` | 8 |  | yes | 9/9 | none | high | Leave open; progress = improving Sanders' exponent or pushing Ruzsa's construction below (log n)^K. |
| `GreensOpenProblems/22.lean` | `green_22` | 8 |  | suspect | 9/9 | none | medium | Consider re-specifying the improvement target (e.g. exp(r^C) or exp(exp(r^eps))). As stated, first try extract |
| `GreensOpenProblems/24.lean` | `conjecture` | 8 |  | yes | 8/8 | none | medium | Leave open; a first milestone would be formalizing the interval count to get gamma >= 1/3 (improving the state |
| `GreensOpenProblems/24.lean` | `green_24` | 4 | 8 | suspect | 8/1 | none | high | Respec as the asymptotic question (the file's variants.conjecture already does this); flag the echo loophole t |
| `GreensOpenProblems/25.lean` | `green_25` | 4 | 8 | suspect | 9/1 | none | high | Respec as bound-improvement statements (the file's green_25.upper/.lower already do this); flag the echo looph |
| `GreensOpenProblems/25.lean` | `green_25.lower` | 8 |  | yes | 8/8 | none | medium | Leave open; milestone: property for k ~ C log log N with explicit constant, then (log log N)^(1+eps). |
| `GreensOpenProblems/25.lean` | `green_25.upper` | 8 |  | yes | 8/8 | none | medium | Leave open; a first milestone is re-analyzing the ESS89 construction to see how far below N/log N it can be pu |
| `GreensOpenProblems/26.lean` | `green_26.variants.open` | 8 |  | yes | 9/9 | none | high | Leave open; monitor whether Yu's method extends beyond p = 3 - that would be the natural next milestone. |
| `GreensOpenProblems/27.lean` | `green_27.equivalent` | 4 | 8 | suspect | 9/1 | none | high | Flag echo loophole; prefer the .lower/.upper improvement forms in the same file. |
| `GreensOpenProblems/27.lean` | `green_27.lower` | 8 |  | yes | 9/9 | none | medium | Leave open. Echo ans := m fails (would need the open fact lowerBest =o m), so the encoding genuinely demands n |
| `GreensOpenProblems/27.lean` | `green_27.upper` | 8 |  | yes | 9/9 | none | medium | Leave open. Echo ans := m fails (would need the open fact m =o (log p)^2). |
| `GreensOpenProblems/28.lean` | `green_28` | 8 |  | yes | 8/8 | none | medium | Leave open; small-support cases are finite semialgebraic problems, so a computational attack on small cases (s |
| `GreensOpenProblems/29.lean` | `green_29` | 8 |  | yes | 9/9 | none | high | Leave open; the obstruction is making almost-periodicity arguments polynomially efficient in K in the nonabeli |
| `GreensOpenProblems/3.lean` | `green_3` | 8 |  | yes | 8/8 | none | medium | Leave open; a milestone would be any measure threshold < 1 forcing a multiplicative triple in open sets. |
| `GreensOpenProblems/31.lean` | `green_31.lower` | 9 |  | yes | 9/10 | none | high | Keep open; no known avenue. Formalization audited: Tendsto(ans - sqrt) atTop plus frequent ans <= F correctly  |
| `GreensOpenProblems/31.lean` | `green_31.upper` | 8 |  | yes | 8/10 | none | medium | Keep open; monitor Sidon-set literature for post-2025 improvements to the 0.98183 constant. |
| `GreensOpenProblems/31.lean` | `green_31.variants.abelian` | 4 | 2 | no | 8/4 | none | high | Report defect upstream: IsSidon needs the distinct-pair/group convention for 2-torsion groups. Meanwhile the f |
| `GreensOpenProblems/31.lean` | `green_31.variants.lower_eventually` | 9 |  | yes | 9/10 | none | high | Keep open. |
| `GreensOpenProblems/31.lean` | `green_31.variants.sidon_01n` | 4 | 2 | no | 8/3 | none | high | Report defect upstream: use a distinct-pair Sidon/B_2 definition for F_2^n. Meanwhile the theorem closes with  |
| `GreensOpenProblems/31.lean` | `green_31.variants.upper_eventually` | 8 |  | yes | 8/10 | none | medium | Keep open; monitor literature. |
| `GreensOpenProblems/31.lean` | `green_31.variants.zmod_p` | 8 |  | yes | 8/9 | none | high | Keep open. Formalization faithful: single o(1) function along atTop forces card(S p)/sqrt(p) -> 1 along primes |
| `GreensOpenProblems/32.lean` | `green_32` | 8 |  | yes | 8/9 | none | high | Keep open. Formalization audited: HasLargeGapDilate embeds 100 < omega p < p as provable conjuncts, which hold |
| `GreensOpenProblems/32.lean` | `green_32.variants.log_regime` | 8 |  | yes | 8/9 | none | medium | Keep open. The universal quantification over all omega ~ 10 log p is a reasonable formalization of 'sets of si |
| `GreensOpenProblems/33.lean` | `green_33` | 8 |  | yes | 8/8 | small | high | Leave open; computational search for optimal additive covers of Z/q for q up to a few thousand could inform th |
| `GreensOpenProblems/35.lean` | `green_35.lower` | 8 |  | yes | 8/10 | medium | medium | Keep open, but check CS17's exact constant: if their proof certifies a value strictly above 0.64 (0.64 being a |
| `GreensOpenProblems/35.lean` | `green_35.upper` | 8 | 6 | suspect | 7/9 | medium | medium | First fix the constant against Green's list / MV10 (0.7549 vs 0.7505). Path to close: LP/annealing search for  |
| `GreensOpenProblems/36.lean` | `green_36` | 9 |  | yes | 10/10 | none | high | Keep open; do not attempt. The file honestly separates Green's disjointness condition (this theorem) from CKS' |
| `GreensOpenProblems/36.lean` | `green_36.variants.cks05` | 9 |  | yes | 10/10 | none | medium | Keep open; verify the CKS 4.1 index pattern against the published paper when possible. |
| `GreensOpenProblems/37.lean` | `green_37` | 4 | 2 | no | 8/4 | none | high | Report the spec defect upstream (answer should be constrained to a closed form, or the statement replaced by t |
| `GreensOpenProblems/37.lean` | `green_37_asymptotic` | 4 | 2 | no | 8/1 | none | high | Report spec defect; replace with a genuine two-sided asymptotic statement (e.g. explicit upper/lower bound pai |
| `GreensOpenProblems/37.lean` | `green_37_bigO` | 2 | 4 | no | 8/1 | none | high | Close via isBigO_refl if a formal resolution is wanted, but better: report spec defect (statement should deman |
| `GreensOpenProblems/37.lean` | `green_37_littleO` | 2 | 4 | no | 8/2 | none | high | Close via the f*N trick if desired; report spec defect upstream. |
| `GreensOpenProblems/37.lean` | `green_37_theta` | 4 | 2 | no | 8/1 | none | high | Report spec defect; a meaningful version must quantify answer over a restricted grammar of functions or state  |
| `GreensOpenProblems/38.lean` | `green_38.lower` | 8 | 5 | yes | 8/7 | large | medium | Literature check arXiv 2607.21517 first. If a larger independent set S in C_7^box m with \|S\|^{1/m} > 367^{1/ |
| `GreensOpenProblems/38.lean` | `green_38.upper` | 9 |  | yes | 9/10 | none | high | Keep open; do not attempt. |
| `GreensOpenProblems/39.lean` | `green_39` | 8 |  | yes | 8/9 | none | medium | Keep open. Formalization audited: proportionCoverable's p=0 and k>p junk branches are unreachable for primes w |
| `GreensOpenProblems/39.lean` | `green_39.variant_101` | 8 |  | yes | 9/9 | none | high | Keep open. |
| `GreensOpenProblems/39.lean` | `green_39.variant_theta` | 8 |  | suspect | 8/9 | none | medium | Keep open; consider asking upstream to confirm the intended reading with Green's text. |
| `GreensOpenProblems/4.lean` | `green_4` | 4 | 2 | no | 7/3 | none | high | Report spec defect upstream (answer should be an explicit family, e.g. the extremalFamily construction, with a |
| `GreensOpenProblems/40.lean` | `green_40` | 8 |  | yes | 9/9 | none | high | Keep as open research target; monitor covering-codes literature (Davydov-type constructions vs. lower-bound me |
| `GreensOpenProblems/40.lean` | `green_40.f_eq_one_for_all` | 8 |  | yes | 9/9 | none | high | Keep open; any resolution of f(2) would be the first step. |
| `GreensOpenProblems/40.lean` | `green_40.f_two_eq_one` | 8 |  | yes | 8/9 | none | high | Keep open; a construction-side attack (linear analogues of Struik's codes) is the identifiable avenue. |
| `GreensOpenProblems/40.lean` | `green_40.variants.all_n` | 4 | 7 | no | 3/7 | none | high | Fix the statement to 'Tendsto f_all atTop (nhds top)'. Alternatively the current statement can be legitimately |
| `GreensOpenProblems/40.lean` | `green_40.variants.arbitrary_subsets` | 8 |  | yes | 9/9 | none | medium | Keep open. |
| `GreensOpenProblems/41.lean` | `green_41` | 4 | 5 | no | 8/10 | none | high | Tighten the spec (e.g. require ans = o of the KrLe bound for the SAME C, or demand a fixed iterated-exp level  |
| `GreensOpenProblems/41.lean` | `green_41.variants.exists_better_bound` | 4 | 5 | no | 8/10 | none | high | Replace by a spec that quantifies the improvement (e.g. double-exponential or polynomial bound). Formal closur |
| `GreensOpenProblems/41.lean` | `green_41.variants.polynomial_bound` | 8 |  | yes | 9/10 | none | high | Keep open; track follow-ups to Kravitz-Leng. |
| `GreensOpenProblems/42.lean` | `green_42` | 8 |  | yes | 9/10 | none | high | Keep open; Fourier interpolation on the plane (Sardari) is the identifiable avenue. |
| `GreensOpenProblems/44.lean` | `green_44` | 8 |  | yes | 8/9 | none | medium | Keep open; connects to inverse large-sieve questions (Green 47). |
| `GreensOpenProblems/46.lean` | `green_46.improve_lower` | 8 |  | yes | 9/10 | none | medium | Keep open (equivalent to improving long-gaps-between-primes lower bounds); fix the [Ra38] attribution to [FGK1 |
| `GreensOpenProblems/46.lean` | `green_46.improve_upper` | 8 |  | yes | 9/10 | none | medium | Keep open. |
| `GreensOpenProblems/46.lean` | `green_46.improve_upper_conjectured` | 9 |  | yes | 9/10 | none | medium | Keep open; no known strategy closes the x^(1+o(1)) vs x^2 gap. |
| `GreensOpenProblems/47.lean` | `green_47` | 9 |  | yes | 9/10 | none | medium | Keep open. |
| `GreensOpenProblems/50.lean` | `green_50` | 8 |  | yes | 8/10 | none | medium | Keep open; investigate whether PFR-era techniques give O(log(1/alpha)) for enough summands - the natural avenu |
| `GreensOpenProblems/51.lean` | `green_51` | 4 | 8 | suspect | 9/1 | none | high | Restate as bracketing asymptotics (as the file's solved variants do) or add a closed-form requirement; treat a |
| `GreensOpenProblems/51.lean` | `green_51.one_half` | 8 |  | suspect | 8/10 | none | medium | Consider strengthening the conclusion to subspaces (0 is always in A+A, so this is plausibly equivalent but sh |
| `GreensOpenProblems/52.lean` | `green_52` | 8 |  | yes | 8/10 | none | medium | Keep open. |
| `GreensOpenProblems/52.lean` | `green_52_log` | 8 |  | yes | 8/10 | none | medium | Keep open. |
| `GreensOpenProblems/54.lean` | `green_54` | 8 |  | suspect | 9/10 | none | medium | Either add the finite-dimensional uniform variant or record the equivalence argument; keep open. |
| `GreensOpenProblems/58.lean` | `green_58` | 8 |  | yes | 9/10 | none | medium | Keep open. |
| `GreensOpenProblems/60.lean` | `green_60` | 8 |  | yes | 9/10 | none | high | Keep open. |
| `GreensOpenProblems/61.lean` | `green_61` | 8 |  | yes | 8/10 | none | high | Keep open; TODO in file to add the two known partial results. |
| `GreensOpenProblems/62.lean` | `green_62` | 9 |  | yes | 9/10 | none | medium | Keep open. |
| `OEIS/228828.lean` | `a.infinite` | 9 |  | yes | 9/10 | none | high | No viable strategy; leave open. Do not attempt. |
| `OEIS/231201.lean` | `conjecture` | 9 |  | yes | 9/10 | none | high | Leave open. Producing primes of the form 2^x + y in every additive decomposition is Crocker/Sierpinski-adjacen |
| `OEIS/232174.lean` | `conjecture` | 9 |  | yes | 9/10 | none | high | Leave open. Requires simultaneous prime values of a linear and a quadratic form in every additive decompositio |
| `OEIS/239957.lean` | `conjecture` | 9 |  | yes | 9/10 | none | high | Leave open. Even under GRH, forcing a primitive root inside the sparse set {k^2+1} below p is out of reach (ch |
| `OEIS/280831.lean` | `conjecture` | 8 |  | yes | 8/9 | none | high | Research problem. Possible avenue: quaternion techniques of Machiavelo-Tsopanidis (which proved Sun's 1-3-5 co |
| `OEIS/281976.lean` | `conjecture` | 8 |  | yes | 8/9 | none | high | Track Wu-She arXiv:2511.23223 and successors; a future full proof would make this cat 5 with large formalizati |
| `OEIS/287616.lean` | `conjecture` | 8 |  | yes | 7/9 | none | medium | Research problem with identifiable avenue: ternary quadratic polynomial universality via theta series / ternar |
| `OEIS/303656.lean` | `conjecture` | 9 |  | yes | 9/10 | none | high | Leave open. Sums of two squares have density x/sqrt(log x) and {3^c+5^d} is log^2-sparse; no covering or circl |
| `OEIS/306477.lean` | `conjecture` | 9 |  | yes | 9/10 | none | high | Leave open. Exponent sum 1/2+1/4+1/6+1/8 = 25/24 barely exceeds 1; quaternary additive problems with a degree- |
| `OEIS/308734.lean` | `conjecture` | 8 |  | yes | 9/9 | none | high | Research problem; avenue = Banerjee's ineffective Gauss-Legendre generalizations plus almost-prime relaxations |
| `OEIS/34693.lean` | `a_isBigO` | 8 |  | yes | 8/9 | none | medium | Possible refutation avenue: known lower-bound constructions for the least prime ≡ 1 (mod n) (Pomerance-style)  |
| `OEIS/34693.lean` | `a_unbounded` | 8 |  | yes | 8/9 | none | medium | Avenue: adapt known omega-results / lower-bound constructions for least primes in progressions to the modulus- |
| `OEIS/34693.lean` | `exists_k` | 9 |  | yes | 9/10 | none | high | Leave open; would follow from a Linnik constant <= 2 with a good implied constant, itself a major open problem |
| `OEIS/34693.lean` | `exists_k_stronger` | 9 |  | yes | 9/10 | none | high | Leave open. |
| `OEIS/357513.lean` | `general_supercongruence` | 8 |  | yes | 7/9 | small | medium | Medium-term research: generalize the AlphaProof m=1 argument (Wolstenholme/WZ-style supercongruence manipulati |
| `OEIS/41.lean` | `noPowerPartitionNumber` | 9 |  | yes | 9/10 | none | high | Leave open. Even the analogous solved problems (perfect powers among Fibonacci numbers) needed deep linear-for |
| `OEIS/56777.lean` | `comesFromPrimeQuadruple_of_a` | 8 |  | yes | 9/9 | none | medium | Research problem of Lehmer/Schinzel totient-rigidity type (compare the classical open conjecture that phi(n+2) |
| `OEIS/63880.lean` | `mod_216_of_a` | 8 |  | yes | 8/8 | none | medium | Attack via the structure route: prove exists_primitive_of_a and a_of_primitive_mul_squarefree (both currently  |
| `OEIS/63880.lean` | `unique_primitive_108` | 8 |  | yes | 9/9 | none | medium | Research: first milestone is proving every primitive term is powerful and divisible by 4 and 27; a full unique |
| `OEIS/67720.lean` | `prime_add_one_of_a` | 8 |  | yes | 9/9 | none | medium | Lehmer-type totient rigidity; avenue: for composite k+1, phi(k+1) <= k - sqrt(k+1)-ish forces phi(k^2+1)/(k^2+ |
| `OEIS/81091.lean` | `conjectureA81091` | 9 |  | yes | 9/10 | none | high | Leave open; no strategy known. |
| `OpenQuantumProblems/13.lean` | `mutuallyUnbiasedBases` | 9 |  | yes | 10/10 | large | high | Keep open. The prime-power piece is itself a large but feasible formalization project (finite-field MUB constr |
| `OpenQuantumProblems/13.lean` | `mutuallyUnbiasedBases_dim10` | 9 |  | yes | 9/10 | large | high | Keep open; no viable formal path known. |
| `OpenQuantumProblems/13.lean` | `mutuallyUnbiasedBases_dim12` | 9 |  | yes | 9/10 | large | high | Keep open; no viable formal path known. |
| `OpenQuantumProblems/13.lean` | `mutuallyUnbiasedBases_dim14` | 9 |  | yes | 9/10 | large | high | Keep open; no viable formal path known. |
| `OpenQuantumProblems/13.lean` | `mutuallyUnbiasedBases_dim15` | 9 |  | yes | 9/10 | large | high | Keep open; no viable formal path known. |
| `OpenQuantumProblems/13.lean` | `mutuallyUnbiasedBases_dim6` | 9 |  | yes | 9/10 | large | high | Keep open. Any progress would come from formalizing the known bounds first; note mutuallyUnbiasedBases_dim6_bo |
| `OpenQuantumProblems/23.lean` | `hasSICPOVM_56` | 1 | 5 | yes | 2/9 | large | medium | Confirm against the primary source (Grassl's exact-solutions data / the 2025 JMP paper) which paper contains t |
| `OpenQuantumProblems/23.lean` | `hasSICPOVM_58` | 8 | 6 | yes | 7/9 | large | medium | Certification avenue: the Weyl-Heisenberg fiducial equations are a polynomial system in ~2d real unknowns; an  |
| `OpenQuantumProblems/23.lean` | `hasSICPOVM_59` | 8 | 6 | yes | 7/9 | large | medium | Same certified-numerics avenue as d=58. |
| `OpenQuantumProblems/23.lean` | `hasSICPOVM_60` | 8 | 6 | yes | 7/9 | large | medium | Same certified-numerics avenue as d=58. |
| `OpenQuantumProblems/23.lean` | `hasSICPOVM_64` | 8 | 6 | yes | 7/9 | large | medium | Same certified-numerics avenue as d=58. |
| `OpenQuantumProblems/23.lean` | `hasSICPOVM_68` | 8 | 6 | yes | 7/9 | large | medium | Same certified-numerics avenue as d=58. |
| `OpenQuantumProblems/23.lean` | `hasSICPOVM_69` | 8 | 6 | yes | 7/9 | large | medium | Same certified-numerics avenue as d=58. |
| `OpenQuantumProblems/23.lean` | `hasSICPOVM_70` | 8 | 6 | yes | 7/9 | large | medium | Same certified-numerics avenue as d=58. |
| `OpenQuantumProblems/23.lean` | `hasSICPOVM_71` | 8 | 6 | yes | 7/9 | large | medium | Same certified-numerics avenue as d=58. |
| `OpenQuantumProblems/23.lean` | `hasSICPOVM_72` | 8 | 6 | yes | 7/9 | large | medium | Same certified-numerics avenue as d=58. |
| `OpenQuantumProblems/23.lean` | `hasSICPOVM_75` | 8 | 6 | yes | 7/9 | large | medium | Same certified-numerics avenue as d=58. |
| `OpenQuantumProblems/23.lean` | `sicPOVMs` | 9 |  | yes | 10/10 | none | high | Keep open. Any conditional resolution (e.g. via Stark conjectures) would itself be research-scale to formalize |
| `OpenQuantumProblems/35.lean` | `ame_10_10_open` | 8 |  | yes | 8/10 | large | high | Keep open; monitor literature/upstream. |
| `OpenQuantumProblems/35.lean` | `ame_10_6_open` | 8 |  | yes | 8/10 | large | high | Keep open; monitor literature/upstream. |
| `OpenQuantumProblems/35.lean` | `ame_11_10_open` | 8 |  | yes | 8/10 | large | high | Keep open; monitor literature/upstream. |
| `OpenQuantumProblems/35.lean` | `ame_11_3_open` | 8 |  | yes | 8/10 | large | medium | Keep open; check Grassl's quantum code tables periodically for [[11,0,6]]_3; a resolution either way would lik |
| `OpenQuantumProblems/35.lean` | `ame_11_4_open` | 8 |  | yes | 8/10 | large | medium | Keep open; watch quantum code tables. |
| `OpenQuantumProblems/35.lean` | `ame_11_6_open` | 8 |  | yes | 8/10 | large | high | Keep open; monitor literature/upstream. |
| `OpenQuantumProblems/35.lean` | `ame_12_10_open` | 8 |  | yes | 8/10 | large | high | Keep open; monitor literature/upstream. |
| `OpenQuantumProblems/35.lean` | `ame_12_5_open` | 8 |  | yes | 8/10 | large | medium | Most promising target of the batch after ame_8_4: examine the upstream AME(11,5) construction (likely code/ort |
| `OpenQuantumProblems/35.lean` | `ame_12_6_open` | 8 |  | yes | 8/10 | large | high | Keep open; monitor literature/upstream. |
| `OpenQuantumProblems/35.lean` | `ame_7_10_open` | 8 |  | yes | 8/10 | large | high | Keep open; monitor literature/upstream. |
| `OpenQuantumProblems/35.lean` | `ame_7_6_open` | 8 |  | yes | 8/10 | large | high | Keep open; monitor literature and upstream. If a construction appears, port it in the style of the upstream AM |
| `OpenQuantumProblems/35.lean` | `ame_8_10_open` | 8 |  | yes | 8/10 | large | high | Keep open; monitor literature/upstream. |
| `OpenQuantumProblems/35.lean` | `ame_8_4_open` | 8 |  | yes | 8/10 | large | high | Keep open. Most code-theoretic of the batch: watch quantum-code tables (Grassl) for a [[8,0,5]]_4 resolution;  |
| `OpenQuantumProblems/35.lean` | `ame_8_6_open` | 8 |  | yes | 8/10 | large | high | Keep open; monitor literature/upstream. |
| `OpenQuantumProblems/35.lean` | `ame_9_10_open` | 8 |  | yes | 8/10 | large | high | Keep open; monitor literature/upstream. |
| `OpenQuantumProblems/35.lean` | `ame_9_6_open` | 8 |  | yes | 8/10 | large | high | Keep open; monitor literature/upstream. |
| `OpenQuantumProblems/35.lean` | `oqp_35` | 9 | 4 | yes | 9/10 | large | high | Keep open. Note the spec-level weakness: the set-valued answer(sorry) equation is formally dischargeable by rf |
| `Paper/CardinalityLindelof.lean` | `HasGδSingletons.lindelof_card` | 8 |  | suspect | 9/10 | none | medium | Consider adding a T2/T3 hypothesis to match the survey convention; treat as likely ZFC-independent, not a proo |
| `Paper/CasasAlvero.lean` | `casas_alvero_conjecture` | 5 | 9 | yes | 9/10 | none | medium | Monitor refereeing of Ghosh's proof; formalization would be research-scale (Koszul homology machinery absent f |
| `Paper/CatchUpConjecture.lean` | `value_of_even_mul_succ_self_div_two` | 8 |  | yes | 7/9 | none | high | General case is genuinely open (game-tree grows like N!); partial progress possible by formalizing small-N cas |
| `Paper/Chvatal.lean` | `exists_maximal_star` | 9 |  | yes | 9/10 | none | high | No feasible path; genuinely hard open problem. Nothing internal to port. |
| `Paper/ClaudesCycles.lean` | `cube_hamiltonian_arc_decomposition_even` | 8 | 6 | yes | 7/8 | medium | medium | Attack m = 4 by exact-cover/SAT (64 vertices, 192 arcs, three arc-disjoint Hamiltonian cycles): a negative cer |
| `Paper/ConjugacyClassSizes.lean` | `conjClassSizes_iff_sym_three` | 8 |  | yes | 8/10 | none | high | Key obstruction: the nonsolvable case, which likely needs CFSG-adjacent arguments; progress = formalizing the  |
| `Paper/DeGiorgi.lean` | `DeGiorgi_eight` | 9 |  | yes | 9/10 | none | high | No feasible formal path; watch literature. |
| `Paper/DeGiorgi.lean` | `DeGiorgi_five` | 9 |  | yes | 9/10 | none | high | No feasible formal path; watch literature. |
| `Paper/DeGiorgi.lean` | `DeGiorgi_four` | 9 |  | yes | 9/10 | none | high | No feasible formal path; watch literature. |
| `Paper/DeGiorgi.lean` | `DeGiorgi_le_eight` | 9 |  | yes | 10/10 | none | high | Not a target; even the solved n=2,3 cases would be research-scale formalization (Liouville-type theorems, elli |
| `Paper/DeGiorgi.lean` | `DeGiorgi_seven` | 9 |  | yes | 9/10 | none | high | No feasible formal path; watch literature. |
| `Paper/DeGiorgi.lean` | `DeGiorgi_six` | 9 |  | yes | 9/10 | none | high | No feasible formal path; watch literature. |
| `Paper/Dubner.lean` | `dubner_conjecture` | 9 |  | yes | 10/10 | none | high | Not a target; any proof would be a historic breakthrough. |
| `Paper/FusibleNumber.lean` | `conj_7_1` | 8 |  | suspect | 8/9 | none | medium | Verify the reformulation against the paper (small literature check); genuine resolution is research-level (the |
| `Paper/HartshorneConjecture.lean` | `harthshorne_conjecture` | 9 |  | yes | 10/10 | none | high | Not a target. Repo hygiene: the statement depends on the sorried instance hasFiniteCoproductsVectorBundles (ne |
| `Paper/Homogenous.lean` | `countablyMonolithicSpace_card_lt` | 8 |  | yes | 9/10 | none | medium | Not a target; possibly independent of ZFC. |
| `Paper/Homogenous.lean` | `countablyMonolithicSpace_exists_nhds_generated_countable` | 8 |  | suspect | 8/10 | none | low | Literature check the exact wording of Problem 17 in [Ar2013] before any resolution attempt. |
| `Paper/Homogenous.lean` | `firstCountableTopology_of_countablyMonolithicSpace` | 8 |  | yes | 8/10 | none | medium | Not a target. |
| `Paper/Homogenous.lean` | `homogeneousSpace_exists_inj_tendsto` | 8 |  | yes | 9/10 | none | high | Not a target; possibly independent of ZFC, in which case the answer(sorry) iff is unprovable either way. |
| `Paper/Homogenous.lean` | `homogeneousSpace_exists_surjective` | 8 |  | yes | 9/10 | none | medium | Not a target; watch set-theoretic topology literature. |
| `Paper/Kurepa.lean` | `kurepa_conjecture` | 9 |  | yes | 9/10 | none | high | Not a target; no known approach beyond computation. |
| `Paper/Kurepa.lean` | `kurepa_conjecture.variants.gcd` | 9 |  | yes | 9/10 | none | high | Not a target. |
| `Paper/Kurepa.lean` | `kurepa_conjecture.variants.prime` | 9 |  | yes | 9/10 | none | high | Not a target. |
| `Paper/LatinTableau.lean` | `LatinTableauConjecture` | 8 |  | yes | 8/9 | none | medium | Watch literature; partial progress possible by verifying small shapes computationally (per-shape statement is  |
| `Paper/MonochromaticQuantumGraph.lean` | `eqSystem10_no_solution_d3` | 8 |  | yes | 8/9 | none | high | Open. For D=3>3 it would follow from the (10,3) case via the fork's generic color-restriction lemma; no known  |
| `Paper/MonochromaticQuantumGraph.lean` | `eqSystem10_no_solution_d3_int` | 8 | 6 | yes | 7/9 | large | medium | Same mod-2 SAT route as N=8 in principle (405 GF(2) variables, 59049 equations, 945 degree-5 monomials each),  |
| `Paper/MonochromaticQuantumGraph.lean` | `eqSystem10_no_solution_d3_real` | 8 |  | yes | 8/9 | none | high | Open; no specific route. |
| `Paper/MonochromaticQuantumGraph.lean` | `eqSystem10_no_solution_d3_trinary_int` | 8 | 6 | yes | 6/9 | large | medium | Same as the N=10 integer case: mod-2 SAT route at research-grade scale; direct exact ternary encoding (405 ter |
| `Paper/MonochromaticQuantumGraph.lean` | `eqSystem10_no_solution_d4` | 8 |  | yes | 8/9 | none | medium | Open. For D=4>3 it would follow from the (10,3) case via the fork's generic color-restriction lemma; no known  |
| `Paper/MonochromaticQuantumGraph.lean` | `eqSystem10_no_solution_d5` | 8 |  | yes | 8/9 | none | medium | Open. For D=5>3 it would follow from the (10,3) case via the fork's generic color-restriction lemma; no known  |
| `Paper/MonochromaticQuantumGraph.lean` | `eqSystem10_no_solution_d6` | 8 |  | yes | 8/9 | none | medium | Open. For D=6>3 it would follow from the (10,3) case via the fork's generic color-restriction lemma; no known  |
| `Paper/MonochromaticQuantumGraph.lean` | `eqSystem10_no_solution_d7` | 8 |  | yes | 8/9 | none | medium | Open. For D=7>3 it would follow from the (10,3) case via the fork's generic color-restriction lemma; no known  |
| `Paper/MonochromaticQuantumGraph.lean` | `eqSystem10_no_solution_d8` | 8 |  | yes | 8/9 | none | medium | Open. For D=8>3 it would follow from the (10,3) case via the fork's generic color-restriction lemma; no known  |
| `Paper/MonochromaticQuantumGraph.lean` | `eqSystem10_no_solution_d9` | 8 |  | yes | 8/9 | none | medium | Open. For D=9>3 it would follow from the (10,3) case via the fork's generic color-restriction lemma; no known  |
| `Paper/MonochromaticQuantumGraph.lean` | `eqSystem12_no_solution_d3` | 8 |  | yes | 8/9 | none | high | Open instance of the general Krenn-Gu conjecture; no specific route known over C. |
| `Paper/MonochromaticQuantumGraph.lean` | `eqSystem14_no_solution_d3` | 8 |  | yes | 8/9 | none | high | Open instance of the general Krenn-Gu conjecture; no specific route known over C. |
| `Paper/MonochromaticQuantumGraph.lean` | `eqSystem16_no_solution_d3` | 8 |  | yes | 8/9 | none | high | Open instance of the general Krenn-Gu conjecture; no specific route known over C. |
| `Paper/MonochromaticQuantumGraph.lean` | `eqSystem6_no_solution_d3` | 8 |  | yes | 8/9 | none | high | Track literature; explore transferring the formally-proved D=N argument downward, or a Nullstellensatz certifi |
| `Paper/MonochromaticQuantumGraph.lean` | `eqSystem6_no_solution_d3_int` | 0 |  | yes | 6/8 | medium | high | Set answer(True), wire QuantumGraphGlobal.no_eqSystem_int into the canonical decl (extend FORMAL_CONJECTURES_S |
| `Paper/MonochromaticQuantumGraph.lean` | `eqSystem6_no_solution_d3_real` | 8 |  | yes | 8/9 | none | high | Open. Bogdanov's R>=0 obstruction (recorded in-file) does not extend to signed weights; fork's integer result  |
| `Paper/MonochromaticQuantumGraph.lean` | `eqSystem6_no_solution_d3_trinary_int` | 0 |  | yes | 5/8 | medium | high | Wire QuantumGraphGlobal.no_eqSystem_trinary_int (verbatim statement match, immediate corollary of the Z result |
| `Paper/MonochromaticQuantumGraph.lean` | `eqSystem6_no_solution_d4` | 8 |  | yes | 8/9 | none | high | Would follow from (6,3) via the fork's generic no_solution_of_color_le (works over any semiring); alternativel |
| `Paper/MonochromaticQuantumGraph.lean` | `eqSystem6_no_solution_d5` | 8 |  | yes | 8/9 | none | high | Same as (6,4): follows from (6,3) if that is ever proved; open. |
| `Paper/MonochromaticQuantumGraph.lean` | `eqSystem6_no_solution_d5_int` | 0 |  | yes | 6/8 | medium | high | Apply FORMAL_CONJECTURES_STATUS_PATCH.diff (targets exactly this decl, answer := True, formal_proof link to Qu |
| `Paper/MonochromaticQuantumGraph.lean` | `eqSystem6_no_solution_d5_real` | 8 |  | yes | 8/9 | none | high | Follows from the (6,3) real case via the fork's generic color-restriction lemma; base case open. |
| `Paper/MonochromaticQuantumGraph.lean` | `eqSystem6_no_solution_d5_trinary_int` | 0 |  | yes | 5/8 | medium | high | Apply FORMAL_CONJECTURES_STATUS_PATCH.diff (targets this decl via no_eqSystem6_d5_trinary_int). |
| `Paper/MonochromaticQuantumGraph.lean` | `eqSystem6_no_solution_ge3` | 8 |  | yes | 8/9 | none | high | Formally equivalent to the single (6,3) case via the fork's no_solution_ge_iff_base (generic semiring); so res |
| `Paper/MonochromaticQuantumGraph.lean` | `eqSystem6_no_solution_ge3_int` | 0 |  | yes | 6/8 | medium | high | Apply the status patch (no_eqSystem6_ge3_int gives exactly the universally quantified statement) after certifi |
| `Paper/MonochromaticQuantumGraph.lean` | `eqSystem6_no_solution_ge3_real` | 8 |  | yes | 8/9 | none | high | Formally equivalent to the (6,3) real case via no_solution_ge_iff_base (generic semiring). |
| `Paper/MonochromaticQuantumGraph.lean` | `eqSystem6_no_solution_ge3_trinary_int` | 0 |  | yes | 5/8 | medium | high | Apply the status patch (no_eqSystem6_ge3_trinary_int matches verbatim). |
| `Paper/MonochromaticQuantumGraph.lean` | `eqSystem8_no_solution_d3` | 8 |  | yes | 8/9 | none | high | Open; no route beyond the general Krenn-Gu program. Watch for extensions of the formal D=N technique. |
| `Paper/MonochromaticQuantumGraph.lean` | `eqSystem8_no_solution_d3_int` | 6 | 8 | yes | 6/8 | large | medium | Extend the QuantumGraphN6D3 pipeline: reduce mod 2 (ring hom argument is N-generic), classify odd-perfect-matc |
| `Paper/MonochromaticQuantumGraph.lean` | `eqSystem8_no_solution_d3_real` | 8 |  | yes | 8/9 | none | high | Open; no specific route. |
| `Paper/MonochromaticQuantumGraph.lean` | `eqSystem8_no_solution_d3_trinary_int` | 6 | 8 | yes | 5/8 | large | medium | Follows for free from any N=8 integer resolution (trinary subset of Z); or attack directly as a finite CSP - b |
| `Paper/MonochromaticQuantumGraph.lean` | `eqSystem_no_solution_ge6_ge3` | 9 |  | yes | 9/10 | none | high | Recognized open problem; realistic progress = new graph classes (extending connectivity<=2 / cubic / sparse re |
| `Paper/MonochromaticQuantumGraph.lean` | `eqSystem_no_solution_ge6_ge3_int` | 8 |  | yes | 7/9 | large | medium | Promising avenue: prove the mod-2 obstruction uniformly in N (the parity lemma forcing an odd perfect-matching |
| `Paper/MonochromaticQuantumGraph.lean` | `eqSystem_no_solution_ge6_ge3_real` | 9 |  | yes | 9/10 | none | high | Open general conjecture (implied by the complex version, itself open). Progress = same avenues as complex case |
| `Paper/MonochromaticQuantumGraph.lean` | `eqSystem_no_solution_ge6_ge3_trinary_int` | 8 |  | yes | 7/9 | large | medium | Follows from any uniform mod-2/integer argument (see eqSystem_no_solution_ge6_ge3_int); no reason to attack th |
