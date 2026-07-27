# Master audit index

**861** `research open` declarations audited (of 1163 in inventory).
Coverage gaps: 302 missing, 0 duplicated.
See [README.md](./README.md) for methodology and category definitions; per-directory detail reports carry the full 13 audit fields per problem.

## Category histogram

| Cat | Meaning | Count |
|---|---|---|
| 0 | Already solved internally | 37 |
| 1 | Already solved externally | 18 |
| 2 | Trivially or easily solvable | 4 |
| 3 | False / refutable as stated | 14 |
| 4 | Vacuously true / accidentally weakened | 59 |
| 5 | Solved mathematically, not yet formalized | 9 |
| 6 | Computationally solvable with certificate | 2 |
| 7 | Plausibly solvable with moderate formal work | 2 |
| 8 | Deep but approachable research problem | 396 |
| 9 | Major open problem / currently infeasible | 316 |
| 10 | Cannot classify without correction/clarification | 4 |

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
| `ErdosProblems/1145.lean` | `erdos_1145` | 8 |  | yes | 9/9 | none | high | Leave open. Any serious attack must first resolve Erdos 28 (A + A = N with bounded representation function). U |
| `ErdosProblems/1146.lean` | `erdos_1146` | 9 |  | yes | 9/9 | none | high | Leave open. A Lean-tractable sub-goal would be formalizing Ruzsa's necessary density condition for essential c |
| `ErdosProblems/1150.lean` | `erdos_1150` | 9 |  | yes | 9/9 | none | high | Leave open. Do not confuse the merged Parseval PR with progress on the main statement. A meaningful next miles |
| `ErdosProblems/1167.lean` | `binary_colors` | 8 | 3 | suspect | 9/9 | none | medium | Resolve the '+1' convention first; then check the aleph_1 instance against the literature on negative relation |
| `ErdosProblems/1167.lean` | `erdos_1167` | 8 | 3 | suspect | 9/9 | none | medium | Before any proof attempt, confirm against erdosproblems.com/1167 (or the Erdos-Hajnal list) whether kappa_alph |
| `ErdosProblems/1167.lean` | `finite_targets` | 8 |  | yes | 9/9 | none | medium | Leave open; if attacked, start from the finite-colour case (gamma finite), where both sides follow from the in |
| `ErdosProblems/1167.lean` | `infinite_targets` | 8 | 3 | suspect | 9/9 | none | medium | Check the literature (Erdos-Hajnal-Mate-Rado, Combinatorial Set Theory, negative relations for triples) for 2^ |
| `ErdosProblems/1167.lean` | `r_eq_two` | 8 | 3 | suspect | 9/9 | none | medium | Same as `binary_colors`: settle the '+1' convention and the aleph_1 instance before attempting a proof; consid |
| `ErdosProblems/1175.lean` | `erdos_1175` | 8 |  | suspect | 9/10 | none | medium | Leave open. The set-theoretic content (Shelah forcing, Erdos-Hajnal triangle-free graphs of large chromatic nu |
| `ErdosProblems/1175.lean` | `erdos_1175.variants.threshold_formulation` | 8 |  | yes | 9/10 | none | medium | Leave open; prefer this formulation over `erdos_1175` when citing the problem. |
| `ErdosProblems/1176.lean` | `erdos_1176` | 1 | 10 | suspect | 9/10 | none | medium | Restate as a consistency/independence statement (as `erdos_1175.variants.shelah_consistency` does, with an exp |
| `ErdosProblems/119.lean` | `erdos_119.parts.iii` | 1 | 5 | suspect | 8/9 | none | medium | Confirm the site's current status and the Korsky/GPT-5.6 write-up, then set answer(True) and either cite the p |
| `ErdosProblems/1192.lean` | `erdos_1192` | 8 |  | yes | 9/9 | none | high | Leave open. Checked that the obvious cheap reduction fails: adjoining 0 to Ruzsa's order-2 just basis does NOT |
| `ErdosProblems/1199.lean` | `erdos_1199` | 9 |  | suspect | 10/10 | none | medium | Verify against erdosproblems.com/1199 whether A+A is meant to include a = b; if not, restate with distinct sum |
| `ErdosProblems/12.lean` | `erdos_12.parts.iii` | 8 |  | yes | 9/9 | none | high | Leave open. A plausible Lean-side warm-up is the Erdos-Sarkozy density-0 theorem (`erdos_12.variants.erdos_sar |
| `ErdosProblems/120.lean` | `erdos_120` | 9 |  | yes | 10/10 | none | high | Leave open (cat 9). A reasonable Lean milestone is `erdos_120.variants.finite_set` itself, which follows from  |
| `ErdosProblems/1201.lean` | `erdos_1201` | 8 |  | yes | 8/9 | none | medium | Leave open. First milestone: the eps = 1/2 variant, which follows from standard results on the largest prime f |
| `ErdosProblems/1203.lean` | `erdos_1203` | 8 | 10 | suspect | 8/9 | none | medium | Confirm the intended range of k in the source (all k ≥ 1? k ≤ n?) and add the corresponding restriction plus a |
| `ErdosProblems/1209.lean` | `erdos_1209.parts.iii.b` | 8 |  | yes | 9/9 | none | medium | Leave open. A plausible line of attack (and a good Lean sub-target) is: for each odd prime p, 2^(2^k) mod p^2  |
| `ErdosProblems/1209.lean` | `erdos_1209.parts.iii.c` | 9 |  | yes | 10/10 | none | high | Leave open (cat 9). Do not attempt. |
| `ErdosProblems/1209.lean` | `erdos_1209.parts.iii.d` | 8 |  | yes | 9/9 | none | medium | Leave open. The most likely route to a positive answer is an averaging/counting argument over n rather than an |
| `ErdosProblems/1210.lean` | `erdos_1210` | 8 |  | yes | 8/8 | none | medium | Leave open. A tractable first step is the trivial bound sum_{a∈A} 1/(n-a) ≪ log n and the matching Mertens est |
| `ErdosProblems/1210.lean` | `erdos_1210.variants.er80_correction` | 8 |  | yes | 8/8 | none | low | Check the literature (and erdosproblems.com/1210 comments) for whether the [Er77c] form is known false for pri |
| `ErdosProblems/1212.lean` | `erdos_1212` | 8 |  | yes | 8/9 | none | medium | Leave open. Concrete strategy worth recording: every move (a,y) → (a,y±1) forces the fixed coordinate a to be  |
| `ErdosProblems/123.lean` | `erdos_123` | 1 |  | yes | 8/4 | none | high | Set answer(True) and import/port the public Lean 4 proof of the d-completeness theorem, adapting it to this fi |
| `ErdosProblems/123.lean` | `erdos_123.variants.powers_2_3_5_snug` | 8 |  | yes | 8/8 | none | medium | Attempt the density heuristic: the 5-smooth numbers in [x,(1+ε)x] number ≍_ε (log x)^2, and a greedy/subset-su |
| `ErdosProblems/124.lean` | `erdos124.ne_zero` | 8 |  | yes | 8/8 | small | medium | Treat as open: first formalize the BEGL96 {3,4,7} case as a template, then look for the general covering/base- |
| `ErdosProblems/125.lean` | `erdos_125.variants.positive_upper_density` | 8 |  | yes | 8/8 | small | medium | Try to prove upperDensity > 0 directly: \|A∩[0,x]\| ≍ x^{log2/log3} ≈ x^{0.631} and \|B∩[0,x]\| ≍ x^{1/2}, so  |
| `ErdosProblems/125.lean` | `erdos_125.variants.zero_density` | 8 |  | yes | 8/8 | small | medium | Resolve the single open bit sign(upperDensity(A+B)); then both this and the complementary declaration close si |
| `ErdosProblems/125.lean` | `erdos_125.variants.zero_lower_positive_upper_density` | 8 |  | yes | 8/8 | small | medium | Prove upperDensity(A+B) > 0 (energy/second-moment bound along x = 4^m or 12^m), then combine with the existing |
| `ErdosProblems/126.lean` | `erdos_126` | 9 |  | yes | 9/9 | none | high | Do not attempt a resolution; at most formalize the Erdős–Turán lower bound f(n) ≫ log n (the solved sibling) t |
| `ErdosProblems/126.lean` | `erdos_126.variants.isLittleO` | 9 |  | yes | 9/9 | none | high | Leave open. A first milestone would be any nontrivial saving, e.g. f(n) ≤ (1−δ)·2n/log n for the extremal A, w |
| `ErdosProblems/128.lean` | `erdos_128` | 4 | 3 | no | 8/3 | none | high | Fix the statement to: answer(sorry) ↔ ∀ V [Fintype V] (G), (∀ V' : Set V, 2 * V'.ncard ≥ Fintype.card V → 50 * |
| `ErdosProblems/13.lean` | `erdos_13.variants.general` | 8 |  | yes | 8/8 | none | high | Two independent tracks: (a) formalize the easy tight construction A = (rN/(r+1), N] to show the bound cannot b |
| `ErdosProblems/137.lean` | `erdos_137` | 8 |  | yes | 9/9 | small | medium | Formalize the partial results first (e.g. a prime p with k < p ≤ n+k dividing exactly one factor to the first  |
| `ErdosProblems/137.lean` | `erdos_137.variants.multiple_powerful_factors` | 8 |  | suspect | 9/9 | none | medium | Leave open; a milestone is the k = 1 case for large n (equivalently the eventual form of erdos_137), via prime |
| `ErdosProblems/138.lean` | `erdos_138` | 9 |  | yes | 10/10 | none | high | Do not attempt. If any work is done here, formalize the Berlekamp lower bound (erdos_138.variants.prime) or th |
| `ErdosProblems/138.lean` | `erdos_138.variants.dvd_two_pow` | 9 |  | yes | 10/9 | none | high | Leave open; the concrete milestone is a Berlekamp-type construction valid for all k (not just prime+1), which  |
| `ErdosProblems/138.lean` | `erdos_138.variants.quotient` | 9 |  | yes | 10/10 | none | high | Do not attempt. A genuinely useful in-repo contribution is the monotonicity lemma W k ≤ W (k+1) and the (solve |
| `ErdosProblems/14.lean` | `erdos_14.parts.i` | 8 |  | yes | 9/9 | none | medium | Leave open. A useful first milestone is the trivial bound (count ≫ N^{1/3} or similar) via counting the ≤ N pa |
| `ErdosProblems/14.lean` | `erdos_14.parts.ii` | 8 |  | yes | 9/9 | small | medium | Attempt a probabilistic/greedy construction (perfect difference sets modulo q give near-unique representation  |
| `ErdosProblems/141.lean` | `erdos_141` | 9 |  | yes | 10/10 | none | high | Do not attempt. Formalizable in-repo work is limited to small explicit examples (the file already has k = 3). |
| `ErdosProblems/141.lean` | `erdos_141.variants.eleven` | 8 | 6 | yes | 8/9 | large | medium | If a CPAP-11 is ever published, importing it is still nontrivial in Lean: one needs primality certificates for |
| `ErdosProblems/141.lean` | `erdos_141.variants.infinite_general_case` | 9 |  | yes | 10/10 | none | high | Do not attempt. |
| `ErdosProblems/141.lean` | `erdos_141.variants.infinite_three` | 9 |  | yes | 10/10 | none | high | Do not attempt. |
| `ErdosProblems/142.lean` | `erdos_142` | 4 | 9 | suspect | 10/1 | none | high | Add a well-formedness side condition to the answer slot (e.g. require the answer to be built from elementary f |
| `ErdosProblems/142.lean` | `erdos_142.variants.lower` | 9 |  | yes | 10/10 | none | high | Leave open. A realistic sub-target is to add the k=3 case as a separate `research solved` variant citing Kelle |
| `ErdosProblems/142.lean` | `erdos_142.variants.three` | 4 | 9 | suspect | 10/1 | none | high | Constrain the answer slot (explicit closed form) or split into a stated conjecture such as r_3(N) = N^{1-o(1)} |
| `ErdosProblems/142.lean` | `erdos_142.variants.upper` | 4 | 2 | no | 9/1 | none | high | Restate as e.g. `exists f, r_k =O f and f =o (known bound)` mirroring erdos_160.better_upper, or fix an explic |
| `ErdosProblems/143.lean` | `erdos_143.parts.i` | 8 |  | yes | 8/8 | none | medium | Leave open; a reasonable first milestone is the easy bound limsup \|A ∩ [1,x]\|/x ≤ 1 and the analysis of the  |
| `ErdosProblems/143.lean` | `erdos_143.parts.ii` | 8 |  | yes | 8/8 | none | medium | Try to adapt Erdős's 1935 primitive-set argument (assign to each x ∈ A the multiples interval and use a densit |
| `ErdosProblems/145.lean` | `erdos_145` | 8 |  | yes | 8/9 | none | medium | The highest-value in-repo work is formalizing the α ≤ 2 case (Erdős 1951), which is elementary sieve counting; |
| `ErdosProblems/15.lean` | `erdos_15` | 4 | 2 | no | 8/4 | none | high | Rewrite as `answer(sorry) <-> exists L : R, Tendsto (fun N => sum_{k in Finset.range N} (-1)^(k+1)*(k+1)/(nth  |
| `ErdosProblems/153.lean` | `erdos_153` | 8 |  | yes | 8/8 | none | medium | First milestone: formalise the trivial Cauchy-Schwarz lower bound and the t ~ n^2/2 count for Sidon sets, then |
| `ErdosProblems/155.lean` | `erdos_155` | 8 |  | yes | 8/8 | none | medium | Formalise F monotone and F(N+1) <= F(N)+1 as API lemmas first (easy), then attempt k=2 via structure of near-e |
| `ErdosProblems/156.lean` | `erdos_156` | 8 |  | yes | 8/8 | none | medium | Medium-term: formalise Ruzsa's probabilistic construction as the `ruzsa_upper_bound` variant first; the N^{1/3 |
| `ErdosProblems/158.lean` | `erdos_158` | 8 |  | yes | 8/8 | none | medium | Attempt to push the [ESS94] Sidon argument (liminf \|A ∩ [1,N]\| N^{-1/2} (log N)^{1/2} < infinity) to B_2[2]; |
| `ErdosProblems/160.lean` | `erdos_160.better_lower` | 8 |  | suspect | 8/9 | none | medium | Rewrite as `exists lb, lb =O h and (forall c>0, exp(c (log n)^{1/12}) =o lb)` with no vestigial implication, t |
| `ErdosProblems/160.lean` | `erdos_160.better_upper` | 8 |  | yes | 8/9 | none | medium | Research-level. A concrete first milestone is formalising the n^{2/3} colouring (erdos_160.known_upper) so tha |
| `ErdosProblems/168.lean` | `erdos_168.parts.i` | 8 |  | yes | 8/8 | small | medium | Compute F(N) for moderate N via the existing decidable definition to pin down numeric bounds, and formalise th |
| `ErdosProblems/168.lean` | `erdos_168.parts.ii` | 9 |  | suspect | 9/10 | none | medium | Do not attempt directly. Prerequisite: determine or characterise the constant (parts.i). |
| `ErdosProblems/17.lean` | `erdos_17` | 8 |  | yes | 9/9 | none | high | Leave open. The two `research solved` variants (BES99, Elsholtz upper bounds) are the realistic formalisation  |
| `ErdosProblems/170.lean` | `erdos170` | 8 |  | yes | 8/9 | small | high | Formalise Erdos-Gal existence and the Wichmann construction first (erdos170.existing_bounds); determining the  |
| `ErdosProblems/172.lean` | `erdos_172` | 9 |  | suspect | 10/10 | none | medium | Restate with `2 <= S.card` (or add the monochromatic-A requirement explicitly in the docstring) so the formal  |
| `ErdosProblems/18.lean` | `erdos_18a` | 8 |  | yes | 8/9 | none | medium | Formalise Vose's construction first (erdos_18_vose); the (log log)^{O(1)} strengthening stays open. |
| `ErdosProblems/18.lean` | `erdos_18b` | 8 |  | yes | 8/8 | none | medium | First milestone: formalise the elementary h(n!) < n bound; then attack n^{o(1)} via greedy/Egyptian-fraction a |
| `ErdosProblems/18.lean` | `erdos_18c` | 8 |  | yes | 9/9 | none | medium | Same as 18b; treat as the hardest of the three. |
| `ErdosProblems/184.lean` | `erdos_184` | 9 |  | yes | 9/10 | none | medium | Do not attempt the full conjecture. Realistic: formalise the Erdos-Gallai O(n log n) bound (variants.n_log_n)  |
| `ErdosProblems/184.lean` | `erdos_184.variants.covering` | 1 | 5 | yes | 6/9 | none | medium | Reclassify to `@[category research solved]` with answer(True) and the Pyber 1985 citation. Formalising Pyber's |
| `ErdosProblems/188.lean` | `erdos_188` | 8 |  | yes | 8/9 | none | medium | Formalise the two bracketing variants (nonempty, estimate) first; determining the exact k is research-scale an |
| `ErdosProblems/189.lean` | `erdos_189.variants.parallelogram` | 8 |  | suspect | 8/9 | none | medium | Change to `answer(sorry) <-> Erdos189For ...` to match the repo convention, then investigate whether Kovac's i |
| `ErdosProblems/193.lean` | `erdos_193` | 8 |  | yes | 8/9 | none | medium | Formalise the Z^2 case (erdos_193_z2) as the accessible target; Z^3 remains open. |
| `ErdosProblems/195.lean` | `erdos_195` | 8 |  | yes | 8/9 | none | high | Leave open. The realistic first milestone is formalizing Adenwalla's explicit permutation of Z with no monoton |
| `ErdosProblems/196.lean` | `erdos_196` | 8 |  | yes | 8/9 | none | high | Leave open (cat 8). A tractable side project is formalizing the DEGS permutation avoiding monotone 5-APs as a  |
| `ErdosProblems/197.lean` | `erdos_197` | 8 |  | yes | 8/9 | none | medium | Leave open. If one believes the answer is yes, the formal path is an explicit interleaved construction of A, B |
| `ErdosProblems/20.lean` | `erdos_20` | 9 |  | yes | 10/10 | none | high | Do not attempt. At most, formalize the Erdős-Rado (k-1)^n n! bound (the sibling variant erdos_20.variants.erdo |
| `ErdosProblems/200.lean` | `erdos_200` | 8 |  | yes | 9/9 | none | medium | Leave open (cat 8). A worthwhile intermediate formalization is variants.upper: d must be divisible by the prim |
| `ErdosProblems/203.lean` | `erdos_203` | 8 | 6 | yes | 8/8 | medium | medium | Leave open, but this is the most computationally attackable item in the batch: search for a finite covering of |
| `ErdosProblems/208.lean` | `erdos_208.parts.i` | 8 |  | yes | 8/9 | none | high | Leave open (cat 8). Formalizing even the classical O(x^{1/3}) gap bound would be a substantial standalone Math |
| `ErdosProblems/208.lean` | `erdos_208.parts.ii` | 9 |  | yes | 10/10 | none | high | Do not attempt. Strictly harder than parts.i. |
| `ErdosProblems/208.lean` | `erdos_208.variants.log_bound` | 9 |  | suspect | 9/10 | none | medium | Recommend a statement fix upstream: convert to `answer(sorry) ↔ (fun n ↦ ...) =O[atTop] fun n ↦ log (s n)` so  |
| `ErdosProblems/212.lean` | `erdos_212` | 8 |  | yes | 9/10 | none | high | Leave open (cat 8). The only identifiable formal route is the conditional one: state and prove 'Bombieri-Lang  |
| `ErdosProblems/213.lean` | `erdos_213` | 8 |  | yes | 9/8 | small | high | Leave open (cat 8). The concrete, finite sub-goal is erdos_213.variants.KK08: formalize the explicit 7-point K |
| `ErdosProblems/218.lean` | `erdos_218.variants.ge` | 9 |  | suspect | 10/10 | none | medium | Do not attempt. |
| `ErdosProblems/218.lean` | `erdos_218.variants.infinite_equal_prime_gap` | 9 |  | yes | 9/10 | none | medium | Leave open. If ever attacked, route through erdos_141.variants.infinite_three and prove the equivalence lemma  |
| `ErdosProblems/218.lean` | `erdos_218.variants.le` | 9 |  | suspect | 10/10 | none | medium | Do not attempt. Optionally file an upstream note to state the < version explicitly alongside the ≤ version. |
| `ErdosProblems/23.lean` | `erdos_23` | 8 |  | yes | 9/10 | none | medium | Leave open (cat 8). The realistic finite sub-goal is erdos_23.variants.n1 / n1_tight on 5 vertices, which is a |
| `ErdosProblems/233.lean` | `erdos_233` | 9 |  | yes | 10/10 | none | high | Do not attempt the main statement. The realistic import is the already-formalized lower_bound variant from the |
| `ErdosProblems/234.lean` | `erdos_234` | 9 |  | yes | 10/10 | none | high | Do not attempt. |
| `ErdosProblems/236.lean` | `erdos_236` | 8 |  | yes | 9/9 | none | medium | Leave open (cat 8). The cheap first milestone is the trivial bound f n ≤ Nat.log2 n + 1 (immediate from List.l |
| `ErdosProblems/238.lean` | `erdos_238` | 8 |  | yes | 8/9 | none | medium | Leave open (cat 8). First milestone would be the c₂ < 2 case, which is trivially true (all gaps above p=2 are  |
| `ErdosProblems/241.lean` | `erdos_241` | 9 |  | yes | 9/10 | none | high | Do not attempt the asymptotic. The Bose-Chowla lower bound (variants.lower_bound) is the only realistically fo |
| `ErdosProblems/241.lean` | `erdos_241.variants.generalization` | 9 |  | yes | 9/10 | none | high | Do not attempt. If any piece is to be done, do variants.r_eq_2 first (Sidon sets, Erdős-Turán upper bound + Si |
| `ErdosProblems/242.lean` | `erdos_242` | 9 |  | yes | 9/9 | none | high | Do not attempt in full. A legitimate partial contribution is a Lean lemma covering the easy residue classes (e |
| `ErdosProblems/242.lean` | `erdos_242.variants.schinzel_generalization` | 9 |  | yes | 9/10 | none | high | Do not attempt. |
| `ErdosProblems/243.lean` | `erdos_243` | 8 |  | yes | 8/9 | none | medium | Leave open (cat 8). Identifiable avenue: prove the easy direction first (the Sylvester recurrence does give a  |
| `ErdosProblems/244.lean` | `erdos_244` | 8 |  | yes | 8/9 | none | medium | Attempt the Romanoff route: formalize the L^2/representation-count argument for the sumset of primes with a sp |
| `ErdosProblems/247.lean` | `erdos_247` | 9 | 8 | yes | 9/10 | none | medium | Do not attempt directly. If pursued, the only identifiable avenue is a combinatorial transcendence criterion ( |
| `ErdosProblems/249.lean` | `erdos_249` | 9 |  | yes | 9/9 | none | medium | No realistic Lean path. Would first require formalizing the Erdős/Lambert-series irrationality technique (see  |
| `ErdosProblems/25.lean` | `erdos_25` | 8 |  | yes | 8/9 | none | medium | Milestone-first approach: prove the easy direction that A always has an upper/lower logarithmic density and fo |
| `ErdosProblems/251.lean` | `erdos_251` | 9 |  | suspect | 9/9 | none | medium | Leave open; if desired, fix the cosmetic mismatch by using 2^(n+1) in the denominator so the Lean constant equ |
| `ErdosProblems/252.lean` | `erdos_252` | 8 |  | yes | 8/9 | none | high | Not resolvable unconditionally today. The pragmatic Lean target is the conditional theorem erdos_252.variants. |
| `ErdosProblems/252.lean` | `erdos_252.variants.k_ge_five` | 8 |  | yes | 8/9 | none | high | Same as erdos_252: pursue the conditional Schinzel/prime-k-tuples implication rather than the unconditional st |
| `ErdosProblems/254.lean` | `erdos_254` | 8 |  | yes | 8/9 | none | medium | First milestone: formalize Cassels' theorem (the weaker in-file variant) — that is the only known result and w |
| `ErdosProblems/257.lean` | `erdos_257` | 8 |  | suspect | 9/9 | none | medium | Target the special cases first (A = N, A = primes) using the already-proved Lambert identity; the universal st |
| `ErdosProblems/260.lean` | `erdos_260` | 8 |  | yes | 8/9 | none | medium | Verify whether arXiv:2606.24972 fully resolves 260 before investing; if it is only a partial density theorem ( |
| `ErdosProblems/263.lean` | `erdos_263.parts.i` | 8 |  | yes | 8/9 | none | high | Compute/verify that a_n = 2^(2^n) is the exact critical case (a_{n+1}/a_n^2 = 1) and look for a Kovač–Tao-styl |
| `ErdosProblems/264.lean` | `erdos_264.parts.ii` | 8 |  | yes | 8/9 | none | medium | Check whether n! satisfies the Kovač–Tao liminf criterion: a_n^2 ∑_{k>n} a_k^{-2} for a_n = n! is ≈ (n!)^2/((n |
| `ErdosProblems/267.lean` | `erdos_267` | 8 |  | yes | 8/9 | none | medium | Port the upstream AlphaProof proof of erdos_267.variants.specialization_pow_two into this fork and verify the  |
| `ErdosProblems/267.lean` | `erdos_267.variants.generalisation_ratio_limit_to_infinity` | 8 |  | suspect | 8/9 | none | medium | Same as erdos_267. Optionally tighten by requiring 0 < n k to remove the fib 0 junk-value branch. |
| `ErdosProblems/269.lean` | `erdos_269.variants.irrational` | 8 |  | suspect | 8/8 | small | medium | Same as the rational variant; additionally consider restating as a single ∀P, (Irrational ∨ rational) decision |
| `ErdosProblems/269.lean` | `erdos_269.variants.rational` | 8 |  | suspect | 8/8 | small | medium | Numerically explore P = {2,3}: compute lcm(a_1..a_n) (which is p^α q^β with α,β the largest exponents seen) an |
| `ErdosProblems/272.lean` | `erdos_272` | 1 | 4 | suspect | 6/8 | none | medium | Fill in answer := fun N => (N:ℝ)^2/2 and retag erdos_272 as research solved, deriving it from erdos_272.varian |
| `ErdosProblems/272.lean` | `erdos_272.variants.szabo_strong` | 8 |  | yes | 8/9 | none | medium | Out of reach until Szabo's theorem is formalized. Interim milestone: formalize the lower-bound construction gi |
| `ErdosProblems/273.lean` | `erdos_273` | 8 | 6 | yes | 8/7 | medium | medium | Two-sided: (a) run a computer search over covering systems with moduli drawn from {4,6,10,12,16,18,22,...} — a |
| `ErdosProblems/274.lean` | `erdos_274` | 8 |  | suspect | 9/9 | none | medium | Restate the conclusion with Subgroup.index (i.e. merge with `herzog_schonheim`) so the infinite-group case is  |
| `ErdosProblems/274.lean` | `herzog_schonheim` | 8 | 9 | yes | 9/9 | none | high | Formalize the classical finite abelian / cyclic case first (via the density-of-cosets argument on Z/n), i.e. p |
| `ErdosProblems/276.lean` | `erdos_276` | 8 |  | yes | 8/8 | small | medium | No cheap path. Explore whether a finite prime set must always exist (which would give answer(False)): a first  |
| `ErdosProblems/279.lean` | `erdos_279` | 8 |  | yes | 8/8 | none | medium | First reduce: setting a_2 ∈ {0,1} already covers one residue class mod 2 for all large n, so the problem reduc |
| `ErdosProblems/28.lean` | `erdos_28` | 9 |  | yes | 10/10 | none | high | Do not attempt. Only meaningful contribution would be formalizing known partial results (e.g. Erdős–Fuchs on t |
| `ErdosProblems/282.lean` | `erdos_282` | 9 | 8 | suspect | 9/10 | none | medium | Before any proof attempt, fix the definition to forbid repeated denominators (e.g. carry the used Finset, or r |
| `ErdosProblems/282.lean` | `erdos_282.variants.general` | 10 | 4 | no | 9/10 | none | high | Rewrite as a family of concrete conjectures (A = odds, A = a mod d, A = squares) or add hypotheses `A.Infinite |
| `ErdosProblems/282.lean` | `erdos_282.variants.graham` | 8 |  | suspect | 8/9 | none | medium | Fix the greedy definition (distinct denominators), then attack the arithmetic-progression case a = 1, d = 2 (o |
| `ErdosProblems/282.lean` | `erdos_282.variants.sq` | 8 |  | suspect | 8/9 | small | medium | Repair the definition to use distinct denominators; then a disproof needs a certified non-terminating orbit (e |
| `ErdosProblems/287.lean` | `erdos_287` | 8 | 6 | yes | 7/8 | medium | medium | Two tracks: (a) formalise the conditional reduction `prime_conjecture_implies` (Egyptian-fraction bookkeeping  |
| `ErdosProblems/287.lean` | `erdos_287.variants.prime_conjecture` | 9 |  | yes | 9/10 | none | high | Do not attempt; keep as a recorded auxiliary open conjecture. If desired, formalise the Hardy-Littlewood heuri |
| `ErdosProblems/288.lean` | `erdos_288` | 8 |  | yes | 8/9 | none | medium | First formalise the single-interval theorem (unique maximal power of 2 in an interval gives negative 2-adic va |
| `ErdosProblems/288.lean` | `erdos_288.variants.exists_k_gt_2` | 8 | 10 | suspect | 8/9 | none | low | Confirm the source wording, then either keep the existential (documenting 'not known for any k > 2') or change |
| `ErdosProblems/288.lean` | `erdos_288.variants.i2_card_eq_1` | 8 |  | yes | 7/8 | small | medium | Attack this case first: sum over [a,b] plus 1/n2 in N forces strong p-adic constraints on n2; a proof here wou |
| `ErdosProblems/288.lean` | `erdos_288.variants.k_intervals` | 8 |  | yes | 8/9 | none | medium | Deprioritise relative to `i2_card_eq_1`/`erdos_288`; nothing is gained by attacking the uniform-in-k form firs |
| `ErdosProblems/289.lean` | `erdos_289` | 8 | 6 | suspect | 7/8 | medium | medium | Search computationally for interval decompositions of 1 for k = 2..12 (each interval [a,b] with b > a); a repe |
| `ErdosProblems/291.lean` | `erdos_291.parts.i` | 8 |  | yes | 8/9 | small | medium | Attack via the file's own `steinerberger_generalization`: gcd(a_n, L_n) = 1 iff for every prime p <= n, p does |
| `ErdosProblems/291.lean` | `erdos_291.variants.shiu_heuristic_asymptotic` | 9 |  | yes | 9/10 | none | high | Do not attempt; record as a heuristic. Any progress would first require part (i). |
| `ErdosProblems/291.lean` | `erdos_291.variants.shiu_heuristic_density_zero` | 8 |  | yes | 8/9 | none | medium | Formalise the Steinerberger criterion, then try to upgrade the Wu-Yan argument from upper density to density;  |
| `ErdosProblems/295.lean` | `erdos_295` | 8 |  | suspect | 8/9 | none | medium | Fix the Fin k.succ off-by-one; first formalise the helper `exists_k` (currently sorry'd), e.g. via a greedy co |
| `ErdosProblems/3.lean` | `erdos_3` | 9 |  | yes | 10/10 | none | high | Do not attempt. If desired, add the known partial results (Behrend lower bound, Bloom-Sisask) as variants, per |
| `ErdosProblems/30.lean` | `erdos_30` | 9 |  | yes | 9/10 | none | high | Do not attempt. Adding the Lindstrom upper bound h(N) <= sqrt(N) + N^{1/4} + 1 as a variant (the file's TODO)  |
| `ErdosProblems/304.lean` | `upper_bound` | 8 |  | yes | 8/9 | none | medium | Formalising Vose's bound (variant `upper_1985`) is the realistic target; the conjecture itself needs a new ide |
| `ErdosProblems/306.lean` | `erdos_306` | 8 |  | yes | 8/9 | none | medium | Milestone: formalise the density/greedy machinery for sums of 1/(pq) (the relevant series diverges), then atte |
| `ErdosProblems/307.lean` | `erdos_307` | 8 | 6 | yes | 8/8 | large | medium | Two options: (a) port the external barrier proof (Closed.lean) to discharge `erdos_307.barrier` here and verif |
| `ErdosProblems/307.lean` | `erdos_307.variants.coprime_one_notMem` | 8 | 6 | yes | 6/3 | medium | medium | Run a bounded computer search over pairwise-coprime sets with elements in [2, 10^4] and small cardinalities; i |
| `ErdosProblems/312.lean` | `erdos_312` | 8 |  | suspect | 8/9 | none | medium | Require a i >= 1 (or use a multiset of positive integers) so that the n >= N_0 hypothesis has real content, an |
| `ErdosProblems/313.lean` | `erdos_313` | 9 |  | yes | 9/10 | none | high | Do not attempt the infinitude claim. Useful nearby work: formalise the m = prod P lemma sketched above (short  |
| `ErdosProblems/313.lean` | `erdos_313.variants.primary_pseudoperfect_are_infinite` | 9 |  | yes | 9/10 | none | high | Do not attempt; consider merging with `erdos_313` or documenting the equivalence, since the two declarations s |
| `ErdosProblems/317.lean` | `erdos_317` | 8 |  | yes | 9/9 | small | high | Treat as genuinely open. First milestone: formalize the computational evidence (min nonzero \|sum\| times 2^n) |
| `ErdosProblems/317.lean` | `erdos_317.variants.claim2` | 8 |  | yes | 8/9 | small | high | Open research statement. Useful intermediate work: formalize `claim2_inequality` (divide through by lcm and us |
| `ErdosProblems/319.lean` | `erdos_319` | 9 |  | yes | 9/10 | none | high | Leave open; the realistic target in this file is `variants.lb` (Croot), not the exact maximum. |
| `ErdosProblems/319.lean` | `erdos_319.variants.isBigO` | 4 | 2 | suspect | 1/3 | none | high | Fill `answer := fun N => (N : ℝ)` and prove: from h N obtain A ⊆ Icc 1 N with c N = #A, so c N <= #(Icc 1 N) = |
| `ErdosProblems/319.lean` | `erdos_319.variants.isLittleO` | 4 | 2 | suspect | 1/4 | none | high | Fill `answer := fun N => (N : ℝ)^2` and prove from c N <= N that c N / N^2 → 0 (`Asymptotics.isLittleO_of_tend |
| `ErdosProblems/319.lean` | `erdos_319.variants.isTheta` | 5 | 4 | suspect | 5/9 | none | medium | Fill answer with `fun N => (N : ℝ)`; the O-direction follows from h in a few lines (members of the set are #A  |
| `ErdosProblems/32.lean` | `erdos_32` | 8 |  | yes | 8/9 | none | medium | Genuinely open; the tractable target in this file is Erdos' O((log N)^2) construction (variants.log_squared),  |
| `ErdosProblems/32.lean` | `erdos_32.variants.log_bound` | 9 |  | yes | 9/10 | none | medium | Do not attempt. If any work is done in this file, do Ruzsa's lower bound (variants.ruzsa) or Erdos' constructi |
| `ErdosProblems/321.lean` | `erdos_321` | 1 | 8 | suspect | 6/9 | none | low | Retrieve erdosproblems.com/321 (and its cited paper) from a network that can reach it; then decide whether the |
| `ErdosProblems/321.lean` | `erdos_321.variants.isBigO` | 4 | 2 | suspect | 1/3 | none | high | Fill `answer := fun N => (N : ℝ)`; prove R N <= N by `Nat.sSup_le` (every member is #A with A ⊆ Finset.Icc 1 N |
| `ErdosProblems/321.lean` | `erdos_321.variants.isLittleO` | 4 | 2 | suspect | 1/4 | none | high | Fill `answer := fun N => (N : ℝ)^2`, reuse R N <= N, conclude via `Asymptotics.IsBigO.trans_isLittleO` with N  |
| `ErdosProblems/321.lean` | `erdos_321.variants.isTheta` | 1 | 5 | suspect | 6/9 | none | low | Get the exact asymptotic from erdosproblems.com/321, fill answer, then formalize the matching upper and lower  |
| `ErdosProblems/323.lean` | `erdos_323.parts.i` | 9 |  | yes | 10/10 | none | high | Do not attempt. If the file is to be advanced, target `variants.k_eq_2` (Landau's theorem on sums of two squar |
| `ErdosProblems/323.lean` | `erdos_323.parts.ii` | 9 |  | yes | 9/10 | none | medium | Do not attempt in full. A meaningful partial step would be the m=1 case (f_{k,1}(x) = floor(x^{1/k})+1) or an  |
| `ErdosProblems/323.lean` | `erdos_323.variants.k_gt_2` | 9 |  | yes | 9/10 | none | high | Do not attempt. The natural (still open) route is to show a positive proportion of integers are sums of three  |
| `ErdosProblems/324.lean` | `erdos_324` | 9 |  | yes | 9/10 | none | high | Do not attempt directly; it reduces to the quintic variant below (f = X^5), which is itself hopeless with curr |
| `ErdosProblems/324.lean` | `erdos_324.variants.quintic` | 9 |  | suspect | 10/10 | medium | high | Do not attempt. A defensible small contribution is a certified search bound (no solutions with max <= B) as a  |
| `ErdosProblems/325.lean` | `erdos_325` | 9 |  | yes | 9/10 | none | high | Do not attempt. The realistic file target is Wooley's bound, which is a research-scale formalization. |
| `ErdosProblems/325.lean` | `erdos_325.variants.weaker` | 9 |  | yes | 9/10 | none | high | Do not attempt; formalizing Wooley's circle-method argument is the only credible partial step and is research- |
| `ErdosProblems/326.lean` | `erdos_326` | 8 | 4 | suspect | 8/9 | none | medium | Fix the specification first: replace `(Set.range b).IsAddBasis` by `(Set.range b).IsAddBasisOfOrder 2` and hoi |
| `ErdosProblems/329.lean` | `erdos_329` | 9 |  | yes | 9/10 | none | high | Do not attempt the exact value. Kruckeberg's 1/sqrt 2 construction (variants.kruckeberg_1961) is the realistic |
| `ErdosProblems/329.lean` | `erdos_329.variants.converse_implication` | 8 | 4 | suspect | 9/10 | none | medium | Restate as `answer(sorry) ↔ (sSup {...} = 1)` (or as the implication in the sound direction, consequent → sSup |
| `ErdosProblems/33.lean` | `erdos_33` | 9 |  | yes | 9/10 | none | high | Do not attempt the exact constant. The tractable target is van Doorn's construction (variants.vanDoorn). |
| `ErdosProblems/330.lean` | `erdos_330_statement` | 1 |  | suspect | 4/4 | none | medium | Fetch the Lean proof linked from erdosproblems.com/330, adapt it to this file's `Rep`/`HasPosDensity` definiti |
| `ErdosProblems/331.lean` | `erdos_331.variants.ruzsa` | 8 |  | yes | 8/8 | none | medium | Attack the refutation side: try to smooth Ruzsa's construction (which has count A n /√n oscillating in [1,√2]) |
| `ErdosProblems/332.lean` | `erdos_332` | 4 | 5 | suspect | 5/8 | none | medium | Either (a) restate as a concrete named implication, e.g. `0 < upperDensity A → HasBoundedGaps (D_A A)`, and fo |
| `ErdosProblems/340.lean` | `erdos_340` | 9 |  | yes | 9/9 | none | high | Do not attempt. If any work is done, target the recorded-but-unproved trivial bound `erdos_340.variants.third` |
| `ErdosProblems/340.lean` | `erdos_340.variants._33_mem_sub` | 8 | 6 | yes | 8/4 | medium | medium | Asymmetric problem: a positive answer is a one-line witness `greedySidon i − greedySidon j = 33` IF such a pai |
| `ErdosProblems/340.lean` | `erdos_340.variants.co_density_zero_sub` | 9 |  | yes | 9/9 | none | high | Same blocker as the other A−A variants: no structural handle on the greedy Sidon set. Not a target. |
| `ErdosProblems/340.lean` | `erdos_340.variants.cofinite_sub` | 9 |  | yes | 9/9 | none | high | Blocked behind `_33_mem_sub`: cofiniteness implies 33 ∈ A−A for the trivial reason that only finitely many exc |
| `ErdosProblems/340.lean` | `erdos_340.variants.isTheta` | 4 | 9 | suspect | 9/1 | none | high | Delete or restate. A defensible replacement is `∀ ε > 0, (fun n ↦ (n:ℝ)^(1/2−ε)) =O[atTop] card ∧ card =O[atTo |
| `ErdosProblems/340.lean` | `erdos_340.variants.sub_hasPosDensity` | 8 |  | yes | 8/8 | small | medium | Compute a long prefix of A005282 (say 10^5 terms) and measure the density of realised differences below N to s |
| `ErdosProblems/341.lean` | `erdos_341` | 8 |  | yes | 9/9 | small | medium | Generate the sequence for many starting sets and test the observed periods (cheap); a single starting set with |
| `ErdosProblems/342.lean` | `erdos_342.parts.i` | 8 |  | yes | 9/9 | small | medium | Nothing formal is worthwhile until someone first proves in Lean that an Ulam sequence exists (the definition i |
| `ErdosProblems/342.lean` | `erdos_342.parts.ii` | 9 |  | yes | 10/10 | none | high | Do not attempt. Disproof requires a genuine theorem about A002858, of which none exist. |
| `ErdosProblems/342.lean` | `erdos_342.parts.iii` | 9 |  | yes | 9/9 | small | high | Deduplicate: link 342.parts.iii and green_7.variants.positive_density so that answering one is recorded agains |
| `ErdosProblems/346.lean` | `erdos_346` | 8 |  | yes | 8/8 | none | medium | Best first milestone is the already-stated but unproved `erdos_346.variants.gt_goldenRatio_not_IsAddComplete`: |
| `ErdosProblems/348.lean` | `erdos_348` | 8 |  | suspect | 8/8 | none | medium | First fix the model: replace `IsAddComplete (Set.range (updateFinset a s 0))` by an index-based completeness p |
| `ErdosProblems/349.lean` | `complete_for_alpha_in_Ioo_one_to_goldenRatio` | 8 | 7 | yes | 6/8 | none | medium | Plausible attack with moderate formal work: (1) show that for 1 < α < φ the distinct values b₀ < b₁ < … of ⌊tα |
| `ErdosProblems/349.lean` | `erdos_349` | 9 |  | suspect | 10/9 | none | medium | Do not target the characterisation. Instead, import the six partial results whose proofs already exist on the  |
| `ErdosProblems/349.lean` | `erdos_349.variants.floor_3_halves_even` | 9 |  | yes | 9/9 | none | high | Do not attempt. |
| `ErdosProblems/349.lean` | `erdos_349.variants.floor_3_halves_odd` | 9 |  | yes | 9/9 | none | high | Do not attempt. Any progress would bear directly on the distribution of {(3/2)ⁿ} mod 1, the central obstructio |
| `ErdosProblems/352.lean` | `erdos_352` | 8 |  | yes | 8/9 | none | medium | Look for the refutation direction first: construct, for each c, a measurable set of measure ≥ c avoiding area- |
| `ErdosProblems/354.lean` | `erdos_354.parts.i` | 8 |  | yes | 8/8 | none | medium | Check the 2025 Acta Math. Hungar. paper before investing; if the problem is still open, the tractable directio |
| `ErdosProblems/354.lean` | `erdos_354.parts.ii` | 4 | 10 | no | 8/2 | none | high | Fix the statement: replace `FloorMultiples.interleave α β 2` by `FloorMultiples.interleave α β γ` in parts.ii, |
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
| `ErdosProblems/358.lean` | `erdos_358.variants.one_le` | 1 | 5 | yes | 3/8 | none | high | Retag as research solved (citing [Ta26]) and record the two-line derivation from parts.ii. Formally: prove the |
| `ErdosProblems/358.lean` | `erdos_358.variants.prime_set` | 9 |  | suspect | 9/9 | none | medium | Do not attempt. Note the heuristic count below: the total number of representations up to x is ≈ x·log 2, so p |
| `ErdosProblems/358.lean` | `erdos_358.variants.prime_set_density_representation` | 8 |  | suspect | 8/9 | small | medium | Cheap and worthwhile first step: compute the density of representable n below 10^7 to see the empirical consta |
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
| `GreensOpenProblems/31.lean` | `green_31.lower` | 9 |  | yes | 9/10 | none | high | Keep open; no known avenue. No internal work targets it (pr_register/campaign_register greps for green_31/Sido |
| `GreensOpenProblems/31.lean` | `green_31.upper` | 8 |  | yes | 8/10 | none | medium | Keep open; monitor the Sidon literature for a constant below 0.98183, then formalize (large analytic Lean proj |
| `GreensOpenProblems/31.lean` | `green_31.variants.abelian` | 4 | 2 | no | 8/3 | none | high | Report the definition defect upstream (IsSidon needs a distinct-pair/group variant in even-order groups). To c |
| `GreensOpenProblems/31.lean` | `green_31.variants.lower_eventually` | 9 |  | yes | 9/10 | none | high | Keep open. |
| `GreensOpenProblems/31.lean` | `green_31.variants.sidon_01n` | 4 | 2 | no | 8/3 | none | high | Report defect upstream: use a distinct-pair Sidon/B_2 definition over F_2^n. To close as-is: at n = 1, (2^1)^{ |
| `GreensOpenProblems/31.lean` | `green_31.variants.upper_eventually` | 8 |  | yes | 8/10 | none | medium | Keep open; monitor literature. |
| `GreensOpenProblems/31.lean` | `green_31.variants.zmod_p` | 8 |  | yes | 8/9 | none | high | Keep open. |
| `GreensOpenProblems/32.lean` | `green_32` | 8 |  | yes | 8/9 | none | high | Keep open. No PR or campaign targets it. |
| `GreensOpenProblems/32.lean` | `green_32.variants.log_regime` | 8 |  | yes | 8/9 | none | medium | Keep open. |
| `GreensOpenProblems/33.lean` | `green_33` | 8 |  | yes | 8/8 | small | high | Leave open; computational search for optimal additive covers of Z/q for q up to a few thousand could inform th |
| `GreensOpenProblems/35.lean` | `green_35.lower` | 8 |  | yes | 8/10 | medium | medium | Keep open. Worth checking CS17's certified constant: if their proof yields something strictly above 0.64 (0.64 |
| `GreensOpenProblems/35.lean` | `green_35.upper` | 8 | 6 | suspect | 7/9 | medium | medium | First reconcile the constant with Green's list / MV10. To attack: search for a step-function density with exac |
| `GreensOpenProblems/36.lean` | `green_36` | 9 |  | yes | 10/10 | none | high | Keep open; do not attempt. The file honestly separates Green's phrasing (here) from CKS's (variant below). |
| `GreensOpenProblems/36.lean` | `green_36.variants.cks05` | 9 |  | yes | 10/10 | none | medium | Keep open; verify the CKS 4.1 index convention against the paper and record it in the docstring. |
| `GreensOpenProblems/37.lean` | `green_37` | 4 | 2 | no | 8/3 | none | high | Report the spec defect upstream (constrain the answer to a closed form, or replace by explicit two-sided bound |
| `GreensOpenProblems/37.lean` | `green_37_asymptotic` | 4 | 2 | no | 8/1 | none | high | Report spec defect; replace with a genuine two-sided asymptotic (explicit upper/lower bound pair, or IsTheta a |
| `GreensOpenProblems/37.lean` | `green_37_bigO` | 2 | 4 | no | 8/1 | none | high | Close with isBigO_refl if a formal resolution is wanted; better, report the spec defect (the bound should have |
| `GreensOpenProblems/37.lean` | `green_37_littleO` | 2 | 4 | no | 8/2 | none | high | Close with the (f+1)*(N+1) trick if desired; report the spec defect upstream. |
| `GreensOpenProblems/37.lean` | `green_37_theta` | 4 | 2 | no | 8/1 | none | high | Report spec defect; a meaningful version must restrict the grammar of comparison functions or state concrete b |
| `GreensOpenProblems/38.lean` | `green_38.lower` | 1 | 6 | yes | 6/8 | medium | medium | Import the certificate: (1) extract the explicit 134753-element subset S of F_7^10 from arXiv:2607.21517 and v |
| `GreensOpenProblems/38.lean` | `green_38.upper` | 9 |  | yes | 9/10 | none | high | Keep open; do not attempt. |
| `GreensOpenProblems/39.lean` | `green_39` | 8 |  | yes | 8/9 | none | medium | Keep open. |
| `GreensOpenProblems/39.lean` | `green_39.variant_101` | 8 |  | yes | 9/9 | none | high | Keep open. |
| `GreensOpenProblems/39.lean` | `green_39.variant_theta` | 8 |  | suspect | 8/9 | none | medium | Keep open; ask upstream to confirm the intended reading against Green's text. |
| `GreensOpenProblems/4.lean` | `green_4` | 4 | 2 | no | 8/4 | none | high | Report the spec defect upstream (the answer should be an explicit family such as extremalFamily x I together w |
| `GreensOpenProblems/40.lean` | `green_40` | 8 |  | yes | 9/9 | none | high | Keep as open research target; monitor covering-code literature (Davydov-type constructions vs lower-bound meth |
| `GreensOpenProblems/40.lean` | `green_40.f_eq_one_for_all` | 8 |  | yes | 8/9 | none | high | Keep open; any resolution of f(2) decides this statement, so it is strictly easier than green_40. |
| `GreensOpenProblems/40.lean` | `green_40.f_two_eq_one` | 8 |  | yes | 8/9 | none | high | Keep open; the construction-side attack (linear analogues of Struik's codes) is the identifiable avenue. The r |
| `GreensOpenProblems/40.lean` | `green_40.variants.all_n` | 4 | 7 | no | 3/7 | none | high | Fix the statement to 'Tendsto f_all atTop (nhds top)'. Alternatively the current statement can be legitimately |
| `GreensOpenProblems/40.lean` | `green_40.variants.arbitrary_subsets` | 8 |  | yes | 9/9 | none | medium | Keep open. f_tilde_le_f is a cheap sanity lemma (iInf over a larger index family). |
| `GreensOpenProblems/41.lean` | `green_41` | 4 | 5 | no | 8/10 | none | high | Tighten the spec (require ans to be o of the KrLe bound for every C, or fix a lower iterated-exponential level |
| `GreensOpenProblems/41.lean` | `green_41.variants.exists_better_bound` | 4 | 1 | no | 3/10 | none | high | Replace by a spec that quantifies the improvement (double-exponential or polynomial), or delete as a duplicate |
| `GreensOpenProblems/41.lean` | `green_41.variants.polynomial_bound` | 8 |  | yes | 9/10 | none | high | Keep open; track follow-ups to Kravitz-Leng. A realistic Lean milestone is the density lower bound minCopies e |
| `GreensOpenProblems/42.lean` | `green_42` | 9 | 8 | yes | 10/10 | none | high | Keep open. Lean effort in this file is better spent importing the linked math-inc Sphere-Packing-Lean results  |
| `GreensOpenProblems/44.lean` | `green_44` | 8 |  | yes | 8/9 | none | medium | Keep open; connects to the inverse large sieve (Green 47). The large-sieve variant is the realistic Lean targe |
| `GreensOpenProblems/46.lean` | `green_46.improve_lower` | 9 | 8 | yes | 10/10 | none | medium | Keep open (cat 9); fix the [Ra38] attribution to [FGK18]. |
| `GreensOpenProblems/46.lean` | `green_46.improve_upper` | 9 |  | yes | 10/10 | none | medium | Keep open (cat 9). Even the recorded solved variant maxY << x^2 is unformalized and would be a large project. |
| `GreensOpenProblems/46.lean` | `green_46.improve_upper_conjectured` | 9 |  | yes | 10/10 | none | medium | Keep open; no known strategy closes the x^(1+o(1)) vs x^2 gap. |
| `GreensOpenProblems/47.lean` | `green_47` | 9 | 8 | yes | 10/10 | none | medium | Keep open. Formal progress needs the Green-Harper machinery, far from Mathlib. |
| `GreensOpenProblems/50.lean` | `green_50` | 4 | 8 | suspect | 8/9 | none | medium | Run 'set_option pp.all true in #check @Green50.green_50' (or #print the statement) as soon as a build is avail |
| `GreensOpenProblems/51.lean` | `green_51` | 4 | 8 | suspect | 9/1 | none | high | Restate as bracketing asymptotics (as the file's own solved variants do) or add a closed-form requirement; tre |
| `GreensOpenProblems/51.lean` | `green_51.one_half` | 8 |  | suspect | 8/9 | none | medium | Consider strengthening the conclusion to subspaces; keep open. A trivial sanity milestone is alpha = 1 (A = un |
| `GreensOpenProblems/52.lean` | `green_52` | 8 |  | yes | 8/9 | none | medium | Keep open. Cheap sanity lemma worth adding: K = 1 forces A = F_2^n, hence codimension 0. |
| `GreensOpenProblems/52.lean` | `green_52_log` | 8 |  | yes | 9/9 | none | medium | Keep open; resolve green_52 first. |
| `GreensOpenProblems/54.lean` | `green_54` | 9 | 8 | suspect | 10/10 | none | medium | Add the finite-dimensional uniform-in-n variant (or record the equivalence argument); keep open. |
| `GreensOpenProblems/58.lean` | `green_58` | 8 |  | yes | 8/9 | none | medium | Keep open. A worthwhile weaker formal target is the same statement with exponent 1/2 + delta. |
| `GreensOpenProblems/60.lean` | `green_60` | 8 |  | yes | 8/9 | none | high | Keep open. Sanity variants could record that \|A\| = 2 forces \|A+A\| = 3, so small cases never obstruct. |
| `GreensOpenProblems/61.lean` | `green_61` | 8 |  | yes | 8/9 | none | high | Keep open; the file has a TODO to add the two known partial results. Formalizing the n^(2/3-o(1)) bound (a Cau |
| `GreensOpenProblems/62.lean` | `green_62` | 9 | 8 | yes | 9/10 | none | medium | Keep open. Tractable variants to add: the 'almost all p' or 'three primes' versions, both theorems. |
| `GreensOpenProblems/7.lean` | `green_7.variants.positive_density` | 9 |  | yes | 9/10 | none | high | Leave open. Only cheap repo-level work available: note that this statement is the exact logical complement of  |
| `GreensOpenProblems/72.lean` | `NoKInLine` | 9 |  | suspect | 10/10 | none | high | Leave open; consider restating as an answer(sorry) question (as the `eventually` variant does) rather than a t |
| `GreensOpenProblems/72.lean` | `green_72` | 9 |  | suspect | 10/10 | none | high | Leave open; recommend converting to an answer(sorry) formulation and repairing the module docstring. A tractab |
| `GreensOpenProblems/72.lean` | `green_72.variants.eventually` | 9 |  | yes | 10/10 | none | high | Leave open. Realistic progress would be a formalisation of the Guy–Kelly counting heuristic, but it is a heuri |
| `GreensOpenProblems/77.lean` | `green_77` | 9 |  | suspect | 10/10 | none | high | Leave open. Repo-level fix worth doing: make Erdos507.minTriangleArea range over all 3-element subsets (assign |
| `GreensOpenProblems/85.lean` | `green_85` | 8 |  | yes | 8/9 | none | medium | Leave open. Identifiable avenue: formalise the Cauchy–Schwarz `green_85_loose` bound first (a genuinely reacha |
| `GreensOpenProblems/9.lean` | `green_9_ii` | 9 |  | yes | 9/10 | none | high | Leave open (cat 9). Note in passing that the sibling `green_9_i` in the same file credits [BlSi20] for r_3(N)  |
| `GreensOpenProblems/9.lean` | `green_9_iii` | 8 | 9 | yes | 9/10 | none | high | Leave open. This is the most 'approachable' of the three parts of Problem 9 (finite-field model, small cases n |
| `GreensOpenProblems/94.lean` | `green_94` | 9 | 8 | yes | 9/10 | none | high | Leave open. Worth cross-referencing FormalConjectures/ErdosProblems/120.lean:erdos_120 (the general '∀ infinit |
| `HilbertProblems/5.lean` | `hilbert_smith_conjecture` | 9 |  | yes | 9/10 | none | high | Leave open. If any work is done, target the API lemmas (admitsLieGroupStructure_of_lieGroup already proved) or |
| `HilbertProblems/5.lean` | `hilbert_smith_padic_formulation` | 9 |  | yes | 9/10 | none | high | Leave open. A tractable sub-goal would be the n = 1 case (Newman/Montgomery-Zippin), still substantial in Lean |
| `Kourovka/19_25.lean` | `kourovka.«19.25»` | 4 | 3 | no | 7/4 | none | high | Repair first: add the hypothesis Nat.card G = Nat.card H (and, for good measure, [Fintype H] nonemptiness is a |
| `Kourovka/20_76.lean` | `kourovka.«20.76»` | 8 |  | yes | 7/8 | small | medium | Leave open; a realistic first milestone is the k = 1 case (all abelian normal subgroups of order <= p implies  |
| `LittProblems/1.lean` | `lam_litt.variants.integrality_implies_algebraicity` | 3 | 9 | no | 9/8 | none | high | Repair IsSolutionOfAlgebraicODE by adding `MvPolynomial.aeval pt q != 0` (or state the ODE as f^(n) = aeval pt |
| `LittProblems/1.lean` | `lam_litt.variants.omega_integrality_implies_algebraicity` | 9 | 4 | suspect | 9/10 | none | medium | Add the side condition MvPolynomial.aeval pt q != 0 to IsSolutionOfAlgebraicODE, then leave the (repaired) sta |
| `Mathoverflow/10799.lean` | `mathoverflow_10799.variants.kahn_kalai_conjecture_7` | 1 | 5 | yes | 8/7 | none | medium | Track down the Diskin-Kreitner 'Scale-Dense Dual-Tribes' write-up (and their Lean file, if public), check that |
| `Mathoverflow/17560.lean` | `mathoverflow_17560` | 9 |  | yes | 9/9 | none | high | Leave open. A legitimate partial step would be to formalize the rational-x case as a lemma and to record the F |
| `Mathoverflow/1973.lean` | `mathoverflow_1973` | 9 |  | yes | 10/10 | none | high | Leave open (cat 9). Nothing actionable in Lean short of a research breakthrough. |
| `Mathoverflow/21003.lean` | `mathoverflow_21003` | 9 |  | yes | 9/9 | none | high | Leave open (cat 9). Mathlib lacks the arithmetic-geometry input; no cheap partial result is available. |
| `Mathoverflow/235893.lean` | `mathoverflow_235893` | 8 |  | yes | 8/8 | none | medium | Leave open. Identifiable avenues: (a) try to transfer the 1-dimensional order/IVT argument using local separat |
| `Mathoverflow/31809.lean` | `mathoverflow_31809` | 9 |  | yes | 9/9 | none | medium | Leave open (cat 9). Either direction is a research problem; even if a counterexample is found on paper, constr |
| `Mathoverflow/339137.lean` | `mathoverflow_339137` | 8 |  | yes | 8/8 | none | medium | Leave open. Concrete progress: verify the statement for small degrees by computation (bounded-degree cases red |
| `Mathoverflow/34145.lean` | `rectangles_cover_unit_square` | 8 |  | yes | 9/9 | none | medium | Leave open. Realistic Lean-side progress is limited to the infrastructure already present (measure of rotated  |
| `Mathoverflow/34145.lean` | `rectangles_pack_unit_square` | 8 |  | yes | 9/9 | none | medium | Leave open. A worthwhile intermediate Lean target is rectangles_pack_square_133_div_132 (a published construct |
| `Mathoverflow/347178.lean` | `mathoverflow_347178` | 8 |  | yes | 7/8 | none | medium | Leave open. Key structural facts to exploit: the inequality sup f(x + grad f(x)) <= sup f is trivial (the map  |
| `Mathoverflow/347178.lean` | `mathoverflow_347178.variants.bounded_iff` | 8 |  | yes | 7/8 | none | medium | Leave open. Only the direction 'f(x + grad f) bounded above => f bounded above' has content (the converse is i |
| `Mathoverflow/347178.lean` | `mathoverflow_347178.variants.bounded_only` | 8 |  | yes | 7/8 | none | medium | Leave open. Same reduction as the main statement: prove sup f(x+grad f(x)) <= sup f as an easy lemma, prove eq |
| `Mathoverflow/507128.lean` | `exists_isFractionRing_self_ideal_ne_top_invertible` | 8 | 10 | suspect | 7/8 | none | low | First fix the encoding: restate as `answer(sorry) <-> exists R ...` (or confirm from the MO thread that an exa |
| `Mathoverflow/75792.lean` | `complexity_two_pow` | 8 | 6 | yes | 9/9 | medium | high | Leave the general statement open. Useful and cheap: use the file's `Reachable.decide` instance to `decide` com |
| `Millenium/NavierStokes.lean` | `navier_stokes_breakdown_R3` | 9 |  | yes | 10/10 | none | high | Leave open. |
| `Millenium/NavierStokes.lean` | `navier_stokes_breakdown_periodic` | 9 |  | yes | 10/10 | none | high | Leave open. |
| `Millenium/NavierStokes.lean` | `navier_stokes_existence_and_smoothness_R3` | 9 |  | yes | 10/10 | none | high | Leave open. Any realistic Lean work here is API (divergence_add/divergence_smul are the file's own open API le |
| `Millenium/NavierStokes.lean` | `navier_stokes_existence_and_smoothness_periodic` | 9 |  | yes | 10/10 | none | high | Leave open. |
| `Millenium/Poincare.lean` | `poincare_conjecture.variants.smooth_dimension_four` | 9 |  | suspect | 10/10 | none | medium | Add [T2Space M] to SmoothConjectureFor (matching ConjectureFor) before any further work; then leave open. |
| `Millenium/Poincare.lean` | `poincare_conjecture.variants.smooth_other_cases` | 3 | 1 | no | 10/10 | none | medium | Update SmoothTrueValues to {1,2,3,5,6,12,56,61,126}, restate as a research-solved theorem citing Hill-Hopkins- |
| `Millenium/PvsNP.lean` | `NP_ne_coNP` | 9 |  | yes | 10/10 | none | high | Leave open. |
| `Millenium/PvsNP.lean` | `P_ne_NP` | 9 |  | yes | 10/10 | none | high | Leave open. The tractable work in this file is the textbook lemmas coP_eq_P and P_subset_NP (both still sorry) |
| `Millenium/RiemannHypothesis.lean` | `generalized_riemann_hypothesis` | 9 |  | yes | 10/10 | none | high | Leave open. |
| `Millenium/RiemannHypothesis.lean` | `riemannHypothesis` | 9 |  | yes | 10/10 | none | high | Leave open. |
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
| `OpenQuantumProblems/23.lean` | `hasSICPOVM_56` | 8 | 5 | yes | 2/9 | large | medium | Confirm against the primary source (Grassl's exact-solutions data / the 2025 JMP paper) which paper contains t |
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
| `OptimizationConstants/1a.lean` | `c1a_eq` | 4 | 2 | no | 8/5 | none | high | Fix the definition first. If one wants the degenerate fact recorded, C1a = 0 is provable in maybe 100 lines: u |
| `OptimizationConstants/1a.lean` | `mem_Ico_c1a` | 4 | 2 | no | 8/5 | medium | high | Fix the definition: take the supremum over t in Icc (-1/2) (1/2) (or over all t) and, preferably, restrict f t |
| `OptimizationConstants/1a.lean` | `mem_Ioc_c1a` | 3 | 4 | no | 8/5 | medium | high | Fix C1a (supremum over t in Icc (-1/2) (1/2), f supported in [-1/4,1/4]) and restate; do not attempt to prove  |
| `Other/BeaverMathOlympiad.lean` | `beaver_math_olympiad_problem_1` | 8 |  | yes | 8/8 | medium | high | Leave open; realistic progress is a longer search plus a search for a modular/measure invariant certifying non |
| `Other/BeaverMathOlympiad.lean` | `beaver_math_olympiad_problem_2_antihydra` | 9 |  | yes | 9/9 | medium | high | Leave open. Do not chase; any progress would be a research result on floor(3n/2) orbits. |
| `Other/BeaverMathOlympiad.lean` | `beaver_math_olympiad_problem_2_antihydra.variants.set` | 9 |  | yes | 9/9 | medium | high | Leave open; if ever proved, derive one form from the other rather than duplicating work. |
| `Other/BeaverMathOlympiad.lean` | `beaver_math_olympiad_problem_5` | 8 |  | yes | 8/8 | medium | high | Leave open; the plausible route is a non-halting invariant on the (a, b) pair, mirroring the Rocq reduction wo |
| `Other/BeaverMathOlympiad.lean` | `beaver_math_olympiad_problem_8` | 0 | 4 | no | 8/2 | small | high | Do NOT propagate the certificate upstream as a solution of BMO#8. Restate the recurrence over Z (or add the ha |
| `Other/EquationalTheories_677_255.lean` | `Finite.Equation677_implies_Equation255` | 9 |  | yes | 9/9 | none | high | Leave open; deprioritize relative to the counterexample direction. Only worth attacking if one first finds a s |
| `Other/EquationalTheories_677_255.lean` | `Finite.Equation677_not_implies_Equation255` | 9 | 6 | yes | 9/9 | large | high | Leave open. Any serious attempt means re-running / extending ETP-scale finite magma search (their exhaustive e |
| `Other/VCDimConvex.lean` | `exists_hasAddVCNDimAtMost_n_of_convex_rn_add_one` | 3 | 8 | no | 8/4 | none | high | Add the hypothesis `(hn : 1 ≤ n)` (or state it only for n ≥ 2) to the canonical statement; then leave it open. |
| `Other/VCDimConvex.lean` | `hasAddVCNDimAtMost_n_one_of_convex_rn_add_one` | 3 | 0 | yes | 6/3 | small | high | Port the branch counterexample and instantiate it at n = 2 to derive `¬ ∀ n ≥ 2, ...`; then replace this lemma |
| `Other/VCDimConvex.lean` | `hasAddVCNDimAtMost_two_one_of_convex_r3` | 3 | 0 | yes | 6/4 | small | high | Correct the canonical file: replace this lemma by `∃ C : Set ℝ³, Convex ℝ C ∧ ¬ HasAddVCNDimAtMost C 2 1`, por |
| `Paper/CardinalityLindelof.lean` | `HasGδSingletons.lindelof_card` | 4 | 5 | no | 9/8 | none | medium | Add [T2Space X] (or [RegularSpace X]) to the existential witness to recover Arhangel'skii's Problem 1; alterna |
| `Paper/CasasAlvero.lean` | `casas_alvero_conjecture` | 5 | 8 | yes | 8/9 | none | medium | Track refereeing of arXiv:2501.09272; do not flip the repo category to research solved until confirmed. Cheape |
| `Paper/CatchUpConjecture.lean` | `value_of_even_mul_succ_self_div_two` | 8 | 6 | yes | 7/9 | medium | medium | First milestone: derive equation lemmas for valueAux and settle small N (say N <= 8) to build API, then hunt f |
| `Paper/Chvatal.lean` | `exists_maximal_star` | 8 |  | yes | 9/9 | none | high | Not a near-term formalization target; a known special case (e.g. downsets generated by sets of size at most 3) |
| `Paper/ClaudesCycles.lean` | `cube_hamiltonian_arc_decomposition_even` | 8 | 6 | suspect | 7/8 | medium | medium | Consider restating per-m (forall m, answer(sorry) iff HasHamiltonianArcDecomposition m) or splitting off m = 4 |
| `Paper/ConjugacyClassSizes.lean` | `conjClassSizes_iff_sym_three` | 8 |  | yes | 9/10 | none | high | Not near-term formalizable: needs CFSG-level finite group theory absent from Mathlib. Extend the in-file API i |
| `Paper/DeGiorgi.lean` | `DeGiorgi_eight` | 9 |  | yes | 10/10 | none | high | Not approachable; same remarks as DeGiorgi_four. |
| `Paper/DeGiorgi.lean` | `DeGiorgi_five` | 9 |  | yes | 10/10 | none | high | Not approachable; same remarks as DeGiorgi_four. |
| `Paper/DeGiorgi.lean` | `DeGiorgi_four` | 9 |  | yes | 10/10 | none | high | Not approachable. A formalizable neighbouring target would be Savin's theorem stated with its extra limit hypo |
| `Paper/DeGiorgi.lean` | `DeGiorgi_le_eight` | 9 |  | yes | 10/10 | none | high | Do not attack directly. Even the solved case n = 2 needs Liouville-type theorems and stability/energy estimate |
| `Paper/DeGiorgi.lean` | `DeGiorgi_seven` | 9 |  | yes | 10/10 | none | high | Not approachable; same remarks as DeGiorgi_four. |
| `Paper/DeGiorgi.lean` | `DeGiorgi_six` | 9 |  | yes | 10/10 | none | high | Not approachable; same remarks as DeGiorgi_four. |
| `Paper/Dubner.lean` | `dubner_conjecture` | 9 |  | yes | 10/10 | none | high | Out of reach; only finite-range sanity checks are feasible, in the spirit of the existing test lemmas. |
| `Paper/FusibleNumber.lean` | `conj_7_1` | 8 |  | suspect | 7/8 | small | medium | First milestone: build IsFusible API (successor structure, the fact that the k-th successor of x is x + (2 - 2 |
| `Paper/HartshorneConjecture.lean` | `harthshorne_conjecture` | 9 |  | suspect | 10/10 | none | medium | Prove hasFiniteCoproductsVectorBundles first (direct sums of locally free sheaves of finite rank) so the state |
| `Paper/Homogenous.lean` | `countablyMonolithicSpace_card_lt` | 8 |  | yes | 8/10 | none | medium | If Mathlib gains Arhangel'skii's cardinality theorem, record the reduction 'Problem 15 implies Problem 16' as  |
| `Paper/Homogenous.lean` | `countablyMonolithicSpace_exists_nhds_generated_countable` | 8 |  | yes | 8/10 | none | medium | Leave open; a Mathlib prerequisite is Sapirovskii-style results on points of countable pi-character in compact |
| `Paper/Homogenous.lean` | `firstCountableTopology_of_countablyMonolithicSpace` | 8 |  | yes | 8/10 | none | medium | Leave open; record that a positive answer here implies Problem 16 via Arhangel'skii's cardinality theorem (fir |
| `Paper/Homogenous.lean` | `homogeneousSpace_exists_inj_tendsto` | 9 |  | yes | 9/10 | none | medium | Leave open. Formal progress would first require the classical cardinal-function toolkit (pi-character, Sapirov |
| `Paper/Homogenous.lean` | `homogeneousSpace_exists_surjective` | 9 |  | yes | 9/10 | none | medium | Leave open. A formalizable warm-up is the metrizable case, or the classical fact that every compact Hausdorff  |
| `Paper/Kurepa.lean` | `kurepa_conjecture` | 9 |  | yes | 9/10 | none | high | Out of reach analytically. The only cheap extension is widening the first_cases sanity check beyond n < 50 (ke |
| `Paper/Kurepa.lean` | `kurepa_conjecture.variants.gcd` | 9 |  | yes | 9/10 | none | high | Treat as an alias; derive it from the main conjecture via gcd_reduction once (if ever) that is proved. |
| `Paper/Kurepa.lean` | `kurepa_conjecture.variants.prime` | 9 |  | yes | 9/10 | none | high | Treat as an alias of the main conjecture; if that is ever proved, close this in one line. |
| `Paper/LatinSquare.lean` | `growthRateZn` | 1 | 5 | yes | 8/10 | none | medium | Re-categorise as `research solved` citing EMM 2019; a Lean proof would require formalizing their circle-method |
| `Paper/LatinSquare.lean` | `latinSquareNearTransversal` | 8 |  | yes | 9/10 | none | high | Leave open. A tractable sub-goal would be formalizing the easy n − O(√n)/greedy bound (every Latin square has  |
| `Paper/LatinSquare.lean` | `latinSquareOrder11Transversal` | 8 | 6 | yes | 9/10 | large | high | Do not attempt. If pursued at all, it would be a symmetry-reduced exhaustive search over order-11 main classes |
| `Paper/LatinSquare.lean` | `numTransversalsZn` | 1 | 5 | yes | 8/10 | none | medium | Re-categorise as `research solved` with the EMM citation, or keep as open-in-Lean but record the literature an |
| `Paper/LatinSquare.lean` | `oddOrderLatinSquareTransversal` | 8 |  | yes | 9/10 | large | high | Leave open. Realistic partial progress: formalize the n ≤ 9 verified cases (still a huge Lean computation) or  |
| `Paper/LatinTableau.lean` | `LatinTableauConjecture` | 8 |  | yes | 8/8 | small | medium | Realistic first milestones: CDS-colorability for rectangular and staircase shapes (where the k-independence nu |
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
| `Paper/PrimeTuples.lean` | `prime_tuples_conjecture` | 9 |  | yes | 10/10 | none | high | Leave open. Optionally cross-link to the existing repo statements to avoid divergence. |
| `Paper/ReedOmegaDeltaChi.lean` | `reed_conjecture_Δ_6_ω_2` | 8 |  | yes | 8/9 | large | medium | Leave open, but this is the most attackable item in the file: progress would be a computer search establishing |
| `Paper/ReedOmegaDeltaChi.lean` | `reed_omega_delta_chi_conjecture` | 9 |  | yes | 9/10 | none | high | Leave open (cat 9). Any tractable Lean work here is on special classes, not the general statement. |
| `Paper/ReedOmegaDeltaChi.lean` | `reed_omega_delta_chi_conjecture_for_finite_graphs` | 9 |  | yes | 9/10 | none | high | Leave open. Milestone-sized sub-targets would be Brooks' theorem (χ ≤ Δ for connected non-complete non-odd-cyc |
| `Paper/StrongSensitivityConjecture.lean` | `strong_sensitivity_conjecture` | 9 |  | suspect | 9/10 | none | medium | Leave open. Two cheap sanity actions: (i) run a small exhaustive search over n ≤ 5 Boolean functions to check  |
| `Paper/VoronovskajaTypeFormula.lean` | `voronovskaja_theorem.bezier_bernstein_operators` | 0 | 5 | yes | 6/8 | none | high | Port the branch to main and verify the build: fetch commit d5661226, which adds 18 supporting modules (Voronov |
| `Paper/VoronovskajaTypeFormula.lean` | `voronovskaja_theorem.bezier_bernstein_operators.variants.answer_smoothness` | 0 | 5 | yes | 6/8 | none | high | Port from d5661226 and verify the build. |
| `Paper/VoronovskajaTypeFormula.lean` | `voronovskaja_theorem.bezier_bernstein_operators.variants.eventually_smooth` | 0 | 5 | yes | 6/8 | none | high | Port together with the main theorem from commit d5661226 and verify the build. |
| `Paper/VoronovskajaTypeFormula.lean` | `voronovskaja_theorem.bezier_bernstein_operators.variants.eventually_smooth.limit_exists` | 0 | 2 | yes | 6/8 | none | high | Port from d5661226; once the main theorem is in place this one is a three-line corollary. |
| `Paper/WeakTiling.lean` | `problem_4_1` | 8 |  | yes | 7/9 | none | medium | Leave open. First real milestone would be formalizing the paper's Theorem 3.4 (necessary condition on gap leng |
| `Paper/WeakTiling.lean` | `problem_4_2` | 8 |  | yes | 8/9 | none | medium | Leave open. Note the Fuglede linkage when prioritising: this is a genuinely research-level target, not a forma |
| `Paper/WeakTiling.lean` | `problem_4_3` | 8 |  | suspect | 8/9 | none | medium | Leave open; if kept, consider relaxing the encoding to allow a general mixture (a probability measure on the s |
| `Paper/WeaklyFirstCountable.lean` | `existsWeaklyFirstCountableCompactBig` | 8 | 10 | suspect | 8/9 | none | medium | Restate as a bare existential (matching existsWeaklyFirstCountableCompactNotFirstCountable) rather than an ans |
| `Paper/WeaklyFirstCountable.lean` | `existsWeaklyFirstCountableCompactNotFirstCountable` | 8 |  | yes | 8/9 | none | medium | Leave open. The realistic Lean milestone is the *solved* companion `CH.existsWeaklyFirstCountableCompactNotFir |
| `Paper/ZagierMZV.lean` | `zagier_conjecture` | 9 |  | yes | 10/10 | none | high | Leave open (cat 9). The tractable neighbouring target is `zagier_upper_bound`, which is itself a deep motivic  |
| `Wikipedia/ABC.lean` | `abc` | 9 |  | yes | 10/10 | none | high | Leave open. Only realistic Lean work is formalising known partial results (e.g. Stewart-Yu exponential bounds, |
| `Wikipedia/ABC.lean` | `abc.variants.lt_constant_mul` | 9 |  | yes | 10/10 | none | high | Leave open; if `abc` is ever proved, derive this by splitting off the finitely many exceptional triples and ta |
| `Wikipedia/ABC.lean` | `abc.variants.quality` | 9 |  | yes | 10/10 | none | high | Leave open. |
| `Wikipedia/AgohGiuga.lean` | `agoh_giuga` | 9 |  | yes | 9/10 | none | high | Leave open. A tractable sub-goal is to formalise the easy direction (prime => p*num + den ≡ 0 mod p^2) via von |
| `Wikipedia/AgohGiuga.lean` | `agoh_giuga.variants.giuga` | 9 |  | yes | 9/9 | none | high | Leave open. The forward direction is a short Fermat-little-theorem argument (sum_{i=1}^{p-1} i^{p-1} ≡ p-1 ≡ - |
| `Wikipedia/Agrawal.lean` | `agrawal_conjecture` | 9 | 8 | yes | 9/9 | large | high | Leave open; the answer(sorry) slot cannot be filled without either a proof or an explicit counterexample. A la |
| `Wikipedia/Agrawal.lean` | `agrawal_conjecture.variants.popovych` | 9 |  | yes | 9/9 | large | high | Leave open. |
| `Wikipedia/AlmostPerfectNumbers.lean` | `exists_almost_perfect_not_power_of_two` | 9 |  | yes | 9/9 | none | high | Leave open. A worthwhile intermediate formalisation is 'every even almost perfect number is a power of 2' or ' |
| `Wikipedia/AmicableNumbers.lean` | `infinitely_many_amicable` | 9 |  | suspect | 9/9 | none | high | Either delete in favour of Erdos830.erdos_830.parts.i, or strengthen IsAmicable-based set to `{(a,b) \| a < b  |
| `Wikipedia/AmicableNumbers.lean` | `opposite_parity_amicable` | 9 | 6 | yes | 9/9 | medium | high | Leave open. A targeted search over squares/twice-squares up to ~10^14 could in principle produce a decidable w |
| `Wikipedia/AmicableNumbers.lean` | `relatively_prime_amicable` | 9 |  | yes | 9/9 | none | high | Leave open. Formalising the known lower bound would need substantial sigma-multiplicativity machinery. |
| `Wikipedia/Andrica.lean` | `andrica_conjecture` | 9 |  | yes | 9/10 | none | high | Leave open. The realistic Lean target in this file is `andrica_conjecture.ferreira_large_n`, not the universal |
| `Wikipedia/ArtinPrimitiveRootsConjecture.lean` | `artin_primitive_roots.parts.i` | 9 |  | yes | 10/10 | none | high | Leave open. The only realistic Lean path is via the GRH-conditional statement, itself a large analytic-number- |
| `Wikipedia/ArtinPrimitiveRootsConjecture.lean` | `artin_primitive_roots.parts.ii` | 9 |  | yes | 10/10 | none | high | Leave open. |
| `Wikipedia/ArtinPrimitiveRootsConjecture.lean` | `artin_primitive_roots.variants.part_ii_power_squarefreePart_modeq_one` | 9 |  | suspect | 10/10 | none | medium | Leave open; separately reconcile the docstring with the `Odd m` hypothesis, or split the even-m case out expli |
| `Wikipedia/ArtinPrimitiveRootsConjecture.lean` | `artin_primitive_roots.variants.part_ii_power_squarefreePart_not_modeq_one` | 9 |  | yes | 10/10 | none | medium | Leave open. |
| `Wikipedia/BalancedPrimes.lean` | `balanced_primes` | 9 |  | yes | 9/9 | none | high | Leave open. Out of reach of current sieve technology. |
| `Wikipedia/BalancedPrimes.lean` | `balanced_primes_order` | 9 |  | suspect | 9/9 | none | high | Leave open; consider reformulating as `∀ k > 0, answer(sorry) k ↔ ...` or as a per-k family. |
| `Wikipedia/BatemanHornConjecture.lean` | `bateman_horn_conjecture` | 3 | 9 | no | 10/10 | none | medium | Fix the definition before any proof attempt: replace the unconditional `∏'` by an ordered limit over primes be |
| `Wikipedia/BealConjecture.lean` | `beal_conjecture` | 9 |  | yes | 10/10 | none | high | Leave open. Progress would mean formalising known cases (e.g. specific exponent triples via modularity), each  |
| `Wikipedia/BeckFialaConjecture.lean` | `beck_fiala_conjecture` | 9 |  | yes | 9/10 | none | high | Leave open. A realistic Lean target in this file is `beck_fiala_theorem` (the 2t-1 bound), whose floating-colo |
| `Wikipedia/BetrothedNumbers.lean` | `infinitely_many_betrothed` | 9 |  | yes | 9/9 | none | high | Leave open. |
| `Wikipedia/BetrothedNumbers.lean` | `same_parity_betrothed` | 9 | 6 | no | 9/9 | medium | high | Add `m ≠ n` (or `m < n`, as `infinitely_many_betrothed` in the same file does) to the statement, then re-class |
| `Wikipedia/BingBorsuk.lean` | `bing_borsuk_conjecture` | 9 |  | yes | 10/10 | none | medium | Leave open. Even the n = 1 and n = 2 cases would require ANR theory, covering-dimension theory and topological |
| `Wikipedia/Bloch.lean` | `blochConstant_exact_value` | 3 | 4 | no | 9/8 | none | high | Fix the definition: require S to be open (or a domain) and f injective *and* conformal on S, e.g. `∃ S ⊆ ball  |
| `Wikipedia/Bloch.lean` | `landauConstant_exact_value` | 9 |  | yes | 9/10 | none | high | Leave open. Any progress would first need Mathlib support for the Koebe/Landau-Schottky machinery; even the cl |
| `Wikipedia/BoundedBurnsideProblem.lean` | `bounded_burnside_problem` | 1 | 5 | yes | 9/10 | none | high | Re-tag as `research solved` with answer(False), and record that closing it in Lean requires formalizing an inf |
| `Wikipedia/Brennanconjecture.lean` | `brennan_universalSpectrum` | 9 |  | yes | 9/10 | none | high | Leave open. A Lean attack would first require Mathlib theory for integral means of univalent functions (Koebe  |
| `Wikipedia/Brennanconjecture.lean` | `brennan_universalSpectrumBounded` | 9 |  | yes | 9/10 | none | high | Leave open; same prerequisite Mathlib theory as `brennan_universalSpectrum`. |
| `Wikipedia/BrocardConjecture.lean` | `brocard_conjecture` | 9 |  | yes | 9/10 | none | high | Leave open. A conditional route (e.g. from Cramer/Riemann-type gap bounds plus a finite check) is not currentl |
| `Wikipedia/Buchi.lean` | `buchi_problem` | 9 |  | yes | 9/10 | none | high | Leave open. Only a conditional variant (assume Bombieri-Lang, conclude M=8) is currently statable; that would  |
| `Wikipedia/Buchi.lean` | `buchi_problem_M5` | 8 |  | yes | 8/9 | medium | medium | Two concrete avenues: (a) run a large search for length-5 nontrivial sequences (elliptic/K3 surface point sear |
| `Wikipedia/Bunyakovsky.lean` | `bunyakovsky_conjecture` | 9 |  | yes | 10/10 | none | high | Leave open. The only tractable sub-result is the degree-1 specialization via Mathlib's Dirichlet theorem (`Nat |
| `Wikipedia/BusyBeaver.lean` | `BB_6` | 9 |  | no | 10/10 | large | high | Fix `Candidate` to `Γ_card = 2`, `Λ_card = n` (and `sanity_check` to `Machine (Fin 2) (Fin n)`), then leave BB |
| `Wikipedia/CarmichaelTotient.lean` | `charmichaelTotient` | 9 |  | yes | 9/10 | none | high | Leave open. Realistic partial targets: extend the in-file elementary reductions (e.g. handle n ≡ 2 mod 4, n di |
| `Wikipedia/Catalan.lean` | `lebesgue_nagell` | 8 |  | yes | 8/10 | none | high | Medium-to-large: the residual range is a finite list of ~150 primes attacked by the modular method (Frey curve |
| `Wikipedia/Catalan.lean` | `pillais_conjecture` | 9 |  | yes | 9/10 | none | high | Leave open. A worthwhile in-repo variant: state the abc-conditional implication, or the known fixed-exponent c |
| `Wikipedia/CernyConjecture.lean` | `cerny_conjecture` | 9 |  | yes | 9/10 | none | high | Leave open. A tractable adjacent contribution: formalize the cubic Frankl-Pin bound (n^3-n)/6, which is a clea |
| `Wikipedia/ClassNumberProblem.lean` | `class_number_problem` | 9 |  | yes | 10/10 | none | high | Leave open. No feasible Lean path; even the heuristic side is unformalizable. Could add the (proved) Stark-Hee |
| `Wikipedia/CollatzConjecture.lean` | `collatz_conjecture` | 9 |  | yes | 10/10 | none | high | Leave open. Do not spend effort. |
| `Wikipedia/CongruentNumber.lean` | `Tunnell_even_converse` | 9 |  | yes | 10/10 | none | high | Leave open or restate conditionally on BSD. |
| `Wikipedia/CongruentNumber.lean` | `Tunnell_odd_converse` | 9 |  | yes | 10/10 | none | high | Leave open, or restate conditionally on BSD, which would turn it into a (still very large) formalization of Tu |
| `Wikipedia/Conway99Graph.lean` | `conway99Graph` | 9 |  | yes | 9/10 | large | high | Leave open. Exhaustive search over 99-vertex graphs is hopeless; progress would come from algebraic/spectral n |
| `Wikipedia/DedekindNumber.lean` | `Dedekind_10` | 9 | 4 | suspect | 8/10 | large | medium | Leave open; do not attempt. If kept, tighten the statement to `M 10 = (<numeral> : ℕ)` shape so the answer slo |
| `Wikipedia/DedekindNumber.lean` | `M_eq` | 4 | 10 | no | 1/2 | none | high | Either delete/downgrade this statement, or replace it with a precise complexity claim (e.g. counting antichain |
| `Wikipedia/DeterminantalConjecture.lean` | `determinantal_conjecture` | 9 |  | yes | 9/9 | none | medium | Leave open. A reachable sub-target: the Hermitian case, or n <= 3 by explicit computation. |
| `Wikipedia/DiameterSimpleFiniteGroups.lean` | `babai_seress_conjecture` | 9 |  | yes | 10/10 | none | high | Leave open; a genuine research problem requiring growth-in-groups machinery entirely absent from Mathlib. |
| `Wikipedia/DiameterSimpleFiniteGroups.lean` | `babai_seress_conjecture_alternating` | 9 |  | yes | 9/10 | none | high | Leave open. Nothing in Mathlib supports expander/growth arguments; a first milestone would be the classical di |
| `Wikipedia/Dickson.lean` | `dickson_conjecture` | 9 |  | yes | 10/10 | none | high | Leave open. Cheap repo-level improvement: derive dickson_conjecture from schinzel_conjecture (a one-line `exac |
| `Wikipedia/Dickson.lean` | `infinite_cousin_primes` | 9 |  | yes | 10/10 | none | high | Leave open. |
| `Wikipedia/Dickson.lean` | `infinite_safe_primes` | 9 |  | yes | 10/10 | none | high | Leave open; rename to infinite_sophie_germain_primes (or state as {q \| q.Prime ∧ ∃ p, q = 2p+1 ∧ p.Prime}) to |
| `Wikipedia/Dickson.lean` | `infinite_sexy_primes` | 9 |  | yes | 10/10 | none | high | Leave open. |
| `Wikipedia/Dickson.lean` | `polignac_conjecture` | 9 |  | yes | 10/10 | none | high | Leave open; possibly restrict to 0 < k and note that Maynard–Tao gives 'for some k'. Alternatively record the  |
| `Wikipedia/EllipticCurveRank.lean` | `finite_twentyone_lt_finrank` | 9 |  | yes | 10/10 | none | high | Leave open. |
| `Wikipedia/EllipticCurveRank.lean` | `half_rank_zero_and_half_rank_one` | 9 |  | yes | 10/10 | none | high | Leave open. Realistic Lean work would first need Mordell–Weil and Selmer machinery that Mathlib does not have. |
| `Wikipedia/EllipticCurveRank.lean` | `rank_elkies28` | 9 | 5 | yes | 9/10 | large | high | Leave open; add GRH hypothesis, or first target the unconditional lower bound. |
| `Wikipedia/EllipticCurveRank.lean` | `rank_elkiesKlagsbrun29` | 9 | 5 | yes | 9/10 | large | high | Leave open as stated. Realistic intermediate goal: formalize the ≥ 29 lower bound (explicit points + height-pa |
| `Wikipedia/EllipticCurveRank.lean` | `rank_height_count_asymptotic` | 3 | 8 | no | 10/3 | none | high | Fix the quantifier: replace `∀ H, 1 < H → ...` by an eventually-form, e.g. `∀ᶠ H in atTop, ...`, or state it a |
| `Wikipedia/EllipticCurveRank.lean` | `twentyone_le_rank_height_count_asymptotic` | 9 |  | yes | 10/10 | none | high | Leave open. |
| `Wikipedia/EllipticCurveRank.lean` | `unbounded_rank_conjecture` | 9 |  | yes | 10/10 | none | high | Leave open. A partial win: prove the n ≤ 29 instances from the explicit points on elkiesKlagsbrun29 — but that |
| `Wikipedia/Euclid.lean` | `euclid_numbers_are_square_free` | 9 | 6 | yes | 9/10 | medium | high | Leave open. Only realistic short-term contribution: extend the computational verification for small n (does no |
| `Wikipedia/Euclid.lean` | `infinite_prime_euclid_numbers` | 9 |  | yes | 9/10 | none | high | Leave open. |
| `Wikipedia/EulerBrick.lean` | `cuboidThree` | 8 |  | suspect | 8/9 | small | medium | Check Sharipov's exact hypothesis and, if it is pairwise coprimality, weaken `gcd a (gcd b c) = 1` to pairwise |
| `Wikipedia/EulerBrick.lean` | `cuboidTwo` | 8 |  | yes | 8/8 | small | medium | Attempt the Asiryan-style reduction (specialize X, reduce irreducibility to a rank-0 elliptic curve / genus ar |
| `Wikipedia/EulerBrick.lean` | `four_dim_euler_brick_existence` | 8 | 6 | yes | 9/2 | large | medium | Two-track: (a) push the K₄ search to 10^8–10^9 with a leg-indexed sieve on a cluster — a hit gives a 4-line `d |
| `Wikipedia/EulerBrick.lean` | `n_dim_euler_brick_existence` | 9 |  | yes | 10/10 | none | medium | Leave open; resolve the n = 4 case first. |
| `Wikipedia/EulerBrick.lean` | `perfect_euler_brick_existence` | 9 |  | yes | 10/10 | none | medium | Leave open. If any of the 2026 preprints is genuine and accepted, re-classify to cat 5. |
| `Wikipedia/EulerSumOfPowers.lean` | `eulers_sum_of_powers_conjecture` | 9 |  | yes | 10/10 | large | high | Leave open. Only realistic contributions: (i) the n = 2 sub-case once FLT lands in Mathlib; (ii) extend comput |
| `Wikipedia/Exponentials.lean` | `four_exponentials_conjecture` | 9 |  | yes | 10/10 | none | high | Leave open. Mathlib does not even have the six exponentials theorem; formalizing that would be the sensible pr |
| `Wikipedia/Exponentials.lean` | `two_pow_three_pow_transcendental` | 9 |  | yes | 10/10 | none | high | Leave open; if the file's four_exponentials_conjecture is ever available, derive this from it (a genuine but n |
| `Wikipedia/FeitThompsonPrimeConjecture.lean` | `feit_thompson_primes` | 9 |  | yes | 9/10 | none | high | Leave open. A worthwhile companion statement would be the known Stephens counterexample to the gcd version, to |
| `Wikipedia/Fermat.lean` | `all_fermat_squarefree` | 9 |  | yes | 9/10 | none | high | Leave open; the Wieferich reduction would be a good @[category research solved] companion lemma. |
| `Wikipedia/Fermat.lean` | `fermat_number_are_composite` | 9 |  | yes | 10/10 | none | high | Leave open; the answer(sorry) slot cannot be filled honestly. Could add supporting @[category research solved] |
| `Wikipedia/Fermat.lean` | `infinite_fermat_composite` | 9 |  | yes | 9/10 | none | medium | Leave open. Cheap partial credit: note that this and infinite_fermat_primes cannot both be false (ℕ = union of |
| `Wikipedia/Fermat.lean` | `infinite_fermat_primes` | 9 |  | yes | 10/10 | none | high | Leave open. |
| `Wikipedia/FermatCatalanConjecture.lean` | `fermat_catalan` | 9 |  | yes | 10/10 | none | high | Leave open. A reasonable formal milestone is Darmon–Granville or the Beal/abc implication rather than the conj |
| `Wikipedia/FibonacciPrimes.lean` | `fib_primes_infinite` | 9 |  | yes | 10/10 | none | high | Leave open. Note the file already proves the equivalence with the index formulation (indices_infinite_iff_fib_ |
| `Wikipedia/FibonacciPrimes.lean` | `fib_primes_infinite.variant` | 9 |  | yes | 10/10 | none | high | Leave open. |
| `Wikipedia/Firoozbakht.lean` | `firoozbakht_conjecture` | 9 |  | yes | 10/10 | none | high | Leave open. Guard against the risk that it is false by keeping the consequence theorem conditional (already do |
| `Wikipedia/FlintCooksonHills.lean` | `cookson_hills_series_converges` | 9 |  | yes | 10/10 | none | high | Leave open. |
| `Wikipedia/FlintCooksonHills.lean` | `flint_hills_series_converges` | 9 |  | yes | 10/10 | none | high | Leave open; the honest answer slot is 'unknown'. A worthwhile companion would be formalizing Alekseyev's impli |
| `Wikipedia/Fuglede.lean` | `FugledeConjecture.variants.dim_1` | 9 |  | yes | 9/10 | none | high | Leave open. Realistic intermediate targets: formalize the finite-abelian-group reductions or the union-of-inte |
| `Wikipedia/Fuglede.lean` | `FugledeConjecture.variants.dim_2` | 9 |  | yes | 9/10 | none | high | Leave open. |
| `Wikipedia/GapConjecture.lean` | `gap_conjecture` | 9 | 8 | yes | 9/10 | none | medium | Leave open. First formal milestone would be generating-set independence of the growth preorder (γ_S ≼ γ_T for  |
| `Wikipedia/GaussCircleProblem.lean` | `error_isBigO` | 9 |  | yes | 10/10 | none | high | Leave open. Formalizable intermediate steps: the trivial O(r) bound, Gauss's 2√2πr bound (the `error_le` sorry |
| `Wikipedia/Gilbreath.lean` | `gilbreath_conjecture` | 9 | 8 | yes | 9/10 | none | high | Leave open. A tractable sub-target is the finite verification pattern (d^k 0 = 1 for k ≤ N) once Nat.nth Prime |
| `Wikipedia/GoldbachConjecture.lean` | `goldbach` | 9 |  | yes | 10/10 | none | high | Leave open. |
| `Wikipedia/GracefulLabeling.lean` | `graceful_tree_conjecture` | 9 | 8 | yes | 9/10 | none | high | Leave open. A realistic formal milestone is the caterpillar case (explicit zig-zag labeling), or the finite ve |
| `Wikipedia/Grimm.lean` | `grimm_conjecture` | 9 |  | yes | 10/10 | none | high | Leave open. Formalizable partial credit: the k = 1, 2 cases and small-n verification. |
| `Wikipedia/Grimm.lean` | `grimm_conjecture_weak` | 9 | 8 | yes | 9/10 | none | high | Leave open; try the same small-k cases as the strong form. |
| `Wikipedia/Hadamard.lean` | `HadamardConjecture` | 9 |  | yes | 9/10 | none | high | Leave open. Highest-value cleanup: finish the ← direction of isHadamard_equiv_isHadamard' (sorry at line 75) s |
| `Wikipedia/Hadamard.lean` | `HadamardConjecture.variants.«167»` | 8 | 6 | yes | 8/9 | large | medium | Do not attempt a search in Lean. Monitor the combinatorial-design literature for a construction; if one appear |
| `Wikipedia/Hall.lean` | `hall_conjecture` | 9 |  | yes | 9/10 | none | high | Consider restating with an answer(sorry) encoding (as the repo does elsewhere for undecided-direction question |
| `Wikipedia/Hall.lean` | `weak_hall_conjecture` | 9 |  | yes | 9/10 | none | high | Leave open; the realistic formal path is 'abc ⟹ weak Hall', which could be stated conditionally in the repo as |
| `Wikipedia/HardyLittlewood.lean` | `first_hardy_littlewood_conjecture` | 4 | 3 | no | 10/10 | none | high | Rewrite: require `Function.Injective m` (or m strictly monotone), and replace `=O[atTop]` by an asymptotic-equ |
| `Wikipedia/HardyLittlewood.lean` | `second_hardy_littlewood_conjecture` | 9 |  | yes | 10/10 | none | high | Prefer an answer(sorry) encoding, as the expected resolution is a disproof. As a proof strategy, only the cond |
| `Wikipedia/IdonealCompleteness.lean` | `idoneal_numbers_completeness` | 9 | 8 | yes | 9/10 | none | high | Leave open. Realistic intermediate targets: formalise 'IsIdoneal n -> n <= 1848 or n is one further exceptiona |
| `Wikipedia/InscribedSquare.lean` | `inscribed_rectangle_problem` | 9 | 8 | yes | 9/10 | none | high | Leave open. Milestone with real value: formalise the elementary solved companion exists_inscribed_rectangle (e |
| `Wikipedia/InscribedSquare.lean` | `inscribed_square_problem` | 9 | 8 | yes | 9/10 | none | high | Leave open. Any Lean progress would first need the solved companions in the same file (exists_inscribed_rectan |
| `Wikipedia/InvariantSubspaceProblem.lean` | `Invariant_subspace_problem` | 9 |  | yes | 10/10 | none | high | Leave open. The only nearby formalisable items in the file are the finite-dimensional case (needs Jordan norma |
| `Wikipedia/InverseGalois.lean` | `inverse_galois_problem` | 9 |  | yes | 10/10 | none | high | Leave open. The realistic Lean milestone is inverse_galois_problem.variants.cyclic (Kronecker-Weber / cyclotom |
| `Wikipedia/Irrational.lean` | `algebraicIndependent_e_pi` | 9 |  | yes | 10/10 | none | high | Leave open; no unconditional approach known. Could optionally be linked to the repo's Schanuel statement as a  |
| `Wikipedia/Irrational.lean` | `irrational_catalanConstant` | 9 |  | yes | 9/10 | none | high | Leave open; do not attempt. Note the several arXiv/ResearchGate 'proofs that Catalan's constant is irrational' |
| `Wikipedia/Irrational.lean` | `irrational_e_plus_pi` | 9 |  | yes | 10/10 | none | high | Leave open. A legitimate repo improvement would be proving the textbook disjunction in Transcendental.lean, wh |
| `Wikipedia/Irrational.lean` | `irrational_e_times_pi` | 9 |  | yes | 10/10 | none | high | Leave open. |
| `Wikipedia/Irrational.lean` | `irrational_e_to_e` | 9 |  | yes | 9/10 | none | high | Leave open. |
| `Wikipedia/Irrational.lean` | `irrational_eulerMascheroniConstant` | 9 |  | yes | 10/10 | none | high | Leave open. A finite computation cannot settle it (only excludes small denominators). |
| `Wikipedia/Irrational.lean` | `irrational_ln_pi` | 9 |  | yes | 9/10 | none | high | Leave open. |
| `Wikipedia/Irrational.lean` | `irrational_pi_to_e` | 9 |  | yes | 9/10 | none | high | Leave open. |
| `Wikipedia/Irrational.lean` | `irrational_pi_to_pi` | 9 |  | yes | 9/10 | none | high | Leave open. |
| `Wikipedia/JacobianConjecture.lean` | `jacobian_conjecture` | 9 |  | yes | 10/10 | none | high | Leave open. A worthwhile, genuinely reachable repo task is closing sanity_check_condition_1 (IsUnit (det J) if |
| `Wikipedia/JugglerConjecture.lean` | `juggler_conjecture` | 9 | 8 | yes | 9/9 | none | high | Leave open. Only cheap improvements are available: mark jugglerStep as computable-friendly (Nat.sqrt for the e |
| `Wikipedia/Kakeya.lean` | `kakeya_set_conjecture` | 9 | 8 | yes | 10/10 | none | high | Leave open. The tractable milestone in this file is the n = 1 instance of KakeyaSetConjectureDim (a Kakeya set |
| `Wikipedia/Kaplansky.lean` | `idempotent_conjecture` | 9 |  | yes | 10/8 | none | high | Leave open, but add the free reduction inside the repo: from zero_divisor_conjecture K G hG, an idempotent a s |
| `Wikipedia/Kaplansky.lean` | `zero_divisor_conjecture` | 9 |  | yes | 10/9 | none | high | Leave open. A realistic Lean sub-target: prove it for left-orderable G (Malcev-Neumann / leading-term argument |
| `Wikipedia/Koethe.lean` | `KotheConjecture` | 9 |  | yes | 9/9 | none | high | Leave open. Useful adjacent API the file itself flags as TODO: basic lemmas about nil ideals (nil ideals are c |
| `Wikipedia/Koethe.lean` | `KotherConjecture.variants.general_matrix` | 9 |  | yes | 9/9 | none | high | Leave open. |
| `Wikipedia/Koethe.lean` | `KotherConjecture.variants.le_KotherRadical` | 9 |  | yes | 9/9 | none | high | Leave open. If any one of the five Koethe variants in this file is ever proved, formalising the classical equi |
| `Wikipedia/Koethe.lean` | `KotherConjecture.variants.matrixOver_KotherRadical` | 9 |  | suspect | 9/9 | none | medium | Cosmetic fix worth making now: drop the unused {I} (hI) binders and correct the docstring from M_2 to M_n. Mat |
| `Wikipedia/Koethe.lean` | `KotherConjecture.variants.two_by_two_matrix` | 9 |  | yes | 9/9 | none | high | Leave open. Note this is a literal instance of general_matrix at n = Fin 2, so it should be derivable from it  |
| `Wikipedia/KomlosConjecture.lean` | `komlos_conjecture` | 8 | 9 | yes | 9/9 | none | high | Leave open. A realistic intermediate target is formalising Beck-Fiala (discrepancy <= 2t-1) or the Spencer 'si |
| `Wikipedia/KummerVandiver.lean` | `kummer_vandiver` | 9 |  | yes | 9/10 | none | high | Leave open. Mathlib currently lacks Iwasawa theory / Herbrand-Ribet-level machinery; even formalising the comp |
| `Wikipedia/LanderParkinAndSelfridgeConjecture.lean` | `lander_parkin_selfridge` | 3 | 9 | no | 9/1 | none | high | Fix the statement by adding hypotheses `0 < n` and `0 < m` (or requiring the common sum to be positive), then  |
| `Wikipedia/LanderParkinAndSelfridgeConjecture.lean` | `lander_parkin_selfridge.variants.five_three` | 8 |  | yes | 9/9 | large | high | Leave open. Realistic partial targets: formalise mod-p obstructions ruling out solutions in residue classes, o |
| `Wikipedia/LegendreConjecture.lean` | `legendre_conjecture` | 9 |  | yes | 10/10 | none | high | Leave open. Cannot be closed without a breakthrough in prime gaps; the only tractable adjacent work is formali |
| `Wikipedia/LehmerMahlerMeasureProblem.lean` | `lehmer_mahler_measure_problem` | 9 |  | yes | 9/9 | none | high | Leave open. Feasible adjacent formalisation targets in the same file are the solved variants (Smyth's non-reci |
| `Wikipedia/LehmerMahlerMeasureProblem.lean` | `lehmer_mahler_measure_problem.variants.best` | 9 |  | yes | 9/10 | none | high | Leave open. Note the file does not even have a lemma computing mahlerMeasureZ lehmerPolynomial numerically; es |
| `Wikipedia/LehmerTotient.lean` | `lehmer_totient` | 9 |  | yes | 9/9 | none | high | Leave open. A tractable sub-result would be formalising the classical constraints on a hypothetical Lehmer num |
| `Wikipedia/LeinsterGroup.lean` | `infinitely_many_leinster_groups` | 8 | 9 | yes | 8/9 | small | medium | Leave open. Identifiable avenue: find/verify an infinite family of non-abelian Leinster groups, which would se |
| `Wikipedia/Lemoine.lean` | `lemoine_conjecture` | 9 |  | yes | 9/10 | none | high | Leave open. No feasible formal route; circle-method machinery for the ternary Goldbach theorem is not in Mathl |
| `Wikipedia/Lemoine.lean` | `lemoine_conjecture_extension` | 9 |  | yes | 9/10 | none | medium | Leave open. Before any proof effort, cross-check the statement against the Kiltinen-Young paper (the Wikipedia |
| `Wikipedia/LittlewoodConjecture.lean` | `littlewood_conjecture` | 9 |  | yes | 10/10 | none | high | Leave open. Mathlib has no homogeneous-dynamics/measure-rigidity infrastructure; even the EKL partial result i |
| `Wikipedia/LittlewoodConjecture.lean` | `padic_littlewood_conjecture` | 9 |  | yes | 10/10 | none | medium | Leave open. Flag in the docstring that the function-field analogue is now known to be false, which is decision |
| `Wikipedia/LonelyRunnerConjecture.lean` | `lonely_runner_conjecture` | 8 | 9 | yes | 9/9 | medium | high | Leave open. Concrete milestone: formalise a single small case (n = 3, i.e. two nonzero speeds) via the standar |
| `Wikipedia/LychrelNumbers.lean` | `isLychrel10_196` | 9 |  | yes | 9/10 | none | high | Leave open. No known proof technique; a partial formal result could be 'lychrelStep^[k] 196 is not a palindrom |
| `Wikipedia/LychrelNumbers.lean` | `no_lychrel_numbers_base10` | 9 |  | yes | 9/10 | none | high | Leave open. There is no known invariant proof technique for base 10; the only formalisable content is the equi |
| `Wikipedia/MagicSquares.lean` | `exists_magic_square_squares` | 8 |  | yes | 9/9 | large | high | Leave open. Identifiable avenue: reduce to rational points on a specific elliptic surface (Bremner) - a resear |
| `Wikipedia/MagicSquares.lean` | `exists_semi_magic_square_cubes` | 8 |  | yes | 8/8 | large | high | Leave open. The most realistic formal contribution is a kernel-checked exhaustive-search certificate extending |
| `Wikipedia/Mahler32.lean` | `mahler_conjecture` | 9 |  | suspect | 9/10 | none | high | Either restrict the hypothesis to 0 < x to match Mahler exactly, or add a remark that the negative case is a d |
| `Wikipedia/Mandelbrot.lean` | `MLC` | 9 |  | yes | 10/10 | none | high | Leave open. Any Lean work should target the supporting API (multibrotSet_eq is already proved) rather than the |
| `Wikipedia/Mandelbrot.lean` | `MLC_general_exponent` | 9 |  | yes | 10/10 | none | high | Leave open. |
| `Wikipedia/Mandelbrot.lean` | `density_of_hyperbolicity` | 9 |  | yes | 10/10 | none | high | Leave open. |
| `Wikipedia/Mandelbrot.lean` | `density_of_hyperbolicity_general_exponent` | 9 |  | yes | 10/10 | none | high | Leave open. |
| `Wikipedia/Mandelbrot.lean` | `volume_frontier_mandelbrotSet_eq_zero` | 9 |  | yes | 10/10 | none | high | Leave open. |
| `Wikipedia/Mandelbrot.lean` | `volume_frontier_multibrotSet_eq_zero` | 9 |  | yes | 10/10 | none | high | Leave open. |
| `Wikipedia/MeanValueProblem.lean` | `mean_value_problem` | 8 |  | suspect | 8/8 | none | medium | Remove the unused `K : R` binder and add a hypothesis p.derivative.eval z <> 0 (or state the bound multiplicat |
| `Wikipedia/Mersenne.lean` | `catalans_mersenne_conjecture` | 9 |  | yes | 10/10 | none | high | Leave open. There is no computational or theoretical handle; do not attempt. |
| `Wikipedia/Mersenne.lean` | `infinitely_many_mersenne_primes` | 9 |  | yes | 10/10 | none | high | Leave open. A worthwhile (non-resolving) formal contribution would be the Euclid-Euler bridge lemma linking th |
| `Wikipedia/Mersenne.lean` | `new_mersenne_conjecture` | 9 |  | yes | 9/10 | none | high | Leave open. Given the proved reduction, this statement is derivable in one line from new_mersenne_conjecture.v |
| `Wikipedia/Mersenne.lean` | `new_mersenne_conjecture.variants.prime` | 9 |  | yes | 9/10 | none | high | Leave open; this is the right canonical target of the two (the general form follows from it in one line via ne |
| `Wikipedia/MoserWorm.lean` | `convex_mosers_worm_problem` | 9 |  | yes | 9/9 | none | high | Leave open; the tractable adjacent targets are the two companion bound theorems (still sorry). Do not fill ans |
| `Wikipedia/MoserWorm.lean` | `mosers_worm_problem` | 9 | 4 | suspect | 9/9 | none | medium | Do not attempt to fill answer(). First tighten the specification: require `IsClosed X` (or `IsCompact X`) in ` |
| `Wikipedia/MovingSofa.lean` | `sofaConstant_eq_volume_iff_eq_gerversSofa` | 3 | 4 | no | 9/3 | none | high | Refute or, better, fix the statement: restrict to `∀ s, (∃ m, IsMovingSofa s m) → (volume s = sofaConstant ↔ ∃ |
| `Wikipedia/NormalityOfPi.lean` | `pi_normal_base_ten` | 9 |  | suspect | 10/10 | none | high | Leave open, but rename/strengthen the Mathlib-shim definition (e.g. `IsSimplyNormalInBase` plus a block-based  |
| `Wikipedia/Oppermann.lean` | `oppermann_conjecture` | 9 |  | yes | 10/10 | none | high | Leave open; optionally restate it as `⟨parts.i x hx, parts.ii x hx⟩` so only two statements carry sorries. |
| `Wikipedia/Oppermann.lean` | `oppermann_conjecture.parts.i` | 9 |  | yes | 10/10 | none | high | Leave open. |
| `Wikipedia/Oppermann.lean` | `oppermann_conjecture.parts.ii` | 9 |  | yes | 10/10 | none | high | Leave open. |
| `Wikipedia/PebblingNumberConjecture.lean` | `pebbling_number_conjecture` | 9 |  | suspect | 9/10 | none | high | Restate with `{V W : Type} (G : SimpleGraph V) (H : SimpleGraph W)` and add a hypothesis of connectedness (or  |
| `Wikipedia/Pell.lean` | `infinite_pellNumber_primes` | 9 |  | yes | 10/10 | none | high | Leave open. The tractable adjacent work (Binet-type formula, P_{2n+1} identity) is already proved in this file |
| `Wikipedia/PerfectNumbers.lean` | `infinitely_many_even_perfect` | 9 |  | yes | 10/10 | none | high | Leave open. Worth linking to FormalConjectures/Wikipedia/Mersenne.lean:infinitely_many_mersenne_primes (line 1 |
| `Wikipedia/PerfectNumbers.lean` | `infinitely_many_perfect` | 9 |  | yes | 10/10 | none | high | Leave open; answer() cannot be filled. |
| `Wikipedia/PerfectNumbers.lean` | `odd_perfect_number_conjecture` | 9 |  | yes | 10/10 | none | high | Leave open. The realistic Lean target in this file is odd_perfect_number.euler_form, for which a formal proof  |
| `Wikipedia/PierceBirkhoff.lean` | `pierce_birkhoff_conjecture` | 9 | 4 | suspect | 9/10 | none | medium | Fix `IsSemiAlgebraic` to allow finite unions of finite intersections of {p = 0}, {q > 0} (and complements), th |
| `Wikipedia/PollocksConjecture.lean` | `pollock_tetrahedral` | 9 |  | yes | 9/10 | none | high | Leave open. A useful supporting contribution would be `tetrahedral n = n*(n+1)*(n+2)/6` divisibility API plus  |
| `Wikipedia/PollocksConjecture.lean` | `pollock_tetrahedral.salzer_levine` | 9 | 6 | yes | 9/8 | small | high | Split the statement: the membership half (343867 ∉ sums of four tetrahedral numbers) is a finite check and is  |
| `Wikipedia/PrimesAndPerfectSquares.lean` | `infinite_prime_sq_add_one` | 9 |  | yes | 10/10 | none | high | Leave open; answer() cannot be filled. |
| `Wikipedia/QuasiperfectNumbers.lean` | `exists_quasiperfect` | 9 |  | yes | 9/10 | none | high | Leave open; answer() cannot be filled. A worthwhile addition would be the known constraint theorems (odd squar |
| `Wikipedia/RamanujanTau.lean` | `lehmer_ramanujan_tau` | 9 |  | suspect | 10/10 | none | high | First discharge `multipliable` and `τ_two` (small/medium Lean work) so the definition is certified non-junk; t |
| `WrittenOnTheWallII/GraphConjecture100.lean` | `conjecture100` | 0 | 4 | suspect | 5/4 | none | high | Port GraphConjecture100ForkProof.lean + GraphConjecture100Complete.lean from branch agent/solve-wowii-100 onto |
| `WrittenOnTheWallII/GraphConjecture103.lean` | `conjecture103` | 8 |  | yes | 6/8 | none | medium | Attack via b(G) >= alpha(G) + alpha(G - S) for a maximum independent set S, plus the induced shortest path of  |
| `WrittenOnTheWallII/GraphConjecture133.lean` | `conjecture133` | 8 |  | yes | 6/8 | none | medium | Split as the file already suggests: the C4-containing branch is essentially free; concentrate on the C4-free b |
| `WrittenOnTheWallII/GraphConjecture141.lean` | `conjecture141` | 7 | 8 | yes | 5/7 | none | medium | Prove: (i) tree(G) >= maxL + 1 by exhibiting the induced star {v} ∪ A for a maximum independent A ⊆ N(v); (ii) |
| `WrittenOnTheWallII/GraphConjecture142.lean` | `conjecture142` | 8 |  | yes | 6/8 | none | medium | Baseline lemma tree(G) >= girth(G) - 1 (a shortest cycle minus one vertex is an induced path); then the conten |
| `WrittenOnTheWallII/GraphConjecture143.lean` | `conjecture143` | 0 |  | yes | 5/1 | none | high | Replace the `sorry` in GraphConjecture143.lean by `exact conjecture143_proved G h hσ` (or import the ForkProof |
| `WrittenOnTheWallII/GraphConjecture144.lean` | `conjecture144` | 8 |  | yes | 6/8 | none | medium | Prove the baseline tree(G) >= girth(G) - 1 first (shortest cycle minus a vertex is an induced path), then atta |
| `WrittenOnTheWallII/GraphConjecture145.lean` | `conjecture145` | 0 |  | yes | 6/3 | none | medium | Recover branch agent/solve-wowii-145-current (or fetch DomTheDeveloper/crl 145.lean), add a ForkProof wrapper  |
| `WrittenOnTheWallII/GraphConjecture146.lean` | `conjecture146` | 0 | 1 | yes | 6/3 | none | medium | Fetch google-deepmind/formal-conjectures PR #4505, confirm it targets this exact statement (same hypotheses hr |
| `WrittenOnTheWallII/GraphConjecture160.lean` | `conjecture160` | 3 | 0 | no | 2/3 | small | high | Either (a) merge the PR #11 correction (replace countInducedC4 by the C4-free indicator) and keep the theorem  |
| `WrittenOnTheWallII/GraphConjecture19.lean` | `conjecture19` | 8 |  | yes | 7/8 | none | medium | Attack via b(G) >= maxL + 1 (an induced star is bipartite) and b(G) >= diam(G) + 1 (a geodesic is induced and  |
| `WrittenOnTheWallII/GraphConjecture194.lean` | `conjecture194` | 8 |  | yes | 8/9 | small | medium | Chvatal-Erdos style approach: a counterexample needs alpha >= kappa + 2 while l_avg >= alpha - 1. Small cases  |
| `WrittenOnTheWallII/GraphConjecture198a.lean` | `conjecture198a` | 8 |  | yes | 8/9 | small | medium | Note b(G) >= alpha(G) + 1, so the hypothesis forces alpha <= 1 + ecc_avg; combine with Chvatal-Erdos-type trac |
| `WrittenOnTheWallII/GraphConjecture2.lean` | `conjecture2` | 0 |  | yes | 5/3 | none | high | Port ProofAudit/2_*.lean (counting core, local choice, double count, double-star spanning-tree bridge, tree le |
| `WrittenOnTheWallII/GraphConjecture200.lean` | `conjecture200` | 8 |  | yes | 7/9 | small | medium | First formalise tree(G) >= maxL + 1 >= ceil(1 + l_avg) (induced star at the arg-max vertex); this converts the |
| `WrittenOnTheWallII/GraphConjecture217.lean` | `conjecture217` | 7 | 5 | yes | 6/7 | medium | medium | Formalise the free half first (residue != 2 implies Ls <= 2 implies a 2-leaf spanning tree, i.e. a Hamiltonian |
| `WrittenOnTheWallII/GraphConjecture291.lean` | `conjecture291` | 8 | 6 | suspect | 7/8 | medium | low | First settle the reading of k against the WOWII definitions popup. Then run an exhaustive search over all conn |
| `WrittenOnTheWallII/GraphConjecture316.lean` | `conjecture316` | 0 |  | yes | 5/1 | none | high | Replace the `sorry` in GraphConjecture316.lean by `exact conjecture316_solved G hG h`, flip the category to re |
| `WrittenOnTheWallII/GraphConjecture40.lean` | `conjecture40` | 8 |  | yes | 7/8 | none | medium | Baseline: f(G) >= ceil(b(G)/2) (the larger side of an induced bipartite subgraph is independent, hence an indu |
| `WrittenOnTheWallII/GraphConjecture59.lean` | `conjecture59` | 3 | 0 | yes | 4/6 | medium | medium | Recover branch audit/wowii59-clean-final (or agent/solve-wowii-59), rebuild the one-file disproof against curr |
| `WrittenOnTheWallII/GraphConjecture61.lean` | `conjecture61` | 8 |  | yes | 7/8 | small | medium | Start from the known residue(G) <= alpha(G) <= f(G) (Favaron-Maheo-Sacle) and try to gain ceil(diam/3) by addi |
