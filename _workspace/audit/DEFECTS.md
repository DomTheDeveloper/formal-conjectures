# Statement defects

170 declarations whose formal statement does not faithfully capture the intended problem,
or whose meaning could not be pinned down. These are the repository's integrity risks: a prover can
produce a green build on many of them without doing any of the intended mathematics.

The dominant pattern is the **`answer()` echo** — a goal `answer(sorry) = e` or `answer(sorry) ↔ P`
where `e`/`P` is already in scope, so the answer term can be instantiated to the thing being asked
about and closed by `rfl`. Fixing these is upstream-reportable work independent of solving anything.

## Category 3 — false as stated  (14)

### `Books/UniformDistributionOfSequences/Equidistribution.lean:isEquidistributedModuloOne_transcendental_three_halves_pow`

Claims that for EVERY transcendental x, the sequence x*(3/2)^n is equidistributed modulo 1.

- **Defect:** The universally-quantified statement over transcendental x does not correspond to any conjecture in the cited book and is false by known results.
- **Match:** no · **Confidence:** medium · **Lean difficulty:** 9/10
- **Flags:** false-as-stated: universal quantifier over transcendental x contradicts Peres-Schlag/Katznelson-type constructions; no matching conjecture in cited source; needs literature check only for the precise citation of the (3/2)^n badly-approximable construction (Akhunzhanov-Moshchevitin)
- **Fix:** Flag for correction upstream: weaken to 'for almost every x' (Koksma/Weyl metric theorem, provable but nontrivial) or delete. Formally refuting the current statement in Lean would require a Peres-Schlag-type Cantor construction — large effort, so the practical action is to fix the statement, not to prove its negation.

### `LittProblems/1.lean:lam_litt.variants.integrality_implies_algebraicity`

If a power series solution of an algebraic ODE has all coefficients in Z[1/N] for some N, then it is algebraic over Q(z).

- **Defect:** The cleared-denominator encoding of the ODE has no q(pt) != 0 side condition, so degenerate 'solutions' are admitted and the statement is false; the intended conjecture is untouched and remains open.
- **Match:** no · **Confidence:** high · **Lean difficulty:** 8/10
- **Flags:** false as stated: degenerate object admitted (q(pt) = 0); same defect present in the sibling omega-integrality statement and in the definition IsSolutionOfAlgebraicODE used by both
- **Fix:** Repair IsSolutionOfAlgebraicODE by adding `MvPolynomial.aeval pt q != 0` (or state the ODE as f^(n) = aeval pt p / aeval pt q in the fraction field). Repair is strongly preferable to formalizing the refutation, since proving sum j! z^j transcendental in Lean needs growth/convergence theory Mathlib lacks for this purpose.

### `Millenium/Poincare.lean:poincare_conjecture.variants.smooth_other_cases`

For every n > 4 outside {1,2,3,5,6,12,56,61}, the smooth Poincare conjecture fails in dimension n (i.e. exotic n-spheres exist).

- **Defect:** n = 126 is a counterexample after Lin-Wang-Xu (2024/25): the file's SmoothTrueValues set is out of date, and the conjecture it encodes was disproved rather than proved.
- **Match:** no · **Confidence:** medium · **Lean difficulty:** 10/10
- **Flags:** status changed externally after the file was written (2025 result); the same missing-[T2Space] defect as smooth_dimension_four would instead make this statement degenerately TRUE for every n - two competing defects, both requiring repair; needs literature check on the exact Theta_126 = 0 <=> theta_6 exists equivalence in Wang-Xu
- **Fix:** Update SmoothTrueValues to {1,2,3,5,6,12,56,61,126}, restate as a research-solved theorem citing Hill-Hopkins-Ravenel + Wang-Xu + Lin-Wang-Xu, and demote/retire the 'conjectured' framing. Formalizing either direction is research-scale.

### `OptimizationConstants/1a.lean:mem_Ioc_c1a`

Exhibit a number in (1.2748, C1a], i.e. improve the known lower bound for Tao's autocorrelation constant 1a.

- **Defect:** Because the broken definition forces C1a = 0, the target set Set.Ioc 1.2748 C1a = Ioc 1.2748 0 is EMPTY, so no value of answer(sorry) can make the statement true.
- **Match:** no · **Confidence:** high · **Lean difficulty:** 5/10
- **Flags:** statement is unsatisfiable as written (empty interval); root cause is the shared broken definition of C1a
- **Fix:** Fix C1a (supremum over t in Icc (-1/2) (1/2), f supported in [-1/4,1/4]) and restate; do not attempt to prove the current statement.

### `Other/VCDimConvex.lean:exists_hasAddVCNDimAtMost_n_of_convex_rn_add_one`

For every n there is a finite d such that every convex set in ℝ^(n+1) has additive VCₙ dimension at most d.

- **Defect:** Missing `1 ≤ n` (the companion conjecture on line 69 does carry `2 ≤ n`). At n = 0 the notion degenerates: `Fin 0 → Fin (d+1)` is a singleton type, the sum ∑ k : Fin 0 is 0, and `HasAddVCNDimAtMost A 0 d` unfolds to 'no y : Set (unit-type) → G with y s ∈ A ↔ i₀ ∈ s', which holds iff A = ∅ or A = univ, independently of d. Since ℝ^(0+1) = (Fin 1 → ℝ) contains convex sets that are neither empty nor everything (e.g. C = {p | p 0 ≤ 0}), the n = 0 instance is false, hence the declaration as stated is false.
- **Match:** no · **Confidence:** high · **Lean difficulty:** 4/10
- **Flags:** Missing positivity hypothesis on n makes the statement false for a purely degenerate reason (spec defect, not a mathematical refutation of the authors' intent).; Even the intended n ≥ 2 case is now under pressure: the verified PR #88 certificate shows d = 1 fails at n = 2; whether the construction scales to arbitrary grid size (which would refute the intended conjecture too) is untested.; verifier:confirmed
- **Fix:** Add the hypothesis `(hn : 1 ≤ n)` (or state it only for n ≥ 2) to the canonical statement; then leave it open. Refuting the current statement in Lean is easy if desired: take n = 0, C = {p | p 0 ≤ 0}, x = elim, y s = if i₀ ∈ s then 0 else 1, using `Subsingleton (Fin 0 → Fin (d+1))`.

### `Other/VCDimConvex.lean:hasAddVCNDimAtMost_n_one_of_convex_rn_add_one`

For n ≥ 2, every convex set in ℝ^(n+1) has additive VCₙ dimension at most 1 (no convex set admits translates cutting out all 2^(2ⁿ) subsets of a 2×…×2 additive grid).

- **Defect:** Faithful; refuted on the mathematics, not on a formalization artifact. Note this declaration's n = 2 instance is exactly `hasAddVCNDimAtMost_two_one_of_convex_r3` above, and here the ambient type is literally `Set (Fin 3 → ℝ)`, i.e. an exact syntactic match for the counterexample branch (no EuclideanSpace transfer needed).
- **Match:** yes · **Confidence:** high · **Lean difficulty:** 3/10
- **Flags:** Canonical repo statement is FALSE as written — high priority defect; whether the conjecture survives for n ≥ 3 is untested (the counterexample only covers n = 2).; Refutation lives only on unmerged fork branches (PR #88 closed).; verifier:confirmed
- **Fix:** Port the branch counterexample and instantiate it at n = 2 to derive `¬ ∀ n ≥ 2, ...`; then replace this lemma with a corrected statement (e.g. ask for the true growth of VCₙ dimension of convex sets in ℝ^(n+1), or restrict to larger n if the authors believe n ≥ 3 survives) and verify the build. Report upstream.

### `Other/VCDimConvex.lean:hasAddVCNDimAtMost_two_one_of_convex_r3`

Every convex set C in ℝ³ has additive VC₂ dimension at most 1, i.e. no convex C admits translates cutting out all 16 subsets of a 2×2 additive grid {x₀(a)+x₁(b) : a,b ∈ {0,1}}.

- **Defect:** The Lean statement faithfully encodes the intended conjecture — and the conjecture itself is false, not merely the formalization. The refuting configuration is non-degenerate: x 0 = ![0, (50000,0,0)], x 1 = ![0, (0,50000,0)] give four DISTINCT grid points forming a genuine 2-dimensional parallelogram, so no degeneracy in the definition is being exploited.
- **Match:** yes · **Confidence:** high · **Lean difficulty:** 4/10
- **Flags:** Canonical repo statement is FALSE as written — high priority defect.; PR #88 was closed without merging, so the refutation exists only on fork branches; main still carries the false claim.; Type mismatch to resolve when porting: branch works in `Fin 3 → ℝ`, canonical lemma in `EuclideanSpace ℝ (Fin 3)`.; verifier:confirmed
- **Fix:** Correct the canonical file: replace this lemma by `∃ C : Set ℝ³, Convex ℝ C ∧ ¬ HasAddVCNDimAtMost C 2 1`, porting the certificate from branch `agent/solve-vc2-convex-counterexample` (file FormalConjectures/Other/VCDimConvexCounterexample.lean) and verifying the build; the only porting work is moving from `R3 := Fin 3 → ℝ` to `ℝ³ = EuclideanSpace ℝ (Fin 3)` (same additive group / module structure, transfer via the WithLp type synonym or `WithLp.equiv`). Also fix the module docstring, which advertises this bound. Consider notifying upstream google-deepmind/formal-conjectures.

### `Wikipedia/BatemanHornConjecture.lean:bateman_horn_conjecture`

For distinct irreducible polynomials with positive leading coefficients satisfying the Schinzel condition, the count of n <= x at which all are simultaneously prime is asymptotic to C * x / (log x)^k with C the Bateman-Horn constant.

- **Defect:** `BatemanHornConstant` is defined with Mathlib's `∏'` (tprod), which is an *unconditional* (Finset-filter) limit and therefore requires `Multipliable`. The Bateman-Horn Euler product is in general only conditionally convergent: the p-th factor is (1-1/p)^{-k}(1-ω_p/p) = 1 + (k-ω_p)/p + O(1/p^2), and Σ_p |k - ω_p|/p diverges whenever ω_p genuinely fluctuates. For polys = {X^2+1} (k=1) one has ω_p = 0 for p ≡ 3 mod 4 and ω_p = 2 for p ≡ 1 mod 4, so |log(term)| ≍ 1/p and the sum over p ≡ 3 mod 4 diverges: the family is NOT multipliable, `∏'` falls back to its junk value 1, and BatemanHornConstant {X^2+1} collapses to 1/D = 1/2. The theorem then asserts #{n ≤ x : n^2+1 prime} ~ (1/2) x / log x, whereas the true (Hardy-Littlewood/Landau) constant is ≈ 0.6864. So the formal statement is not the Bateman-Horn conjecture and is believed false.
- **Match:** no · **Confidence:** medium · **Lean difficulty:** 10/10
- **Flags:** MAJOR: tprod junk value — Bateman-Horn Euler product is only conditionally convergent, so BatemanHornConstant degenerates to 1/D for e.g. {X^2+1}; off-by-one: n = 0 counted; natAbs allows negative polynomial values to count as prime
- **Fix:** Fix the definition before any proof attempt: replace the unconditional `∏'` by an ordered limit over primes below x (e.g. `Tendsto (fun N => ∏ p ∈ primesBelow N, ...) atTop (𝓝 C)`), or bundle the constant as an existential 'C is the limit of the truncated products'. Then re-classify as cat 9.

### `Wikipedia/Bloch.lean:blochConstant_exact_value`

Ahlfors-Grunsky conjecture: the Bloch constant B (largest r such that every holomorphic f on the unit disk with f'(0)=1 contains a schlicht disk of radius r in its image) equals Gamma(1/3)Gamma(11/12)/(Gamma(1/4)sqrt(1+sqrt3)) ~ 0.4719.

- **Defect:** `blochConstant` (line 114) quantifies the schlicht set as an ARBITRARY set `∃ S ⊆ ball 0 1, ball x B ⊆ f '' S ∧ InjOn f S`, with no openness/connectedness/domain requirement on S. By the axiom of choice, whenever ball x B ⊆ f '' (ball 0 1) one can choose a set-theoretic section S (one preimage per point of the ball); then f '' S = ball x B and InjOn f S holds automatically. Hence the defining set of `blochConstant` is literally the same as that of `landauConstant` (line 170), i.e. blochConstant = landauConstant as defined, not the Bloch constant.
- **Match:** no · **Confidence:** high · **Lean difficulty:** 8/10
- **Flags:** major semantic mismatch: InjOn-on-arbitrary-set loophole makes Bloch constant = Landau constant; formal statement false as written; intended Ahlfors-Grunsky conjecture remains open; same loophole affects blochRadius (line 45) and the research-solved theorems blochConstant_lower_bound / blochConstant_upper_bound (the latter also becomes false)
- **Fix:** Fix the definition: require S to be open (or a domain) and f injective *and* conformal on S, e.g. `∃ S ⊆ ball 0 1, IsOpen S ∧ ...`, or define blochRadius via `∃ S, IsOpen S ∧ InjOn f S ∧ ball x B = f '' S`. Then re-tag as open. Refuting the current statement in Lean would need Landau's theorem L >= 1/2 (not in Mathlib), so the practical action is a definition repair, not a proof.

### `Wikipedia/EllipticCurveRank.lean:rank_height_count_asymptotic`

For 1 ≤ r ≤ 20, the number of elliptic curves over ℚ of naive height ≤ H and rank ≥ r is H^((21-r)/24 + o(1)).

- **Defect:** Two defects. (1) FALSE AS STATED: the o(1) is encoded as a single f with `∀ H : ℕ, 1 < H → ncard = (H:ℝ)^((21-r)/24 + f H)`, an exact equality required at *every* H > 1. But heightLE 2 and heightLE 3 are empty (naiveHeight E = max (4|A|³) (27B²) ≤ 3 forces A = B = 0, excluded by Δ_ne_zero), so the left side is 0 while (H:ℝ)^x is a positive rpow for H ≥ 2. Even for H = 4..~10 the set {E | r ≤ E.rank} is empty for r ≥ 1 (the only curves of height ≤ 4 are y² = x³ ± x, rank 0). Hence no f can exist and the theorem is unprovable/refutable. (2) The docstring says 'curves with rank r' but the statement counts `r ≤ E.rank`; these agree only to within the o(1), so it is a benign but real prose/formal mismatch.
- **Match:** no · **Confidence:** high · **Lean difficulty:** 3/10
- **Flags:** FALSE AS STATED: small-H emptiness vs strictly positive rpow; docstring/statement mismatch: 'rank = r' vs 'r ≤ rank'; the sibling twentyone_le_rank_height_count_asymptotic avoids the bug only because it uses ≤
- **Fix:** Fix the quantifier: replace `∀ H, 1 < H → ...` by an eventually-form, e.g. `∀ᶠ H in atTop, ...`, or state it as two-sided bounds H^(c-ε) ≤ N(H) ≤ H^(c+ε) for large H. Then re-classify as open (cat 8/9).

### `Wikipedia/LanderParkinAndSelfridgeConjecture.lean:lander_parkin_selfridge`

If a sum of n positive k-th powers equals a sum of m positive k-th powers with every left value different from every right value, then n + m >= k.

- **Defect:** The docstring says 'for positive integers k, n, m', but the Lean statement quantifies over ALL k n m : N with no positivity on n or m. Taking n = m = 0 makes every hypothesis vacuous and both sums equal to 0, forcing the conclusion k <= 0 for every k. The formal statement is therefore false.
- **Match:** no · **Confidence:** high · **Lean difficulty:** 1/10
- **Flags:** missing positivity hypothesis on n and m; empty-index degenerate object admitted; prose docstring (positive n, m) does not match the formal quantification
- **Fix:** Fix the statement by adding hypotheses `0 < n` and `0 < m` (or requiring the common sum to be positive), then re-classify as cat 8/9. Do not attempt to prove the current form. Cannot verify by build here (no lake cache); the refutation is a one-liner once stated as a negation.

### `Wikipedia/MovingSofa.lean:sofaConstant_eq_volume_iff_eq_gerversSofa`

Stated: for EVERY subset s of the plane, s has area equal to the sofa constant if and only if s equals Gerver's sofa. Intended: Gerver's sofa is the unique area-maximising moving sofa (up to rigid motion).

- **Defect:** The universally quantified `∀ s : Set ℝ²` has no restriction to moving sofas and no quotient by rigid motions. Any set with the same measure as Gerver's sofa — e.g. a translate, or Gerver's sofa with one point added or deleted — would have to be literally equal to gerversSofa. Uniqueness in the literature is uniqueness among maximal-area sofas up to congruence.
- **Match:** no · **Confidence:** high · **Lean difficulty:** 3/10
- **Flags:** FALSE AS STATED; quantifier scope: ∀ s ranges over all subsets, not over moving sofas; uniqueness stated up to equality rather than up to rigid motion; null-set perturbation counterexample
- **Fix:** Refute or, better, fix the statement: restrict to `∀ s, (∃ m, IsMovingSofa s m) → (volume s = sofaConstant ↔ ∃ g : ℝ² ≃ᵃⁱ[ℝ] ℝ², s = g '' gerversSofa)`. Then port the intended content from [Ba24] (research-scale). Verify the refutation builds (cannot run lake here).

### `WrittenOnTheWallII/GraphConjecture160.lean:conjecture160`

For a connected graph G, the maximum number of leaves of a spanning tree is at least max_v l(v) + max_v T(v) * c_{C4}(G), where T(v) counts triangles at v; the file codes c_{C4}(G) as the NUMBER of induced 4-cycles.

- **Defect:** The WOWII invariant chi_{C4}(G) is a CHARACTERISTIC FUNCTION (1 if G has no 4-cycle, 0 otherwise), not the count of induced 4-cycles. The file uses `countInducedC4 G`, which turns a bounded correction term into an unbounded one and makes the statement false. Fork PR #11 ('Fix WOWII 160 C4-free characteristic', citing upstream issue #4423) proposes exactly this repair; the sibling file GraphConjecture133.lean already uses the characteristic-function convention.
- **Match:** no · **Confidence:** high · **Lean difficulty:** 3/10
- **Flags:** mis-transcribed invariant: countInducedC4 instead of the C4-free characteristic function; statement is refutable by a 5-vertex graph; the INTENDED WOWII 160 remains open
- **Fix:** Either (a) merge the PR #11 correction (replace countInducedC4 by the C4-free indicator) and keep the theorem research open, or (b) merge PR #4 and mark the current statement disproved. Recommend (a)+(b): fix the invariant AND record the counterexample to the mis-transcribed version.

### `WrittenOnTheWallII/GraphConjecture59.lean:conjecture59`

For a connected graph G, the largest induced forest satisfies f(G) >= ceil(sqrt(residue(G) * b(G))), where residue is the Havel-Hakimi residue and b the largest induced bipartite subgraph size.

- **Defect:** The statement matches the documented reading; what is refuted is exactly the statement as written. Whether the ORIGINAL WOWII 59 is thereby refuted depends on the (unverified) transcription of DeLaVina's invariants — the source page returns 403 from this environment.
- **Match:** yes · **Confidence:** medium · **Lean difficulty:** 6/10
- **Flags:** statement is refuted by an explicit finite counterexample built in this fork; counterexample relies on bv_decide/LRAT certificates produced by CI-patched sources — rebuild and re-audit; needs literature check: cannot confirm the transcription of WOWII 59 (source page 403), so the original conjecture may differ
- **Fix:** Recover branch audit/wowii59-clean-final (or agent/solve-wowii-59), rebuild the one-file disproof against current main, and rewrite the canonical theorem as an explicit refutation (`¬ ∀ ...` with the Fin 18 witness) marked research solved.

## Category 4 — provable without the mathematics  (59)

### `Books/BugeaudDistributionModuloOne/Problem10_6.lean:problem_10_6_variant_2`

Find a strictly increasing integer sequence with intermediate growth (m_n >= exp(n^alpha) eventually, for some 0<alpha<1) that is dense mod 1 for every irrational xi.

- **Defect:** The exists-alpha quantifier admits alpha < 1/2, and the increasing enumeration of {2^a*3^b : a,b>=1} has m_n = exp((sqrt(2*log2*log3)+o(1))*sqrt(n)), so it satisfies HasIntermediateGrowth for any alpha < 1/2; density for every irrational xi is exactly Furstenberg's x2,x3 theorem (1967), stated as furstenberg_two_three in the same file. So the formal statement is a known theorem, not an open problem — the intended 'very rapidly increasing' problem needs growth beyond exp(c*sqrt(n)).
- **Match:** no · **Confidence:** high · **Lean difficulty:** 9/10
- **Flags:** accidentally-weakened: exists-alpha allows alpha<1/2, admitting the known Furstenberg example; formal statement is not open; fix: require alpha > 1/2
- **Fix:** Either restrict to alpha > 1/2 (which restores openness) or reclassify as a corollary of Furstenberg. Closing the current formal statement requires formalizing Furstenberg's x2-x3 theorem plus the counting asymptotics of {2^a*3^b} — research-scale Lean effort (large).

### `Books/UniformDistributionOfSequences/Equidistribution.lean:isAccumulationPoint_three_halves_pow`

Find (as an answer() term) an accumulation point of the sequence of fractional parts of (3/2)^n.

- **Defect:** The intended problem — exhibit an EXPLICIT accumulation point, which is genuinely open — is not enforced by the answer() encoding: the degenerate closed-form witness answer := limsup_n fract((3/2)^n) (or sSup of the accumulation-point set) provably IS an accumulation point, because for n>=1 the values fract((3/2)^n) = (3^n mod 2^n)/2^n are in lowest terms with denominator exactly 2^n (numerator odd), hence pairwise distinct; a bounded sequence with pairwise distinct values has its limsup as a cluster point approached by infinitely many distinct values, giving membership in closure(range \ {x}).
- **Match:** suspect · **Confidence:** medium · **Lean difficulty:** 5/10
- **Flags:** answer()-encoding admits degenerate non-informative witness (limsup/sSup of the accumulation set), much weaker than the intended 'find an explicit point'
- **Fix:** Close the formal statement via answer := Filter.limsup (fun n => Int.fract ((3/2)^n)) atTop: prove fract((3/2)^n) = (3^n % 2^n)/2^n, oddness of 3^n % 2^n, pairwise distinctness, then limsup-is-cluster-point via Filter.frequently_lt_of_lt_limsup / eventually_lt_of_limsup_lt; alternatively flag upstream that the answer() encoding trivializes 'find'.

### `ErdosProblems/128.lean:erdos_128`

If every induced subgraph of an n-vertex graph G on at least n/2 vertices has more than n²/50 edges, must G contain a triangle?

- **Defect:** MAJOR quantifier-scope defect: V' is universally quantified together with the conclusion, so the RHS reads 'for every graph G and every vertex subset V' with 2|V'|+1 ≥ n and 50·e(G[V']) > n², G has a triangle' — i.e. a single dense large induced subgraph is required to force a triangle. The intended hypothesis is that EVERY such V' is dense (the ∀ V' must sit inside the hypothesis). Secondary off-by-one: 2*V'.ncard + 1 ≥ Fintype.card V encodes |V'| ≥ (n−1)/2 rather than |V'| ≥ n/2.
- **Match:** no · **Confidence:** high · **Lean difficulty:** 3/10
- **Flags:** quantifier order / witness scope loophole — different problem from the intended one; off-by-one in the |V'| ≥ n/2 threshold; trivialised: provable by a Fin 2 counterexample once answer(False) is filled in
- **Fix:** Fix the statement to: answer(sorry) ↔ ∀ V [Fintype V] (G), (∀ V' : Set V, 2 * V'.ncard ≥ Fintype.card V → 50 * (G.induce V').edgeSet.ncard > Fintype.card V ^ 2) → ¬ G.CliqueFree 3. Do not 'solve' the current version — flag it as a formalization bug and repair it.

### `ErdosProblems/142.lean:erdos_142`

Find an asymptotic formula (up to Theta) for r_k(N), the largest size of a subset of {1,...,N} containing no non-trivial k-term arithmetic progression.

- **Defect:** The `answer(sorry)` slot is an unconstrained function N -> R and appears on the right of `=Theta[atTop]`. Since `answer` elaborates in postpone mode (FormalConjectures/Util/Answer.lean:117), a solver may legitimately instantiate it with `fun N => (r k N : R)` and close the goal with `Asymptotics.isTheta_refl _ _`. Nothing in the statement forces the answer to be a closed form independent of r, so the formal statement does not encode 'prove an asymptotic formula'.
- **Match:** suspect · **Confidence:** high · **Lean difficulty:** 1/10
- **Flags:** answer()-loophole: isTheta_refl with answer := r k closes the goal; no constraint tying the answer to an explicit/elementary function
- **Fix:** Add a well-formedness side condition to the answer slot (e.g. require the answer to be built from elementary functions, or state two separate O/Omega bounds with explicit constants) before treating this as a research target; otherwise the statement is closable by self-reference.

### `ErdosProblems/142.lean:erdos_142.variants.three`

Find an asymptotic formula (up to Theta) for r_3(N), the largest 3-AP-free subset of {1,...,N}.

- **Defect:** Same answer()-loophole as erdos_142: answer := `fun N => (r 3 N : R)` plus `isTheta_refl` closes the goal. Mathematically the intended question (matching upper and lower bounds for r_3) is one of the best-known open problems in additive combinatorics.
- **Match:** suspect · **Confidence:** high · **Lean difficulty:** 1/10
- **Flags:** answer()-loophole: isTheta_refl
- **Fix:** Constrain the answer slot (explicit closed form) or split into a stated conjecture such as r_3(N) = N^{1-o(1)}-type bounds; then re-audit.

### `ErdosProblems/142.lean:erdos_142.variants.upper`

Find a function f_k with r_k(N) = O(f_k(N)).

- **Defect:** Completely degenerate as formalised: the goal is `(fun N => (r k N : R)) =O[atTop] (answer(sorry) : N -> R)` with no further constraint on the answer. Instantiating answer := `fun N => (r k N : R)` and applying `Asymptotics.isBigO_refl _ _` proves it in one line. Unlike erdos_160.better_upper there is no second conjunct forcing the bound to be an improvement, so the statement carries no mathematical content.
- **Match:** no · **Confidence:** high · **Lean difficulty:** 1/10
- **Flags:** major answer()-loophole: one-line proof by isBigO_refl; statement weaker than intended (different problem)
- **Fix:** Restate as e.g. `exists f, r_k =O f and f =o (known bound)` mirroring erdos_160.better_upper, or fix an explicit target bound; then re-audit.

### `ErdosProblems/15.lean:erdos_15`

Does the alternating series sum_{n>=1} (-1)^n n / p_n converge, where p_n is the n-th prime?

- **Defect:** Mathlib's `Summable f` means the NET of finite partial sums converges (unconditional summability), which for a real/rational series is equivalent to absolute summability. The Erdos question is about conditional convergence of the ordered partial sums sum_{n<=N}. Since sum_n n/p_n diverges (n/p_n ~ 1/log n), `Summable` is provably FALSE here, so the formal statement collapses to `answer := False` and is decidable today with elementary Mathlib input, while the actual open question is untouched. Additionally the series is stated in Q, where the limit of a convergent real series need not even exist.
- **Match:** no · **Confidence:** high · **Lean difficulty:** 4/10
- **Flags:** major semantic mismatch: Summable (unconditional) used for a conditional-convergence question; series stated over Q, whose completion issues make even the intended reading wrong; as stated the answer is forced to False
- **Fix:** Rewrite as `answer(sorry) <-> exists L : R, Tendsto (fun N => sum_{k in Finset.range N} (-1)^(k+1)*(k+1)/(nth Prime k)) atTop (nhds L)` over R (not Q). Meanwhile the current statement can be discharged: |f k| = (k+1)/p_k >= 1/p_k, and Mathlib's `Nat.Primes.not_summable_indicator_one_div_natCast` (sum of prime reciprocals diverges) plus `Real.summable_abs_iff` gives ¬Summable; a Q-summable family would also be R-summable via the continuous embedding.

### `ErdosProblems/319.lean:erdos_319.variants.isBigO`

Find g with c(N) = O(g(N)) for the Erdos 319 extremal function c.

- **Defect:** Accidentally weakened: any g growing at least linearly is a valid answer, so the statement carries no information about the actual problem. Explicitly acknowledged by the formalisation note at lines 49-54.
- **Match:** suspect · **Confidence:** high · **Lean difficulty:** 3/10
- **Flags:** trivially satisfiable answer() — does not certify optimality
- **Fix:** Fill `answer := fun N => (N : ℝ)` and prove: from h N obtain A ⊆ Icc 1 N with c N = #A, so c N <= #(Icc 1 N) = N; conclude with `Asymptotics.isBigO_of_le`. Then verify the build (lake cannot be run in this container).

### `ErdosProblems/319.lean:erdos_319.variants.isLittleO`

Find g with c(N) = o(g(N)) for the Erdos 319 extremal function c.

- **Defect:** Same escape-hatch weakening as isBigO: any super-linear g works, e.g. N^2.
- **Match:** suspect · **Confidence:** high · **Lean difficulty:** 4/10
- **Flags:** trivially satisfiable answer() — does not certify optimality
- **Fix:** Fill `answer := fun N => (N : ℝ)^2` and prove from c N <= N that c N / N^2 → 0 (`Asymptotics.isLittleO_of_tendsto` / `isBigO.trans_isLittleO`). Verify the build afterwards.

### `ErdosProblems/321.lean:erdos_321.variants.isBigO`

Find g with R(N) = O(g(N)) for the Erdos 321 extremal function R.

- **Defect:** Accidentally weakened: g(N) = N is a valid answer since R N <= N by definition, so the statement says nothing about the problem. The file's own formalisation note concedes that trivial solutions exist.
- **Match:** suspect · **Confidence:** high · **Lean difficulty:** 3/10
- **Flags:** trivially satisfiable answer()
- **Fix:** Fill `answer := fun N => (N : ℝ)`; prove R N <= N by `Nat.sSup_le` (every member is #A with A ⊆ Finset.Icc 1 N, so #A <= N), then `Asymptotics.isBigO_of_le`. Verify the build.

### `ErdosProblems/321.lean:erdos_321.variants.isLittleO`

Find g with R(N) = o(g(N)) for the Erdos 321 extremal function R.

- **Defect:** Same escape-hatch weakening: g(N) = N^2 works trivially.
- **Match:** suspect · **Confidence:** high · **Lean difficulty:** 4/10
- **Flags:** trivially satisfiable answer()
- **Fix:** Fill `answer := fun N => (N : ℝ)^2`, reuse R N <= N, conclude via `Asymptotics.IsBigO.trans_isLittleO` with N = o(N^2). Verify the build.

### `ErdosProblems/332.lean:erdos_332`

Find conditions on A ⊆ ℕ that guarantee that D(A) — the set of integers occurring infinitely often as a difference a₁−a₂ of elements of A — is syndetic (has bounded gaps).

- **Defect:** The statement is `(answer(sorry) : Set ℕ → Prop) A → HasBoundedGaps (D_A A)` — a bare sufficient-condition implication. Filling the answer slot with `fun _ ↦ False` (or any unsatisfiable predicate) makes the theorem vacuously true with a one-line proof and answers nothing. The file's own docstring concedes 'If the condition is a solution to the problem is up to human judgement.' This is not a yes/no question and admits no faithful single formal statement.
- **Match:** suspect · **Confidence:** medium · **Lean difficulty:** 8/10
- **Flags:** vacuous-answer loophole: `fun _ ↦ False` closes the theorem; problem is a 'find conditions' question, not a proposition — arguably belongs in category 10 as unformalisable in this shape; needs literature check on whether erdosproblems.com records a specific intended sufficient condition
- **Fix:** Either (a) restate as a concrete named implication, e.g. `0 < upperDensity A → HasBoundedGaps (D_A A)`, and formalise the Følner/Bogolyubov argument (A−A ⊇ Bohr set ⇒ syndetic) — a substantial Mathlib gap; or (b) keep the answer slot but add a nontriviality guard (e.g. require the condition to be satisfied by some explicit A). Recommend (a).

### `ErdosProblems/340.lean:erdos_340.variants.isTheta`

Determine the exact order of growth of |A∩[1,N]| for the greedy Sidon (Mian–Chowla) sequence, as a Θ-asymptotic.

- **Defect:** Two defects. (1) The answer slot has type ℕ → ℝ and IsTheta is reflexive, so filling it with the left-hand function itself, `fun n ↦ ((Set.range greedySidon ∩ Set.Icc 1 n).ncard : ℝ)`, closes the theorem by `IsTheta.refl` while saying nothing. (2) The hypotheses (ε : ℝ) (hε : ε > 0) are copied from erdos_340 and are completely unused, so the statement is ε-independent and the docstring (which is a verbatim copy of erdos_340's) does not describe it.
- **Match:** suspect · **Confidence:** high · **Lean difficulty:** 1/10
- **Flags:** tautological-answer loophole (IsTheta is reflexive); unused hypotheses ε, hε; docstring duplicated from erdos_340 and does not describe the Θ formulation
- **Fix:** Delete or restate. A defensible replacement is `∀ ε > 0, (fun n ↦ (n:ℝ)^(1/2−ε)) =O[atTop] card ∧ card =O[atTop] (fun n ↦ (n:ℝ)^(1/2))`, or drop the variant entirely and keep erdos_340. If kept, at minimum remove the unused ε hypotheses.

### `ErdosProblems/354.lean:erdos_354.parts.ii`

Intended (apparently): is there some ratio γ strictly between 1 and 2 for which the interleaved union {⌊γᵏα⌋} ∪ {⌊γᵏβ⌋} is complete whenever α, β > 0 and α/β is irrational?

- **Defect:** BUG: the bound variable γ never appears in the body. The statement reads `∃ γ ∈ Set.Ioo (1:ℝ) 2, ∀ α>0, ∀ β>0, Irrational (α/β) → IsAddCompleteNatSeq' (FloorMultiples.interleave α β 2)` — the last argument is the literal `2`, not γ. Since Set.Ioo (1:ℝ) 2 is provably nonempty (e.g. 3/2), the whole statement is logically equivalent to erdos_354.parts.i. The two docstrings are also verbatim identical, reinforcing that this is a copy-paste error: the third argument should be γ.
- **Match:** no · **Confidence:** high · **Lean difficulty:** 2/10
- **Flags:** unused bound variable γ — statement collapses to parts.i; docstring copy-pasted from parts.i; needs literature check to recover the intended γ range
- **Fix:** Fix the statement: replace `FloorMultiples.interleave α β 2` by `FloorMultiples.interleave α β γ` in parts.ii, and rewrite the docstring so it states the γ-quantified question rather than duplicating part (i). Until then this declaration should not be counted as an open problem. Verify the intended γ range against erdosproblems.com/354 before committing.

### `ErdosProblems/357.lean:erdos_357.parts.ii.bigO_version`

How does f(n) grow: exhibit g with g = O(f), answer(sorry)-encoded.

- **Defect:** answer(sorry)-encoding admits degenerate witnesses: answer := fun n => (f n : R) closes it by isBigO_refl, and answer := 0 by isBigO_zero. The file's own formalisation note (lines 43-52) acknowledges these trivial solutions and appeals to a 'mathematically interesting answer' convention that is not machine-checkable.
- **Match:** suspect · **Confidence:** high · **Lean difficulty:** 1/10
- **Flags:** answer-encoding trivializable (acknowledged in-file)
- **Fix:** Tighten the encoding (e.g. require an explicit elementary function with a stated exponent) or accept as convention-guarded; do not count a trivial closure as progress.

### `ErdosProblems/357.lean:erdos_357.parts.ii.bigO_version_symm`

How does f(n) grow: exhibit g with f = O(g), answer(sorry)-encoded.

- **Defect:** Degenerate witness answer := fun n => (f n : R) closes it by isBigO_refl; answer := fun n => (n:R) also works after the easy lemma f n <= n. In-file note acknowledges the loophole.
- **Match:** suspect · **Confidence:** high · **Lean difficulty:** 1/10
- **Flags:** answer-encoding trivializable (acknowledged in-file)
- **Fix:** Same as bigO_version: tighten encoding or treat as convention-guarded.

### `ErdosProblems/357.lean:erdos_357.parts.ii.bigTheta_version`

How does f(n) grow: exhibit g with f = Theta(g), answer(sorry)-encoded.

- **Defect:** Degenerate witness answer := fun n => (f n : R) closes it by Asymptotics.isTheta_refl. In-file note acknowledges the loophole.
- **Match:** suspect · **Confidence:** high · **Lean difficulty:** 1/10
- **Flags:** answer-encoding trivializable (acknowledged in-file)
- **Fix:** Same as bigO_version.

### `ErdosProblems/357.lean:erdos_357.parts.ii.littleO_version`

How does f(n) grow: exhibit g with g = o(f), answer(sorry)-encoded.

- **Defect:** Degenerate witness answer := 0 closes it: the zero function is little-o of anything (Asymptotics.isLittleO_zero). In-file note explicitly names answer = 0 as a trivial solution.
- **Match:** suspect · **Confidence:** high · **Lean difficulty:** 1/10
- **Flags:** answer-encoding trivializable (acknowledged in-file)
- **Fix:** Same as bigO_version.

### `ErdosProblems/357.lean:erdos_357.parts.ii.littleO_version_symm`

How does f(n) grow: exhibit g with f = o(g), answer(sorry)-encoded.

- **Defect:** Degenerate witness answer := fun n => (n:R)^2 closes it after the short lemma f n <= n (StrictMono a : Fin k -> Z into Icc 1 n forces k <= n, so the sSup is <= n), since n = o(n^2). Slightly more work than the other variants but still a routine closure.
- **Match:** suspect · **Confidence:** high · **Lean difficulty:** 3/10
- **Flags:** answer-encoding trivializable via overshoot (acknowledged in-file)
- **Fix:** Same as bigO_version; note a non-degenerate answer o(n) would resolve parts.i.

### `ErdosProblems/357.lean:erdos_357.variants.monotone.parts.ii.bigO_version`

Growth of h(n): exhibit g with g = O(h), answer(sorry)-encoded.

- **Defect:** Same trivialization as the f-versions: answer := fun n => (h n : R) via isBigO_refl, or answer := 0. Also h = f provably, so this duplicates parts.ii.bigO_version.
- **Match:** suspect · **Confidence:** high · **Lean difficulty:** 1/10
- **Flags:** answer-encoding trivializable (acknowledged in-file); h provably equals f
- **Fix:** Tighten encoding or treat as convention-guarded.

### `ErdosProblems/357.lean:erdos_357.variants.monotone.parts.ii.bigO_version_symm`

Growth of h(n): exhibit g with h = O(g), answer(sorry)-encoded.

- **Defect:** answer := fun n => (h n : R) closes it by isBigO_refl. h = f provably.
- **Match:** suspect · **Confidence:** high · **Lean difficulty:** 1/10
- **Flags:** answer-encoding trivializable (acknowledged in-file); h provably equals f
- **Fix:** Tighten encoding or treat as convention-guarded.

### `ErdosProblems/357.lean:erdos_357.variants.monotone.parts.ii.bigTheta_version`

Growth of h(n): exhibit g with h = Theta(g), answer(sorry)-encoded.

- **Defect:** answer := fun n => (h n : R) closes it by isTheta_refl. h = f provably.
- **Match:** suspect · **Confidence:** high · **Lean difficulty:** 1/10
- **Flags:** answer-encoding trivializable (acknowledged in-file); h provably equals f
- **Fix:** Tighten encoding or treat as convention-guarded.

### `ErdosProblems/357.lean:erdos_357.variants.monotone.parts.ii.littleO_version`

Growth of h(n): exhibit g with g = o(h), answer(sorry)-encoded.

- **Defect:** answer := 0 closes it by isLittleO_zero. h = f provably.
- **Match:** suspect · **Confidence:** high · **Lean difficulty:** 1/10
- **Flags:** answer-encoding trivializable (acknowledged in-file); h provably equals f
- **Fix:** Tighten encoding or treat as convention-guarded.

### `ErdosProblems/357.lean:erdos_357.variants.monotone.parts.ii.littleO_version_symm`

Growth of h(n): exhibit g with h = o(g), answer(sorry)-encoded.

- **Defect:** answer := fun n => (n:R)^2 closes it after the short lemma h n <= n (values in Icc 1 n, forced injective, so k <= n). h = f provably.
- **Match:** suspect · **Confidence:** high · **Lean difficulty:** 3/10
- **Flags:** answer-encoding trivializable via overshoot (acknowledged in-file); h provably equals f
- **Fix:** Tighten encoding or treat as convention-guarded.

### `ErdosProblems/36.lean:erdos_36`

Minimum overlap problem: determine the limit of M(N)/N (answer(sorry)-encoded).

- **Defect:** answer := atTop.liminf MinOverlapQuotient (or Filter.limsup / a lim term) turns the statement into 'the limit exists', which is a known theorem (existence of the limit, in-file variants.exists tagged research solved with the 0.385694 bound, attributed to Haugland). The intended problem - identify the actual constant, only known to lie in (0.379005, 0.380926854) with no closed form - is open.
- **Match:** suspect · **Confidence:** medium · **Lean difficulty:** 9/10
- **Flags:** answer-encoding admits non-informative witness (liminf); limit-existence attribution (Haugland) taken from in-file solved tag - needs literature check for exact citation
- **Fix:** Tighten encoding (e.g. require a closed-form or high-precision decimal with matching Tendsto proof), or treat closure as 'formalize Haugland's limit-existence theorem' (large effort).

### `ErdosProblems/36.lean:erdos_36.variants.lower`

Minimum overlap problem: exhibit an explicit c with 0.379005 < c <= liminf M(N)/N, i.e. beat White's 2022 lower bound.

- **Defect:** The answer-encoding admits the degenerate witness c := atTop.liminf MinOverlapQuotient: then 0.379005 < c is exactly White's 2022 theorem (stated strictly in-file as white_2022) and c <= liminf is le_refl. So the formal statement requires no NEW bound, only a formalization of White's known result, whereas the intended problem is to find a genuinely better explicit bound.
- **Match:** suspect · **Confidence:** high · **Lean difficulty:** 9/10
- **Flags:** answer-encoding admits degenerate witness c := liminf
- **Fix:** Either tighten the encoding to demand an explicit decimal strictly above 0.379005, or treat closure as 'formalize White 2022' (large effort).

### `ErdosProblems/361.lean:erdos_361.bigO`

Erdos 361: for c > 0, how large can A be inside {1,...,floor(cn)} such that n is NOT a sum of any subset of A? Formalized as an =O growth statement with answer(sorry).

- **Defect:** Two independent defects. (1) The hypothesis 'hA : forall c n, A n = ...' re-binds c, shadowing the outer (c : R) (hc : 0 < c); quantifying over ALL c makes hA unsatisfiable: hA 0 1 forces A 1 = 0 (Icc 1 0 empty, only the empty set survives the filter, sup card = 0) while hA 2 1 forces A 1 = 2 (subsets of {1,2} with total sum != 1 include {1,2}), so the hypothesis is contradictory and the theorem is vacuously provable with ANY answer. (2) Even ignoring the shadowing, the filter condition 'n != sum over B' only excludes sets whose OWN total equals n, not sets having a SUBSET summing to n; the intended extremal function requires 'forall S subseteq B, n != sum S'. As written the sup is trivially about floor(cn), a different (trivial) quantity.
- **Match:** no · **Confidence:** high · **Lean difficulty:** 2/10
- **Flags:** shadowed quantifier makes hypothesis contradictory (vacuous); filter checks only B's own sum, not subset sums - wrong extremal function; outer c and hc unused; answer-encoding weak even after fix
- **Fix:** Fix the statement: remove the inner 'forall c' (use the outer c) and change the filter to exclude all B having a subset summing to n; then re-audit. Current statement closable by deriving False from hA 0 1 and hA 2 1 (decide/norm_num on tiny finsets).

### `ErdosProblems/361.lean:erdos_361.bigTheta`

Same Erdos 361 question formalized as an =Theta growth statement with answer(sorry).

- **Defect:** Identical defects to erdos_361.bigO: inner 'forall c' shadows the outer c making hA contradictory (A 1 = 0 and A 1 = 2), and the filter excludes only sets whose own total sum is n rather than sets with a subset summing to n.
- **Match:** no · **Confidence:** high · **Lean difficulty:** 2/10
- **Flags:** shadowed quantifier makes hypothesis contradictory (vacuous); filter checks only B's own sum, not subset sums; outer c and hc unused
- **Fix:** Fix statement as for bigO; current version closable by contradiction from hA 0 1 and hA 2 1.

### `ErdosProblems/361.lean:erdos_361.smallO`

Same Erdos 361 question formalized as an =o growth statement with answer(sorry).

- **Defect:** Identical defects to erdos_361.bigO: contradictory shadowed hypothesis and own-sum-only filter.
- **Match:** no · **Confidence:** high · **Lean difficulty:** 2/10
- **Flags:** shadowed quantifier makes hypothesis contradictory (vacuous); filter checks only B's own sum, not subset sums; outer c and hc unused
- **Fix:** Fix statement as for bigO; current version closable by contradiction from hA 0 1 and hA 2 1.

### `ErdosProblems/40.lean:erdos_40`

For which functions g with g(N) -> infinity does |A cap [1,N]| >> sqrt(N)/g(N) force A+A to represent some integer infinitely often (limsup of the representation function = infinity)?

- **Defect:** The open-ended 'for what functions g?' question is encoded as 'Erdos40ForSet answer(sorry)', i.e. exhibit ANY set G of functions for which the implication holds. G := emptyset satisfies Erdos40ForSet vacuously (fun g hg => absurd hg (Set.not_mem_empty g)), as does any set of non-divergent functions. Nothing in the statement demands nontriviality or maximality, so the formal theorem is a one-liner that answers a different (empty) question.
- **Match:** no · **Confidence:** high · **Lean difficulty:** 1/10
- **Flags:** answer()-encoding trivializable by G = empty set (major semantic mismatch); open-ended 'characterize the class' question fundamentally hard to capture with answer()
- **Fix:** Report the trivialization upstream: the encoding needs a nontriviality constraint (e.g. require some divergent g in G, or state it for a specific g). As stated, 'exact fun g hg => absurd hg (Set.not_mem_empty g)' with answer := emptyset would close it.

### `ErdosProblems/409.lean:erdos_409.parts.i`

For each n > 0, give the least number of iterations of n -> phi(n)+1 needed to reach a prime (IsLeast of the iteration-count set equals answer(sorry)).

- **Defect:** answer(sorry) elaborates in a context containing n, so answer := sInf {i | Nat.Prime ((phi . + 1)^[i] n)} closes the theorem: the set is nonempty by the fully-proved in-file termination theorem, and IsLeast S (sInf S) follows from Nat.sInf_mem / Nat.sInf_le. This definitional self-answer resolves the formal statement without answering the intended 'how many iterations?' question, for which no closed form or asymptotic is known.
- **Match:** suspect · **Confidence:** high · **Lean difficulty:** 2/10
- **Flags:** answer()-encoding admits definitional self-answer sInf S; linter does not catch parametrized non-iff answer forms
- **Fix:** Flag upstream that the encoding admits the sInf non-answer; a faithful version should demand a closed form or asymptotic with a nontriviality criterion (as the file's own note admits for the asymptotic variants).

### `ErdosProblems/409.lean:erdos_409.parts.i.isBigO`

Find (the simplest) g with c(n) = O(g(n)) for the phi(n)+1 iteration count c.

- **Defect:** answer := fun n => (c n : R) closes it by isBigO_refl; 'simplest g' is prose-only and not enforced by the statement.
- **Match:** suspect · **Confidence:** high · **Lean difficulty:** 1/10
- **Flags:** acknowledged trivializable answer()-encoding (isBigO_refl)
- **Fix:** Same as isTheta variant: accept as design-acknowledged placeholder or add a nontriviality spec.

### `ErdosProblems/409.lean:erdos_409.parts.i.isLittleO`

Find (the simplest) g with c(n) = o(g(n)) for the phi(n)+1 iteration count c.

- **Defect:** answer := fun n => ((n : R) + 1) * (c n + 1) closes it in a few lines: c n <= eps*(n+1)*(c n + 1) once eps*(n+1) >= 1, so the little-o holds regardless of what c is. No nontriviality is enforced.
- **Match:** suspect · **Confidence:** high · **Lean difficulty:** 2/10
- **Flags:** acknowledged trivializable answer()-encoding (inflate by a divergent factor)
- **Fix:** Same as the other asymptotic variants.

### `ErdosProblems/409.lean:erdos_409.parts.i.isTheta`

With c(n) the least iteration count of n -> phi(n)+1 to reach a prime, determine Theta(c(n)).

- **Defect:** c is a local hypothesis variable, so answer := fun n => (c n : R) closes the goal by Asymptotics.isTheta_refl (well, IsBigO.refl in both directions). The file's own formalisation note concedes that 'trivial or sub-optimal solutions will therefore exist' and appeals to human judgment of non-triviality.
- **Match:** suspect · **Confidence:** high · **Lean difficulty:** 1/10
- **Flags:** acknowledged trivializable answer()-encoding (isTheta_refl)
- **Fix:** Acknowledge as design-accepted loophole; a real contribution would prove nontrivial bounds (e.g. c(n) << log n type results), which is research-level.

### `ErdosProblems/409.lean:erdos_409.parts.iii`

For a fixed prime p, determine the natural density of the set of n whose phi(n)+1 iteration reaches p.

- **Defect:** The goal is 'alpha = answer(sorry)' with alpha itself a local hypothesis variable (the assumed density). answer := alpha closes the theorem by rfl, using nothing. Additionally, the statement presupposes the density exists (hypothesis hA), though existence is itself part of the open question, so even the intended reading is conditional/weakened.
- **Match:** no · **Confidence:** high · **Lean difficulty:** 1/10
- **Flags:** answer()-encoding trivialized by in-scope witness alpha (rfl); density existence assumed rather than asserted
- **Fix:** Report upstream: answer must be stated as a function of p only (move alpha out of scope, e.g. 'HasDensity (answer p)'), and existence of the density should be part of the claim.

### `ErdosProblems/409.lean:erdos_409.variants.sigma_isBigO`

Find g with c(n) = O(g(n)) for the sigma(n)-1 iteration count c.

- **Defect:** answer := fun n => (c n : R) via isBigO_refl; also vacuous if termination fails.
- **Match:** suspect · **Confidence:** high · **Lean difficulty:** 1/10
- **Flags:** acknowledged trivializable answer()-encoding; vacuous if sigma termination fails
- **Fix:** Design-acknowledged placeholder.

### `ErdosProblems/409.lean:erdos_409.variants.sigma_isLittleO`

Find g with c(n) = o(g(n)) for the sigma(n)-1 iteration count c.

- **Defect:** answer := fun n => ((n : R) + 1) * (c n + 1) closes it (eps*(n+1) >= 1 eventually); also vacuous if termination fails.
- **Match:** suspect · **Confidence:** high · **Lean difficulty:** 2/10
- **Flags:** acknowledged trivializable answer()-encoding; vacuous if sigma termination fails
- **Fix:** Design-acknowledged placeholder.

### `ErdosProblems/409.lean:erdos_409.variants.sigma_isTheta`

Determine Theta of the least iteration count c(n) of n -> sigma(n)-1 to reach a prime.

- **Defect:** answer := fun n => (c n : R) closes it by IsTheta reflexivity without using h. Moreover, if sigma-termination fails, h is unsatisfiable and the theorem is vacuous for every answer — a second independent weakness.
- **Match:** suspect · **Confidence:** high · **Lean difficulty:** 1/10
- **Flags:** acknowledged trivializable answer()-encoding; vacuous if sigma termination fails (hypothesis h unsatisfiable)
- **Fix:** Design-acknowledged placeholder; treat as spec-weak.

### `GreensOpenProblems/16.lean:green_16`

For each N, exhibit a maximum-size subset of [N] with no solution to x+3y=2z+2w in distinct elements, with its cardinality given as an answer() term.

- **Defect:** The encoding admits the degenerate echo answer := Green16.f N (the sSup definition in the same file): the theorem then only asserts that a maximum-cardinality solution-free subset exists and is MaximalFor, a routine finite argument (~30 lines) that resolves nothing. Also asks for the exact value for every N, stronger than the intended asymptotic determination of f(N).
- **Match:** suspect · **Confidence:** high · **Lean difficulty:** 3/10
- **Flags:** answer-echo loophole (answer := f N); exact-value-for-all-N reading stronger than source's asymptotic question
- **Fix:** Tighten the spec (e.g. ask for asymptotics of f, or forbid self-referential answers by convention); the echo closure could be formalized quickly if one only wants to discharge the formal statement.

### `GreensOpenProblems/24.lean:green_24`

Give, as an answer() term, the exact maximum number of affine translates of {0,1,3} that a set of n integers can contain, for every n.

- **Defect:** Doubly unfaithful: (1) the degenerate echo answer := max013AffineTranslates n closes the theorem by intro n; rfl, resolving nothing; (2) even under an honest-answer convention the statement demands an exact closed form for every n, far stronger than the source's asymptotic question (conjectured (1/3 + o(1))n^2), and such an exact formula is unlikely to exist.
- **Match:** suspect · **Confidence:** high · **Lean difficulty:** 1/10
- **Flags:** answer-echo loophole (rfl); exact-formula-for-all-n vs asymptotic source question
- **Fix:** Respec as the asymptotic question (the file's variants.conjecture already does this); flag the echo loophole to maintainers.

### `GreensOpenProblems/25.lean:green_25`

Characterize, as an answer() set, exactly which functions k(N) have the property that every partition of [N] into k(N) parts has union of restricted sumsets of size at least N/10 (for large N).

- **Defect:** The statement is 'S = answer(sorry)' for an explicitly defined set S of functions; the degenerate echo answer := S closes it by rfl. Under an honest-answer convention it demands an exact characterization of the threshold set of functions, well beyond the source's ask (narrow the gap between log log N and N/log N).
- **Match:** suspect · **Confidence:** high · **Lean difficulty:** 1/10
- **Flags:** answer-echo loophole (rfl); exact-characterization vs threshold-gap source question
- **Fix:** Respec as bound-improvement statements (the file's green_25.upper/.lower already do this); flag the echo loophole.

### `GreensOpenProblems/27.lean:green_27.equivalent`

Give, as an answer() function, the asymptotics (up to equivalence along primes) of m(p), the smallest size of a set A in Z/pZ, |A| >= 2, whose sumset A+A has no element with a unique representation.

- **Defect:** The degenerate echo answer := m closes the theorem by IsEquivalent.refl (m - m = 0 is little-o of anything), resolving nothing. Under an honest-answer convention it asks for the exact asymptotic order of m(p), which is open (known window: ~log p * sqrt(logloglog p)/logologloglog p up to (log p)^2 by Bedert).
- **Match:** suspect · **Confidence:** high · **Lean difficulty:** 1/10
- **Flags:** answer-echo loophole (IsEquivalent.refl)
- **Fix:** Flag echo loophole; prefer the .lower/.upper improvement forms in the same file.

### `GreensOpenProblems/31.lean:green_31.variants.abelian`

Decide whether every finite abelian group G has a Sidon subset of size at least 0.01 sqrt(|G|). Intended open, but under the repo's IsSidon the formal right-hand side is provably FALSE.

- **Defect:** IsSidon (Basic.lean:57) quantifies over ALL quadruples, including i1 = i2 and j1 = j2. In a group of exponent 2 take x != y: x + x = 0 = y + y, and the conclusion forces x = y. So every IsSidon subset of (ZMod 2)^n has card <= 1, while 0.01*sqrt(2^14) = 1.28 > 1. The intended (Babai-Sos / B_2) convention discounts these 2-torsion coincidences; under it F_2^n has Sidon sets of size ~sqrt(|G|) (graph of x -> x^3 over F_{2^m}) and Green's question is genuinely open.
- **Match:** no · **Confidence:** high · **Lean difficulty:** 3/10
- **Flags:** major semantic mismatch: char-2 collapse of IsSidon; formal statement refutable while the intended conjecture is open
- **Fix:** Report the definition defect upstream (IsSidon needs a distinct-pair/group variant in even-order groups). To close as-is: instantiate G := Fin 14 -> ZMod 2, use Real.sqrt 16384 = 128 to force card S >= 2, pick x != y in S and apply the Sidon hypothesis at (x, y, x, y).

### `GreensOpenProblems/31.lean:green_31.variants.sidon_01n`

Decide whether {0,1}^n contains Sidon sets of size N^{0.51} (N = 2^n). Intended open, but under the repo's IsSidon every Sidon subset of F_2^n has at most one element, so the formal right-hand side is FALSE.

- **Defect:** Same char-2 collapse as the abelian variant: for x != y in F_2^n, x + x = 0 = y + y contradicts IsSidon, so card (S n) <= 1 < (2^n)^{0.51} for every n >= 1. The binary-Sidon (B_2) literature sums DISTINCT elements, under which sets of size ~2^{n/2} exist and the N^{0.51} vs N^{0.5753} gap is the real open problem.
- **Match:** no · **Confidence:** high · **Lean difficulty:** 3/10
- **Flags:** major semantic mismatch: char-2 collapse of IsSidon; answer-encoding trivialized (False); collateral: sidon_01n_clz01 becomes vacuous
- **Fix:** Report defect upstream: use a distinct-pair Sidon/B_2 definition over F_2^n. To close as-is: at n = 1, (2^1)^{0.51} > 1 forces two distinct elements of S 1 and the IsSidon instantiation (x, y, x, y) gives False.

### `GreensOpenProblems/37.lean:green_37`

Determine exactly the least size m(N,k) of a set of naturals containing, for every d = 1..N, a k-term AP of common difference d.

- **Defect:** Tautologically closable: answer := Green37.m N k, the sInf of the very set in the statement (defined at 37.lean:40-41, in scope with N, k). IsLeast then follows from Nat.sInf_mem (nonemptiness witness A = Finset.range ((k-1)*N+1), which contains 0, d, ..., (k-1)d for every d <= N) plus Nat.sInf_le. Nothing forces a closed form. It also over-demands in another direction: an exact value for every (N,k), whereas Green asks for the growth rate (unknown already for k = 3; k = 2 is the classical restricted difference basis problem, Theta(sqrt N)).
- **Match:** no · **Confidence:** high · **Lean difficulty:** 3/10
- **Flags:** tautological answer loophole (answer := m N k); asks for an exact formula rather than the intended asymptotics
- **Fix:** Report the spec defect upstream (constrain the answer to a closed form, or replace by explicit two-sided bounds). To close as-is: nonemptiness via Finset.range ((k-1)*N+1), then Nat.sInf_mem / Nat.sInf_le.

### `GreensOpenProblems/37.lean:green_37_asymptotic`

Find a function f with m(N,k) = f(N) for all large N.

- **Defect:** answer(sorry) : N -> R elaborates with k in scope, so answer := fun N => (m N k : R) is admissible and the goal becomes eventually (m N k : R) = (m N k : R), closed by Filter.Eventually.of_forall (fun _ => rfl). Even read in good faith, 'eventual exact equality with a formula' mis-states Green's request to estimate m(N,k).
- **Match:** no · **Confidence:** high · **Lean difficulty:** 1/10
- **Flags:** tautological answer loophole; eventual exact equality mis-specifies 'determine asymptotic behavior'
- **Fix:** Report spec defect; replace with a genuine two-sided asymptotic (explicit upper/lower bound pair, or IsTheta against a concrete elementary function).

### `GreensOpenProblems/37.lean:green_37_theta`

Determine the Theta-class of m(N,k).

- **Defect:** answer := fun N => (m N k : R) gives f =Theta[atTop] f, closed by Asymptotics.isTheta_refl. No constraint ties the comparison function to a closed form.
- **Match:** no · **Confidence:** high · **Lean difficulty:** 1/10
- **Flags:** tautological answer loophole
- **Fix:** Report spec defect; a meaningful version must restrict the grammar of comparison functions or state concrete bounds.

### `GreensOpenProblems/4.lean:green_4`

Exhibit a largest product-free subset of the alternating group A_n (formalized as MaximalFor ProdFree ncard applied to an answer(sorry) family S n).

- **Defect:** Nonconstructive-choice loophole: alternatingGroup (Fin n) is a finite type, so Set (alternatingGroup (Fin n)) is finite, ProdFree holds of the empty set, and ncard is bounded; a cardinality-maximizer therefore exists for every n (Set.Finite.exists_maximalFor) and answer := fun n => Classical.choose (that existence) closes the theorem with no structural description at all. The intended problem - describing the extremal sets - is not captured. The statement also demands optimality for EVERY n while the literature settles only large n.
- **Match:** no · **Confidence:** high · **Lean difficulty:** 4/10
- **Flags:** nonconstructive answer loophole: no explicit extremal family demanded; demands all n while KLM22 covers only large n
- **Fix:** Report the spec defect upstream (the answer should be an explicit family such as extremalFamily x I together with a proof of optimality). To close as-is: Set.Finite.exists_maximalFor over {S | ProdFree S} with the empty set as nonemptiness witness, then Classical.choice.

### `GreensOpenProblems/40.lean:green_40.variants.all_n`

Intended: does f_all(r) = limsup_n (minimal linear covering density) tend to infinity with r? As formalized it instead asks whether f_all r is eventually EXACTLY infinity.

- **Defect:** Target-filter defect: ENNReal has a greatest element, so Filter.atTop = principal {top}. Hence 'Tendsto f_all atTop atTop' says 'for all large r, limsup_n minDensity n r = top', not divergence. The file's other two variants correctly use nhds top, showing this is a slip.
- **Match:** no · **Confidence:** high · **Lean difficulty:** 7/10
- **Flags:** filter-target defect: atTop instead of nhds top on an ENNReal codomain; resolvable with the unintended answer False; intended problem stays open
- **Fix:** Fix the statement to 'Tendsto f_all atTop (nhds top)'. Alternatively the current statement can be legitimately closed with answer(False) by formalizing bounded-density covering constructions - moderate-to-large Lean work with no Mathlib coding-theory support.

### `GreensOpenProblems/41.lean:green_41`

Quantitative pyjama problem: exhibit a bound ans on the number of rotations of the width-eps pyjama set needed to cover the plane that lies strictly below the Kravitz-Leng triple exponential exp(exp(exp(eps^-C))).

- **Defect:** Two independent loopholes make this a restatement of the known bound rather than an improvement. (i) C-inflation: the prover chooses C, so taking C := C0 + 1 (C0 the Kravitz-Leng exponent) and ans := exp^3(eps^-C0) satisfies both conjuncts for eps < 1, since eps^-C0 < eps^-C. (ii) Answer scope: the answer(sorry) : R hole sits under the binders for C, eps0 and eps, so ans := (minCopies eps : R) is legal and makes the first conjunct le_refl.
- **Match:** no · **Confidence:** high · **Lean difficulty:** 10/10
- **Flags:** answer-encoding weaker than intended (C inflatable; ans may depend on eps); no Lean proof of any quantitative pyjama bound exists anywhere
- **Fix:** Tighten the spec (require ans to be o of the KrLe bound for every C, or fix a lower iterated-exponential level). Even the current weakened statement needs a Lean formalization of quantitative pyjama - research-scale, nothing exists.

### `GreensOpenProblems/41.lean:green_41.variants.exists_better_bound`

Existential version: is there some bound on minCopies(eps) strictly below the Kravitz-Leng triple exponential? As encoded, taking ans := minCopies eps makes it equivalent to the KrLe bound itself.

- **Defect:** With ans := minCopies eps the two conjuncts collapse to minCopies eps < exp^3(eps^-C), which holds by Kravitz-Leng for any C > C0. The RHS is therefore TRUE by known literature and carries no 'better bound' content, contradicting the docstring's claim that this is an existential version of the main problem.
- **Match:** no · **Confidence:** high · **Lean difficulty:** 10/10
- **Flags:** existential witness trivializes 'better bound'; statement duplicates a solved sibling
- **Fix:** Replace by a spec that quantifies the improvement (double-exponential or polynomial), or delete as a duplicate. Formal closure would be answer(True) plus a formalization of KrLe - research-scale.

### `GreensOpenProblems/50.lean:green_50`

If A subset F_2^n has density alpha > 0, must the 10-fold sumset 10A contain a coset of a subspace of dimension at least n - C log_2(1/alpha) for an absolute constant C?

- **Defect:** The notation '10 • A' for A : Finset (F_2 n) is ambiguous and may not mean the tenfold sumset. Under 'open scoped Pointwise' two instances supply SMul N (Finset (F_2 n)): Finset.smulFinset (elementwise, A.image (10 • .)) and AddMonoid.toNatSMul coming from the pointwise Finset.addMonoid (the tenfold sumset). Finset.smulFinset is declared much later in Mathlib than AddMonoid.toNatSMul and equal-priority instances are tried most-recent-first, so the elementwise reading is the more likely resolution - and in characteristic 2 it gives A.image (fun _ => 0) = {0}.
- **Match:** suspect · **Confidence:** medium · **Lean difficulty:** 9/10
- **Flags:** instance ambiguity: pointwise-monoid nsmul (sumset) vs Finset.smulFinset (elementwise) for '10 • A' - potentially trivializing in characteristic 2; module docstring conflates 'pointwise scalar multiplication' with 'iterated addition of a set'; needs literature check: post-2024 PFR-era work may bear on O(log(1/alpha)) codimension for bounded sumsets
- **Fix:** Run 'set_option pp.all true in #check @Green50.green_50' (or #print the statement) as soon as a build is available. If 10 • A elaborates via Finset.smulFinset, rewrite as an explicit tenfold sumset and re-audit as cat 8. Do not attempt a proof before this is settled.

### `GreensOpenProblems/51.lean:green_51`

Determine exactly, as a function of (n, alpha), the largest coset dimension guaranteed inside A+A for every A subset F_2^n of density at least alpha.

- **Defect:** 'answer(sorry) = guaranteedMaxCosetDim' admits the tautological witness answer(guaranteedMaxCosetDim), closed by rfl; nothing in the elaborator forbids it. Moreover the exact-function-for-all-(n,alpha) reading is stronger than the source's asymptotic question, and the junk regimes (alpha > 1 gives sInf of the empty set = 0) would have to be reproduced by any honest closed form.
- **Match:** suspect · **Confidence:** high · **Lean difficulty:** 1/10
- **Flags:** answer-echo loophole (closable by rfl); exact-value-for-all-parameters vs asymptotic source question; sInf junk value 0 for alpha > 1 (no 0 < alpha <= 1 hypothesis)
- **Fix:** Restate as bracketing asymptotics (as the file's own solved variants do) or add a closed-form requirement; treat any rfl-style closure as illegitimate. Same answer-echo pattern already flagged in batch 28 for green_16/24/25/27.

### `Kourovka/19_25.lean:kourovka.«19.25»`

If two finite groups of the SAME ORDER have equal values of sum_{g} phi(order g) and one of them is simple, must the other be simple?

- **Defect:** The hypothesis '|G| = |H|' from the source ('two finite groups of the same order') is MISSING from the Lean statement. Only the equality of the totient sums is assumed.
- **Match:** no · **Confidence:** high · **Lean difficulty:** 4/10
- **Flags:** missing hypothesis |G| = |H| (major semantic mismatch: answer-encoding becomes decidable by an 8-element counterexample); closing the Lean statement as written would NOT resolve Kourovka 19.25
- **Fix:** Repair first: add the hypothesis Nat.card G = Nat.card H (and, for good measure, [Fintype H] nonemptiness is already implied). Only then triage the repaired statement (expected cat 8).

### `OptimizationConstants/1a.lean:c1a_eq`

Determine the exact value of Tao's autocorrelation constant 1a.

- **Defect:** With the broken t-range the constant collapses to 0, so 'the exact value' is answerable as answer := 0 with a short measure-theoretic argument - nothing to do with the real constant, whose value is a hard open problem.
- **Match:** no · **Confidence:** high · **Lean difficulty:** 5/10
- **Flags:** answer-encoding trivialized by the definitional defect; resolving it would falsely mark a research-open problem as solved
- **Fix:** Fix the definition first. If one wants the degenerate fact recorded, C1a = 0 is provable in maybe 100 lines: upper bound via the indicator test function, lower bound via nonnegativity of the sup-set.

### `OptimizationConstants/1a.lean:mem_Ico_c1a`

Exhibit a number in [C1a, 1.5029), i.e. improve the known upper bound for Tao's autocorrelation constant 1a.

- **Defect:** The definition of C1a is broken: the mass is integrated over [-1/4,1/4] but the autoconvolution supremum is taken over t in [1/2,1], which is disjoint from the support of f*f for f supported in [-1/4,1/4]. Consequently C1a = 0 and the interval is [0, 1.5029), so any answer such as 1.2748 works.
- **Match:** no · **Confidence:** high · **Lean difficulty:** 5/10
- **Flags:** wrong t-range in the definition of C1a (major semantic mismatch); the companion theorem c1a_lower_bound (1.2748 <= C1a, tagged research solved) is FALSE under the current definition
- **Fix:** Fix the definition: take the supremum over t in Icc (-1/2) (1/2) (or over all t) and, preferably, restrict f to functions supported in [-1/4,1/4]. Then re-triage (expected cat 8).

### `Paper/CardinalityLindelof.lean:HasGδSingletons.lindelof_card`

Asserts there exists a Lindelöf topological space in which every singleton is a G_delta set and whose cardinality exceeds the continuum.

- **Defect:** The formal statement imposes no separation axiom beyond what G_delta-singletons force (which is exactly T1). Arhangel'skii's Problem 1 is about Lindelöf Hausdorff/Tychonoff spaces - that is the famous ZFC-open question. For merely T1 spaces the answer has been known since Juhász: Arhangel'skii proved every Lindelöf space with points G_delta has cardinality below the first measurable cardinal, and Juhász constructed Lindelöf T1 (explicitly NON-Hausdorff) spaces of countable pseudocharacter of arbitrarily large cardinality below the first measurable. So the Lean statement is a ZFC theorem, not the open problem.
- **Match:** no · **Confidence:** medium · **Lean difficulty:** 8/10
- **Flags:** missing separation axiom (T2/T3) - statement appears provable in ZFC as written; major semantic mismatch: formal version is a known theorem, intended version is the open problem; needs literature check (Arhangel'skii 2013 PDF and Tall survey PDFs both returned HTTP 403); verifier:confirmed
- **Fix:** Add [T2Space X] (or [RegularSpace X]) to the existential witness to recover Arhangel'skii's Problem 1; alternatively keep the current statement, relabel it research solved, and formalize Juhász's construction (substantial but classical).

### `Wikipedia/DedekindNumber.lean:M_eq`

Intended: find a (efficiently computable) closed form for the Dedekind numbers M(n). As formalized: exhibit some function equal to M.

- **Defect:** `M = answer(sorry)` places no constraint on the answer term: `answer(M')` closes it via the already-proved `M_eq_M'`, and `answer(kisielewiczFormula)` closes it modulo the in-file `M_eq_kisielewiczFormula`. The docstring's real content ('no closed form allowing efficient computation is known') is a complexity-theoretic/informal claim that this encoding cannot express.
- **Match:** no · **Confidence:** high · **Lean difficulty:** 2/10
- **Flags:** answer(sorry) trivialization: any provably-equal function is a legal answer; prose/formal mismatch: 'no efficient closed form' is not expressed by the statement
- **Fix:** Either delete/downgrade this statement, or replace it with a precise complexity claim (e.g. counting antichains is #P-complete — Provan-Ball style) that can actually be formalized. As it stands `answer(M')` + `exact M_eq_M'` closes it in one line.

### `Wikipedia/HardyLittlewood.lean:first_hardy_littlewood_conjecture`

First Hardy–Littlewood (prime k-tuples) conjecture: the count of admissible prime constellations (p, p+m_1, ..., p+m_k) with p ≤ n is asymptotic to C_P ∫_2^n dt/(log t)^{k+1}.

- **Defect:** Two independent defects. (1) The docstring (and the actual conjecture) assert an ASYMPTOTIC EQUIVALENCE π_P(n) ~ C_P ∫_2^n dt/log^{k+1}t, but the formal statement only asserts `π_P =O[atTop] (fun n => C * ∫ ...)`. Big-O absorbs the constant C entirely, so the formal claim is merely an upper bound of the correct order of magnitude — which is a classical theorem (Selberg/Brun sieve, Halberstam–Richert), not an open conjecture. All the content of the conjecture (the lower bound, i.e. infinitude of prime tuples, and the exact constant) has been dropped. (2) `m` is not required to be injective.
- **Match:** no · **Confidence:** high · **Lean difficulty:** 10/10
- **Flags:** major semantic mismatch: O(·) instead of ~ turns an open conjecture into a known sieve upper bound; missing injectivity hypothesis on the shift tuple m makes the statement conjecturally false for repeated shifts; the file's Richards incompatibility theorem depends on this weakened definition and is likely unprovable as stated
- **Fix:** Rewrite: require `Function.Injective m` (or m strictly monotone), and replace `=O[atTop]` by an asymptotic-equivalence statement (`Filter.Tendsto (π_P n / (C * ∫ ...)) atTop (𝓝 1)` or `IsEquivalent`). Also re-examine `not_first_and_secondHardyLittlewoodConjecture` in the same file, whose proof of Richards' incompatibility needs the lower-bound half that the current definition lacks.

## Category 10 — unclassifiable  (4)

### `ErdosProblems/282.lean:erdos_282.variants.general`

Classify all pairs (x, A) for which the greedy unit-fraction process with denominators from A terminates on x.

- **Defect:** Three problems. (1) The target is an `answer(sorry) : Set (Q x Set N)`; under the repo's default `alwaysTrue` answer setting a non-Prop `answer(sorry)` elaborates to an opaque `sorryAx`, so the compiled statement is unprovable as it stands; under `postpone`/`withAuxiliary` it is trivially closable by supplying the tautological set `{p | greedyUnitFractionRem p.2 p.1 =^f[atTop] 0}` and `Iff.rfl`. (2) The hypothesis 'A infinite' from the problem text is dropped: A = empty gives sInf = 0 and 1/0 = 0, so the remainder is constant and the answer set is polluted by degenerate A. (3) x is unrestricted, so all x <= 0 vacuously 'terminate' (remainder goes negative and the `prev <= 0` branch clamps to 0 at step 1), whereas the source restricts to x in (0,1).
- **Match:** no · **Confidence:** high · **Lean difficulty:** 10/10
- **Flags:** answer-set encoding trivializable by the tautological set; missing hypothesis A.Infinite and x in Ioo 0 1; degenerate objects admitted (empty A, x <= 0)
- **Fix:** Rewrite as a family of concrete conjectures (A = odds, A = a mod d, A = squares) or add hypotheses `A.Infinite`, `x in Ioo 0 1` and a non-tautological answer format; do not attempt as stated.

### `ErdosProblems/422.lean:erdos_422`

For Hofstadter-style f with f(1)=f(2)=1, f(n)=f(n-f(n-1))+f(n-f(n-2)): does f miss infinitely many integers?

- **Defect:** f is declared with 'partial def', which in Lean 4 produces an opaque constant with NO equational lemmas: the logic cannot prove f 1 = 1 or any value of f. The formal statement is about an arbitrary unspecified function of type PNat -> PNat.
- **Match:** no · **Confidence:** high · **Lean difficulty:** 10/10
- **Flags:** partial def = opaque constant, no equation lemmas: statement independent of axioms; PNat truncated subtraction in the recursion body; well-definedness of the intended f is itself open
- **Fix:** Redefine f before any proof attempt: e.g. an Option-valued/fuel-based total function or an inductively defined graph relation capturing the (possibly partial) recurrence; note PNat subtraction also truncates at 1, which must be handled explicitly. Flag upstream.

### `ErdosProblems/422.lean:erdos_422.variants.eventually_const`

Does the Hofstadter-style f become eventually constant?

- **Defect:** Same partial-def opacity defect: EventuallyConst f atTop for an opaque constant f is independent of the axioms.
- **Match:** no · **Confidence:** high · **Lean difficulty:** 10/10
- **Flags:** partial def = opaque constant, no equation lemmas
- **Fix:** Same fix as erdos_422: redefine f, then re-state.

### `ErdosProblems/422.lean:erdos_422.variants.surjective`

Is the Hofstadter-style f surjective?

- **Defect:** Same defect: f is a partial-def opaque constant with no defining equations; Function.Surjective f is independent of the axioms.
- **Match:** no · **Confidence:** high · **Lean difficulty:** 10/10
- **Flags:** partial def = opaque constant, no equation lemmas
- **Fix:** Same fix as erdos_422: redefine f, then re-state.

## Faithfulness concerns in otherwise open problems  (93)

Statements flagged `suspect` or `no` on match, but not otherwise defective.

| Declaration | Cat | Match | Note |
|---|---|---|---|
| `Arxiv/1609.08688/sIncreasingrTuples.lean:maximalLength_le_strong` | 8 | suspect | Formalized as the exact bound F(n) <= sqrt(n)^3 for every n. If the paper's Conjecture 1.8 is the asymptotic form F(n) = n^{3/2+o(1)}, the Lean statem |
| `ErdosProblems/1054.lean:erdos_1054.parts.iii` | 8 | suspect | The statement wraps the limsup in 'exists A, A.HasDensity 1 and ...' but A never occurs in the limsup (copy-paste from parts.ii). Since Set.univ has d |
| `ErdosProblems/1055.lean:erdos_1055` | 9 | suspect | IsOfClass has a vacuity bug at r = 2: the 'equality for at least one prime factor' clause unfolds to 'forall m <= 1, IsOfClass m q -> m = 1', which is |
| `ErdosProblems/1074.lean:erdos_1074.variants.EHSNumbers_one_half` | 8 | suspect | Hardy-Subbarao only wrote they 'expect [the limit] to be around 0.5, if it exists'; formalizing this as density exactly 1/2 is an over-precise renderi |
| `ErdosProblems/1093.lean:erdos_1093.parts.i` | 8 | suspect | Off-by-one risk in the smoothness threshold. `deficiency n k` uses Mathlib's `Nat.smoothNumbers k`, which is {m ≠ 0 \| ∀ p ∈ m.primeFactors, p < k}, i |
| `ErdosProblems/1093.lean:erdos_1093.parts.ii` | 8 | suspect | Inherits exactly the same `smoothNumbers k` (p < k) vs 'p ≤ k' off-by-one as parts.i. Otherwise faithful: pair encoding is (k, n) = (x.1, x.2), the k= |
| `ErdosProblems/1095.lean:erdos_1095.variants.log_equivalent` | 8 | no | PROSE/FORMAL MISMATCH. The docstring states log g(k) \asymp k/log k (same ORDER, i.e. Θ / IsTheta), but the Lean uses `~[atTop]`, which is `Asymptotic |
| `ErdosProblems/1167.lean:binary_colors` | 8 | suspect | Inherits the cardinal-vs-ordinal '+1' problem from `erdos_1167`: for infinite kappa_alpha the '+1' disappears entirely, so the hypothesis is weaker th |
| `ErdosProblems/1167.lean:erdos_1167` | 8 | suspect | Two concerns. (1) The '+1' is formalized as CARDINAL addition (the docstring says so explicitly), which makes it a no-op whenever kappa_alpha is infin |
| `ErdosProblems/1167.lean:infinite_targets` | 8 | suspect | This variant drops '+1' entirely (correctly, under the cardinal reading), so it is a 'pure' stepping-down assertion. But that is exactly the reading t |
| `ErdosProblems/1167.lean:r_eq_two` | 8 | suspect | Same cardinal-vs-ordinal '+1' issue as `erdos_1167`, and here it bites hardest: for infinite kappa the hypothesis reduces to 2^lambda -> (kappa)^3 whi |
| `ErdosProblems/1175.lean:erdos_1175` | 8 | suspect | The hypothesis is `G.chromaticCardinal = mu` (exact equality) rather than the usual `≥ mu`; the file itself notes this and provides the `threshold_for |
| `ErdosProblems/1176.lean:erdos_1176` | 1 | suspect | The statement itself is a faithful rendering (edge colour type of size aleph_1, vertex colour type countable, a vertex colour class containing edges o |
| `ErdosProblems/119.lean:erdos_119.parts.iii` | 1 | suspect | Quantifier order is weakened: the file states ∀ z, ∃ c > 0, ∀ᶠ n, ... whereas the natural reading of the question (and of Beck's theorem, which the fi |
| `ErdosProblems/1199.lean:erdos_1199` | 9 | suspect | `A + A` (Set.Pointwise) is {a+b : a,b ∈ A}, which INCLUDES the doubles 2a. Some statements of Owings' problem use {a+b : a ≠ b}. Requiring the doubles |
| `ErdosProblems/1203.lean:erdos_1203` | 8 | suspect | The range of the max is not specified in the source snippet and the file takes ⨆ over ALL k : ℕ. This drags in junk terms: k = 0 and k = 1 give Real.l |
| `ErdosProblems/137.lean:erdos_137.variants.multiple_powerful_factors` | 8 | suspect | Off-by-one: the docstring says N = m(m+1)⋯(m+n) but the Lean product ∏ x ∈ Finset.Ioc m (m+n) equals (m+1)⋯(m+n) (n factors, starting at m+1). Since t |
| `ErdosProblems/160.lean:erdos_160.better_lower` | 8 | suspect | The second conjunct is malformed: `forall c > 0, (exp(c log n^{1/12}) =O h -> forall c > 0, exp(c log n^{1/12}) =o lower_bound)` shadows the binder c, |
| `ErdosProblems/168.lean:erdos_168.parts.ii` | 9 | suspect | Uses `Filter.atTop.limsup (fun N => F N / N)` rather than the limit. This is semantically harmless because the limit is known to exist (so limsup = li |
| `ErdosProblems/172.lean:erdos_172` | 9 | suspect | The inner quantifier ranges over every nonempty S : Finset A, including singletons, so the statement also forces every element of A itself to have col |
| `ErdosProblems/189.lean:erdos_189.variants.parallelogram` | 8 | suspect | The theorem commits to one direction (`¬ Erdos189For ...`) of a question the docstring itself calls open, instead of using the repo's `answer(sorry) < |
| `ErdosProblems/208.lean:erdos_208.variants.log_bound` | 9 | suspect | The file's own docstring records that Erdős proposed this bound but was 'very doubtful' about it. It is nevertheless asserted here as a bare theorem ( |
| `ErdosProblems/218.lean:erdos_218.variants.ge` | 9 | suspect | Same ≤ vs < issue as variants.le; the two together force the equality set to have density 0. |
| `ErdosProblems/218.lean:erdos_218.variants.le` | 9 | suspect | The docstring and the source phrase this with a strict comparison (d_n < d_{n+1}); the Lean statement uses ≤. Because the same file also asserts the ≥ |
| `ErdosProblems/251.lean:erdos_251` | 9 | suspect | Index shift: Nat.nth Nat.Prime n is 0-indexed (nth 0 = 2) but the exponent is also n, so the Lean value is ∑_{n≥0} p_{n+1}/2^n = 2·(intended ∑_{n≥1} p |
| `ErdosProblems/257.lean:erdos_257` | 8 | suspect | If 0 ∈ A the term is 1/(2^0-1) = 1/0 = 0 (Lean junk value) rather than undefined; the intended A ⊆ positive integers. Harmless: A\{0} is still infinit |
| `ErdosProblems/267.lean:erdos_267.variants.generalisation_ratio_limit_to_infinity` | 8 | suspect | Two cosmetic mismatches: (a) the docstring says n_k/k → ∞ but the formal condition is n(k+1)/(k+1) → ∞ — equivalent, since it is the same sequence rei |
| `ErdosProblems/269.lean:erdos_269.variants.irrational` | 8 | suspect | Same off-by-one as erdos_269.variants.rational (the n = 0 term contributes 1/lcm(∅) = 1). Note also that this and the 'rational' variant are not exact |
| `ErdosProblems/269.lean:erdos_269.variants.rational` | 8 | suspect | `series P` = ∑_{n≥0} 1/partialLcm P n and partialLcm P 0 = Finset.lcm ∅ = 1, so the Lean value is 1 + (intended ∑_{n≥1} 1/[a_1..a_n]). Adding 1 preser |
| `ErdosProblems/272.lean:erdos_272` | 1 | suspect | The formal statement only asks for an asymptotic equivalence maxArithInterCard N ~ f(N), which is strictly weaker than 'what is the largest t?'. That  |
| `ErdosProblems/274.lean:erdos_274` | 8 | suspect | The conclusion is equality of subgroup CARDINALITIES (#(P.parts i)), whereas Herzog–Schönheim is about equality of INDICES. For finite G the two coinc |
| `ErdosProblems/282.lean:erdos_282` | 9 | suspect | `greedyUnitFractionRem` re-selects the least element of A at every step and never excludes already-used denominators, so it does NOT in general produc |
| `ErdosProblems/282.lean:erdos_282.variants.graham` | 8 | suspect | Graham's arithmetic condition is transcribed correctly (Nat divisions x.den / gcd(x.den, gcd(a,d)) and d / gcd(a,d) are exact, so no truncation). Same |
| `ErdosProblems/282.lean:erdos_282.variants.sq` | 8 | suspect | The membership range for Graham's theorem is transcribed correctly. But the repeated-denominator defect is severe here: for x = 1/2 (which lies in [0, |
| `ErdosProblems/288.lean:erdos_288.variants.exists_k_gt_2` | 8 | suspect | The docstring reads 'Is it true for any k > 2 that only finitely many ...', which in mathematical English normally means 'for every k > 2' - but the L |
| `ErdosProblems/289.lean:erdos_289` | 8 | suspect | Faithful except for a junk-value hole: the intervals live in N and (0 : Q)^-1 = 0, so an interval [0,1] has 'length 2' but contributes exactly 1. This |
| `ErdosProblems/295.lean:erdos_295` | 8 | suspect | Off-by-one: `k N := Nat.find (exists_k N)` searches over k such that there is a representation indexed by `Fin k.succ`, so `k N` equals (true minimal  |
| `ErdosProblems/312.lean:erdos_312` | 8 | suspect | Two encoding issues. (1) Elements are drawn from N, and (0 : R)^-1 = 0, so the multiset may be padded with arbitrarily many zeros without changing any |
| `ErdosProblems/319.lean:erdos_319.variants.isTheta` | 5 | suspect | Θ only pins the answer up to constants, so `answer := fun N => (N : ℝ)` is the correct and complete answer — much weaker than the actual question (the |
| `ErdosProblems/321.lean:erdos_321` | 1 | suspect | The formal statement demands an exact closed form R N = answer for EVERY N. A solution recorded on erdosproblems.com for this kind of question is almo |
| `ErdosProblems/321.lean:erdos_321.variants.isTheta` | 1 | suspect | answer() up to constants; the Bleicher-Erdos bounds in the same file differ by a log_r N factor, so a Theta statement is exactly what a solution would |
| `ErdosProblems/324.lean:erdos_324.variants.quintic` | 9 | suspect | Stated as a positive theorem rather than an answer()-encoded question, so a refutation could not be recorded without rewriting the declaration. Mathem |
| `ErdosProblems/326.lean:erdos_326` | 8 | suspect | Two issues. (1) B is only required to satisfy `(Set.range b).IsAddBasis` — a basis of SOME order — whereas the source (and the Cassels context, where  |
| `ErdosProblems/329.lean:erdos_329.variants.converse_implication` | 8 | suspect | Degenerate encoding, as the docstring itself admits: with the consequent known false, the implication is logically equivalent to `sSup ≠ 1`. So the de |
| `ErdosProblems/330.lean:erdos_330_statement` | 1 | suspect | Two spec risks against the prose. (1) `Set.HasPosDensity` (FormalConjecturesForMathlib/Data/Set/Density.lean:100) requires the natural density to EXIS |
| `ErdosProblems/348.lean:erdos_348` | 8 | suspect | Two issues. (1) Deletion is modelled by `Function.updateFinset a s 0` (zeroing m indices) and completeness by `IsAddComplete (Set.range …)`, i.e. subs |
| `ErdosProblems/349.lean:erdos_349` | 9 | suspect | Mathematically faithful — IsGoodPair uses IsAddComplete on `Set.range (fun n ↦ ⌊t·αⁿ⌋)`, i.e. subset sums of DISTINCT values, matching 'sum of distinc |
| `ErdosProblems/358.lean:erdos_358.variants.prime_set` | 9 | suspect | Off-by-one: `intervalRepresentations` requires 0 < u, but `Nat.nth Nat.Prime` is 0-indexed (nth Prime 0 = 2), so the prime 2 is never used — the state |
| `ErdosProblems/358.lean:erdos_358.variants.prime_set_density_representation` | 8 | suspect | Uses `intervalRepresentations` (which allows u = v, i.e. a single prime) rather than `intervalRepresentationsNonTrivial`; the intended conjecture is n |
| `ErdosProblems/394.lean:erdos_394.variants.factorial_gap_conjecture` | 8 | suspect | Docstring (and site prose) says 'for all 1 <= k < n' but the formal statement quantifies 2 <= k < n. k=1 would involve the junk value t_0 (sInf of emp |
| `ErdosProblems/409.lean:erdos_409.variants.sigma` | 8 | suspect | As with parts.i, answer := sInf S is available since n is in scope; but here nonemptiness of S (termination of the sigma-1 iteration) is itself open,  |
| `ErdosProblems/41.lean:erdos_41` | 8 | suspect | NtupleCondition quantifies over 3-element Finsets, so only sums of three DISTINCT elements must be distinct; the standard B_3 condition also forbids c |
| `ErdosProblems/416.lean:erdos_416.parts.ii` | 2 | no | answer() encoding trivializes the question: nothing constrains f to be a 'formula', so f := V itself is a legal witness. |
| `ErdosProblems/422.lean:erdos_422.variants.growth_rate` | 2 | no | Double defect: (a) f is opaque (partial def), (b) the answer() encoding admits the self-witness g := fun n => (f n : R), which closes the goal by isBi |
| `GreensOpenProblems/14.lean:green_14_polynomial` | 1 | suspect | The as-formalized question is NOT open: W(k,r) >= W(3,r) for all k >= 4 (a colouring with no red 3-AP a fortiori has no red 4-AP, so the guarantee set |
| `GreensOpenProblems/16.lean:zhao_question` | 8 | suspect | Two issues: (1) an open yes/no question is formalized as a committed NO (not-exists h -> 0 with g(N) >= N^(1/3-h(N)) eventually) instead of the repo's |
| `GreensOpenProblems/22.lean:green_22` | 8 | suspect | Formalizing 'find reasonable bounds' as 'any o(exp(exp(r^50)))' is fragile: published round-exponent bounds almost always carry slack, so an o()-impro |
| `GreensOpenProblems/35.lean:green_35.upper` | 8 | suspect | Baseline constant likely mis-transcribed: the MV10 record is usually quoted as 1.50992 in the doubled normalization, i.e. c(inf) <= 0.75496 (~0.7549/0 |
| `GreensOpenProblems/37.lean:green_37_bigO` | 2 | no | Any upper bound qualifies, so the statement says nothing about the true growth. Two closures: (a) tautological, answer := fun N => (m N k : R) via Asy |
| `GreensOpenProblems/37.lean:green_37_littleO` | 2 | no | answer := fun N => ((m N k : R) + 1) * (N + 1) is little-o-valid for ANY nonnegative function with no knowledge of m (\|\|f N\|\| <= c \|\|ans N\|\| o |
| `GreensOpenProblems/39.lean:green_39.variant_theta` | 8 | suspect | Documented reinterpretation: Green's literal 'sqrt p replaced by p^theta' (with ~C p^theta translates) is trivially false by pigeonhole for theta < 1/ |
| `GreensOpenProblems/51.lean:green_51.one_half` | 8 | suspect | The source asks for a SUBSPACE of codimension O_C(1); via guaranteedMaxCosetDim the formalization only guarantees a coset (affine subspace), a weaker  |
| `GreensOpenProblems/54.lean:green_54` | 9 | suspect | The docstring states the finite-dimensional problem (K in R^n, gamma_n, constants uniform in n) while the Lean statement lives on R^N with the infinit |
| `GreensOpenProblems/72.lean:NoKInLine` | 9 | suspect | This is a repo-invented generalisation, not Green's Problem 72 verbatim, and it is stated in the direction that experts believe is FALSE at k = 3: the |
| `GreensOpenProblems/72.lean:green_72` | 9 | suspect | The formal statement 'AllowedSetSize 3 N = 2N for all N >= 3' is a correct rendering of the classical no-three-in-line CONJECTURE, but it is widely be |
| `GreensOpenProblems/77.lean:green_77` | 9 | suspect | The asymptotic encoding (∃ o → 0 with alpha ≪ n^{-2+o(n)}) is a correct reading of 'n^{-2+o(1)}'. The suspicion is in the imported definition Erdos507 |
| `LittProblems/1.lean:lam_litt.variants.omega_integrality_implies_algebraicity` | 9 | suspect | IsSolutionOfAlgebraicODE clears denominators as f^(n) * q(pt) = p(pt) without requiring q(pt) != 0, so ANY differentially algebraic f qualifies (take  |
| `Mathoverflow/507128.lean:exists_isFractionRing_self_ideal_ne_top_invertible` | 8 | suspect | The declaration ASSERTS the existence, with no answer(...) wrapper, even though it is filed as research open and the underlying MO question is (as far |
| `Millenium/Poincare.lean:poincare_conjecture.variants.smooth_dimension_four` | 9 | suspect | SmoothConjectureFor omits [T2Space M], unlike ConjectureFor which has it. Non-Hausdorff smooth 4-manifolds (e.g. R^4 with a doubled origin, a legitima |
| `Other/BeaverMathOlympiad.lean:beaver_math_olympiad_problem_8` | 0 | no | The Lean statement is TRUE and already proved in-repo, but only because of N-subtraction truncation: at index 462 the orbit is (675, 1347) with a - b/ |
| `Paper/ClaudesCycles.lean:cube_hamiltonian_arc_decomposition_even` | 8 | suspect | The intended question is per-m ('for which even m > 2 does a decomposition exist?'), but the formalization collapses it into a single answer(sorry) if |
| `Paper/FusibleNumber.lean:conj_7_1` | 8 | suspect | Faithful up to the four reindexings documented in the docstring (verified: the (n+1)-st successor of x is x + (2 - 2^(-n))m, and inverting q = (s^(n+1 |
| `Paper/HartshorneConjecture.lean:harthshorne_conjecture` | 9 | suspect | The mathematical content is right, but the statement uses the categorical coproduct in S.VectorBundles, whose HasFiniteCoproducts instance is supplied |
| `Paper/StrongSensitivityConjecture.lean:strong_sensitivity_conjecture` | 9 | suspect | The literature conjecture is usually bs(f) = O(s(f)^2); this file asserts the constant-free bs(f) ≤ s(f)^2, which is strictly stronger. Since Ambainis |
| `Paper/WeakTiling.lean:problem_4_3` | 8 | suspect | The paper says 'convex linear combination of proper tilings'; the Lean version fixes a *countable* combination indexed by ℕ with coefficients in ℝ≥0 s |
| `Paper/WeaklyFirstCountable.lean:existsWeaklyFirstCountableCompactBig` | 8 | suspect | The answer() encoding presumes the question has a ZFC-decidable truth value. The source explicitly asks for an example 'in ZFC', which is exactly the  |
| `Wikipedia/AmicableNumbers.lean:infinitely_many_amicable` | 9 | suspect | Two issues. (a) This is a verbatim `type_of%` duplicate of FormalConjectures/ErdosProblems/830.lean:erdos_830.parts.i — the same open problem is state |
| `Wikipedia/ArtinPrimitiveRootsConjecture.lean:artin_primitive_roots.variants.part_ii_power_squarefreePart_modeq_one` | 9 | suspect | The module docstring and the theorem docstring describe this case as 'a = b^m, m a maximal power' with no parity restriction, but the Lean statement a |
| `Wikipedia/BalancedPrimes.lean:balanced_primes_order` | 9 | suspect | The source poses the question per order k ('are there infinitely many balanced primes of order k?'). The formalisation bundles all k into a single ∀ u |
| `Wikipedia/BetrothedNumbers.lean:same_parity_betrothed` | 9 | no | `m ≠ n` is missing. Taking m = n, IsBetrothed m m says σ(m) = 2m + 1, i.e. m is a QUASIPERFECT number, and Even m ↔ Even m is trivially true. So the f |
| `Wikipedia/BusyBeaver.lean:BB_6` | 9 | no | The state/symbol roles are SWAPPED. In `FormalConjecturesForMathlib/Computability/TuringMachine/BusyBeavers.lean`, `Machine Γ Λ := Λ → Γ → Option (Opt |
| `Wikipedia/DedekindNumber.lean:Dedekind_10` | 9 | suspect | Same answer-encoding weakness as `M_eq`: `M 10 = answer(M' 10)` or `answer(kisielewiczFormula 10)` are formally legal answers that convey nothing. The |
| `Wikipedia/EulerBrick.lean:cuboidThree` | 8 | suspect | The Lean coprimality hypothesis is `gcd a (gcd b c) = 1`, i.e. SETWISE coprimality, whereas the docstring says 'pairwise different coprime integers'.  |
| `Wikipedia/Koethe.lean:KotherConjecture.variants.matrixOver_KotherRadical` | 9 | suspect | The binder {I : TwoSidedIdeal R} (hI : IsNil I) is entirely unused: I does not occur in the conclusion matrix n (Nil* R) = Nil* (Matrix n n R). Becaus |
| `Wikipedia/Mahler32.lean:mahler_conjecture` | 9 | suspect | Two deviations, one harmless and one a strengthening. (a) IsZNumber quantifies over n > 0 rather than n >= 0; this is exactly equivalent to Mahler's d |
| `Wikipedia/MeanValueProblem.lean:mean_value_problem` | 8 | suspect | Two spec defects, both minor. (1) The parameter `K : R` is declared but never used anywhere in the statement - dead binder inherited from the K=4 / K= |
| `Wikipedia/MoserWorm.lean:mosers_worm_problem` | 9 | suspect | WormCovers requires only `MeasurableSet X` — no closedness, boundedness or connectedness. The classical problem asks for a 'shape' (in practice a clos |
| `Wikipedia/NormalityOfPi.lean:pi_normal_base_ten` | 9 | suspect | `IsNormalInBase` in FormalConjecturesForMathlib/NumberTheory/NormalNumber.lean (line 62) only requires each single digit d < b to have limiting freque |
| `Wikipedia/PebblingNumberConjecture.lean:pebbling_number_conjecture` | 9 | suspect | Both factors are forced onto the SAME vertex type V (G H : SimpleGraph V), whereas Graham's conjecture concerns G on V and H on W for arbitrary vertex |
| `Wikipedia/PierceBirkhoff.lean:pierce_birkhoff_conjecture` | 9 | suspect | `IsSemiAlgebraic` is defined as a finite UNION of zero sets {p = 0} together with a finite union of open sets {q > 0} — there are no intersections and |
| `Wikipedia/RamanujanTau.lean:lehmer_ramanujan_tau` | 9 | suspect | Δ is defined with an infinite product ∏' (n : ℕ+), (1 - X^n)^24 whose convergence is the in-file lemma `multipliable`, which is still sorry. If that l |
| `WrittenOnTheWallII/GraphConjecture100.lean:conjecture100` | 0 | suspect | The module docstring says 'length(Gbar)' is interpreted as the DIAMETER of the complement (Gᶜ.ediam) and adds hGc : Gᶜ.Connected to keep that finite,  |
| `WrittenOnTheWallII/GraphConjecture291.lean:conjecture291` | 8 | suspect | The file's own docstring concedes that its k ('first step at which a zero appears') is 'strictly weaker than n - residue(G)'. Since k occurs on the RI |
