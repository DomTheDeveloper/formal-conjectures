# Statement defects

68 declarations whose formal statement does not faithfully capture the intended problem,
or whose meaning could not be pinned down. These are the repository's integrity risks: a prover can
produce a green build on many of them without doing any of the intended mathematics.

The dominant pattern is the **`answer()` echo** — a goal `answer(sorry) = e` or `answer(sorry) ↔ P`
where `e`/`P` is already in scope, so the answer term can be instantiated to the thing being asked
about and closed by `rfl`. Fixing these is upstream-reportable work independent of solving anything.

## Category 3 — false as stated  (1)

### `Books/UniformDistributionOfSequences/Equidistribution.lean:isEquidistributedModuloOne_transcendental_three_halves_pow`

Claims that for EVERY transcendental x, the sequence x*(3/2)^n is equidistributed modulo 1.

- **Defect:** The universally-quantified statement over transcendental x does not correspond to any conjecture in the cited book and is false by known results.
- **Match:** no · **Confidence:** medium · **Lean difficulty:** 9/10
- **Flags:** false-as-stated: universal quantifier over transcendental x contradicts Peres-Schlag/Katznelson-type constructions; no matching conjecture in cited source; needs literature check only for the precise citation of the (3/2)^n badly-approximable construction (Akhunzhanov-Moshchevitin)
- **Fix:** Flag for correction upstream: weaken to 'for almost every x' (Koksma/Weyl metric theorem, provable but nontrivial) or delete. Formally refuting the current statement in Lean would require a Peres-Schlag-type Cantor construction — large effort, so the practical action is to fix the statement, not to prove its negation.

## Category 4 — provable without the mathematics  (40)

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

Decide whether every finite abelian group G contains a Sidon subset of size at least 0.01 sqrt(|G|). Intended open; but under the repo's IsSidon the statement is provably FALSE.

- **Defect:** The repo definition IsSidon (Basic.lean:57) quantifies over ALL quadruples including i1=i2, j1=j2: taking i1=i2=x, j1=j2=y with x != y in F_2^n gives x+x = 0 = y+y but the conclusion forces x=y. Hence every subset of F_2^n with two distinct elements fails IsSidon, so all Sidon sets there have card <= 1. G = F_2^14 then violates 0.01*sqrt(16384) = 1.28 <= card. The intended question uses the group-Sidon convention that discounts 2-torsion coincidences (Babai-Sos style), under which F_2^n has Sidon sets of size ~sqrt(|G|) (graph of x^3 over F_{2^m}) and the question is genuinely open.
- **Match:** no · **Confidence:** high · **Lean difficulty:** 4/10
- **Flags:** definition admits degenerate collapse in 2-torsion groups; answer(sorry) iff encoding decidable via defect, not via the intended mathematics; intended conjecture remains open
- **Fix:** Report defect upstream: IsSidon needs the distinct-pair/group convention for 2-torsion groups. Meanwhile the formal theorem closes with answer := False, witness G := (Fin 14 -> ZMod 2), a two-element Sidon-violation lemma, and 0.01*Real.sqrt(2^14) = 1.28 > 1.

### `GreensOpenProblems/31.lean:green_31.variants.sidon_01n`

Decide whether there are Sidon subsets of {0,1}^n of size N^{0.51} (N = 2^n). Intended open; but under the repo's IsSidon in F_2^n every Sidon set has at most 1 element, so the formal statement is provably FALSE.

- **Defect:** Same char-2 collapse as the abelian variant: in F_2^n, any two distinct x,y give x+x = 0 = y+y violating IsSidon, so card <= 1 < (2^n)^{0.51} for n >= 1. The binary-Sidon literature (CLZ01) defines B_2 sets via sums of DISTINCT elements, under which sets of size ~2^{n/2} exist and the N^{0.51}-vs-N^{0.5753} gap is the real open problem.
- **Match:** no · **Confidence:** high · **Lean difficulty:** 3/10
- **Flags:** definition admits degenerate collapse in char 2; answer-encoding trivialized (False); companion solved-variant sidon_01n_clz01 also vacuous under this definition; intended conjecture remains open
- **Fix:** Report defect upstream: use a distinct-pair Sidon/B_2 definition for F_2^n. Meanwhile the theorem closes with answer := False plus the two-element violation lemma and 1 < 2^{0.51 n}.

### `GreensOpenProblems/37.lean:green_37`

Determine exactly the minimum size m(N,k) of a set of naturals containing a k-term AP of common difference d for every d = 1..N. Formalized as IsLeast of the cardinality set at answer(sorry).

- **Defect:** The answer-encoding is tautologically closable: answer := Green37.m N k (the sInf of the very same set) satisfies IsLeast via Nat.sInf_mem once the set is shown nonempty (witness A = Finset.range ((k-1)*N+1), which contains the AP 0, d, ..., (k-1)d for every d <= N) plus Nat.sInf_le. Nothing forces a closed form, so the formal statement does not capture 'determine m(N,k)' - whose asymptotics are unknown even for k = 3 (k = 2 is the classical restricted difference basis problem, Theta(sqrt N)).
- **Match:** no · **Confidence:** high · **Lean difficulty:** 4/10
- **Flags:** tautological answer loophole (answer := m N k); intended problem is an open estimation question
- **Fix:** Report the spec defect upstream (answer should be constrained to a closed form, or the statement replaced by two-sided explicit bounds). If closing as-is: prove nonemptiness with range((k-1)N+1) and apply Nat.sInf_mem / Nat.sInf_le.

### `GreensOpenProblems/37.lean:green_37_asymptotic`

Find a function f with m(N,k) = f(N) for all large N. Trivialized: answer := fun N => (m N k : R) closes it by rfl.

- **Defect:** answer(sorry) : N -> R elaborates with k in scope, so fun N => (m N k : R) is admissible and the statement becomes eventually (m N k : R) = (m N k : R), provable by Filter.Eventually.of_forall (fun _ => rfl). Additionally, even a good-faith reading (eventual EXACT equality with a formula) over-demands relative to Green's 'estimate m(N,k)'.
- **Match:** no · **Confidence:** high · **Lean difficulty:** 1/10
- **Flags:** tautological answer loophole; eventual exact equality is a mis-specification of 'determine asymptotic behavior'
- **Fix:** Report spec defect; replace with a genuine two-sided asymptotic statement (e.g. explicit upper/lower bound pairs, or IsTheta against a concrete elementary function).

### `GreensOpenProblems/37.lean:green_37_theta`

Find the Theta-class of m(N,k). Trivialized: answer := the function itself, closed by isTheta_refl.

- **Defect:** answer := fun N => (m N k : R) gives f =Theta f, provable by Asymptotics.isTheta_refl. No constraint to a closed-form comparison function.
- **Match:** no · **Confidence:** high · **Lean difficulty:** 1/10
- **Flags:** tautological answer loophole
- **Fix:** Report spec defect; a meaningful version must quantify answer over a restricted grammar of functions or state concrete bounds.

### `GreensOpenProblems/4.lean:green_4`

Exhibit a largest product-free subset of the alternating group A_n (for the given n). Formalized as MaximalFor ProdFree ncard at an answer(sorry) family.

- **Defect:** Choice loophole: a maximizer exists for every n by finiteness (Set (alternatingGroup (Fin n)) is a finite type, ProdFree holds for the empty set, ncard is bounded), so answer := fun n => Classical.choose (exists_maximalFor ...) closes the theorem without any structural description - the formal statement never demands an explicit set. The intended problem (describe the extremal sets) is solved for large n in arXiv:2205.15191 (the file's own large_green_4 records its Theorem 1.1 as research solved) but the all-n version with explicit description is not captured by this encoding either way.
- **Match:** no · **Confidence:** high · **Lean difficulty:** 3/10
- **Flags:** nonconstructive tautological answer loophole; intended large-n case already solved in literature (arXiv:2205.15191)
- **Fix:** Report spec defect upstream (answer should be an explicit family, e.g. the extremalFamily construction, with a proof of optimality). To close as-is: prove exists S, MaximalFor ProdFree ncard S by Finite.exists_max over the subtype {S // ProdFree S}, then choose.

### `GreensOpenProblems/40.lean:green_40.variants.all_n`

Intended: does f_all(r) = limsup_n (minimal linear covering density) tend to infinity with r? As formalized it instead asks whether f_all r is eventually EXACTLY infinity.

- **Defect:** Target filter bug: in ENNReal (an OrderTop) Filter.atTop = pure top, so 'Tendsto f_all atTop atTop' says 'for all large r, limsup_n minDensity n r = top' - not divergence. The file's other two variants correctly use nhds top, showing this is a slip.
- **Match:** no · **Confidence:** high · **Lean difficulty:** 7/10
- **Flags:** filter-target defect: atTop instead of nhds top on ENNReal codomain; resolvable with unintended answer False; intended problem stays open
- **Fix:** Fix the statement to 'Tendsto f_all atTop (nhds top)'. Alternatively the current statement can be legitimately closed with answer(False) by formalizing bounded-density covering constructions (shortened Hamming + direct sums) - moderate Lean work.

### `GreensOpenProblems/41.lean:green_41`

Quantitative pyjama problem: exhibit a bound ans(eps) on the number of rotations of the eps-pyjama set needed to cover the plane that is strictly below the Kravitz-Leng triple-exponential exp(exp(exp(eps^-C))).

- **Defect:** C-inflation loophole: the prover chooses C. Taking C := C0+1 (C0 the Kravitz-Leng exponent) and ans := exp(exp(exp(eps^-C0))) satisfies both conjuncts for eps<1, since eps^-C0 < eps^-C. So the statement follows from the existing KrLe bound and does not force any improvement.
- **Match:** no · **Confidence:** high · **Lean difficulty:** 10/10
- **Flags:** answer-encoding weaker than intended (quantifier over C inflatable); no Lean proof of any quantitative pyjama bound exists anywhere
- **Fix:** Tighten the spec (e.g. require ans = o of the KrLe bound for the SAME C, or demand a fixed iterated-exp level lower). Closing the current formal statement still requires formalizing quantitative pyjama - research-scale.

### `GreensOpenProblems/41.lean:green_41.variants.exists_better_bound`

Existential version: is there some bound on minCopies(eps) strictly below the Kravitz-Leng triple-exponential? As encoded, taking ans := minCopies eps makes this equivalent to the KrLe bound itself with a larger C.

- **Defect:** With ans := minCopies eps the two conjuncts reduce to minCopies eps < exp^3(eps^-C), which holds by KrLe for any C > C0. So the RHS is True by known literature and carries no 'better bound' content.
- **Match:** no · **Confidence:** high · **Lean difficulty:** 10/10
- **Flags:** answer-encoding trivializes 'better bound'
- **Fix:** Replace by a spec that quantifies the improvement (e.g. double-exponential or polynomial bound). Formal closure = answer(True) + formalizing KrLe (research-scale).

### `GreensOpenProblems/51.lean:green_51`

Determine exactly, as a function of (n, alpha), the largest coset dimension guaranteed inside A+A for every A subset F_2^n of density >= alpha.

- **Defect:** Exact-function-for-all-(n,alpha) reading is stronger than the source's asymptotic question, and the equation 'answer(sorry) = guaranteedMaxCosetDim' admits the tautological witness answer(guaranteedMaxCosetDim) closed by rfl; nothing in the elaborator forbids it.
- **Match:** suspect · **Confidence:** high · **Lean difficulty:** 1/10
- **Flags:** answer-echo loophole (rfl); exact-value-for-all-parameters vs asymptotic source question
- **Fix:** Restate as bracketing asymptotics (as the file's solved variants do) or add a closed-form requirement; treat any rfl-style closure as illegitimate.

## Category 10 — unclassifiable  (3)

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

## Faithfulness concerns in otherwise open problems  (24)

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
| `ErdosProblems/394.lean:erdos_394.variants.factorial_gap_conjecture` | 8 | suspect | Docstring (and site prose) says 'for all 1 <= k < n' but the formal statement quantifies 2 <= k < n. k=1 would involve the junk value t_0 (sInf of emp |
| `ErdosProblems/409.lean:erdos_409.variants.sigma` | 8 | suspect | As with parts.i, answer := sInf S is available since n is in scope; but here nonemptiness of S (termination of the sigma-1 iteration) is itself open,  |
| `ErdosProblems/41.lean:erdos_41` | 8 | suspect | NtupleCondition quantifies over 3-element Finsets, so only sums of three DISTINCT elements must be distinct; the standard B_3 condition also forbids c |
| `ErdosProblems/416.lean:erdos_416.parts.ii` | 2 | no | answer() encoding trivializes the question: nothing constrains f to be a 'formula', so f := V itself is a legal witness. |
| `ErdosProblems/422.lean:erdos_422.variants.growth_rate` | 2 | no | Double defect: (a) f is opaque (partial def), (b) the answer() encoding admits the self-witness g := fun n => (f n : R), which closes the goal by isBi |
| `GreensOpenProblems/14.lean:green_14_polynomial` | 1 | suspect | The as-formalized question is NOT open: W(k,r) >= W(3,r) for all k >= 4 (a colouring with no red 3-AP a fortiori has no red 4-AP, so the guarantee set |
| `GreensOpenProblems/16.lean:zhao_question` | 8 | suspect | Two issues: (1) an open yes/no question is formalized as a committed NO (not-exists h -> 0 with g(N) >= N^(1/3-h(N)) eventually) instead of the repo's |
| `GreensOpenProblems/22.lean:green_22` | 8 | suspect | Formalizing 'find reasonable bounds' as 'any o(exp(exp(r^50)))' is fragile: published round-exponent bounds almost always carry slack, so an o()-impro |
| `GreensOpenProblems/35.lean:green_35.upper` | 8 | suspect | Baseline constant likely mis-transcribed: literature (per abstracts surfaced in search) reports the best construction as 1.50992 in the doubled normal |
| `GreensOpenProblems/37.lean:green_37_bigO` | 2 | no | Two quick closures: (a) tautological answer := fun N => (m N k : R), by Asymptotics.isBigO_refl; (b) legitimate answer := fun N => (N : R) + 1 with th |
| `GreensOpenProblems/37.lean:green_37_littleO` | 2 | no | answer := fun N => (m N k : R) * N is littleO-valid for ANY f (\|\|f N\|\| <= c * \|\|f N\|\| * N once N >= 1/c), needing no knowledge of m; alternati |
| `GreensOpenProblems/39.lean:green_39.variant_theta` | 8 | suspect | Deliberate, documented reinterpretation: Green's literal 'sqrt p replaced by p^theta' (with ~p^theta translates) is trivially false by pigeonhole for  |
| `GreensOpenProblems/51.lean:green_51.one_half` | 8 | suspect | Source asks for a SUBSPACE of codimension O_C(1); the formalization (via guaranteedMaxCosetDim) only guarantees a coset/affine subspace - a weaker con |
| `GreensOpenProblems/54.lean:green_54` | 8 | suspect | Source is finite-dimensional (R^n, gamma_n) with implicit uniformity in n; the file formalizes on R^N with the product Gaussian. Compact balanced K of |
| `Paper/CardinalityLindelof.lean:HasGδSingletons.lindelof_card` | 8 | suspect | The survey's blanket convention is Tychonoff spaces; the Lean statement imposes no separation axiom. Points-Gδ does force T1 (for x≠y each of {x},{y}  |
| `Paper/FusibleNumber.lean:conj_7_1` | 8 | suspect | The file documents four deviations from the paper's Conjecture 7.1 (index shift, replacing s^(n+1)(x) by the explicit value x+(2-1/2^n)m, successor ph |
| `Paper/Homogenous.lean:countablyMonolithicSpace_exists_nhds_generated_countable` | 8 | suspect | Could not verify against the survey whether Problem 17 asks for a point of countable character or of countable π-character; the formalization uses ful |
