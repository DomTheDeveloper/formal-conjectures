# Audit detail — Paper

78 research-open declarations. Fields per problem: plain statement, source, category, match, status, action, difficulties, compute, confidence, evidence, flags.

## `HasGδSingletons.lindelof_card` — Vacuously true / accidentally weakened (cat 4)

**File:** `FormalConjectures/Paper/CardinalityLindelof.lean:39`  
**Secondary category:** 5 (Solved mathematically, not yet formalized)  
**Statement:** Asserts there exists a Lindelöf topological space in which every singleton is a G_delta set and whose cardinality exceeds the continuum.  
**Source:** Problem 1 in A. V. Arhangel'skii, 'Selected old open problems in general topology', Bul. Acad. Ştiinţe Repub. Mold. Mat. 73 (2013) 37-46; see also F. D. Tall, 'Set-theoretic problems concerning Lindelöf spaces' (arXiv:1104.2796).  
**Statement matches intent:** no — The formal statement imposes no separation axiom beyond what G_delta-singletons force (which is exactly T1). Arhangel'skii's Problem 1 is about Lindelöf Hausdorff/Tychonoff spaces - that is the famous ZFC-open question. For merely T1 spaces the answer has been known since Juhász: Arhangel'skii proved every Lindelöf space with points G_delta has cardinality below the first measurable cardinal, and Juhász constructed Lindelöf T1 (explicitly NON-Hausdorff) spaces of countable pseudocharacter of arbitrarily large cardinality below the first measurable. So the Lean statement is a ZFC theorem, not the open problem.  
**Known status:** As stated: TRUE in ZFC (Juhász's non-Hausdorff examples reach cardinalities of countable cofinality well above the continuum, e.g. beth_omega). The intended (T2/T3) problem is open in ZFC; consistently false by Shelah 1978 and Gorelic 1993 (Lindelöf T3 space with points G_delta of size 2^{omega_1} > c). No internal PR/campaign touches this file.  
**Difficulty:** math 9/10, Lean 8/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** HasGδSingletons (FormalConjecturesForMathlib/Topology/GDelta.lean) only requires forall x, IsGδ {x}; that implies T1 but not T2. Literature (Tall's survey and follow-ups) states: Arhangel'skii proved points-G_delta Lindelöf spaces have cardinality less than the first measurable, and Juhász showed the bound is sharp for T1 spaces, with the examples explicitly not Hausdorff.  
**Flags:** missing separation axiom (T2/T3) - statement appears provable in ZFC as written; major semantic mismatch: formal version is a known theorem, intended version is the open problem; needs literature check (Arhangel'skii 2013 PDF and Tall survey PDFs both returned HTTP 403); verifier:confirmed  
**Next action:** Add [T2Space X] (or [RegularSpace X]) to the existential witness to recover Arhangel'skii's Problem 1; alternatively keep the current statement, relabel it research solved, and formalize Juhász's construction (substantial but classical).

## `casas_alvero_conjecture` — Solved mathematically, not yet formalized (cat 5)

**File:** `FormalConjectures/Paper/CasasAlvero.lean:122`  
**Secondary category:** 8 (Deep but approachable research problem)  
**Statement:** Over a characteristic-zero field, a monic polynomial P of degree d that shares a nontrivial factor with each of its Hasse derivatives of order 0..d-1 must equal (X - a)^d.  
**Source:** Casas-Alvero conjecture; Graf von Bothmer-Labs-Schicho-van de Woestijne, arXiv:math/0605090; claimed proof: S. Ghosh, 'Proof of the Casas-Alvero conjecture', arXiv:2501.09272 (v1 Jan 2025, v2 Mar 2026).  
**Statement matches intent:** yes  
**Known status:** A proof for every degree d >= 3 in characteristic 0 via Koszul homology is claimed by Soham Ghosh (arXiv:2501.09272, revised March 2026); the preprint is not withdrawn but no journal acceptance was found. Previously known cases: d <= 8, d = p^k, d = 2p^k.  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** Formalization is faithful: HasCasasAlveroProp P := forall i in range P.natDegree, not (IsCoprime P (P.hasseDeriv i)). The i = 0 instance is harmless (IsCoprime P P fails automatically for non-unit P), and degree 0 is trivial since range 0 is empty and a monic constant equals 1 = (X-C a)^0. The in-file casas_alvero_iff_r shows the shared-root version is equivalent. No internal PR/campaign covers this file.  
**Flags:** claimed literature proof not confirmed peer-reviewed; needs literature check  
**Next action:** Track refereeing of arXiv:2501.09272; do not flip the repo category to research solved until confirmed. Cheaper formalization targets in the same file are the p^k and 2p^k cases. Any edit needs a build check (lake unavailable in this container).

## `value_of_even_mul_succ_self_div_two` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/Paper/CatchUpConjecture.lean:178`  
**Secondary category:** 6 (Computationally solvable with certificate)  
**Statement:** In the combinatorial game Catch-Up played on {1,...,N}, if the total N(N+1)/2 is even then optimal play ends in a draw.  
**Source:** A. Isaksen, M. Ismail, S. J. Brams, A. Nealen, 'Catch-Up: A Game in Which the Lead Alternates', Game & Puzzle Design 1(2) (2015), 38-49.  
**Statement matches intent:** yes  
**Known status:** Open; verified by computer for small N in the original paper. No formal proof known; no repo PR/campaign work on this file.  
**Difficulty:** math 7/10, Lean 9/10 · **Compute:** medium · **Confidence:** medium  
**Evidence:** N = 0 is fine (Icc 1 0 empty, value = draw). N*(N+1)/2 is exact natural division so no truncation defect. value is defined by well-founded recursion on remaining.card and is marked noncomputable, so even finite instances need real work.  
**Flags:** valueAux is noncomputable: small cases cannot be closed by plain decide without unfolding lemmas  
**Next action:** First milestone: derive equation lemmas for valueAux and settle small N (say N <= 8) to build API, then hunt for the pairing/mirroring invariant suggested by the authors' computations.

## `exists_maximal_star` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/Paper/Chvatal.lean:45`  
**Statement:** Chvátal's conjecture: in any downward-closed family F of subsets of a finite set, some star {A in F : x in A} is a largest intersecting subfamily of F.  
**Source:** V. Chvátal (1974), https://users.encs.concordia.ca/~chvatal/conjecture.html ; correlation-inequality approaches in arXiv:1608.08954.  
**Statement matches intent:** yes  
**Known status:** Long-standing open problem (since 1974) with a prize offered by Chvátal; known for various restricted classes (Snevily, Stein, Berge). No repo PR/campaign targets it - the PRs matching 'Chvátal' (#71, #84, #86, #90) concern the Bondy-Chvátal path closure used for WOWII Conjecture 217, a different problem.  
**Difficulty:** math 9/10, Lean 9/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Degenerate cases check out: F empty and F = {empty set} both satisfy the statement (the only intersecting subfamily is empty, card 0). Intersecting requires A cap B nonempty also for A = B, correctly excluding the empty set from intersecting families; the star at x is itself intersecting, so the conclusion says exactly 'some star is maximum'. Type alpha carries Fintype, DecidableEq and Nonempty, so nothing is vacuous.  
**Next action:** Not a near-term formalization target; a known special case (e.g. downsets generated by sets of size at most 3) would be a reasonable research solved companion.

## `cube_hamiltonian_arc_decomposition_even` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/Paper/ClaudesCycles.lean:85`  
**Secondary category:** 6 (Computationally solvable with certificate)  
**Statement:** Asks whether, for every even m > 2, the arcs of the digraph on (Z/m)^3 in which each vertex points to its three coordinate-successors can be partitioned into three directed Hamiltonian cycles.  
**Source:** D. E. Knuth, 'Claude's Cycles' (2026), https://www-cs-faculty.stanford.edu/~knuth/papers/claude-cycles.pdf ; odd case formalized at https://github.com/kim-em/KnuthClaudeLean ; m = 2 impossible by Aubert-Schneider, JCTB 32 (1982) 347-349.  
**Statement matches intent:** suspect — The intended question is per-m ('for which even m > 2 does a decomposition exist?'), but the formalization collapses it into a single answer(sorry) iff (forall even m > 2, ...). If the truth varies with m, the formal answer is just False and could be discharged by one counterexample without settling the intended question.  
**Known status:** Open per Knuth (2026): odd m >= 3 solved by explicit construction, m = 2 impossible, even m > 2 unknown. No repo PR/campaign covers this file.  
**Difficulty:** math 7/10, Lean 8/10 · **Compute:** medium · **Confidence:** medium  
**Evidence:** HasHamiltonianArcDecomposition is well formed: each sigma c is a single cycle with full support whose steps are coordinate bumps, and 'forall v b, exists unique c, sigma c v = bumpAt b v' forces the three cycles to partition all 3m^3 arcs. For m > 1 the three bumps at a vertex are distinct, so there is no degeneracy.  
**Flags:** answer()-encoding collapses a family of per-m questions into one universally quantified statement (weakening); source is a 2026 paper past the knowledge cutoff - status taken from the file's own documentation  
**Next action:** Consider restating per-m (forall m, answer(sorry) iff HasHamiltonianArcDecomposition m) or splitting off m = 4. For m = 4 (64 vertices, 192 arcs) a SAT/ILP search for three arc-disjoint directed Hamiltonian cycles is feasible and yields a kernel-checkable witness (three explicit permutation tables) if one exists.

## `conjClassSizes_iff_sym_three` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/Paper/ConjugacyClassSizes.lean:131`  
**Statement:** Markel's S_3-conjecture: a nontrivial finite group in which distinct conjugacy classes have distinct sizes must be isomorphic to the symmetric group S_3.  
**Source:** F. M. Markel, 'Groups with many conjugate elements', J. Algebra 26 (1973) 69-74; solvable case: J. Zhang, J. Algebra 170 (1994) 608-624, and Knörr-Lempken-Thielcke, Israel J. Math 91 (1995) 61-76; Arad-Muzychuk-Oliver, J. Algebra 280 (2004) 537-576.  
**Statement matches intent:** yes  
**Known status:** Open in general; proved for solvable groups (recorded separately in this file as conjClassSizes_iff_sym_three_solvable, also sorry). Reductions of Arad-Muzychuk-Oliver push it towards almost simple groups. No repo PR/campaign covers this file.  
**Difficulty:** math 9/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** HasDistinctConjClassSizes G is injectivity of c -> Nat.card c.carrier on ConjClasses G, the standard ah-group condition; [Nontrivial G] correctly excludes the trivial group (which is also an ah-group). The file proves by decide that S_3 is an ah-group and that ah-groups have trivial center.  
**Next action:** Not near-term formalizable: needs CFSG-level finite group theory absent from Mathlib. Extend the in-file API instead (trivial center is already proved; class-number and centralizer bounds are natural next lemmas).

## `DeGiorgi_eight` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Paper/DeGiorgi.lean:166`  
**Statement:** De Giorgi's conjecture in dimension 8, the last dimension in which it is expected to hold (it fails for n >= 9).  
**Source:** De Giorgi (1978); Savin, Ann. Math. 169 (2009); del Pino-Kowalczyk-Wei, Ann. Math. 174 (2011) for the n >= 9 counterexample.  
**Statement matches intent:** yes  
**Known status:** Open. No repo PR/campaign covers it.  
**Difficulty:** math 10/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Instantiation of DeGiorgi_conclusion 8; the companion DeGiorgi_ge_nine records sharpness.  
**Next action:** Not approachable; same remarks as DeGiorgi_four.

## `DeGiorgi_five` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Paper/DeGiorgi.lean:145`  
**Statement:** De Giorgi's conjecture in dimension 5.  
**Source:** De Giorgi (1978); Savin, Ann. Math. 169 (2009).  
**Statement matches intent:** yes  
**Known status:** Open. No repo PR/campaign covers it.  
**Difficulty:** math 10/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Instantiation of DeGiorgi_conclusion 5.  
**Next action:** Not approachable; same remarks as DeGiorgi_four.

## `DeGiorgi_four` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Paper/DeGiorgi.lean:138`  
**Statement:** De Giorgi's conjecture in dimension 4: bounded entire solutions of Laplace(u) + u - u^3 = 0 on R^4 that are strictly monotone in x_1 have hyperplane level sets.  
**Source:** De Giorgi (1978); Savin, Ann. Math. 169 (2009) covers 4 <= n <= 8 under an extra limit hypothesis.  
**Statement matches intent:** yes  
**Known status:** Open (Savin's proof needs a hypothesis not present here). No repo PR/campaign covers it.  
**Difficulty:** math 10/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Instantiation of DeGiorgi_conclusion 4 with the shared definitions audited above.  
**Next action:** Not approachable. A formalizable neighbouring target would be Savin's theorem stated with its extra limit hypothesis, as a separate research solved declaration.

## `DeGiorgi_le_eight` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Paper/DeGiorgi.lean:90`  
**Statement:** De Giorgi's conjecture in every dimension 1 <= n <= 8: every bounded C^2 solution of Laplace(u) + u - u^3 = 0 on R^n whose first partial derivative is everywhere positive has hyperplane level sets.  
**Source:** E. De Giorgi (1978); n=2 Ghoussoub-Gui (Math. Ann. 311, 1998); n=3 Ambrosio-Cabré (JAMS 13, 2000); 4 <= n <= 8 under an extra limit assumption: Savin (Ann. Math. 169, 2009); sharpness: del Pino-Kowalczyk-Wei (Ann. Math. 174, 2011).  
**Statement matches intent:** yes  
**Known status:** Open for 4 <= n <= 8 (Savin's theorem additionally assumes u tends to +-1 as x_1 tends to +-infinity, which is not assumed here), so this aggregated statement is open. Cases n <= 3 are theorems; n = 1 is already proved in-file. No repo PR/campaign covers this file.  
**Difficulty:** math 10/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** IsBoundedSolution (ContDiff 2, bounded, Laplace u + u - u^3 = 0), HasPositiveDeriv via lineDeriv in the direction of the first basis vector, and HasHyperplaneLevelSets (each level set of an attained value equals an affine subspace whose direction has rank n-1) faithfully render the conjecture. [NeZero n] excludes n = 0 and makes the n - 1 truncation harmless.  
**Flags:** aggregates the solved cases n <= 3 with the genuinely open range 4 <= n <= 8  
**Next action:** Do not attack directly. Even the solved case n = 2 needs Liouville-type theorems and stability/energy estimates far beyond current Mathlib analysis; the realistic first step is Mathlib infrastructure for entire solutions of semilinear elliptic PDE.

## `DeGiorgi_seven` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Paper/DeGiorgi.lean:159`  
**Statement:** De Giorgi's conjecture in dimension 7.  
**Source:** De Giorgi (1978); Savin, Ann. Math. 169 (2009).  
**Statement matches intent:** yes  
**Known status:** Open. No repo PR/campaign covers it.  
**Difficulty:** math 10/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Instantiation of DeGiorgi_conclusion 7.  
**Next action:** Not approachable; same remarks as DeGiorgi_four.

## `DeGiorgi_six` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Paper/DeGiorgi.lean:152`  
**Statement:** De Giorgi's conjecture in dimension 6.  
**Source:** De Giorgi (1978); Savin, Ann. Math. 169 (2009).  
**Statement matches intent:** yes  
**Known status:** Open. No repo PR/campaign covers it.  
**Difficulty:** math 10/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Instantiation of DeGiorgi_conclusion 6.  
**Next action:** Not approachable; same remarks as DeGiorgi_four.

## `dubner_conjecture` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Paper/Dubner.lean:58`  
**Statement:** Every even number greater than 4208 is the sum of two twin primes (primes p such that p-2 or p+2 is also prime).  
**Source:** H. Dubner, 'Twin prime conjectures', https://scispace.com/pdf/twin-prime-conjectures-3icaxy6b0m.pdf  
**Statement matches intent:** yes  
**Known status:** Open, and strictly stronger than both Goldbach's conjecture and the twin prime conjecture (it implies there are infinitely many twin primes). Verified numerically to large bounds. No repo PR/campaign covers this file.  
**Difficulty:** math 10/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** IsTwinPrime p := p.Prime and ((p-2).Prime or (p+2).Prime). Natural subtraction at p = 2 gives 0 (not prime) and 4 is not prime, so 2 is correctly not a twin prime (test t1); no truncation artefact anywhere else since p < 2 is never prime. Hypotheses 4208 < n and Even n match the published statement.  
**Flags:** implies the twin prime conjecture - infeasible  
**Next action:** Out of reach; only finite-range sanity checks are feasible, in the spirit of the existing test lemmas.

## `conj_7_1` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/Paper/FusibleNumber.lean:68`  
**Statement:** Conjecture 7.1 on fusible numbers: if y is the successor of a fusible number x and m = y - x, then every fusible q in [y+1-m/2^n, y+1-m/2^(n+1)) is obtained by fusing the (n+1)-st successor of x with the fusible number z = 2q - 1 - x - (2 - 2^(-n))m.  
**Source:** J. Erickson, G. Nivasch, J. Xu, 'Fusible numbers and Peano Arithmetic', LMCS 18(3:6) 2022 / arXiv:2003.14342, Conjecture 7.1.  
**Statement matches intent:** suspect — Faithful up to the four reindexings documented in the docstring (verified: the (n+1)-st successor of x is x + (2 - 2^(-n))m, and inverting q = (s^(n+1)(x) + z + 1)/2 gives exactly the stated z). But the conclusion only asserts IsFusible z, dropping the side conditions |s^(n+1)(x) - z| < 1 and z in [x+1-m/2^n, x+1) that are part of Conjecture 7.1, so the Lean version is formally slightly weaker.  
**Known status:** Open (a conjecture in the published LMCS paper; parts of that paper were formalized in Lean by Junyan Xu, but not this conjecture). No repo PR/campaign covers this file.  
**Difficulty:** math 7/10, Lean 8/10 · **Compute:** small · **Confidence:** medium  
**Evidence:** l 0 = y + 1 - m = x + 1 and l n increases to y + 1, so the intervals [l n, l (n+1)) do partition [x+1, y+1) as intended; nmem_Ioo together with IsFusible x, IsFusible y and x < y correctly encodes 'y is the successor of x'. All arithmetic is over the rationals, so no truncation or division-by-zero issues.  
**Flags:** conclusion omits the |s^(n+1)(x) - z| < 1 and z-range assertions of the published conjecture (minor weakening)  
**Next action:** First milestone: build IsFusible API (successor structure, the fact that the k-th successor of x is x + (2 - 2^(1-k))m, density in intervals) before attacking 7.1.

## `harthshorne_conjecture` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Paper/HartshorneConjecture.lean:101`  
**Statement:** Hartshorne's splitting conjecture: for n >= 7 every rank-2 vector bundle on complex projective n-space splits as a direct sum of two (necessarily line) bundles.  
**Source:** R. Hartshorne, 'Varieties of small codimension in projective space', Bull. AMS 80 (1974), Conjecture 6.3; MathOverflow question 13990.  
**Statement matches intent:** suspect — The mathematical content is right, but the statement uses the categorical coproduct in S.VectorBundles, whose HasFiniteCoproducts instance is supplied by the sorry-ed theorem hasFiniteCoproductsVectorBundles in the same file. The class is Prop-valued so no junk value leaks, but the meaning of the coproduct is only pinned down once that (true) statement is actually proved. Also Splitting demands components not isomorphic to the bundle rather than explicitly of rank 1 - equivalent here, but indirect.  
**Known status:** Major open problem, closely tied to Hartshorne's codimension-2 complete intersection conjecture; no proof and no counterexample. The file itself has a TODO noting that sanity checks are missing. No repo PR/campaign covers it.  
**Difficulty:** math 10/10, Lean 10/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** P(Fin (n+1); Spec (.of C)) is projective n-space over C (n+1 homogeneous coordinates) and 7 <= n matches Conjecture 6.3; VectorBundles.Splitting (Fin 2) is an isomorphism onto a coproduct of two bundles, neither isomorphic to the original, which for rank 2 forces two line bundles.  
**Flags:** statement's meaning depends on a sorry-ed instance (hasFiniteCoproductsVectorBundles); file carries a TODO acknowledging missing sanity checks  
**Next action:** Prove hasFiniteCoproductsVectorBundles first (direct sums of locally free sheaves of finite rank) so the statement is unconditionally meaningful, and add sanity lemmas (O(a) + O(b) splits; rank of a coproduct adds). The conjecture itself is not a formalization target.

## `countablyMonolithicSpace_card_lt` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/Paper/Homogenous.lean:95`  
**Statement:** Is every homogeneous omega-monolithic compact Hausdorff space of cardinality at most the continuum?  
**Source:** Problem 16 in A. V. Arhangel'skii, 'Selected old open problems in general topology' (2013).  
**Statement matches intent:** yes  
**Known status:** Open, but formally implied by Problem 15 (firstCountableTopology_of_countablyMonolithicSpace) plus Arhangel'skii's classical theorem that first-countable compact Hausdorff spaces have cardinality at most the continuum; so it is the weaker of the two neighbouring statements. No repo PR/campaign covers this file.  
**Difficulty:** math 8/10, Lean 10/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** The conclusion is #X <= continuum, matching 'not greater than c'; hypotheses are T2, compact, homogeneous and omega-monolithic exactly as in the source.  
**Flags:** answer()-encoding; weaker than the neighbouring Problem 15 statement  
**Next action:** If Mathlib gains Arhangel'skii's cardinality theorem, record the reduction 'Problem 15 implies Problem 16' as an API lemma - the cheapest real progress available here.

## `countablyMonolithicSpace_exists_nhds_generated_countable` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/Paper/Homogenous.lean:107`  
**Statement:** Does every nonempty omega-monolithic compact Hausdorff space contain at least one point with a countable neighbourhood basis?  
**Source:** Problem 17 in A. V. Arhangel'skii, 'Selected old open problems in general topology' (2013).  
**Statement matches intent:** yes  
**Known status:** Open. Consistent with known examples: the one-point compactification of an uncountable discrete space is omega-monolithic and not first countable, yet has points of countable character. No repo PR/campaign covers this file.  
**Difficulty:** math 8/10, Lean 10/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** (nhds x).IsCountablyGenerated is the correct rendering of 'x has a countable neighbourhood basis'.  
**Flags:** answer()-encoding; possible independence from ZFC  
**Next action:** Leave open; a Mathlib prerequisite is Sapirovskii-style results on points of countable pi-character in compacta.

## `firstCountableTopology_of_countablyMonolithicSpace` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/Paper/Homogenous.lean:87`  
**Statement:** Is every homogeneous omega-monolithic compact Hausdorff space first countable? (omega-monolithic means the closure of every countable subset is metrizable.)  
**Source:** Problem 15 in A. V. Arhangel'skii, 'Selected old open problems in general topology' (2013).  
**Statement matches intent:** yes  
**Known status:** Open. Neighbouring known results: homogeneous compacta of countable tightness are first countable (Juhász-Nyikos-Szentmiklossy, under extra axioms), and omega-monolithicity is a strong smallness condition. No repo PR/campaign covers this file.  
**Difficulty:** math 8/10, Lean 10/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** CountablyMonolithicSpace requires MetrizableSpace (closure s) for every countable s - the standard omega-monolithic condition - and the instance from metrizable spaces is proved in-file as a sanity check.  
**Flags:** answer()-encoding; possible independence from ZFC  
**Next action:** Leave open; record that a positive answer here implies Problem 16 via Arhangel'skii's cardinality theorem (first countable compact Hausdorff implies cardinality at most the continuum).

## `homogeneousSpace_exists_inj_tendsto` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Paper/Homogenous.lean:56`  
**Statement:** Does every infinite homogeneous compact Hausdorff space contain a nontrivial convergent sequence (an injective sequence with a limit)?  
**Source:** Problem 13 in A. V. Arhangel'skii, 'Selected old open problems in general topology' (2013); classical van Douwen-Arhangel'skii circle of problems.  
**Statement matches intent:** yes  
**Known status:** Long-standing open problem; known under extra hypotheses (e.g. countable tightness), with no ZFC answer and no consistent counterexample known to me. No repo PR/campaign covers this file.  
**Difficulty:** math 9/10, Lean 10/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** answer(sorry) iff (for all infinite compact Hausdorff homogeneous X there is an injective sequence converging to a point) faithfully renders 'nontrivial convergent sequence'; HomogeneousSpace is the standard point-transitivity-by-homeomorphisms definition, with a discrete-space sanity instance proved in-file.  
**Flags:** answer()-encoding is unresolvable if the problem turns out to be independent of ZFC  
**Next action:** Leave open. Formal progress would first require the classical cardinal-function toolkit (pi-character, Sapirovskii's theorem), which Mathlib lacks.

## `homogeneousSpace_exists_surjective` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Paper/Homogenous.lean:65`  
**Statement:** Is every compact Hausdorff space a continuous image of some homogeneous compact Hausdorff space?  
**Source:** Problem 14 in A. V. Arhangel'skii, 'Selected old open problems in general topology' (2013); cf. Motorov's results for metrizable compacta.  
**Statement matches intent:** yes  
**Known status:** Open; known for metrizable compacta (Motorov: every metrizable compactum is a continuous image of a homogeneous compact metrizable space). No repo PR/campaign covers this file.  
**Difficulty:** math 9/10, Lean 10/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** Degenerate cases are harmless (X empty or a singleton: take Y = X, which is homogeneous). The statement asserts existence of a compact Hausdorff homogeneous Y with a continuous surjection onto X.  
**Flags:** witness universe pinned to Type 0 (minor)  
**Next action:** Leave open. A formalizable warm-up is the metrizable case, or the classical fact that every compact Hausdorff space is a continuous image of a zero-dimensional compact space.

## `kurepa_conjecture` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Paper/Kurepa.lean:46`  
**Statement:** Kurepa's conjecture: for every n > 2 the left factorial !n = 0! + 1! + ... + (n-1)! is not divisible by n.  
**Source:** D. Kurepa, 'On the left factorial function !N', Math. Balkanica 1 (1971) 147-153; OEIS A003422; Guy, Unsolved Problems in Number Theory, B44.  
**Statement matches intent:** yes  
**Known status:** Open; several claimed proofs have been withdrawn (notably Barsky-Benzaghou 2004, retracted 2011). Verified computationally to roughly 2^40 (Andrejic-Tatarevic). No repo PR/campaign covers this file.  
**Difficulty:** math 9/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** left_factorial n is the sum of m! over range n, the standard !n; the hypothesis 2 < n is needed since !2 = 2 is divisible by 2, a genuine exception that is correctly excluded.  
**Next action:** Out of reach analytically. The only cheap extension is widening the first_cases sanity check beyond n < 50 (kernel decide gets expensive fast because of factorial sizes).

## `kurepa_conjecture.variants.gcd` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Paper/Kurepa.lean:92`  
**Statement:** Equivalent gcd form of Kurepa's conjecture: gcd(n!, !n) = 2 for every n > 2.  
**Source:** Kurepa (1971); equivalence proved in-file as kurepa_conjecture.gcd_reduction.  
**Statement matches intent:** yes  
**Known status:** Open; provably equivalent to kurepa_conjecture through the fully proved kurepa_conjecture.gcd_reduction in the same file. No repo PR/campaign covers it.  
**Difficulty:** math 9/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** The statement is gcd(n!, !n) = 2 for 2 < n, and the in-file gcd_reduction establishing the equivalence with the divisibility form is proved without sorry; a first_cases test confirms n < 50.  
**Flags:** equivalent restatement of kurepa_conjecture (in-file reduction already proved)  
**Next action:** Treat as an alias; derive it from the main conjecture via gcd_reduction once (if ever) that is proved.

## `kurepa_conjecture.variants.prime` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Paper/Kurepa.lean:53`  
**Statement:** Kurepa's conjecture restricted to odd primes: for every prime p > 2, p does not divide !p.  
**Source:** Kurepa (1971); the reduction to primes is the in-file proved lemma kurepa_conjecture.prime_reduction.  
**Statement matches intent:** yes  
**Known status:** Open, and by the fully proved kurepa_conjecture.prime_reduction in the same file it is equivalent to the general conjecture. It is also an immediate weakening of kurepa_conjecture (itself sorry), so it carries no independent difficulty.  
**Difficulty:** math 9/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** p.Prime appears as an explicit implication after 2 < p; prime_reduction proves the equivalence with the general form and contains no sorry.  
**Flags:** equivalent duplicate of kurepa_conjecture within the same file  
**Next action:** Treat as an alias of the main conjecture; if that is ever proved, close this in one line.

## `growthRateZn` — Already solved externally (cat 1)

**File:** `FormalConjectures/Paper/LatinSquare.lean:161`  
**Secondary category:** 5 (Solved mathematically, not yet formalized)  
**Statement:** lim over odd n of (1/n)·log(z_n/n!) equals −1, where z_n is the number of transversals of the Z_n Cayley table.  
**Source:** Wanless survey 2011, Conjecture 6.9. Resolved by Eberhard–Manners–Mrazović, JEMS 21 (2019).  
**Statement matches intent:** yes  
**Known status:** SOLVED EXTERNALLY. From z_n = (e^{-1/2}+o(1)) n!^2/n^{n-1}: log(z_n/n!) = log n! − (n−1) log n + O(1) = −n + log n + O(log n), so (1/n) log(z_n/n!) → −1. The survey explicitly says 'it is not even known if this limit exists'; EMM's asymptotic settles both existence and the value.  
**Difficulty:** math 8/10, Lean 10/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** Same EMM asymptotic as numTransversalsZn; direct Stirling computation gives the limit −1. Numerics from the file's own test values are consistent.  
**Flags:** MISLABELLED STATUS: `@[category research open]` for a conjecture resolved in 2019.; needs literature check to confirm no later refinement changes the constant.; verifier:confirmed  
**Next action:** Re-categorise as `research solved` citing EMM 2019; a Lean proof would require formalizing their circle-method asymptotic (research-scale). Nothing internal exists.

## `latinSquareNearTransversal` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/Paper/LatinSquare.lean:70`  
**Statement:** Brualdi–Stein conjecture: every Latin square of order n contains a partial transversal of size n-1 (n-1 cells with distinct rows, distinct columns and distinct symbols).  
**Source:** Wanless survey 2011, Conjecture 5.1 (Brualdi; Stein 1975).  
**Statement matches intent:** yes  
**Known status:** Open for all n. Montgomery (arXiv:2310.19779, 2023) proved it for all sufficiently large n; Hatami–Shor give n − O(log^2 n) unconditionally. No fork PR/branch touches this.  
**Difficulty:** math 9/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Web check confirms Montgomery 2023 resolves RBS only for large n; the general-n statement is still listed as open (also tracked as google-deepmind/formal-conjectures issue #2271).  
**Flags:** Same free-section-variable answer() encoding issue as oddOrderLatinSquareTransversal: a single counterexample n makes the theorem unprovable rather than giving answer = False.  
**Next action:** Leave open. A tractable sub-goal would be formalizing the easy n − O(√n)/greedy bound (every Latin square has a partial transversal of size ≥ ⌈n/2⌉ or ≥ 2n/3 by Koksma/Drake), which is a real but self-contained Lean project.

## `latinSquareOrder11Transversal` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/Paper/LatinSquare.lean:55`  
**Secondary category:** 6 (Computationally solvable with certificate)  
**Statement:** Does every Latin square of order 11 have a transversal? (The smallest odd order for which Ryser's conjecture is unverified.)  
**Source:** Wanless, 'Transversals in Latin Squares: A Survey' 2011, remark following Conjecture 3.2.  
**Statement matches intent:** yes  
**Known status:** Open. Exhaustive verification stops at n = 9 (McKay–McLeod–Wanless). The number of main classes of order-11 Latin squares is ≈ 2·10^24, so brute force is out of reach; Montgomery's large-n theorem gives no information at n = 11.  
**Difficulty:** math 9/10, Lean 10/10 · **Compute:** large · **Confidence:** high  
**Evidence:** Fixed n = 11, so no free-variable pathology; `∃ σ, IsTransversal L σ` is decidable for each L but the class of L is astronomically large. Kernel-checkable finite computation exists in principle (hence cat2 = 6) but the search space rules it out.  
**Next action:** Do not attempt. If pursued at all, it would be a symmetry-reduced exhaustive search over order-11 main classes with a kernel-checkable certificate — currently infeasible (≈10^24 classes).

## `numTransversalsZn` — Already solved externally (cat 1)

**File:** `FormalConjectures/Paper/LatinSquare.lean:146`  
**Secondary category:** 5 (Solved mathematically, not yet formalized)  
**Statement:** There exist constants 0 < c1 < c2 < 1 with c1^n n! ≤ z_n ≤ c2^n n! for all odd n ≥ 3, where z_n is the number of transversals of the Cayley table of Z_n.  
**Source:** Wanless survey 2011, Conjecture 6.7 (Vardi). Resolved by S. Eberhard, F. Manners, R. Mrazović, 'Additive triples of bijections, or the toroidal semiqueens problem', J. Eur. Math. Soc. 21 (2019); arXiv:1510.05987.  
**Statement matches intent:** yes  
**Known status:** SOLVED EXTERNALLY (post-dates the 2011 survey). EMM prove z_n = (e^{-1/2}+o(1)) n!^2 / n^{n-1} for odd n via the circle method on (Z/nZ)^n. Hence (z_n/n!)^{1/n} → 1/e, giving the required c1 < 1/e < c2 for large n; the finitely many small odd n are handled because z_n > 0 for all odd n. Numerical sanity check at n = 7: e^{-1/2}·7!^2/7^6 ≈ 131 vs z(7) = 133.  
**Difficulty:** math 8/10, Lean 10/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** WebSearch confirms the EMM JEMS 2019 paper counts exactly the transversals of the cyclic Latin square. My own arithmetic check of their asymptotic against the file's z(7) = 133 agrees to 1.5%. Wanless's survey (2011) predates the resolution, which is why the file still marks it open.  
**Flags:** MISLABELLED STATUS: `@[category research open]` but the underlying conjecture was resolved in 2019.; needs literature check on whether the *explicit-constant* form for all odd n ≥ 3 (not just asymptotically) was stated anywhere; the deduction from EMM plus finitely many checks is routine but not written down in this exact form.; verifier:confirmed  
**Next action:** Re-categorise as `research solved` with the EMM citation, or keep as open-in-Lean but record the literature answer (c1, c2 straddling 1/e, e.g. c1 = 1/5, c2 = 17/20 works given the asymptotic). Formalizing EMM in Lean is research-scale (circle method over (Z/nZ)^n).

## `oddOrderLatinSquareTransversal` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/Paper/LatinSquare.lean:39`  
**Statement:** Ryser's conjecture: every Latin square of odd order n has a transversal (a set of n cells, one per row and column, with n distinct symbols).  
**Source:** Wanless, 'Transversals in Latin Squares: A Survey', Surveys in Combinatorics 2011, Conjecture 3.2 (Ryser 1967). https://users.monash.edu.au/~iwanless/papers/transurveyBCC.pdf  
**Statement matches intent:** yes  
**Known status:** Open in general. Verified by computer for n ≤ 9 (see companion `oddOrderLeq9LatinSquareTransversal`). Richard Montgomery, 'A proof of the Ryser-Brualdi-Stein conjecture for large even n' (arXiv:2310.19779, 2023) settles the RBS family for all sufficiently large n; no bound on n0 is effective, so the ∀n statement remains open. No PR/branch in this fork touches Latin squares (pr_register.json: no hits for latin/transversal).  
**Difficulty:** math 9/10, Lean 10/10 · **Compute:** large · **Confidence:** high  
**Evidence:** Section `variable {n : ℕ}` is auto-bound, so the statement elaborates to `∀ {n}, answer ↔ (Odd n → ∀ L, ∃ σ, IsTransversal L σ)`. Since the RHS is vacuously true for even n, the only satisfiable answer is True, and then the theorem is exactly Ryser's conjecture — so the encoding is sound in the positive direction.  
**Flags:** answer-encoding cannot express a NEGATIVE answer: with a free section variable n, `∀ n, (A ↔ P n)` is unprovable (for any A) if P fails for a single odd n, rather than yielding answer = False. Cleaner would be `answer ↔ ∀ n, Odd n → ...`.; Prop-valued answer() could in principle be discharged by instantiating it with the RHS itself (Iff.rfl); repo convention presumably requires True/False.  
**Next action:** Leave open. Realistic partial progress: formalize the n ≤ 9 verified cases (still a huge Lean computation) or the trivial n ∈ {1,3} cases; a full proof needs Montgomery's absorption machinery plus an effective n0, which does not exist.

## `LatinTableauConjecture` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/Paper/LatinTableau.lean:43`  
**Statement:** The Latin Tableau Conjecture: the graph on the cells of any Young diagram (two cells adjacent when in the same row or column) has a proper colouring whose first k colour classes together cover exactly as many cells as the largest union of k independent sets, for every k.  
**Source:** T. Y. Chow, M. G. Tiefenbruck, 'The Latin Tableau Conjecture', Electron. J. Combin. 32(2) (2025) #P2.48; origin: Chow-Fan-Goemans-Vondrak, 'Wide partitions, Latin tableaux, and Rota's basis conjecture' (arXiv:math/0205288).  
**Statement matches intent:** yes  
**Known status:** Open: the conjecture, over two decades old and tied to Rota's basis conjecture, is equivalent to CDS-colorability of Young-diagram graphs, which is what is stated here. An 'AI proof' preprint circulating on academia.edu is not a credible resolution. No repo PR/campaign covers this file.  
**Difficulty:** math 8/10, Lean 8/10 · **Compute:** small · **Confidence:** medium  
**Evidence:** YoungDiagram.toSimpleGraph is SimpleGraph.fromRel on same-row-or-same-column, the intended rook-type graph on cells; indepNumK G k is a supremum over unions of k independent sets, well defined because the cell type is a Fintype.  
**Flags:** needs literature check on whether the EJC paper settles special cases that should be recorded as research solved  
**Next action:** Realistic first milestones: CDS-colorability for rectangular and staircase shapes (where the k-independence numbers have closed forms), and a lemma computing indepNumK for Young-diagram graphs as a maximum over unions of k rook placements.

## `eqSystem10_no_solution_d3` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/Paper/MonochromaticQuantumGraph.lean:471`  
**Statement:** Is there no complex 3-color perfectly monochromatic weighting of K10?  
**Source:** Krenn-Gu conjecture: Krenn-Gu-Soltesz arXiv:1902.06023; MathOverflow 311325; Chandran-Gajjala arXiv:2202.05562; Chandran-Gajjala-Illickan-Krenn arXiv:2407.00303 (MFCS 2024); mariokrenn.wordpress.com/graph-theory-question  
**Statement matches intent:** yes  
**Known status:** Krenn-Gu conjecture (even N>=6, D>=3 => no perfectly monochromatic weighting) is open as of 2026-07. Known partial results: Bogdanov proved the nonnegative-real case (MO 311325); Chandran-Gajjala proved it for vertex connectivity <= 2 and cubic graphs (arXiv:2202.05562, arXiv:2407.00303); DeepMind agents formally proved the D=N and N=4,D>=4 complex cases (already marked solved in this file). This fork internally proved the N=6 integer/trinary cases (PR #96) via mod-2 SAT, which does NOT bear on C or R. D=10 (=N) case is already formally solved; 3<=D<=9 are open.  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Formalization audited: pmSumListAux with fuel=length correctly enumerates perfect matchings pairing head with later vertices; only u<v edges with colors (iota u, iota v) are ever read, so unconstrained EdgeN ghost fields (u>=v, loops) are inert; allEqual = chain equality along [0..N-1] = constancy; positive witnesses N=4 D=2/3 and N=6 D=2 verified by native_decide in-file, confirming the encoding admits the known physical constructions. answer(sorry) <-> (no-solution) encoding is faithful.  
**Next action:** Open. For D=3>3 it would follow from the (10,3) case via the fork's generic color-restriction lemma; no known attack on the base case over C.

## `eqSystem10_no_solution_d3_int` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/Paper/MonochromaticQuantumGraph.lean:692`  
**Secondary category:** 6 (Computationally solvable with certificate)  
**Statement:** Is there no integer edge-weighting of K10 with 3 colors satisfying the system?  
**Source:** Krenn-Gu conjecture: Krenn-Gu-Soltesz arXiv:1902.06023; MathOverflow 311325; Chandran-Gajjala arXiv:2202.05562; Chandran-Gajjala-Illickan-Krenn arXiv:2407.00303 (MFCS 2024); mariokrenn.wordpress.com/graph-theory-question  
**Statement matches intent:** yes  
**Known status:** Open; not covered by the fork campaign or literature.  
**Difficulty:** math 7/10, Lean 9/10 · **Compute:** large · **Confidence:** medium  
**Evidence:** Mod-2 reduction is valid for every N; feasibility, not validity, is the obstruction at N=10.  
**Flags:** resolution contingent on mod-2 UNSAT holding at N=10  
**Next action:** Same mod-2 SAT route as N=8 in principle (405 GF(2) variables, 59049 equations, 945 degree-5 monomials each), but orbit classification under S_10 and certificate sizes are at or beyond comfortable scale; treat as research-grade computation.

## `eqSystem10_no_solution_d3_real` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/Paper/MonochromaticQuantumGraph.lean:625`  
**Statement:** Is there no real 3-color perfectly monochromatic weighting of K10?  
**Source:** Krenn-Gu conjecture: Krenn-Gu-Soltesz arXiv:1902.06023; MathOverflow 311325; Chandran-Gajjala arXiv:2202.05562; Chandran-Gajjala-Illickan-Krenn arXiv:2407.00303 (MFCS 2024); mariokrenn.wordpress.com/graph-theory-question  
**Statement matches intent:** yes  
**Known status:** Krenn-Gu conjecture (even N>=6, D>=3 => no perfectly monochromatic weighting) is open as of 2026-07. Known partial results: Bogdanov proved the nonnegative-real case (MO 311325); Chandran-Gajjala proved it for vertex connectivity <= 2 and cubic graphs (arXiv:2202.05562, arXiv:2407.00303); DeepMind agents formally proved the D=N and N=4,D>=4 complex cases (already marked solved in this file). This fork internally proved the N=6 integer/trinary cases (PR #96) via mod-2 SAT, which does NOT bear on C or R. Over R the mod-2 route is unavailable and Bogdanov's argument needs nonnegativity, so the real case is essentially as hard as the complex one (and implied by it).  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Formalization audited: pmSumListAux with fuel=length correctly enumerates perfect matchings pairing head with later vertices; only u<v edges with colors (iota u, iota v) are ever read, so unconstrained EdgeN ghost fields (u>=v, loops) are inert; allEqual = chain equality along [0..N-1] = constancy; positive witnesses N=4 D=2/3 and N=6 D=2 verified by native_decide in-file, confirming the encoding admits the known physical constructions. answer(sorry) <-> (no-solution) encoding is faithful.  
**Next action:** Open; no specific route.

## `eqSystem10_no_solution_d3_trinary_int` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/Paper/MonochromaticQuantumGraph.lean:769`  
**Secondary category:** 6 (Computationally solvable with certificate)  
**Statement:** Is there no {-1,0,1}-valued edge-weighting of K10 with 3 colors satisfying the system?  
**Source:** Krenn-Gu conjecture: Krenn-Gu-Soltesz arXiv:1902.06023; MathOverflow 311325; Chandran-Gajjala arXiv:2202.05562; Chandran-Gajjala-Illickan-Krenn arXiv:2407.00303 (MFCS 2024); mariokrenn.wordpress.com/graph-theory-question  
**Statement matches intent:** yes  
**Known status:** Open; implied by the (open) N=10 integer case.  
**Difficulty:** math 6/10, Lean 9/10 · **Compute:** large · **Confidence:** medium  
**Evidence:** Finite in principle; scale is the obstruction.  
**Flags:** resolution contingent on mod-2 UNSAT at N=10  
**Next action:** Same as the N=10 integer case: mod-2 SAT route at research-grade scale; direct exact ternary encoding (405 ternary vars, 59049 arithmetic constraints over sums of 945 degree-5 monomials) likely infeasible.

## `eqSystem10_no_solution_d4` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/Paper/MonochromaticQuantumGraph.lean:479`  
**Statement:** Is there no complex 4-color perfectly monochromatic weighting of K10?  
**Source:** Krenn-Gu conjecture: Krenn-Gu-Soltesz arXiv:1902.06023; MathOverflow 311325; Chandran-Gajjala arXiv:2202.05562; Chandran-Gajjala-Illickan-Krenn arXiv:2407.00303 (MFCS 2024); mariokrenn.wordpress.com/graph-theory-question  
**Statement matches intent:** yes  
**Known status:** Krenn-Gu conjecture (even N>=6, D>=3 => no perfectly monochromatic weighting) is open as of 2026-07. Known partial results: Bogdanov proved the nonnegative-real case (MO 311325); Chandran-Gajjala proved it for vertex connectivity <= 2 and cubic graphs (arXiv:2202.05562, arXiv:2407.00303); DeepMind agents formally proved the D=N and N=4,D>=4 complex cases (already marked solved in this file). This fork internally proved the N=6 integer/trinary cases (PR #96) via mod-2 SAT, which does NOT bear on C or R. D=10 (=N) case is already formally solved; 3<=D<=9 are open.  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** Formalization audited: pmSumListAux with fuel=length correctly enumerates perfect matchings pairing head with later vertices; only u<v edges with colors (iota u, iota v) are ever read, so unconstrained EdgeN ghost fields (u>=v, loops) are inert; allEqual = chain equality along [0..N-1] = constancy; positive witnesses N=4 D=2/3 and N=6 D=2 verified by native_decide in-file, confirming the encoding admits the known physical constructions. answer(sorry) <-> (no-solution) encoding is faithful. Downward-closure in D means (10,3) implies this case.  
**Next action:** Open. For D=4>3 it would follow from the (10,3) case via the fork's generic color-restriction lemma; no known attack on the base case over C.

## `eqSystem10_no_solution_d5` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/Paper/MonochromaticQuantumGraph.lean:487`  
**Statement:** Is there no complex 5-color perfectly monochromatic weighting of K10?  
**Source:** Krenn-Gu conjecture: Krenn-Gu-Soltesz arXiv:1902.06023; MathOverflow 311325; Chandran-Gajjala arXiv:2202.05562; Chandran-Gajjala-Illickan-Krenn arXiv:2407.00303 (MFCS 2024); mariokrenn.wordpress.com/graph-theory-question  
**Statement matches intent:** yes  
**Known status:** Krenn-Gu conjecture (even N>=6, D>=3 => no perfectly monochromatic weighting) is open as of 2026-07. Known partial results: Bogdanov proved the nonnegative-real case (MO 311325); Chandran-Gajjala proved it for vertex connectivity <= 2 and cubic graphs (arXiv:2202.05562, arXiv:2407.00303); DeepMind agents formally proved the D=N and N=4,D>=4 complex cases (already marked solved in this file). This fork internally proved the N=6 integer/trinary cases (PR #96) via mod-2 SAT, which does NOT bear on C or R. D=10 (=N) case is already formally solved; 3<=D<=9 are open.  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** Formalization audited: pmSumListAux with fuel=length correctly enumerates perfect matchings pairing head with later vertices; only u<v edges with colors (iota u, iota v) are ever read, so unconstrained EdgeN ghost fields (u>=v, loops) are inert; allEqual = chain equality along [0..N-1] = constancy; positive witnesses N=4 D=2/3 and N=6 D=2 verified by native_decide in-file, confirming the encoding admits the known physical constructions. answer(sorry) <-> (no-solution) encoding is faithful. Downward-closure in D means (10,3) implies this case.  
**Next action:** Open. For D=5>3 it would follow from the (10,3) case via the fork's generic color-restriction lemma; no known attack on the base case over C.

## `eqSystem10_no_solution_d6` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/Paper/MonochromaticQuantumGraph.lean:495`  
**Statement:** Is there no complex 6-color perfectly monochromatic weighting of K10?  
**Source:** Krenn-Gu conjecture: Krenn-Gu-Soltesz arXiv:1902.06023; MathOverflow 311325; Chandran-Gajjala arXiv:2202.05562; Chandran-Gajjala-Illickan-Krenn arXiv:2407.00303 (MFCS 2024); mariokrenn.wordpress.com/graph-theory-question  
**Statement matches intent:** yes  
**Known status:** Krenn-Gu conjecture (even N>=6, D>=3 => no perfectly monochromatic weighting) is open as of 2026-07. Known partial results: Bogdanov proved the nonnegative-real case (MO 311325); Chandran-Gajjala proved it for vertex connectivity <= 2 and cubic graphs (arXiv:2202.05562, arXiv:2407.00303); DeepMind agents formally proved the D=N and N=4,D>=4 complex cases (already marked solved in this file). This fork internally proved the N=6 integer/trinary cases (PR #96) via mod-2 SAT, which does NOT bear on C or R. D=10 (=N) case is already formally solved; 3<=D<=9 are open.  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** Formalization audited: pmSumListAux with fuel=length correctly enumerates perfect matchings pairing head with later vertices; only u<v edges with colors (iota u, iota v) are ever read, so unconstrained EdgeN ghost fields (u>=v, loops) are inert; allEqual = chain equality along [0..N-1] = constancy; positive witnesses N=4 D=2/3 and N=6 D=2 verified by native_decide in-file, confirming the encoding admits the known physical constructions. answer(sorry) <-> (no-solution) encoding is faithful. Downward-closure in D means (10,3) implies this case.  
**Next action:** Open. For D=6>3 it would follow from the (10,3) case via the fork's generic color-restriction lemma; no known attack on the base case over C.

## `eqSystem10_no_solution_d7` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/Paper/MonochromaticQuantumGraph.lean:503`  
**Statement:** Is there no complex 7-color perfectly monochromatic weighting of K10?  
**Source:** Krenn-Gu conjecture: Krenn-Gu-Soltesz arXiv:1902.06023; MathOverflow 311325; Chandran-Gajjala arXiv:2202.05562; Chandran-Gajjala-Illickan-Krenn arXiv:2407.00303 (MFCS 2024); mariokrenn.wordpress.com/graph-theory-question  
**Statement matches intent:** yes  
**Known status:** Krenn-Gu conjecture (even N>=6, D>=3 => no perfectly monochromatic weighting) is open as of 2026-07. Known partial results: Bogdanov proved the nonnegative-real case (MO 311325); Chandran-Gajjala proved it for vertex connectivity <= 2 and cubic graphs (arXiv:2202.05562, arXiv:2407.00303); DeepMind agents formally proved the D=N and N=4,D>=4 complex cases (already marked solved in this file). This fork internally proved the N=6 integer/trinary cases (PR #96) via mod-2 SAT, which does NOT bear on C or R. D=10 (=N) case is already formally solved; 3<=D<=9 are open.  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** Formalization audited: pmSumListAux with fuel=length correctly enumerates perfect matchings pairing head with later vertices; only u<v edges with colors (iota u, iota v) are ever read, so unconstrained EdgeN ghost fields (u>=v, loops) are inert; allEqual = chain equality along [0..N-1] = constancy; positive witnesses N=4 D=2/3 and N=6 D=2 verified by native_decide in-file, confirming the encoding admits the known physical constructions. answer(sorry) <-> (no-solution) encoding is faithful. Downward-closure in D means (10,3) implies this case.  
**Next action:** Open. For D=7>3 it would follow from the (10,3) case via the fork's generic color-restriction lemma; no known attack on the base case over C.

## `eqSystem10_no_solution_d8` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/Paper/MonochromaticQuantumGraph.lean:511`  
**Statement:** Is there no complex 8-color perfectly monochromatic weighting of K10?  
**Source:** Krenn-Gu conjecture: Krenn-Gu-Soltesz arXiv:1902.06023; MathOverflow 311325; Chandran-Gajjala arXiv:2202.05562; Chandran-Gajjala-Illickan-Krenn arXiv:2407.00303 (MFCS 2024); mariokrenn.wordpress.com/graph-theory-question  
**Statement matches intent:** yes  
**Known status:** Krenn-Gu conjecture (even N>=6, D>=3 => no perfectly monochromatic weighting) is open as of 2026-07. Known partial results: Bogdanov proved the nonnegative-real case (MO 311325); Chandran-Gajjala proved it for vertex connectivity <= 2 and cubic graphs (arXiv:2202.05562, arXiv:2407.00303); DeepMind agents formally proved the D=N and N=4,D>=4 complex cases (already marked solved in this file). This fork internally proved the N=6 integer/trinary cases (PR #96) via mod-2 SAT, which does NOT bear on C or R. D=10 (=N) case is already formally solved; 3<=D<=9 are open.  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** Formalization audited: pmSumListAux with fuel=length correctly enumerates perfect matchings pairing head with later vertices; only u<v edges with colors (iota u, iota v) are ever read, so unconstrained EdgeN ghost fields (u>=v, loops) are inert; allEqual = chain equality along [0..N-1] = constancy; positive witnesses N=4 D=2/3 and N=6 D=2 verified by native_decide in-file, confirming the encoding admits the known physical constructions. answer(sorry) <-> (no-solution) encoding is faithful. Downward-closure in D means (10,3) implies this case.  
**Next action:** Open. For D=8>3 it would follow from the (10,3) case via the fork's generic color-restriction lemma; no known attack on the base case over C.

## `eqSystem10_no_solution_d9` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/Paper/MonochromaticQuantumGraph.lean:519`  
**Statement:** Is there no complex 9-color perfectly monochromatic weighting of K10?  
**Source:** Krenn-Gu conjecture: Krenn-Gu-Soltesz arXiv:1902.06023; MathOverflow 311325; Chandran-Gajjala arXiv:2202.05562; Chandran-Gajjala-Illickan-Krenn arXiv:2407.00303 (MFCS 2024); mariokrenn.wordpress.com/graph-theory-question  
**Statement matches intent:** yes  
**Known status:** Krenn-Gu conjecture (even N>=6, D>=3 => no perfectly monochromatic weighting) is open as of 2026-07. Known partial results: Bogdanov proved the nonnegative-real case (MO 311325); Chandran-Gajjala proved it for vertex connectivity <= 2 and cubic graphs (arXiv:2202.05562, arXiv:2407.00303); DeepMind agents formally proved the D=N and N=4,D>=4 complex cases (already marked solved in this file). This fork internally proved the N=6 integer/trinary cases (PR #96) via mod-2 SAT, which does NOT bear on C or R. D=10 (=N) case is already formally solved; 3<=D<=9 are open.  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** Formalization audited: pmSumListAux with fuel=length correctly enumerates perfect matchings pairing head with later vertices; only u<v edges with colors (iota u, iota v) are ever read, so unconstrained EdgeN ghost fields (u>=v, loops) are inert; allEqual = chain equality along [0..N-1] = constancy; positive witnesses N=4 D=2/3 and N=6 D=2 verified by native_decide in-file, confirming the encoding admits the known physical constructions. answer(sorry) <-> (no-solution) encoding is faithful. Downward-closure in D means (10,3) implies this case.  
**Next action:** Open. For D=9>3 it would follow from the (10,3) case via the fork's generic color-restriction lemma; no known attack on the base case over C.

## `eqSystem12_no_solution_d3` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/Paper/MonochromaticQuantumGraph.lean:538`  
**Statement:** Is there no complex 3-color perfectly monochromatic weighting of K12?  
**Source:** Krenn-Gu conjecture: Krenn-Gu-Soltesz arXiv:1902.06023; MathOverflow 311325; Chandran-Gajjala arXiv:2202.05562; Chandran-Gajjala-Illickan-Krenn arXiv:2407.00303 (MFCS 2024); mariokrenn.wordpress.com/graph-theory-question  
**Statement matches intent:** yes  
**Known status:** Krenn-Gu conjecture (even N>=6, D>=3 => no perfectly monochromatic weighting) is open as of 2026-07. Known partial results: Bogdanov proved the nonnegative-real case (MO 311325); Chandran-Gajjala proved it for vertex connectivity <= 2 and cubic graphs (arXiv:2202.05562, arXiv:2407.00303); DeepMind agents formally proved the D=N and N=4,D>=4 complex cases (already marked solved in this file). This fork internally proved the N=6 integer/trinary cases (PR #96) via mod-2 SAT, which does NOT bear on C or R.  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Formalization audited: pmSumListAux with fuel=length correctly enumerates perfect matchings pairing head with later vertices; only u<v edges with colors (iota u, iota v) are ever read, so unconstrained EdgeN ghost fields (u>=v, loops) are inert; allEqual = chain equality along [0..N-1] = constancy; positive witnesses N=4 D=2/3 and N=6 D=2 verified by native_decide in-file, confirming the encoding admits the known physical constructions. answer(sorry) <-> (no-solution) encoding is faithful.  
**Next action:** Open instance of the general Krenn-Gu conjecture; no specific route known over C.

## `eqSystem14_no_solution_d3` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/Paper/MonochromaticQuantumGraph.lean:546`  
**Statement:** Is there no complex 3-color perfectly monochromatic weighting of K14?  
**Source:** Krenn-Gu conjecture: Krenn-Gu-Soltesz arXiv:1902.06023; MathOverflow 311325; Chandran-Gajjala arXiv:2202.05562; Chandran-Gajjala-Illickan-Krenn arXiv:2407.00303 (MFCS 2024); mariokrenn.wordpress.com/graph-theory-question  
**Statement matches intent:** yes  
**Known status:** Krenn-Gu conjecture (even N>=6, D>=3 => no perfectly monochromatic weighting) is open as of 2026-07. Known partial results: Bogdanov proved the nonnegative-real case (MO 311325); Chandran-Gajjala proved it for vertex connectivity <= 2 and cubic graphs (arXiv:2202.05562, arXiv:2407.00303); DeepMind agents formally proved the D=N and N=4,D>=4 complex cases (already marked solved in this file). This fork internally proved the N=6 integer/trinary cases (PR #96) via mod-2 SAT, which does NOT bear on C or R.  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Formalization audited: pmSumListAux with fuel=length correctly enumerates perfect matchings pairing head with later vertices; only u<v edges with colors (iota u, iota v) are ever read, so unconstrained EdgeN ghost fields (u>=v, loops) are inert; allEqual = chain equality along [0..N-1] = constancy; positive witnesses N=4 D=2/3 and N=6 D=2 verified by native_decide in-file, confirming the encoding admits the known physical constructions. answer(sorry) <-> (no-solution) encoding is faithful.  
**Next action:** Open instance of the general Krenn-Gu conjecture; no specific route known over C.

## `eqSystem16_no_solution_d3` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/Paper/MonochromaticQuantumGraph.lean:554`  
**Statement:** Is there no complex 3-color perfectly monochromatic weighting of K16?  
**Source:** Krenn-Gu conjecture: Krenn-Gu-Soltesz arXiv:1902.06023; MathOverflow 311325; Chandran-Gajjala arXiv:2202.05562; Chandran-Gajjala-Illickan-Krenn arXiv:2407.00303 (MFCS 2024); mariokrenn.wordpress.com/graph-theory-question  
**Statement matches intent:** yes  
**Known status:** Krenn-Gu conjecture (even N>=6, D>=3 => no perfectly monochromatic weighting) is open as of 2026-07. Known partial results: Bogdanov proved the nonnegative-real case (MO 311325); Chandran-Gajjala proved it for vertex connectivity <= 2 and cubic graphs (arXiv:2202.05562, arXiv:2407.00303); DeepMind agents formally proved the D=N and N=4,D>=4 complex cases (already marked solved in this file). This fork internally proved the N=6 integer/trinary cases (PR #96) via mod-2 SAT, which does NOT bear on C or R.  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Formalization audited: pmSumListAux with fuel=length correctly enumerates perfect matchings pairing head with later vertices; only u<v edges with colors (iota u, iota v) are ever read, so unconstrained EdgeN ghost fields (u>=v, loops) are inert; allEqual = chain equality along [0..N-1] = constancy; positive witnesses N=4 D=2/3 and N=6 D=2 verified by native_decide in-file, confirming the encoding admits the known physical constructions. answer(sorry) <-> (no-solution) encoding is faithful.  
**Next action:** Open instance of the general Krenn-Gu conjecture; no specific route known over C.

## `eqSystem6_no_solution_d3` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/Paper/MonochromaticQuantumGraph.lean:404`  
**Statement:** Is there no complex edge-weighting of K6 with 3 colors whose perfect-matching sums are 1 on the 3 monochromatic vertex colorings and 0 on all others (i.e. no 6-photon 3-dimensional GHZ graph)?  
**Source:** Krenn-Gu conjecture: Krenn-Gu-Soltesz arXiv:1902.06023; MathOverflow 311325; Chandran-Gajjala arXiv:2202.05562; Chandran-Gajjala-Illickan-Krenn arXiv:2407.00303 (MFCS 2024); mariokrenn.wordpress.com/graph-theory-question  
**Statement matches intent:** yes  
**Known status:** Krenn-Gu conjecture (even N>=6, D>=3 => no perfectly monochromatic weighting) is open as of 2026-07. Known partial results: Bogdanov proved the nonnegative-real case (MO 311325); Chandran-Gajjala proved it for vertex connectivity <= 2 and cubic graphs (arXiv:2202.05562, arXiv:2407.00303); DeepMind agents formally proved the D=N and N=4,D>=4 complex cases (already marked solved in this file). This fork internally proved the N=6 integer/trinary cases (PR #96) via mod-2 SAT, which does NOT bear on C or R. The (6,3) complex case is the flagship smallest open case (reward offered by Krenn).  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Formalization audited: pmSumListAux with fuel=length correctly enumerates perfect matchings pairing head with later vertices; only u<v edges with colors (iota u, iota v) are ever read, so unconstrained EdgeN ghost fields (u>=v, loops) are inert; allEqual = chain equality along [0..N-1] = constancy; positive witnesses N=4 D=2/3 and N=6 D=2 verified by native_decide in-file, confirming the encoding admits the known physical constructions. answer(sorry) <-> (no-solution) encoding is faithful. Extensive numerical searches by Krenn's group found no solution; no proof known.  
**Next action:** Track literature; explore transferring the formally-proved D=N argument downward, or a Nullstellensatz certificate over a symmetry-reduced variable set (135 complex vars, degree 3 - currently infeasible). Fork's mod-2 route provably cannot decide the complex case.

## `eqSystem6_no_solution_d3_int` — Already solved internally (cat 0)

**File:** `FormalConjectures/Paper/MonochromaticQuantumGraph.lean:658`  
**Statement:** Is there no integer edge-weighting of K6 with 3 colors satisfying the monochromatic quantum graph system? (Answer proved: True - no solution.)  
**Source:** Krenn-Gu conjecture: Krenn-Gu-Soltesz arXiv:1902.06023; MathOverflow 311325; Chandran-Gajjala arXiv:2202.05562; Chandran-Gajjala-Illickan-Krenn arXiv:2407.00303 (MFCS 2024); mariokrenn.wordpress.com/graph-theory-question  
**Statement matches intent:** yes  
**Known status:** Solved internally: fork PR #96 (merged 2026-07-22) adds QuantumGraphN6D3/ (47-orbit reflected LRAT certificates, mod-2 obstruction) + QuantumGraphColorRestriction.lean; campaign 'quantum-n6d3-color-restriction'. Upstream submission tracked as google-deepmind/formal-conjectures#4511 (not yet merged upstream; upstream master still marks it open). Not known in the literature as a published result.  
**Difficulty:** math 6/10, Lean 8/10 · **Compute:** medium · **Confidence:** high  
**Evidence:** QuantumGraphN6D3/QuantumGraphGlobal.lean proves no_eqSystem_zmod2 (47 S_6-orbit CNFs, reflected LRAT UNSAT certificates, semantic/parity/orbit bridges proved in Lean) and derives no_eqSystem_int by the ring hom Z -> ZMod 2 (pmSum commutes with semiring homs; RHS 0/1 preserved). Proof modules import the canonical FormalConjectures.Paper.MonochromaticQuantumGraph definitions (verified: no redefinition of EqSystemN/pmSum/WeightsN), so the proved proposition is exactly the negated existential of the audited decl; closing it needs only answer := True plus iff-intro. PR #96 merged into fork main 2026-07-22; audit workflow quantum_full_color_restriction_audit.yml replays verify.sh; PR #117 audit reports structural layer axiom-clean.  
**Flags:** proof depends on Lean.ofReduceBool/Lean.trustCompiler (native reflected LRAT), weaker than pure-kernel; 47 LRAT certificates not in repo: downloaded from third-party fork release, SHA-256 pinned; canonical decl still answer(sorry)/research open; FORMAL_CONJECTURES_STATUS_PATCH.diff unapplied; proof modules outside lake build (verify.sh + LEAN_PATH); cannot rebuild in this container; status patch flips only d5/ge3 variants; d3_int itself not in the diff though it is the campaign's core theorem; verifier:confirmed  
**Next action:** Set answer(True), wire QuantumGraphGlobal.no_eqSystem_int into the canonical decl (extend FORMAL_CONJECTURES_STATUS_PATCH.diff, which currently omits the d3 pair), re-run setup_certificates.sh + verify.sh, and track upstream PR google-deepmind#4511; consider a pure-kernel LRAT replay to drop ofReduceBool/trustCompiler.

## `eqSystem6_no_solution_d3_real` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/Paper/MonochromaticQuantumGraph.lean:590`  
**Statement:** Is there no real edge-weighting of K6 with 3 colors satisfying the monochromatic quantum graph system?  
**Source:** Krenn-Gu conjecture: Krenn-Gu-Soltesz arXiv:1902.06023; MathOverflow 311325; Chandran-Gajjala arXiv:2202.05562; Chandran-Gajjala-Illickan-Krenn arXiv:2407.00303 (MFCS 2024); mariokrenn.wordpress.com/graph-theory-question  
**Statement matches intent:** yes  
**Known status:** Krenn-Gu conjecture (even N>=6, D>=3 => no perfectly monochromatic weighting) is open as of 2026-07. Known partial results: Bogdanov proved the nonnegative-real case (MO 311325); Chandran-Gajjala proved it for vertex connectivity <= 2 and cubic graphs (arXiv:2202.05562, arXiv:2407.00303); DeepMind agents formally proved the D=N and N=4,D>=4 complex cases (already marked solved in this file). This fork internally proved the N=6 integer/trinary cases (PR #96) via mod-2 SAT, which does NOT bear on C or R. Over R the mod-2 route is unavailable and Bogdanov's argument needs nonnegativity, so the real case is essentially as hard as the complex one (and implied by it).  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Formalization audited: pmSumListAux with fuel=length correctly enumerates perfect matchings pairing head with later vertices; only u<v edges with colors (iota u, iota v) are ever read, so unconstrained EdgeN ghost fields (u>=v, loops) are inert; allEqual = chain equality along [0..N-1] = constancy; positive witnesses N=4 D=2/3 and N=6 D=2 verified by native_decide in-file, confirming the encoding admits the known physical constructions. answer(sorry) <-> (no-solution) encoding is faithful.  
**Next action:** Open. Bogdanov's R>=0 obstruction (recorded in-file) does not extend to signed weights; fork's integer result does not extend to R.

## `eqSystem6_no_solution_d3_trinary_int` — Already solved internally (cat 0)

**File:** `FormalConjectures/Paper/MonochromaticQuantumGraph.lean:727`  
**Statement:** Is there no {-1,0,1}-valued edge-weighting of K6 with 3 colors satisfying the system? (Answer proved: True.)  
**Source:** Krenn-Gu conjecture: Krenn-Gu-Soltesz arXiv:1902.06023; MathOverflow 311325; Chandran-Gajjala arXiv:2202.05562; Chandran-Gajjala-Illickan-Krenn arXiv:2407.00303 (MFCS 2024); mariokrenn.wordpress.com/graph-theory-question  
**Statement matches intent:** yes  
**Known status:** Solved internally: fork PR #96 (merged 2026-07-22) adds QuantumGraphN6D3/ (47-orbit reflected LRAT certificates, mod-2 obstruction) + QuantumGraphColorRestriction.lean; campaign 'quantum-n6d3-color-restriction'. Upstream submission tracked as google-deepmind/formal-conjectures#4511 (not yet merged upstream; upstream master still marks it open). Not known in the literature as a published result.  
**Difficulty:** math 5/10, Lean 8/10 · **Compute:** medium · **Confidence:** high  
**Evidence:** QuantumGraphN6D3/QuantumGraphGlobal.lean proves no_eqSystem_zmod2 (47 S_6-orbit CNFs, reflected LRAT UNSAT certificates, semantic/parity/orbit bridges proved in Lean) and derives no_eqSystem_int by the ring hom Z -> ZMod 2 (pmSum commutes with semiring homs; RHS 0/1 preserved). Proof modules import the canonical FormalConjectures.Paper.MonochromaticQuantumGraph definitions (verified: no redefinition of EqSystemN/pmSum/WeightsN), so the proved proposition is exactly the negated existential of the audited decl; closing it needs only answer := True plus iff-intro. PR #96 merged into fork main 2026-07-22; audit workflow quantum_full_color_restriction_audit.yml replays verify.sh; PR #117 audit reports structural layer axiom-clean. no_eqSystem_trinary_int matches the audited statement verbatim (trinary witnesses are integer witnesses). Trinary restriction over ghost edges is harmless since any solution can zero unread edges - checked.  
**Flags:** proof depends on Lean.ofReduceBool/Lean.trustCompiler (native reflected LRAT), weaker than pure-kernel; 47 LRAT certificates not in repo: downloaded from third-party fork release, SHA-256 pinned; canonical decl still answer(sorry)/research open; FORMAL_CONJECTURES_STATUS_PATCH.diff unapplied; proof modules outside lake build (verify.sh + LEAN_PATH); cannot rebuild in this container; status patch omits this decl though the theorem exists; verifier:confirmed  
**Next action:** Wire QuantumGraphGlobal.no_eqSystem_trinary_int (verbatim statement match, immediate corollary of the Z result) into the canonical decl; extend the status patch, which omits the d3 trinary decl.

## `eqSystem6_no_solution_d4` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/Paper/MonochromaticQuantumGraph.lean:413`  
**Statement:** Same non-existence question for K6 with 4 colors over C.  
**Source:** Krenn-Gu conjecture: Krenn-Gu-Soltesz arXiv:1902.06023; MathOverflow 311325; Chandran-Gajjala arXiv:2202.05562; Chandran-Gajjala-Illickan-Krenn arXiv:2407.00303 (MFCS 2024); mariokrenn.wordpress.com/graph-theory-question  
**Statement matches intent:** yes  
**Known status:** Krenn-Gu conjecture (even N>=6, D>=3 => no perfectly monochromatic weighting) is open as of 2026-07. Known partial results: Bogdanov proved the nonnegative-real case (MO 311325); Chandran-Gajjala proved it for vertex connectivity <= 2 and cubic graphs (arXiv:2202.05562, arXiv:2407.00303); DeepMind agents formally proved the D=N and N=4,D>=4 complex cases (already marked solved in this file). This fork internally proved the N=6 integer/trinary cases (PR #96) via mod-2 SAT, which does NOT bear on C or R. Implied by the (6,3) case via color restriction; D=6 case is already formally solved.  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Formalization audited: pmSumListAux with fuel=length correctly enumerates perfect matchings pairing head with later vertices; only u<v edges with colors (iota u, iota v) are ever read, so unconstrained EdgeN ghost fields (u>=v, loops) are inert; allEqual = chain equality along [0..N-1] = constancy; positive witnesses N=4 D=2/3 and N=6 D=2 verified by native_decide in-file, confirming the encoding admits the known physical constructions. answer(sorry) <-> (no-solution) encoding is faithful. Fork's QuantumGraphColorRestriction.lean proves solvability is downward-closed in D over any semiring, so (6,3) => (6,4); the base case is open.  
**Next action:** Would follow from (6,3) via the fork's generic no_solution_of_color_le (works over any semiring); alternatively attack directly. First milestone: any proof for some D in {3,4,5} at N=6 over C.

## `eqSystem6_no_solution_d5` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/Paper/MonochromaticQuantumGraph.lean:422`  
**Statement:** Same non-existence question for K6 with 5 colors over C.  
**Source:** Krenn-Gu conjecture: Krenn-Gu-Soltesz arXiv:1902.06023; MathOverflow 311325; Chandran-Gajjala arXiv:2202.05562; Chandran-Gajjala-Illickan-Krenn arXiv:2407.00303 (MFCS 2024); mariokrenn.wordpress.com/graph-theory-question  
**Statement matches intent:** yes  
**Known status:** Krenn-Gu conjecture (even N>=6, D>=3 => no perfectly monochromatic weighting) is open as of 2026-07. Known partial results: Bogdanov proved the nonnegative-real case (MO 311325); Chandran-Gajjala proved it for vertex connectivity <= 2 and cubic graphs (arXiv:2202.05562, arXiv:2407.00303); DeepMind agents formally proved the D=N and N=4,D>=4 complex cases (already marked solved in this file). This fork internally proved the N=6 integer/trinary cases (PR #96) via mod-2 SAT, which does NOT bear on C or R. Implied by the (6,3) case via color restriction; D=6 case already formally solved.  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Formalization audited: pmSumListAux with fuel=length correctly enumerates perfect matchings pairing head with later vertices; only u<v edges with colors (iota u, iota v) are ever read, so unconstrained EdgeN ghost fields (u>=v, loops) are inert; allEqual = chain equality along [0..N-1] = constancy; positive witnesses N=4 D=2/3 and N=6 D=2 verified by native_decide in-file, confirming the encoding admits the known physical constructions. answer(sorry) <-> (no-solution) encoding is faithful. Downward-closure lemma exists in fork (generic alpha); base case open.  
**Next action:** Same as (6,4): follows from (6,3) if that is ever proved; open.

## `eqSystem6_no_solution_d5_int` — Already solved internally (cat 0)

**File:** `FormalConjectures/Paper/MonochromaticQuantumGraph.lean:666`  
**Statement:** Is there no integer solution for K6 with 5 colors? (Answer proved: True.)  
**Source:** Krenn-Gu conjecture: Krenn-Gu-Soltesz arXiv:1902.06023; MathOverflow 311325; Chandran-Gajjala arXiv:2202.05562; Chandran-Gajjala-Illickan-Krenn arXiv:2407.00303 (MFCS 2024); mariokrenn.wordpress.com/graph-theory-question  
**Statement matches intent:** yes  
**Known status:** Solved internally: fork PR #96 (merged 2026-07-22) adds QuantumGraphN6D3/ (47-orbit reflected LRAT certificates, mod-2 obstruction) + QuantumGraphColorRestriction.lean; campaign 'quantum-n6d3-color-restriction'. Upstream submission tracked as google-deepmind/formal-conjectures#4511 (not yet merged upstream; upstream master still marks it open). Not known in the literature as a published result.  
**Difficulty:** math 6/10, Lean 8/10 · **Compute:** medium · **Confidence:** high  
**Evidence:** QuantumGraphN6D3/QuantumGraphGlobal.lean proves no_eqSystem_zmod2 (47 S_6-orbit CNFs, reflected LRAT UNSAT certificates, semantic/parity/orbit bridges proved in Lean) and derives no_eqSystem_int by the ring hom Z -> ZMod 2 (pmSum commutes with semiring homs; RHS 0/1 preserved). Proof modules import the canonical FormalConjectures.Paper.MonochromaticQuantumGraph definitions (verified: no redefinition of EqSystemN/pmSum/WeightsN), so the proved proposition is exactly the negated existential of the audited decl; closing it needs only answer := True plus iff-intro. PR #96 merged into fork main 2026-07-22; audit workflow quantum_full_color_restriction_audit.yml replays verify.sh; PR #117 audit reports structural layer axiom-clean. QuantumGraphColorRestriction.no_eqSystem6_d5_int matches the audited statement verbatim (restriction of 5-color solutions to 3 colors).  
**Flags:** proof depends on Lean.ofReduceBool/Lean.trustCompiler (native reflected LRAT), weaker than pure-kernel; 47 LRAT certificates not in repo: downloaded from third-party fork release, SHA-256 pinned; canonical decl still answer(sorry)/research open; FORMAL_CONJECTURES_STATUS_PATCH.diff unapplied; proof modules outside lake build (verify.sh + LEAN_PATH); cannot rebuild in this container; verifier:confirmed  
**Next action:** Apply FORMAL_CONJECTURES_STATUS_PATCH.diff (targets exactly this decl, answer := True, formal_proof link to QuantumGraphColorRestriction.lean no_eqSystem6_d5_int) after re-running verify.sh.

## `eqSystem6_no_solution_d5_real` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/Paper/MonochromaticQuantumGraph.lean:598`  
**Statement:** Same non-existence question for K6 with 5 colors over R.  
**Source:** Krenn-Gu conjecture: Krenn-Gu-Soltesz arXiv:1902.06023; MathOverflow 311325; Chandran-Gajjala arXiv:2202.05562; Chandran-Gajjala-Illickan-Krenn arXiv:2407.00303 (MFCS 2024); mariokrenn.wordpress.com/graph-theory-question  
**Statement matches intent:** yes  
**Known status:** Krenn-Gu conjecture (even N>=6, D>=3 => no perfectly monochromatic weighting) is open as of 2026-07. Known partial results: Bogdanov proved the nonnegative-real case (MO 311325); Chandran-Gajjala proved it for vertex connectivity <= 2 and cubic graphs (arXiv:2202.05562, arXiv:2407.00303); DeepMind agents formally proved the D=N and N=4,D>=4 complex cases (already marked solved in this file). This fork internally proved the N=6 integer/trinary cases (PR #96) via mod-2 SAT, which does NOT bear on C or R. Over R the mod-2 route is unavailable and Bogdanov's argument needs nonnegativity, so the real case is essentially as hard as the complex one (and implied by it).  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Formalization audited: pmSumListAux with fuel=length correctly enumerates perfect matchings pairing head with later vertices; only u<v edges with colors (iota u, iota v) are ever read, so unconstrained EdgeN ghost fields (u>=v, loops) are inert; allEqual = chain equality along [0..N-1] = constancy; positive witnesses N=4 D=2/3 and N=6 D=2 verified by native_decide in-file, confirming the encoding admits the known physical constructions. answer(sorry) <-> (no-solution) encoding is faithful. Downward-closure lemma applies verbatim to alpha = R.  
**Next action:** Follows from the (6,3) real case via the fork's generic color-restriction lemma; base case open.

## `eqSystem6_no_solution_d5_trinary_int` — Already solved internally (cat 0)

**File:** `FormalConjectures/Paper/MonochromaticQuantumGraph.lean:737`  
**Statement:** Is there no {-1,0,1}-valued solution for K6 with 5 colors? (Answer proved: True.)  
**Source:** Krenn-Gu conjecture: Krenn-Gu-Soltesz arXiv:1902.06023; MathOverflow 311325; Chandran-Gajjala arXiv:2202.05562; Chandran-Gajjala-Illickan-Krenn arXiv:2407.00303 (MFCS 2024); mariokrenn.wordpress.com/graph-theory-question  
**Statement matches intent:** yes  
**Known status:** Solved internally: fork PR #96 (merged 2026-07-22) adds QuantumGraphN6D3/ (47-orbit reflected LRAT certificates, mod-2 obstruction) + QuantumGraphColorRestriction.lean; campaign 'quantum-n6d3-color-restriction'. Upstream submission tracked as google-deepmind/formal-conjectures#4511 (not yet merged upstream; upstream master still marks it open). Not known in the literature as a published result.  
**Difficulty:** math 5/10, Lean 8/10 · **Compute:** medium · **Confidence:** high  
**Evidence:** QuantumGraphN6D3/QuantumGraphGlobal.lean proves no_eqSystem_zmod2 (47 S_6-orbit CNFs, reflected LRAT UNSAT certificates, semantic/parity/orbit bridges proved in Lean) and derives no_eqSystem_int by the ring hom Z -> ZMod 2 (pmSum commutes with semiring homs; RHS 0/1 preserved). Proof modules import the canonical FormalConjectures.Paper.MonochromaticQuantumGraph definitions (verified: no redefinition of EqSystemN/pmSum/WeightsN), so the proved proposition is exactly the negated existential of the audited decl; closing it needs only answer := True plus iff-intro. PR #96 merged into fork main 2026-07-22; audit workflow quantum_full_color_restriction_audit.yml replays verify.sh; PR #117 audit reports structural layer axiom-clean. no_eqSystem6_d5_trinary_int matches verbatim; pointwise restriction preserved by color restriction (no_pointwise_solution_of_color_le).  
**Flags:** proof depends on Lean.ofReduceBool/Lean.trustCompiler (native reflected LRAT), weaker than pure-kernel; 47 LRAT certificates not in repo: downloaded from third-party fork release, SHA-256 pinned; canonical decl still answer(sorry)/research open; FORMAL_CONJECTURES_STATUS_PATCH.diff unapplied; proof modules outside lake build (verify.sh + LEAN_PATH); cannot rebuild in this container; verifier:confirmed  
**Next action:** Apply FORMAL_CONJECTURES_STATUS_PATCH.diff (targets this decl via no_eqSystem6_d5_trinary_int).

## `eqSystem6_no_solution_ge3` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/Paper/MonochromaticQuantumGraph.lean:442`  
**Statement:** For N=6 and every D>=3, is there no complex solution to the monochromatic quantum graph system?  
**Source:** Krenn-Gu conjecture: Krenn-Gu-Soltesz arXiv:1902.06023; MathOverflow 311325; Chandran-Gajjala arXiv:2202.05562; Chandran-Gajjala-Illickan-Krenn arXiv:2407.00303 (MFCS 2024); mariokrenn.wordpress.com/graph-theory-question  
**Statement matches intent:** yes  
**Known status:** Krenn-Gu conjecture (even N>=6, D>=3 => no perfectly monochromatic weighting) is open as of 2026-07. Known partial results: Bogdanov proved the nonnegative-real case (MO 311325); Chandran-Gajjala proved it for vertex connectivity <= 2 and cubic graphs (arXiv:2202.05562, arXiv:2407.00303); DeepMind agents formally proved the D=N and N=4,D>=4 complex cases (already marked solved in this file). This fork internally proved the N=6 integer/trinary cases (PR #96) via mod-2 SAT, which does NOT bear on C or R.  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Formalization audited: pmSumListAux with fuel=length correctly enumerates perfect matchings pairing head with later vertices; only u<v edges with colors (iota u, iota v) are ever read, so unconstrained EdgeN ghost fields (u>=v, loops) are inert; allEqual = chain equality along [0..N-1] = constancy; positive witnesses N=4 D=2/3 and N=6 D=2 verified by native_decide in-file, confirming the encoding admits the known physical constructions. answer(sorry) <-> (no-solution) encoding is faithful. QuantumGraphColorRestriction.no_solution_ge_iff_base reduces the whole family to D=3; that base case is the open prize question.  
**Next action:** Formally equivalent to the single (6,3) case via the fork's no_solution_ge_iff_base (generic semiring); so resolving (6,3) over C closes this too.

## `eqSystem6_no_solution_ge3_int` — Already solved internally (cat 0)

**File:** `FormalConjectures/Paper/MonochromaticQuantumGraph.lean:674`  
**Statement:** For N=6 and every D>=3, is there no integer solution? (Answer proved: True.)  
**Source:** Krenn-Gu conjecture: Krenn-Gu-Soltesz arXiv:1902.06023; MathOverflow 311325; Chandran-Gajjala arXiv:2202.05562; Chandran-Gajjala-Illickan-Krenn arXiv:2407.00303 (MFCS 2024); mariokrenn.wordpress.com/graph-theory-question  
**Statement matches intent:** yes  
**Known status:** Solved internally: fork PR #96 (merged 2026-07-22) adds QuantumGraphN6D3/ (47-orbit reflected LRAT certificates, mod-2 obstruction) + QuantumGraphColorRestriction.lean; campaign 'quantum-n6d3-color-restriction'. Upstream submission tracked as google-deepmind/formal-conjectures#4511 (not yet merged upstream; upstream master still marks it open). Not known in the literature as a published result.  
**Difficulty:** math 6/10, Lean 8/10 · **Compute:** medium · **Confidence:** high  
**Evidence:** QuantumGraphN6D3/QuantumGraphGlobal.lean proves no_eqSystem_zmod2 (47 S_6-orbit CNFs, reflected LRAT UNSAT certificates, semantic/parity/orbit bridges proved in Lean) and derives no_eqSystem_int by the ring hom Z -> ZMod 2 (pmSum commutes with semiring homs; RHS 0/1 preserved). Proof modules import the canonical FormalConjectures.Paper.MonochromaticQuantumGraph definitions (verified: no redefinition of EqSystemN/pmSum/WeightsN), so the proved proposition is exactly the negated existential of the audited decl; closing it needs only answer := True plus iff-intro. PR #96 merged into fork main 2026-07-22; audit workflow quantum_full_color_restriction_audit.yml replays verify.sh; PR #117 audit reports structural layer axiom-clean. no_eqSystem6_ge3_int : forall D >= 3, no integer solution - verbatim match via downward-closure of solvability in D.  
**Flags:** proof depends on Lean.ofReduceBool/Lean.trustCompiler (native reflected LRAT), weaker than pure-kernel; 47 LRAT certificates not in repo: downloaded from third-party fork release, SHA-256 pinned; canonical decl still answer(sorry)/research open; FORMAL_CONJECTURES_STATUS_PATCH.diff unapplied; proof modules outside lake build (verify.sh + LEAN_PATH); cannot rebuild in this container; verifier:confirmed  
**Next action:** Apply the status patch (no_eqSystem6_ge3_int gives exactly the universally quantified statement) after certificate replay.

## `eqSystem6_no_solution_ge3_real` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/Paper/MonochromaticQuantumGraph.lean:606`  
**Statement:** For N=6 and every D>=3, is there no real solution?  
**Source:** Krenn-Gu conjecture: Krenn-Gu-Soltesz arXiv:1902.06023; MathOverflow 311325; Chandran-Gajjala arXiv:2202.05562; Chandran-Gajjala-Illickan-Krenn arXiv:2407.00303 (MFCS 2024); mariokrenn.wordpress.com/graph-theory-question  
**Statement matches intent:** yes  
**Known status:** Krenn-Gu conjecture (even N>=6, D>=3 => no perfectly monochromatic weighting) is open as of 2026-07. Known partial results: Bogdanov proved the nonnegative-real case (MO 311325); Chandran-Gajjala proved it for vertex connectivity <= 2 and cubic graphs (arXiv:2202.05562, arXiv:2407.00303); DeepMind agents formally proved the D=N and N=4,D>=4 complex cases (already marked solved in this file). This fork internally proved the N=6 integer/trinary cases (PR #96) via mod-2 SAT, which does NOT bear on C or R. Over R the mod-2 route is unavailable and Bogdanov's argument needs nonnegativity, so the real case is essentially as hard as the complex one (and implied by it).  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Formalization audited: pmSumListAux with fuel=length correctly enumerates perfect matchings pairing head with later vertices; only u<v edges with colors (iota u, iota v) are ever read, so unconstrained EdgeN ghost fields (u>=v, loops) are inert; allEqual = chain equality along [0..N-1] = constancy; positive witnesses N=4 D=2/3 and N=6 D=2 verified by native_decide in-file, confirming the encoding admits the known physical constructions. answer(sorry) <-> (no-solution) encoding is faithful.  
**Next action:** Formally equivalent to the (6,3) real case via no_solution_ge_iff_base (generic semiring).

## `eqSystem6_no_solution_ge3_trinary_int` — Already solved internally (cat 0)

**File:** `FormalConjectures/Paper/MonochromaticQuantumGraph.lean:747`  
**Statement:** For N=6 and every D>=3, is there no {-1,0,1}-valued solution? (Answer proved: True.)  
**Source:** Krenn-Gu conjecture: Krenn-Gu-Soltesz arXiv:1902.06023; MathOverflow 311325; Chandran-Gajjala arXiv:2202.05562; Chandran-Gajjala-Illickan-Krenn arXiv:2407.00303 (MFCS 2024); mariokrenn.wordpress.com/graph-theory-question  
**Statement matches intent:** yes  
**Known status:** Solved internally: fork PR #96 (merged 2026-07-22) adds QuantumGraphN6D3/ (47-orbit reflected LRAT certificates, mod-2 obstruction) + QuantumGraphColorRestriction.lean; campaign 'quantum-n6d3-color-restriction'. Upstream submission tracked as google-deepmind/formal-conjectures#4511 (not yet merged upstream; upstream master still marks it open). Not known in the literature as a published result.  
**Difficulty:** math 5/10, Lean 8/10 · **Compute:** medium · **Confidence:** high  
**Evidence:** QuantumGraphN6D3/QuantumGraphGlobal.lean proves no_eqSystem_zmod2 (47 S_6-orbit CNFs, reflected LRAT UNSAT certificates, semantic/parity/orbit bridges proved in Lean) and derives no_eqSystem_int by the ring hom Z -> ZMod 2 (pmSum commutes with semiring homs; RHS 0/1 preserved). Proof modules import the canonical FormalConjectures.Paper.MonochromaticQuantumGraph definitions (verified: no redefinition of EqSystemN/pmSum/WeightsN), so the proved proposition is exactly the negated existential of the audited decl; closing it needs only answer := True plus iff-intro. PR #96 merged into fork main 2026-07-22; audit workflow quantum_full_color_restriction_audit.yml replays verify.sh; PR #117 audit reports structural layer axiom-clean.  
**Flags:** proof depends on Lean.ofReduceBool/Lean.trustCompiler (native reflected LRAT), weaker than pure-kernel; 47 LRAT certificates not in repo: downloaded from third-party fork release, SHA-256 pinned; canonical decl still answer(sorry)/research open; FORMAL_CONJECTURES_STATUS_PATCH.diff unapplied; proof modules outside lake build (verify.sh + LEAN_PATH); cannot rebuild in this container; verifier:confirmed  
**Next action:** Apply the status patch (no_eqSystem6_ge3_trinary_int matches verbatim).

## `eqSystem8_no_solution_d3` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/Paper/MonochromaticQuantumGraph.lean:451`  
**Statement:** Is there no complex 3-color perfectly monochromatic weighting of K8?  
**Source:** Krenn-Gu conjecture: Krenn-Gu-Soltesz arXiv:1902.06023; MathOverflow 311325; Chandran-Gajjala arXiv:2202.05562; Chandran-Gajjala-Illickan-Krenn arXiv:2407.00303 (MFCS 2024); mariokrenn.wordpress.com/graph-theory-question  
**Statement matches intent:** yes  
**Known status:** Krenn-Gu conjecture (even N>=6, D>=3 => no perfectly monochromatic weighting) is open as of 2026-07. Known partial results: Bogdanov proved the nonnegative-real case (MO 311325); Chandran-Gajjala proved it for vertex connectivity <= 2 and cubic graphs (arXiv:2202.05562, arXiv:2407.00303); DeepMind agents formally proved the D=N and N=4,D>=4 complex cases (already marked solved in this file). This fork internally proved the N=6 integer/trinary cases (PR #96) via mod-2 SAT, which does NOT bear on C or R.  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Formalization audited: pmSumListAux with fuel=length correctly enumerates perfect matchings pairing head with later vertices; only u<v edges with colors (iota u, iota v) are ever read, so unconstrained EdgeN ghost fields (u>=v, loops) are inert; allEqual = chain equality along [0..N-1] = constancy; positive witnesses N=4 D=2/3 and N=6 D=2 verified by native_decide in-file, confirming the encoding admits the known physical constructions. answer(sorry) <-> (no-solution) encoding is faithful.  
**Next action:** Open; no route beyond the general Krenn-Gu program. Watch for extensions of the formal D=N technique.

## `eqSystem8_no_solution_d3_int` — Computationally solvable with certificate (cat 6)

**File:** `FormalConjectures/Paper/MonochromaticQuantumGraph.lean:683`  
**Secondary category:** 8 (Deep but approachable research problem)  
**Statement:** Is there no integer edge-weighting of K8 with 3 colors satisfying the system?  
**Source:** Krenn-Gu conjecture: Krenn-Gu-Soltesz arXiv:1902.06023; MathOverflow 311325; Chandran-Gajjala arXiv:2202.05562; Chandran-Gajjala-Illickan-Krenn arXiv:2407.00303 (MFCS 2024); mariokrenn.wordpress.com/graph-theory-question  
**Statement matches intent:** yes  
**Known status:** Open in the literature; not covered by the fork's N=6 campaign. The fork's mod-2 reduction strategy applies verbatim to N=8.  
**Difficulty:** math 6/10, Lean 8/10 · **Compute:** large · **Confidence:** medium  
**Evidence:** The whole N=6 proof architecture (parity lemma: monochromatic equations force odd perfect-matching count on the color-0 diagonal support; orbit classification; semantic CNF bridge) is N-generic in design; only the finite enumeration and certificates must be redone at larger scale (S_8 orbit count and CNF sizes grow sharply but stay SAT-feasible).  
**Flags:** resolution contingent on mod-2 UNSAT holding at N=8; otherwise route fails without deciding the Z case  
**Next action:** Extend the QuantumGraphN6D3 pipeline: reduce mod 2 (ring hom argument is N-generic), classify odd-perfect-matching diagonal supports of K8 up to S_8, emit one CNF per orbit (252 GF(2) weight variables, 6561 coloring equations, 105 degree-4 GF(2) monomials each), run CaDiCaL, and check LRAT reflectively. Contingent on the mod-2 system actually being UNSAT for N=8 (expected, unverified); a mod-2 SAT witness would leave the Z case open.

## `eqSystem8_no_solution_d3_real` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/Paper/MonochromaticQuantumGraph.lean:615`  
**Statement:** Is there no real 3-color perfectly monochromatic weighting of K8?  
**Source:** Krenn-Gu conjecture: Krenn-Gu-Soltesz arXiv:1902.06023; MathOverflow 311325; Chandran-Gajjala arXiv:2202.05562; Chandran-Gajjala-Illickan-Krenn arXiv:2407.00303 (MFCS 2024); mariokrenn.wordpress.com/graph-theory-question  
**Statement matches intent:** yes  
**Known status:** Krenn-Gu conjecture (even N>=6, D>=3 => no perfectly monochromatic weighting) is open as of 2026-07. Known partial results: Bogdanov proved the nonnegative-real case (MO 311325); Chandran-Gajjala proved it for vertex connectivity <= 2 and cubic graphs (arXiv:2202.05562, arXiv:2407.00303); DeepMind agents formally proved the D=N and N=4,D>=4 complex cases (already marked solved in this file). This fork internally proved the N=6 integer/trinary cases (PR #96) via mod-2 SAT, which does NOT bear on C or R. Over R the mod-2 route is unavailable and Bogdanov's argument needs nonnegativity, so the real case is essentially as hard as the complex one (and implied by it).  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Formalization audited: pmSumListAux with fuel=length correctly enumerates perfect matchings pairing head with later vertices; only u<v edges with colors (iota u, iota v) are ever read, so unconstrained EdgeN ghost fields (u>=v, loops) are inert; allEqual = chain equality along [0..N-1] = constancy; positive witnesses N=4 D=2/3 and N=6 D=2 verified by native_decide in-file, confirming the encoding admits the known physical constructions. answer(sorry) <-> (no-solution) encoding is faithful.  
**Next action:** Open; no specific route.

## `eqSystem8_no_solution_d3_trinary_int` — Computationally solvable with certificate (cat 6)

**File:** `FormalConjectures/Paper/MonochromaticQuantumGraph.lean:758`  
**Secondary category:** 8 (Deep but approachable research problem)  
**Statement:** Is there no {-1,0,1}-valued edge-weighting of K8 with 3 colors satisfying the system?  
**Source:** Krenn-Gu conjecture: Krenn-Gu-Soltesz arXiv:1902.06023; MathOverflow 311325; Chandran-Gajjala arXiv:2202.05562; Chandran-Gajjala-Illickan-Krenn arXiv:2407.00303 (MFCS 2024); mariokrenn.wordpress.com/graph-theory-question  
**Statement matches intent:** yes  
**Known status:** Open; implied by the (open) N=8 integer case and by the mod-2 route.  
**Difficulty:** math 5/10, Lean 8/10 · **Compute:** large · **Confidence:** medium  
**Evidence:** Fully finite problem (3^252 assignments) so certificate-based resolution is structurally guaranteed to be possible in principle; mod-2 route is the practical path.  
**Flags:** resolution contingent on mod-2 UNSAT at N=8 (else fall back to exact ternary SAT encoding, much larger)  
**Next action:** Follows for free from any N=8 integer resolution (trinary subset of Z); or attack directly as a finite CSP - but the mod-2 SAT route is strictly easier and already suffices, so extend the N=6 pipeline as for eqSystem8_no_solution_d3_int.

## `eqSystem_no_solution_ge6_ge3` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Paper/MonochromaticQuantumGraph.lean:564`  
**Statement:** The full Krenn-Gu conjecture over C: for every even N>=6 and D>=3 there is no perfectly monochromatic edge-weighting of K_N (equivalently, no linear-optics GHZ state of dimension >=3 with >=6 photons from perfect-matching interference).  
**Source:** Krenn-Gu conjecture: Krenn-Gu-Soltesz arXiv:1902.06023; MathOverflow 311325; Chandran-Gajjala arXiv:2202.05562; Chandran-Gajjala-Illickan-Krenn arXiv:2407.00303 (MFCS 2024); mariokrenn.wordpress.com/graph-theory-question  
**Statement matches intent:** yes  
**Known status:** Krenn-Gu conjecture (even N>=6, D>=3 => no perfectly monochromatic weighting) is open as of 2026-07. Known partial results: Bogdanov proved the nonnegative-real case (MO 311325); Chandran-Gajjala proved it for vertex connectivity <= 2 and cubic graphs (arXiv:2202.05562, arXiv:2407.00303); DeepMind agents formally proved the D=N and N=4,D>=4 complex cases (already marked solved in this file). This fork internally proved the N=6 integer/trinary cases (PR #96) via mod-2 SAT, which does NOT bear on C or R. This is the general conjecture itself, open since 2017/2019 with a monetary reward.  
**Difficulty:** math 9/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Formalization audited: pmSumListAux with fuel=length correctly enumerates perfect matchings pairing head with later vertices; only u<v edges with colors (iota u, iota v) are ever read, so unconstrained EdgeN ghost fields (u>=v, loops) are inert; allEqual = chain equality along [0..N-1] = constancy; positive witnesses N=4 D=2/3 and N=6 D=2 verified by native_decide in-file, confirming the encoding admits the known physical constructions. answer(sorry) <-> (no-solution) encoding is faithful. Chandran-Gajjala-Illickan-Krenn (MFCS 2024) explicitly state the general conjecture remains open.  
**Next action:** Recognized open problem; realistic progress = new graph classes (extending connectivity<=2 / cubic / sparse results) or the N=6 base cases. Fork lemma reduces D to 3 for each N but the N-family remains infinite.

## `eqSystem_no_solution_ge6_ge3_int` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/Paper/MonochromaticQuantumGraph.lean:700`  
**Statement:** For every even N>=6 and D>=3, is there no integer solution (Krenn-Gu over Z)?  
**Source:** Krenn-Gu conjecture: Krenn-Gu-Soltesz arXiv:1902.06023; MathOverflow 311325; Chandran-Gajjala arXiv:2202.05562; Chandran-Gajjala-Illickan-Krenn arXiv:2407.00303 (MFCS 2024); mariokrenn.wordpress.com/graph-theory-question  
**Statement matches intent:** yes  
**Known status:** Open. Fork solved the N=6 slice (all D>=3); the infinite N-family needs a uniform argument. Not in the literature.  
**Difficulty:** math 7/10, Lean 9/10 · **Compute:** large · **Confidence:** medium  
**Evidence:** Internal base case N=6 done (PR #96); combinatorial mod-2 statement looks like a tractable research target, far easier than the complex conjecture.  
**Flags:** would be a publishable new partial result toward Krenn-Gu if the uniform mod-2 argument works  
**Next action:** Promising avenue: prove the mod-2 obstruction uniformly in N (the parity lemma forcing an odd perfect-matching diagonal support is already N-generic; what is missing is a general theorem that no odd-support graph on N>=6 vertices satisfies the boolean system). The fork's no_solution_even_ge6_ge3_iff_d3 already reduces D to 3 for each N.

## `eqSystem_no_solution_ge6_ge3_real` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Paper/MonochromaticQuantumGraph.lean:633`  
**Statement:** The Krenn-Gu conjecture restricted to real weights: for every even N>=6, D>=3, no real solution.  
**Source:** Krenn-Gu conjecture: Krenn-Gu-Soltesz arXiv:1902.06023; MathOverflow 311325; Chandran-Gajjala arXiv:2202.05562; Chandran-Gajjala-Illickan-Krenn arXiv:2407.00303 (MFCS 2024); mariokrenn.wordpress.com/graph-theory-question  
**Statement matches intent:** yes  
**Known status:** Krenn-Gu conjecture (even N>=6, D>=3 => no perfectly monochromatic weighting) is open as of 2026-07. Known partial results: Bogdanov proved the nonnegative-real case (MO 311325); Chandran-Gajjala proved it for vertex connectivity <= 2 and cubic graphs (arXiv:2202.05562, arXiv:2407.00303); DeepMind agents formally proved the D=N and N=4,D>=4 complex cases (already marked solved in this file). This fork internally proved the N=6 integer/trinary cases (PR #96) via mod-2 SAT, which does NOT bear on C or R. Over R the mod-2 route is unavailable and Bogdanov's argument needs nonnegativity, so the real case is essentially as hard as the complex one (and implied by it).  
**Difficulty:** math 9/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Formalization audited: pmSumListAux with fuel=length correctly enumerates perfect matchings pairing head with later vertices; only u<v edges with colors (iota u, iota v) are ever read, so unconstrained EdgeN ghost fields (u>=v, loops) are inert; allEqual = chain equality along [0..N-1] = constancy; positive witnesses N=4 D=2/3 and N=6 D=2 verified by native_decide in-file, confirming the encoding admits the known physical constructions. answer(sorry) <-> (no-solution) encoding is faithful.  
**Next action:** Open general conjecture (implied by the complex version, itself open). Progress = same avenues as complex case.

## `eqSystem_no_solution_ge6_ge3_trinary_int` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/Paper/MonochromaticQuantumGraph.lean:779`  
**Statement:** For every even N>=6 and D>=3, is there no {-1,0,1}-valued solution?  
**Source:** Krenn-Gu conjecture: Krenn-Gu-Soltesz arXiv:1902.06023; MathOverflow 311325; Chandran-Gajjala arXiv:2202.05562; Chandran-Gajjala-Illickan-Krenn arXiv:2407.00303 (MFCS 2024); mariokrenn.wordpress.com/graph-theory-question  
**Statement matches intent:** yes  
**Known status:** Open; strictly implied by the general integer version (itself open beyond N=6). Fork solved the N=6 slice.  
**Difficulty:** math 7/10, Lean 9/10 · **Compute:** large · **Confidence:** medium  
**Evidence:** Trinary witnesses are integer witnesses, so this is the weakest of the general family; internal N=6 base case done.  
**Next action:** Follows from any uniform mod-2/integer argument (see eqSystem_no_solution_ge6_ge3_int); no reason to attack the trinary family separately.

## `prime_tuples_conjecture` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Paper/PrimeTuples.lean:33`  
**Statement:** Dickson/Hardy–Littlewood prime k-tuples conjecture: if k ≥ 2 linear forms a_i n + b_i (a_i > 0) have no fixed prime divisor, then infinitely many n make all of them simultaneously prime.  
**Source:** Friedlander–Luca–Stoiciu, 'On the irrationality of a divisor function series', Integers 7 (2007); classically Dickson 1904 / Hardy–Littlewood 1923 / Schinzel Hypothesis H.  
**Statement matches intent:** yes  
**Known status:** Major open problem — contains the twin prime conjecture (k=2, a=(1,1), b=(0,2)) and Sophie Germain / Polignac as special cases. No progress beyond bounded gaps (Zhang/Maynard/Tao), which give no single admissible tuple.  
**Difficulty:** math 10/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** hab quantifies 'for every prime p there is n with p ∤ ∏ (a_i n + b_i)', which is exactly the Schinzel/Dickson no-fixed-prime-divisor condition; ranging n over ℕ covers all residues mod p so the ℕ/ℤ distinction is immaterial. Products and primality are in ℕ throughout (a i : ℕ+ coerced), no junk values.  
**Flags:** DUPLICATE: essentially the same statement already lives in FormalConjectures/Wikipedia/Dickson.lean:dickson_conjecture (linear forms, ℤ[X] version) and generalised in FormalConjectures/Wikipedia/Schinzel.lean:schinzel_conjecture. Consider consolidating or cross-referencing; also FormalConjectures/Wikipedia/BatemanHornConjecture.lean and Bunyakovsky.lean overlap.  
**Next action:** Leave open. Optionally cross-link to the existing repo statements to avoid divergence.

## `reed_conjecture_Δ_6_ω_2` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/Paper/ReedOmegaDeltaChi.lean:64`  
**Statement:** The (claimed) simplest open instance of Reed's conjecture: every triangle-free graph with maximum degree exactly 6 is 5-colourable.  
**Source:** MathOverflow 37923 (Andrew D. King); openproblemgarden 'Bounding the chromatic number of triangle-free graphs with fixed maximum degree'.  
**Statement matches intent:** yes  
**Known status:** Open. Literature check confirms the triangle-free case of Reed is open for every Δ > 4 up to where Johansson/Molloy's χ = O(Δ/log Δ) takes over; recent work only settles restricted subclasses (e.g. maximal triangle-free graphs with Δ < 7). Equivalent to: no 6-chromatic triangle-free graph of maximum degree 6 exists. Smallest triangle-free 6-chromatic graphs are known to have between 32 and 40 vertices (arXiv:1707.07581) but their max degree exceeds 6.  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** large · **Confidence:** medium  
**Evidence:** Search confirms the triangle-free small-Δ cases of Reed are open; the docstring's claim that Δ=6/ω=2 is *the* simplest open case may be off by one (Δ=5/ω=2 ⇒ χ ≤ 4 also appears unresolved), but the stated theorem is a genuine open instance either way.  
**Flags:** Docstring claim 'the simplest open case' is not clearly supported — some sources point to Δ = 5, ω = 2 (χ ≤ 4). Does not affect correctness of the formal statement. needs literature check.; Stated for arbitrary V : Type with no finiteness; equivalent to the finite case by de Bruijn–Erdős, but a Lean proof would have to go through compactness.  
**Next action:** Leave open, but this is the most attackable item in the file: progress would be a computer search establishing that no triangle-free 6-chromatic graph with Δ ≤ 6 exists below some vertex count, combined with a discharging/Kempe-chain reducibility argument. Formalizing even a partial reducibility lemma is a real project.

## `reed_omega_delta_chi_conjecture` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Paper/ReedOmegaDeltaChi.lean:38`  
**Statement:** Reed's conjecture: every graph satisfies χ ≤ ⌈(ω + Δ + 1)/2⌉, stated here for arbitrary (possibly infinite) graphs using ℕ∞-valued clique number and max degree.  
**Source:** B. Reed, 'ω, Δ and χ', J. Graph Theory 27 (1998) 177–212; http://www.openproblemgarden.org/op/reeds_omega_delta_and_chi_conjecture  
**Statement matches intent:** yes  
**Known status:** Recognized hard open problem. Reed proved χ ≤ ⌈(1−ε)(Δ+1) + εω⌉ for a small ε; the ε = 1/2 case is open and is known only for restricted classes (line graphs, quasi-line graphs, claw-free, large-Δ random-like cases). No fork PR/branch.  
**Difficulty:** math 9/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Infinite-V case is not a loophole: if Δ is finite then χ ≤ Δ+1 by greedy + de Bruijn–Erdős (available with choice in Lean), so χ = ⊤ with finite ω, Δ cannot occur; if Δ = ⊤ the RHS is ⊤ and the inequality is trivially true. So this statement is equivalent (modulo dBE) to the finite-graph version below.  
**Flags:** Universe restriction to `V : Type` (Type 0) only — harmless mathematically since χ, ω, Δ depend only on finite subgraphs, but the statement is formally weaker than a Type* version.; Near-duplicate of reed_omega_delta_chi_conjecture_for_finite_graphs in the same file.  
**Next action:** Leave open (cat 9). Any tractable Lean work here is on special classes, not the general statement.

## `reed_omega_delta_chi_conjecture_for_finite_graphs` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Paper/ReedOmegaDeltaChi.lean:52`  
**Statement:** Reed's conjecture χ ≤ ⌈(ω + Δ + 1)/2⌉ for finite graphs, using the ℕ-valued cliqueNum and maxDegree.  
**Source:** B. Reed, 'ω, Δ and χ', J. Graph Theory 27 (1998) 177–212.  
**Statement matches intent:** yes  
**Known status:** Recognized hard open problem; this is the canonical (finite) form. Verified for Δ ≤ 4 and for many structured classes; still open in general. Nothing internal.  
**Difficulty:** math 9/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Faithful transcription with all needed Fintype/DecidableRel instances; no vacuity, no truncation (no ℕ-subtraction, everything in ℕ∞).  
**Flags:** Near-duplicate of the arbitrary-V version above; the two are equivalent via de Bruijn–Erdős, so proving one gives the other with modest extra work.  
**Next action:** Leave open. Milestone-sized sub-targets would be Brooks' theorem (χ ≤ Δ for connected non-complete non-odd-cycle) in Mathlib, and Reed's conjecture for Δ ≤ 4.

## `strong_sensitivity_conjecture` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Paper/StrongSensitivityConjecture.lean:98`  
**Statement:** For every Boolean function f on n bits, block sensitivity is at most the square of sensitivity: bs(f) ≤ s(f)^2.  
**Source:** Nisan–Szegedy, Comput. Complexity 4 (1994), Section 4 open problems; Hatami–Kulkarni–Pankratov 'Variations on the Sensitivity Conjecture' (arXiv:1011.0354) Question 3.1; Huang, arXiv:1907.00847, concluding remarks.  
**Statement matches intent:** suspect — The literature conjecture is usually bs(f) = O(s(f)^2); this file asserts the constant-free bs(f) ≤ s(f)^2, which is strictly stronger. Since Ambainis–Sun (arXiv:1108.3494) achieve bs(f) ≥ (2/3)s(f)^2 − (1/3)s(f), the constant-free version is not contradicted, but it could conceivably be false while the O(·) form is true — in which case a small counterexample search would refute the Lean statement without touching the real conjecture.  
**Known status:** Open. Huang's 2019 theorem gives deg(f) ≤ s(f)^2 hence bs(f) ≤ 2·deg(f)^2 ≤ O(s(f)^4); reducing the exponent from 4 to 2 is a well-known open problem in analysis of Boolean functions. Nothing internal (pr_register.json has no sensitivity PRs).  
**Difficulty:** math 9/10, Lean 10/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** Definitions audited and correct: `flip x B` flips exactly the bits in B; blockSensitivityAt takes the Finset.sup of |cB| over collections cB of pairwise-disjoint blocks each of which flips f — the empty block is automatically excluded since flip x ∅ = x, so no degenerate-block loophole; n = 0 gives bs = s = 0 and the statement holds. `{cB | IsValidBlockConfig f x cB}` is a Finset via Fintype + Classical, so no junk sup.  
**Flags:** Constant-free bound is stronger than the O(s^2) form actually conjectured in the cited references — potential spec mismatch; if refuted by a small example the *intended* conjecture would still be open.  
**Next action:** Leave open. Two cheap sanity actions: (i) run a small exhaustive search over n ≤ 5 Boolean functions to check bs ≤ s^2 has no small counterexample (would justify keeping the constant-free form); (ii) consider restating as ∃ C, bs(f) ≤ C·s(f)^2 to match the source.

## `voronovskaja_theorem.bezier_bernstein_operators` — Already solved internally (cat 0)

**File:** `FormalConjectures/Paper/VoronovskajaTypeFormula.lean:126`  
**Secondary category:** 5 (Solved mathematically, not yet formalized)  
**Statement:** Determine lim_{n→∞} √n (B_{n,α} f(x) − f(x)) for the Bézier variant of the Bernstein operators with shape parameter α > 0, α ≠ 1, for C² functions on [0,1].  
**Source:** Ulrich Abel, open problem in *Constructive Theory of Functions, Sozopol 2010*, https://www.math.bas.bg/mathmod/Proceedings_CTF/CTF-2010/files_CTF-2010/Open_problems.pdf  
**Statement matches intent:** yes  
**Known status:** SOLVED INTERNALLY (branch-only; canonical main still says sorry). Fork branch `solve-voronovskaja-no-sorry` / `solve-voronovskaja-certified` / `agent/solve-voronovskaja-clean`, commit d56612263ca6756cd1753ae5a0dbd6f1ed246cf5. PRs #7, #18, #19, #20, #29, #36, #51, #54, #55, #69, #70, #259 (all closed or open, none merged); PR #51 body: 'proves the explicit sqrt n asymptotic … identifies the limit as the powered-Gaussian first-moment constant times sqrt(x*(1-x))*f′(x)'. Upstream submission google-deepmind/formal-conjectures#4525 referenced in PR #69.  
**Difficulty:** math 6/10, Lean 8/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Fetched the branch source: the four target theorems are proved (`simpa using tendsto_bezierBernstein_all α hα_pos f hf x hx`, etc.) and grep over VoronovskajaMain/Proof/Expectation/DiscreteLaw/MomentLimit found no `sorry`, `axiom` or `native_decide`. The answer independently checks out: the Bézier weights make P(K ≥ k) = J_{n,k}(x)^α, so (K−nx)/√(nx(1−x)) converges to the law with survival function Φ̄^α, whose mean is μ_α = ∫_0^∞ ((1−Φ)^α + Φ^α − 1) dt — exactly `bezierVoronovskajaConstant`. Sign check: μ_α < 0 for α > 1, as expected since raising the survival function to a power > 1 shifts K down.  
**Flags:** Branch-only: canonical main file is still `@[category research open]` with sorry. campaign_register.json flags that at least one fork campaign (bmo8) produced a claim that had to be archived — spot-check the axiom audit before trusting.; The branch replaces `import FormalConjectures.Util.ProblemImports` with `import FormalConjecturesUtil`/module split, so porting is not a one-file copy.; verifier:confirmed  
**Next action:** Port the branch to main and verify the build: fetch commit d5661226, which adds 18 supporting modules (VoronovskajaDefinitions/DiscreteLaw/Expectation/MomentLimit/TaylorBound/Remainder/Proof/Main plus the Classical* chain) and a #print-axioms audit file VoronovskajaNonlinearAudit.lean. I could not run lake here, so the build/axiom claim is unverified in this container.

## `voronovskaja_theorem.bezier_bernstein_operators.variants.answer_smoothness` — Already solved internally (cat 0)

**File:** `FormalConjectures/Paper/VoronovskajaTypeFormula.lean:170`  
**Secondary category:** 5 (Solved mathematically, not yet formalized)  
**Statement:** Give both the required smoothness order m and the explicit limit formula for √n(B_{n,α}f(x) − f(x)), α > 0, α ≠ 1.  
**Source:** Ulrich Abel, CTF Sozopol 2010 open problems.  
**Statement matches intent:** yes  
**Known status:** SOLVED INTERNALLY on branch commit d5661226 (answer: threshold m = 2).  
**Difficulty:** math 6/10, Lean 8/10 · **Compute:** none · **Confidence:** high  
**Evidence:** No vacuity risk from the answer: ContDiffOn ℝ m f I is satisfiable for every m (all C^∞ functions qualify), so a large m cannot trivialize the statement; and limitFormula is fixed before ∀ f x, so it cannot be tuned per function.  
**Flags:** Branch-only; canonical main still open with sorry.; This variant is nearly a duplicate of `variants.eventually_smooth`; consider merging once ported.; verifier:confirmed  
**Next action:** Port from d5661226 and verify the build.

## `voronovskaja_theorem.bezier_bernstein_operators.variants.eventually_smooth` — Already solved internally (cat 0)

**File:** `FormalConjectures/Paper/VoronovskajaTypeFormula.lean:140`  
**Secondary category:** 5 (Solved mathematically, not yet formalized)  
**Statement:** For α > 0, α ≠ 1, there is a smoothness threshold beyond which every C^m function on [0,1] satisfies √n(B_{n,α}f(x) − f(x)) → L(f,x) for one explicit formula L.  
**Source:** Ulrich Abel, CTF Sozopol 2010 open problems (same source as above).  
**Statement matches intent:** yes  
**Known status:** SOLVED INTERNALLY on branch commit d5661226 (see the sibling entry). Proof: `refine eventually_atTop.2 ⟨2, fun m hm f x hx hfm ↦ ?_⟩; apply tendsto_bezierBernstein_all …; exact hfm.of_le (by exact_mod_cast hm)`.  
**Difficulty:** math 6/10, Lean 8/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Formalization is sound: limitFormula is bound before ∀ f x so it must be uniform in f and x (but may depend on α, which is bound earlier) — no witness-scope loophole. `∀ᶠ m in atTop` is the right reading of 'sufficiently smooth' since ContDiffOn ℝ m is antitone in m.  
**Flags:** Branch-only; canonical main still open with sorry.; verifier:confirmed  
**Next action:** Port together with the main theorem from commit d5661226 and verify the build.

## `voronovskaja_theorem.bezier_bernstein_operators.variants.eventually_smooth.limit_exists` — Already solved internally (cat 0)

**File:** `FormalConjectures/Paper/VoronovskajaTypeFormula.lean:155`  
**Secondary category:** 2 (Trivially or easily solvable)  
**Statement:** Existence-only half of the Bézier–Bernstein Voronovskaja problem: for sufficiently smooth f, the sequence √n(B_{n,α}f(x) − f(x)) converges to some limit.  
**Source:** Ulrich Abel, CTF Sozopol 2010 open problems ('Prove or disprove the existence of the limit').  
**Statement matches intent:** yes  
**Known status:** SOLVED INTERNALLY on branch commit d5661226: `refine eventually_atTop.2 ⟨2, …⟩; refine ⟨bezierVoronovskajaConstant α * √(x*(1−x)) * iteratedDerivWithin 1 f I x, ?_⟩; apply tendsto_bezierBernstein_all …`.  
**Difficulty:** math 6/10, Lean 8/10 · **Compute:** none · **Confidence:** high  
**Evidence:** The ∃ L is inside the ∀ f x scope, so L may legitimately depend on f and x — correct quantifier order for an existence claim, no weakening beyond what the source intends.  
**Flags:** Branch-only; canonical main still open with sorry.; Once the sibling explicit-limit theorem is available in the repo, this becomes cat 2 (immediate corollary).; verifier:confirmed  
**Next action:** Port from d5661226; once the main theorem is in place this one is a three-line corollary.

## `problem_4_1` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/Paper/WeakTiling.lean:78`  
**Statement:** If Ω ⊂ ℝ is a finite union of intervals and ν is a weak tiling measure for Ω (1_Ω ∗ ν = 1_{Ω^c} a.e.), must supp(ν) have bounded density (uniformly bounded number of points in each unit interval)?  
**Source:** Problem 4.1 of 'Geometric implications of weak tiling', arXiv:2506.23631 (Analysis Mathematica, 2025).  
**Statement matches intent:** yes  
**Known status:** Open — posed June 2025 in the source paper; web check confirms the paper's Section 4 lists exactly these three problems and no resolution is indexed. No PR or branch in this fork touches weak tiling or Fuglede.  
**Difficulty:** math 7/10, Lean 9/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** The Bochner-integral junk-value trap is closed here: Ω is bounded and ν is locally finite, so t ↦ 1_Ω(x−t) is ν-integrable for every x (its support x − Ω is bounded), hence `∫ = 0` genuinely means ν(x − Ω) = 0 rather than the integral defaulting to 0 for a non-integrable function.  
**Flags:** `Measure.positivity` from the paper ('positive, locally finite Borel measure') is not stated, but Mathlib measures are nonnegative by construction, so nothing is lost.; Relies on `MeasureTheory.Measure.support` having the intended (closed topological support) meaning; not verifiable without a build.; needs literature check for post-2025 follow-ups.  
**Next action:** Leave open. First real milestone would be formalizing the paper's Theorem 3.4 (necessary condition on gap lengths for finite unions of intervals), which is finite/elementary compared with the open problem.

## `problem_4_2` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/Paper/WeakTiling.lean:87`  
**Statement:** If Ω ⊂ ℝ is a finite union of three or more intervals and Ω weakly tiles its complement, must it tile its complement properly (by translates along some set T)?  
**Source:** Problem 4.2 of 'Geometric implications of weak tiling', arXiv:2506.23631.  
**Statement matches intent:** yes  
**Known status:** Open. Per the source, a positive answer would give the 'spectral ⇒ tile' direction of Fuglede's conjecture for finite unions of intervals — i.e. it is at least as hard as a known open case of Fuglede. See FormalConjectures/Wikipedia/Fuglede.lean for the related conjecture already in the repo.  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** IsProperTiling Ω T = IsWeakTilingMeasure Ω (Measure.sum of Diracs on T), which is the correct 'tiling by translates' notion (the Dirac sum is a weak tiling measure iff the translates of Ω by T partition Ω^c up to null sets).  
**Flags:** needs literature check for post-2025 follow-ups.; Same Measure.support / Bochner-integral caveats as problem_4_1 (both benign here).  
**Next action:** Leave open. Note the Fuglede linkage when prioritising: this is a genuinely research-level target, not a formalization exercise.

## `problem_4_3` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/Paper/WeakTiling.lean:97`  
**Statement:** If Ω is a finite union of intervals with weak tiling measure ν, must ν be a convex combination of proper tiling measures?  
**Source:** Problem 4.3 of 'Geometric implications of weak tiling', arXiv:2506.23631.  
**Statement matches intent:** suspect — The paper says 'convex linear combination of proper tilings'; the Lean version fixes a *countable* combination indexed by ℕ with coefficients in ℝ≥0 summing to 1. If the true decomposition required an integral over a continuum of proper tilings, the formal statement would be false while the intended problem stayed open. Also `∀ i, IsProperTiling Ω (T i)` is demanded even for indices with c i = 0, a harmless mild strengthening.  
**Known status:** Open — posed in the June 2025 source paper; per that paper a positive answer implies a positive answer to Problem 4.2 (hence to a case of Fuglede).  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** Encoding ν = Measure.sum (fun i ↦ (c i : ℝ≥0∞) • Measure.sum (Diracs on T i)) is a well-formed countable convex combination; the coefficient sum condition ∑' c i = 1 is in ℝ≥0 so there is no ENNReal/ℝ mismatch.  
**Flags:** Countable-vs-general convex combination is a possible semantic narrowing of the source problem (minor spec issue, could become major if the answer differs between the two forms).; needs literature check for post-2025 follow-ups.  
**Next action:** Leave open; if kept, consider relaxing the encoding to allow a general mixture (a probability measure on the space of proper tilings) so that a 'no' answer for the countable form cannot be mistaken for a resolution of the source problem.

## `existsWeaklyFirstCountableCompactBig` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/Paper/WeaklyFirstCountable.lean:85`  
**Secondary category:** 10 (Cannot classify without correction/clarification)  
**Statement:** Is there (provably in ZFC) a weakly first countable compact Hausdorff space of cardinality strictly greater than the continuum?  
**Source:** A. Arhangelskii, 'Selected old open problems in general topology', Bul. Acad. Ştiinţe Repub. Mold. Mat. 73 (2013) 37–46, Problem 2.  
**Statement matches intent:** suspect — The answer() encoding presumes the question has a ZFC-decidable truth value. The source explicitly asks for an example 'in ZFC', which is exactly the situation where existence may be independent of ZFC — in which case neither answer = True nor answer = False is provable and the Lean theorem is unprovable rather than answerable. The companion Problem 3 is (more honestly) stated as a bare ∃.  
**Known status:** Open (a 'selected old open problem'). Under CH, Yakovlev's 1976 construction gives a weakly first countable compact Hausdorff non-first-countable space (recorded in-file as CH.existsWeaklyFirstCountableCompactNotFirstCountable); the cardinality question is separate and no ZFC example is known.  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** WeaklyFirstCountableTopology is a correct rendering of a countable antitone weak base: x ∈ V x n, V x antitone, and O open ↔ ∀ x ∈ O ∃ k, V x k ⊆ O. The in-file instance from FirstCountableTopology is proved, so the class is non-degenerate. Restricting X to Type 0 is harmless: Cardinal.{0} contains cardinals far above 𝔠.  
**Flags:** answer()-encoding of a possibly ZFC-independent existence question — the theorem may be unprovable in either direction (this is why cat2 = 10 is recorded).; Prop-valued answer() could be discharged by Iff.rfl if the repo does not enforce True/False answers.; needs literature check: I could not confirm whether a ZFC upper bound |X| ≤ 𝔠 for weakly first countable compacta is a known theorem (which would make the answer provably False).  
**Next action:** Restate as a bare existential (matching existsWeaklyFirstCountableCompactNotFirstCountable) rather than an answer(sorry) ↔ …, then leave open. Meaningful progress would be either a ZFC construction or a consistency proof that no such space exists.

## `existsWeaklyFirstCountableCompactNotFirstCountable` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/Paper/WeaklyFirstCountable.lean:97`  
**Statement:** Construct, in ZFC alone, a weakly first countable compact Hausdorff space that is not first countable.  
**Source:** Arhangelskii, 'Selected old open problems in general topology' (2013), Problem 3; Yakovlev, Dokl. Akad. Nauk 229 (1976) (CH construction).  
**Statement matches intent:** yes  
**Known status:** Open. Yakovlev 1976 constructs such a space under CH; no ZFC construction is known, and it is not known whether one is consistent-ly impossible. No fork PR/branch touches this file.  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** T2Space + CompactSpace + the weak-base class is exactly Arhangelskii's 'compact' convention (his blanket convention is Tychonoff, and compact Hausdorff ⇒ Tychonoff, so nothing is missing). No vacuity: the class has instances (every first countable space).  
**Flags:** Universe restriction to Type 0; a witness in a higher universe would not satisfy this statement, though no known candidate needs one.; needs literature check for progress since 2013.  
**Next action:** Leave open. The realistic Lean milestone is the *solved* companion `CH.existsWeaklyFirstCountableCompactNotFirstCountable` (Yakovlev under CH) or the textbook `exists_weakly_first_countable_not_first_countable` (Arens space) — both are also still sorry and are far more tractable than the ZFC problem.

## `zagier_conjecture` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Paper/ZagierMZV.lean:93`  
**Statement:** Zagier's conjecture: the ℚ-vector space spanned by multiple zeta values of weight n has dimension exactly d_n, where d_0 = 1, d_1 = 0, d_2 = 1 and d_n = d_{n−2} + d_{n−3}.  
**Source:** D. Zagier, 'Values of zeta functions and their applications', First European Congress of Mathematics (1994); Terasoma, Invent. Math. 149 (2002); Deligne–Goncharov, Ann. Sci. ENS 38 (2005); OEIS A000931.  
**Statement matches intent:** yes  
**Known status:** Major open problem. The upper bound dim ≤ d_n is the theorem of Terasoma / Deligne–Goncharov (recorded in-file as `zagier_upper_bound`, still sorry). The matching lower bound is wide open and would imply, among other things, strong algebraic-independence statements about ζ(3), ζ(5), … that are far beyond current technology (only ζ(3) irrational is known). No PR/branch in this fork.  
**Difficulty:** math 10/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** AdmissibleIndex requires s_1 ≥ 2 and all later entries positive, matching the convergence condition; junk values from tsum-divergence only arise for non-admissible indices, which are excluded from mzvSetOfWeight. Weight-0 and weight-1 base cases are already proved in-file (dim 1 and 0), consistent with d_0 = 1, d_1 = 0. Module.finrank returning 0 for infinite-dimensional spaces is harmless since the Terasoma bound makes every 𝒵_n finite-dimensional.  
**Flags:** Prop-valued answer(sorry) ↔ ∀ n, …: sound here (both True and False are expressible since the statement is a single ∀ over n), unlike the LatinSquare free-variable cases.; The `zagier_upper_bound` companion is marked `research solved` but is still sorry — it is the deep Terasoma/Deligne–Goncharov theorem, not a quick win.  
**Next action:** Leave open (cat 9). The tractable neighbouring target is `zagier_upper_bound`, which is itself a deep motivic theorem — also not a realistic Lean project. A genuinely reachable milestone is formalizing convergence of multiZeta for admissible indices and the sum/stuffle relations.
