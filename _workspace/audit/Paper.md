# Audit detail — Paper

58 research-open declarations. Fields per problem: plain statement, source, category, match, status, action, difficulties, compute, confidence, evidence, flags.

## `HasGδSingletons.lindelof_card` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/Paper/CardinalityLindelof.lean:39`  
**Statement:** Does there exist a Lindelöf topological space in which every singleton is a Gδ set and whose cardinality exceeds the continuum? (Arhangel'skii, Problem 1 of his 2013 'Selected old open problems' survey.)  
**Source:** A. V. Arhangel'skii, Selected Old Open Problems in General Topology, Bul. Acad. Ştiinţe Repub. Mold. Mat. 2013, Problem 1  
**Statement matches intent:** suspect — The survey's blanket convention is Tychonoff spaces; the Lean statement imposes no separation axiom. Points-Gδ does force T1 (for x≠y each of {x},{y} being Gδ yields separating opens), but not Hausdorff/regular, so a non-Hausdorff example could conceivably satisfy the formal statement more easily than the intended problem.  
**Known status:** Consistently such spaces exist (Shelah; Gorelic 1993 constructs, consistent with CH, a Lindelöf points-Gδ space of size 2^ℵ1 > 𝔠), so the negation is not provable in ZFC; whether ZFC outright proves existence is a well-known open problem — the statement is plausibly independent. The file's own TODO acknowledges the consistency results. No internal PR/campaign targets it.  
**Difficulty:** math 9/10, Lean 10/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** HasGδSingletons defined in FormalConjecturesForMathlib/Topology/GDelta.lean (audited, correct). Statement quantifies over Type 0, which realizes all Cardinal.{0} cardinalities, so no universe defect. Classical consistency results (Shelah, Gorelic) make the ∃ unrefutable in ZFC.  
**Flags:** missing separation axiom: intended for Tychonoff/Hausdorff spaces, formalization only forces T1 implicitly; likely independent of ZFC — Lean statement may be neither provable nor refutable; needs literature check  
**Next action:** Consider adding a T2/T3 hypothesis to match the survey convention; treat as likely ZFC-independent, not a proof target. No fast path.

## `casas_alvero_conjecture` — Solved mathematically, not yet formalized (cat 5)

**File:** `FormalConjectures/Paper/CasasAlvero.lean:122`  
**Secondary category:** 9 (Major open problem / currently infeasible)  
**Statement:** Casas-Alvero conjecture: a monic polynomial of degree d over a characteristic-zero field that shares a nontrivial common factor with each of its Hasse derivatives of order 1..d-1 must equal (X-α)^d for some α.  
**Source:** arXiv:2501.09272 (S. Ghosh, Proof of the Casas-Alvero conjecture); arXiv:math/0605090 (Graf von Bothmer et al.)  
**Statement matches intent:** yes  
**Known status:** Soham Ghosh's claimed complete proof via Koszul homology (arXiv:2501.09272, v1 Jan 2025, revised v2 Mar 2026) is standing as of Jul 2026 and is cited by other papers as a complete proof; no refutation found, but journal refereeing not confirmed. Prior partial results: degrees ≤ 8, p^k, 2p^k. The file's HasCasasAlveroProp is faithful (i=0 term ¬IsCoprime P P is vacuously satisfied for non-unit P; not-coprime over K correctly captures shared factor).  
**Difficulty:** math 9/10, Lean 10/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** WebSearch: arXiv 2501.09272 v2 (Mar 2026) not withdrawn; secondary citations describe it as a complete proof; no error report found. File docstring itself notes the claimed proof. Secondary cat 9 reflects fallback if the proof has a gap.  
**Flags:** recent claimed proof — community verification/refereeing status uncertain, needs continued literature monitoring; formalization research-scale  
**Next action:** Monitor refereeing of Ghosh's proof; formalization would be research-scale (Koszul homology machinery absent from Mathlib). Keep category open in repo until the proof is refereed, then flip to solved with citation.

## `value_of_even_mul_succ_self_div_two` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/Paper/CatchUpConjecture.lean:178`  
**Statement:** In the Catch-Up game on {1,...,N}, if the total T_N = N(N+1)/2 is even (N ≡ 0 or 3 mod 4) then optimal play ends in a draw.  
**Source:** Isaksen–Ismail–Brams–Nealen, 'Catch-Up: A Game in Which the Lead Alternates', Game & Puzzle Design 1(2) 2015; upstream issue google-deepmind/formal-conjectures#1324  
**Statement matches intent:** yes  
**Known status:** Open. Computational verification extended from n=18 (original paper) to n=28 (Brams et al. follow-up, MPRA 108784); no general proof. The negamax evaluator was audited: first-move exactly-one-pick rule, forced continuation while strictly behind, stop-on-catch-up, and cannot-catch-up loss pruning all faithfully implement the published rules; N=0 edge case (empty Icc, draw) is consistent; Nat division N*(N+1)/2 is exact.  
**Difficulty:** math 7/10, Lean 9/10 · **Compute:** none · **Confidence:** high  
**Evidence:** WebSearch confirms the draw conjecture is open and computationally verified to n=28. Model fidelity verified line-by-line against the rules in the module docstring and the 2015 paper's rules.  
**Next action:** General case is genuinely open (game-tree grows like N!); partial progress possible by formalizing small-N cases via kernel evaluation of valueAux, but that does not touch the ∀N statement.

## `exists_maximal_star` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Paper/Chvatal.lean:45`  
**Statement:** Chvátal's conjecture: in any downward-closed finite family F of sets, some star (all members of F containing a fixed element x) attains the maximum cardinality of an intersecting subfamily of F.  
**Source:** V. Chvátal 1974; https://users.encs.concordia.ca/~chvatal/conjecture.html; arXiv:1608.08954  
**Statement matches intent:** yes  
**Known status:** Famous open problem for 50+ years; known for families closed under compressions and other special cases; correlation-inequality reformulations exist (Friedgut et al.). Formalization audited: Intersecting includes A=B so ∅ is excluded from intersecting subfamilies; ∃x ∀G quantifier order is the correct statement; empty-F and empty-star edge cases are fine.  
**Difficulty:** math 9/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Statement matches Chvátal's conjecture exactly; no defect found. No PR/campaign/duplicate in repo.  
**Next action:** No feasible path; genuinely hard open problem. Nothing internal to port.

## `cube_hamiltonian_arc_decomposition_even` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/Paper/ClaudesCycles.lean:85`  
**Secondary category:** 6 (Computationally solvable with certificate)  
**Statement:** Answer-encoded yes/no: is it true that for every even m > 2 the 3m^3 arcs of the directed torus digraph on (ZMod m)^3 decompose into three arc-disjoint directed Hamiltonian cycles?  
**Source:** D. E. Knuth, 'Claude's Cycles' (2026), https://www-cs-faculty.stanford.edu/~knuth/papers/claude-cycles.pdf; Aubert–Schneider, JCTB 32 (1982)  
**Statement matches intent:** yes  
**Known status:** Odd m > 1 solved (Claude/Knuth construction; formalized in Lean at kim-em/KnuthClaudeLean, referenced by the sibling theorem's formal_proof attribute). m = 2 impossible (Aubert–Schneider). Even m > 2 open as of mid-2026: follow-up arXiv papers (2603.24708, 2605.04734 etc.) all treat odd modulus only. Definitions audited: bumpAt/cubeAdj, ∃!-cycle-per-arc condition correctly encodes an arc partition; for m ≥ 2 the three out-arcs at each vertex are distinct.  
**Difficulty:** math 7/10, Lean 8/10 · **Compute:** medium · **Confidence:** medium  
**Evidence:** WebSearch: Knuth paper + ecosystem (KnuthClaudeLean, arXiv follow-ups) confirm odd case solved, even case not mentioned as resolved anywhere as of Jul 2026.  
**Flags:** answer-encoding: one failing even m (e.g. m=4) decides the whole statement False, while a positive answer needs all even m — weaker than the per-m open problem; 2026-vintage problem — needs ongoing literature check  
**Next action:** Attack m = 4 by exact-cover/SAT (64 vertices, 192 arcs, three arc-disjoint Hamiltonian cycles): a negative certificate would prove answer = False and close the formal statement; a positive one only removes the smallest case. Knuth's m=3 exact-cover analysis (4554 decompositions) suggests the search is tractable.

## `conjClassSizes_iff_sym_three` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/Paper/ConjugacyClassSizes.lean:131`  
**Statement:** Markel's S3-conjecture: every nontrivial finite group whose distinct conjugacy classes all have distinct sizes (ah-group) is isomorphic to S3.  
**Source:** F. M. Markel, J. Algebra 26 (1973); Zhou–Gorshkov arXiv:2606.22244; Knörr–Lempken–Thielcke 1995; Zhang 1994; Arad–Muzychuk–Oliver 2004  
**Statement matches intent:** yes  
**Known status:** Open in general. Proved for solvable groups independently by Zhang (1994) and Knörr–Lempken–Thielcke (1995) (stated as the sibling solved theorem); Arad–Muzychuk–Oliver and recent work (Zhou–Gorshkov 2026 on {2,3,5}-groups) give further reductions. Formalization audited: conjClassCard = Nat.card of class carrier, injectivity encoding is correct; file proves S3 is an ah-group by decide and that ah-groups have trivial center.  
**Difficulty:** math 8/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Well-documented open conjecture; supporting API/test lemmas in the file are sorry-free and consistent with the definition.  
**Next action:** Key obstruction: the nonsolvable case, which likely needs CFSG-adjacent arguments; progress = formalizing the solvable case (itself a large project). Not a near-term target.

## `DeGiorgi_eight` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Paper/DeGiorgi.lean:166`  
**Statement:** De Giorgi's conjecture in dimension 8 (the largest dimension where it is conjectured true; fails for n ≥ 9).  
**Source:** De Giorgi 1978; Savin, Annals 169 (2009); del Pino–Kowalczyk–Wei, Annals 174 (2011)  
**Statement matches intent:** yes  
**Known status:** Open unconditionally (Savin conditional); sharpness of n ≤ 8 shown by del Pino–Kowalczyk–Wei.  
**Difficulty:** math 9/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Same audited encoding as DeGiorgi_le_eight.  
**Next action:** No feasible formal path; watch literature.

## `DeGiorgi_five` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Paper/DeGiorgi.lean:145`  
**Statement:** De Giorgi's conjecture in dimension 5.  
**Source:** De Giorgi 1978; Savin, Annals 169 (2009) (conditional result)  
**Statement matches intent:** yes  
**Known status:** Open unconditionally (Savin conditional).  
**Difficulty:** math 9/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Same audited encoding as DeGiorgi_le_eight.  
**Next action:** No feasible formal path; watch literature.

## `DeGiorgi_four` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Paper/DeGiorgi.lean:138`  
**Statement:** De Giorgi's conjecture in dimension 4: bounded monotone entire Allen-Cahn solutions on ℝ⁴ have hyperplane level sets.  
**Source:** De Giorgi 1978; Savin, Annals 169 (2009) (conditional result)  
**Statement matches intent:** yes  
**Known status:** Open. Savin's theorem gives it only under the additional limit hypothesis lim u = ±1; unconditional n=4 remains unresolved as of knowledge cutoff.  
**Difficulty:** math 9/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Same audited encoding as DeGiorgi_le_eight.  
**Next action:** No feasible formal path; watch literature.

## `DeGiorgi_le_eight` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Paper/DeGiorgi.lean:90`  
**Statement:** De Giorgi's conjecture: for n ≤ 8, every bounded C² entire solution of Δu + u - u³ = 0 on ℝⁿ with ∂₁u > 0 everywhere has all level sets equal to hyperplanes.  
**Source:** De Giorgi 1978; Ghoussoub–Gui 1998 (n=2); Ambrosio–Cabré 2000 (n=3); Savin 2009 (conditional 4≤n≤8); del Pino–Kowalczyk–Wei 2011 (n≥9 fails)  
**Statement matches intent:** yes  
**Known status:** Major open problem in elliptic PDE: n=1,2,3 solved; 4 ≤ n ≤ 8 open unconditionally (Savin proved it assuming the limit condition u(x',x_n)→±1); n ≥ 9 false. Proving this ∀n≤8 statement requires the open cases. Formalization audited: hyperplane-level-set encoding (affine subspace of finrank n-1 for each attained value), lineDeriv positivity, and the PDE are all faithful; n-1 truncation harmless since NeZero n.  
**Difficulty:** math 10/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Statement subsumes the open dimensions 4-8. File's own n=1 case is proved sorry-free, validating the encoding.  
**Next action:** Not a target; even the solved n=2,3 cases would be research-scale formalization (Liouville-type theorems, elliptic regularity).

## `DeGiorgi_seven` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Paper/DeGiorgi.lean:159`  
**Statement:** De Giorgi's conjecture in dimension 7.  
**Source:** De Giorgi 1978; Savin, Annals 169 (2009) (conditional result)  
**Statement matches intent:** yes  
**Known status:** Open unconditionally (Savin conditional).  
**Difficulty:** math 9/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Same audited encoding as DeGiorgi_le_eight.  
**Next action:** No feasible formal path; watch literature.

## `DeGiorgi_six` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Paper/DeGiorgi.lean:152`  
**Statement:** De Giorgi's conjecture in dimension 6.  
**Source:** De Giorgi 1978; Savin, Annals 169 (2009) (conditional result)  
**Statement matches intent:** yes  
**Known status:** Open unconditionally (Savin conditional).  
**Difficulty:** math 9/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Same audited encoding as DeGiorgi_le_eight.  
**Next action:** No feasible formal path; watch literature.

## `dubner_conjecture` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Paper/Dubner.lean:58`  
**Statement:** Dubner's conjecture: every even number greater than 4208 is the sum of two twin primes (members of twin-prime pairs).  
**Source:** H. Dubner, 'Twin prime conjectures', J. Recreational Math. 30(3) 1999-2000  
**Statement matches intent:** yes  
**Known status:** Open. Strictly stronger than both the Goldbach conjecture (for n > 4208) and the twin prime conjecture (it implies infinitely many twin primes), so it is at least as hard as two famous open problems. Numerically verified to large bounds; 4208 is the largest known even number not so expressible. IsTwinPrime audited: ℕ-subtraction p-2 truncates only for p ≤ 2 where primality fails anyway (test lemmas t1-t5 confirm).  
**Difficulty:** math 10/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Implies twin prime conjecture: for any bound B one takes even n > max(4208,2B) and gets a twin prime ≥ n/2. Statement faithful.  
**Next action:** Not a target; any proof would be a historic breakthrough.

## `conj_7_1` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/Paper/FusibleNumber.lean:68`  
**Statement:** Erickson–Nivasch–Xu Conjecture 7.1 (reformulated): if y is the fusible successor of x with gap m, then every fusible q in the dyadic subinterval [y+1-m/2^n, y+1-m/2^(n+1)) arises by fusing the explicit (n+1)-st successor x+(2-1/2^n)m of x with another fusible number (given explicitly as 2q-1-x-(2-1/2^n)m).  
**Source:** J. Erickson, G. Nivasch, J. Xu, 'Fusible numbers and Peano Arithmetic', arXiv:2003.14342 / LMCS 18(3):6 (2022), Conjecture 7.1  
**Statement matches intent:** suspect — The file documents four deviations from the paper's Conjecture 7.1 (index shift, replacing s^(n+1)(x) by the explicit value x+(2-1/2^n)m, successor phrased as no-fusible-in-Ioo, explicit witness z). The substitution of the explicit successor value presupposes the conjectural successor-gap-halving structure; the equivalence with the paper's statement is asserted, not formally established, so the formal statement could differ from Conjecture 7.1 if that structure fails.  
**Known status:** Open. The paper proves the fusible numbers are well-ordered with order type ε₀ and establishes PA-unprovability results; Conjecture 7.1 on the local successor structure remains open. No internal work targets it.  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** IsFusible inductive definition matches the paper's definition exactly (smallest set containing 0 closed under (a+b+1)/2 for |a-b|<1); test lemmas for 1/2 and 1 are proved.  
**Flags:** documented reformulation — equivalence with paper's Conjecture 7.1 not formally established; needs literature check for the exact Conjecture 7.1 statement  
**Next action:** Verify the reformulation against the paper (small literature check); genuine resolution is research-level (the fusible ordering is proof-theoretically wild).

## `harthshorne_conjecture` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Paper/HartshorneConjecture.lean:101`  
**Statement:** Hartshorne's conjecture on vector bundles: every rank-2 algebraic vector bundle on ℙⁿ over ℂ with n ≥ 7 splits (is decomposable into two proper summands, hence a sum of line bundles).  
**Source:** R. Hartshorne, 'Varieties of small codimension in projective space', Bull. AMS 80 (1974), Conjecture 6.3  
**Statement matches intent:** yes  
**Known status:** Famous open problem in algebraic geometry (equivalent to: every smooth codimension-2 subvariety of ℙⁿ, n ≥ 7, is a complete intersection). Open even for n = 6 (conjecture is stated from 7). Splitting encoding audited: 'no component iso to the whole bundle' rules out X⊕0-type degenerate splittings, so a Splitting (Fin 2) of a rank-2 bundle forces two nonzero (line-bundle) summands — faithful for rank 2.  
**Difficulty:** math 10/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Category VectorBundles is the induced (full) subcategory of S.Modules, so isos and coproducts have the intended meaning provided the sorried HasFiniteCoproducts instance is in fact correct (finite direct sums of vector bundles are vector bundles).  
**Flags:** conjecture statement relies on a sorried API instance (hasFiniteCoproductsVectorBundles); declaration name typo 'harthshorne_conjecture'  
**Next action:** Not a target. Repo hygiene: the statement depends on the sorried instance hasFiniteCoproductsVectorBundles (needed for ∐ in Splitting) — that API theorem should be proven to make the conjecture statement self-contained; also fix the 'harthshorne' name typo.

## `countablyMonolithicSpace_card_lt` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/Paper/Homogenous.lean:95`  
**Statement:** Answer-encoded yes/no: does every homogeneous ω-monolithic compact Hausdorff space have cardinality at most the continuum? (Arhangel'skii 2013, Problem 16 — a monolithic variant of van Douwen's problem.)  
**Source:** Arhangel'skii, Selected Old Open Problems in General Topology (2013), Problem 16  
**Statement matches intent:** yes  
**Known status:** Open. Related to van Douwen's famous problem whether a homogeneous compactum can exceed 𝔠 (also open); the ω-monolithic restriction is Arhangel'skii's variant.  
**Difficulty:** math 9/10, Lean 10/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** Statement faithful modulo the cosmetic name mismatch.  
**Flags:** name/statement mismatch: _card_lt vs ≤ 𝔠 (cosmetic)  
**Next action:** Not a target; possibly independent of ZFC.

## `countablyMonolithicSpace_exists_nhds_generated_countable` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/Paper/Homogenous.lean:107`  
**Statement:** Answer-encoded yes/no: does every nonempty ω-monolithic compact Hausdorff space contain a point with countably generated neighborhood filter (a point of countable character)? (Arhangel'skii 2013, Problem 17.)  
**Source:** Arhangel'skii, Selected Old Open Problems in General Topology (2013), Problem 17  
**Statement matches intent:** suspect — Could not verify against the survey whether Problem 17 asks for a point of countable character or of countable π-character; the formalization uses full countable generation of 𝓝 x (countable character). If the original asks for π-character, the formal universal statement is strictly stronger and its answer could differ.  
**Known status:** Open as listed in the 2013 survey; no resolution known to me.  
**Difficulty:** math 8/10, Lean 10/10 · **Compute:** none · **Confidence:** low  
**Evidence:** (𝓝 x).IsCountablyGenerated is the correct Mathlib encoding of countable character at x; Nonempty X hypothesis correctly noted as needed.  
**Flags:** needs literature check: character vs π-character in the original Problem 17  
**Next action:** Literature check the exact wording of Problem 17 in [Ar2013] before any resolution attempt.

## `firstCountableTopology_of_countablyMonolithicSpace` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/Paper/Homogenous.lean:87`  
**Statement:** Answer-encoded yes/no: is every homogeneous ω-monolithic compact Hausdorff space first countable? (Arhangel'skii 2013, Problem 15.)  
**Source:** Arhangel'skii, Selected Old Open Problems in General Topology (2013), Problem 15  
**Statement matches intent:** yes  
**Known status:** Open. Known partial results connect ω-monolithic compacta of countable tightness to first countability under convergence hypotheses, but the homogeneous case is unresolved.  
**Difficulty:** math 8/10, Lean 10/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** CountablyMonolithicSpace class audited; MetrizableSpace instance for closures in metrizable spaces proved in-file as sanity check.  
**Next action:** Not a target.

## `homogeneousSpace_exists_inj_tendsto` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/Paper/Homogenous.lean:56`  
**Statement:** Answer-encoded yes/no: does every infinite homogeneous compact Hausdorff space contain a nontrivial (injective) convergent sequence? (Arhangel'skii 2013, Problem 13.)  
**Source:** Arhangel'skii, Selected Old Open Problems in General Topology (2013), Problem 13  
**Statement matches intent:** yes  
**Known status:** Longstanding open problem in the circle of Efimov's problem; no ZFC answer and, to my knowledge, no consistent counterexample known either. Injective convergent sequence correctly encodes 'nontrivial convergent sequence'; compact+T2 gives the survey's Tychonoff convention.  
**Difficulty:** math 9/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Type-0 quantification is the repo standard and realizes all relevant cardinalities; HomogeneousSpace class audited (homeomorphism transitivity).  
**Flags:** possible ZFC independence would make the answer-encoding unresolvable  
**Next action:** Not a target; possibly independent of ZFC, in which case the answer(sorry) iff is unprovable either way.

## `homogeneousSpace_exists_surjective` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/Paper/Homogenous.lean:65`  
**Statement:** Answer-encoded yes/no: is every compact Hausdorff space a continuous image of a homogeneous compact Hausdorff space? (Arhangel'skii 2013, Problem 14.)  
**Source:** Arhangel'skii, Selected Old Open Problems in General Topology (2013), Problem 14  
**Statement matches intent:** yes  
**Known status:** Open problem (attributed to van Douwen's circle of problems on homogeneous compacta). Formalization keeps Y in the same universe as X, which is harmless since Type 0 is closed under the standard constructions used for preimage spaces.  
**Difficulty:** math 9/10, Lean 10/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** Statement faithful: ∃ homogeneous compact Hausdorff Y and continuous surjection Y → X, for all compact Hausdorff X.  
**Next action:** Not a target; watch set-theoretic topology literature.

## `kurepa_conjecture` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Paper/Kurepa.lean:46`  
**Statement:** Kurepa's left-factorial conjecture: for all n > 2, n does not divide !n = 0! + 1! + ... + (n-1)!.  
**Source:** Đ. Kurepa 1971; Guy, Unsolved Problems in Number Theory, B44; OEIS A003422  
**Statement matches intent:** yes  
**Known status:** Open since 1971. A claimed proof by Barsky–Benzaghou (2004) was retracted (2011). Verified computationally for all primes up to ~2^40 (Andrejić–Tatarević and successors). The file proves (sorry-free) the reduction to odd primes and the gcd-form equivalence, plus decide-checks for n < 50 — the definition of left_factorial and the % n ≠ 0 encoding are faithful.  
**Difficulty:** math 9/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Long-recognized stubborn open problem in number theory; in-file textbook equivalences validate the formalization.  
**Next action:** Not a target; no known approach beyond computation.

## `kurepa_conjecture.variants.gcd` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Paper/Kurepa.lean:92`  
**Statement:** Equivalent gcd form of Kurepa's conjecture: gcd(n!, !n) = 2 for all n > 2.  
**Source:** Đ. Kurepa 1971; Guy B44  
**Statement matches intent:** yes  
**Known status:** Equivalent to the main conjecture — gcd_reduction is proved sorry-free in the file; decide-checked for n < 50.  
**Difficulty:** math 9/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** kurepa_conjecture.gcd_reduction (textbook, proved) establishes the equivalence internally.  
**Next action:** Not a target.

## `kurepa_conjecture.variants.prime` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Paper/Kurepa.lean:53`  
**Statement:** Kurepa's conjecture restricted to primes: for every prime p > 2, p does not divide !p.  
**Source:** Đ. Kurepa 1971; Guy B44  
**Statement matches intent:** yes  
**Known status:** Equivalent to the full conjecture — the equivalence (prime_reduction) is proved sorry-free in the same file — so exactly as open and as hard.  
**Difficulty:** math 9/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** kurepa_conjecture.prime_reduction (textbook, proved) shows the restriction carries the full content.  
**Next action:** Not a target.

## `LatinTableauConjecture` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/Paper/LatinTableau.lean:43`  
**Statement:** Latin Tableau Conjecture (CDS-colorability form): for every Young diagram, the graph on its cells with edges between cells sharing a row or column admits a proper ℕ-coloring whose first k color classes together attain the maximum size of a union of k independent sets, for every k.  
**Source:** T. Y. Chow, M. G. Tiefenbruck, 'The Latin Tableau Conjecture', Electron. J. Combin. 32(2) (2025) #P48; arXiv:2408.04086; originates in Chow–Fan–Goemans–Vondrák's wide partition conjecture work (~2003)  
**Statement matches intent:** yes  
**Known status:** Open. The 2025 EJC paper by Chow–Tiefenbruck studies the conjecture (equivalent to existence conditions for Latin tableaux of given shape and type, a generalization tied to Rota's basis conjecture / wide partition conjecture) and proves special cases; no proof of the full conjecture in the credible literature (an academia.edu 'constructive AI proof' preprint is not a credible source). Definitions audited: toSimpleGraph via fromRel is correct; CDSColorable's ∀k includes the degenerate k=0 case consistently (both sides 0); indepNumK's sSup is well-defined for finite graphs.  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** WebSearch confirms the EJC 2025 paper poses/studies the conjecture as open; repo-local defs in FormalConjecturesForMathlib/Combinatorics/{YoungDiagram,SimpleGraph/Coloring}.lean audited and faithful to the docstring.  
**Flags:** needs literature check for any post-2025 resolution; non-credible 'AI proof' preprint circulating (academia.edu) — do not treat as a solution  
**Next action:** Watch literature; partial progress possible by verifying small shapes computationally (per-shape statement is finitely checkable), but the ∀-diagram statement is open research.

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
**Flags:** proof depends on Lean.ofReduceBool/Lean.trustCompiler (native reflected LRAT), weaker than pure-kernel; 47 LRAT certificates not in repo: downloaded from third-party fork release, SHA-256 pinned; canonical decl still answer(sorry)/research open; FORMAL_CONJECTURES_STATUS_PATCH.diff unapplied; proof modules outside lake build (verify.sh + LEAN_PATH); cannot rebuild in this container; status patch flips only d5/ge3 variants; d3_int itself not in the diff though it is the campaign's core theorem  
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
**Flags:** proof depends on Lean.ofReduceBool/Lean.trustCompiler (native reflected LRAT), weaker than pure-kernel; 47 LRAT certificates not in repo: downloaded from third-party fork release, SHA-256 pinned; canonical decl still answer(sorry)/research open; FORMAL_CONJECTURES_STATUS_PATCH.diff unapplied; proof modules outside lake build (verify.sh + LEAN_PATH); cannot rebuild in this container; status patch omits this decl though the theorem exists  
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
**Flags:** proof depends on Lean.ofReduceBool/Lean.trustCompiler (native reflected LRAT), weaker than pure-kernel; 47 LRAT certificates not in repo: downloaded from third-party fork release, SHA-256 pinned; canonical decl still answer(sorry)/research open; FORMAL_CONJECTURES_STATUS_PATCH.diff unapplied; proof modules outside lake build (verify.sh + LEAN_PATH); cannot rebuild in this container  
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
**Flags:** proof depends on Lean.ofReduceBool/Lean.trustCompiler (native reflected LRAT), weaker than pure-kernel; 47 LRAT certificates not in repo: downloaded from third-party fork release, SHA-256 pinned; canonical decl still answer(sorry)/research open; FORMAL_CONJECTURES_STATUS_PATCH.diff unapplied; proof modules outside lake build (verify.sh + LEAN_PATH); cannot rebuild in this container  
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
**Flags:** proof depends on Lean.ofReduceBool/Lean.trustCompiler (native reflected LRAT), weaker than pure-kernel; 47 LRAT certificates not in repo: downloaded from third-party fork release, SHA-256 pinned; canonical decl still answer(sorry)/research open; FORMAL_CONJECTURES_STATUS_PATCH.diff unapplied; proof modules outside lake build (verify.sh + LEAN_PATH); cannot rebuild in this container  
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
**Flags:** proof depends on Lean.ofReduceBool/Lean.trustCompiler (native reflected LRAT), weaker than pure-kernel; 47 LRAT certificates not in repo: downloaded from third-party fork release, SHA-256 pinned; canonical decl still answer(sorry)/research open; FORMAL_CONJECTURES_STATUS_PATCH.diff unapplied; proof modules outside lake build (verify.sh + LEAN_PATH); cannot rebuild in this container  
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
