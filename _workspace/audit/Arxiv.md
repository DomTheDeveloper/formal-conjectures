# Audit detail — Arxiv

16 research-open declarations. Fields per problem: plain statement, source, category, match, status, action, difficulties, compute, confidence, evidence, flags.

## `curling_number_conjecture` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/Arxiv/0912.2382/CurlingNumberConjecture.lean:54`  
**Statement:** Starting from any finite nonempty integer sequence and repeatedly appending the curling number of the current sequence, one eventually appends a 1.  
**Source:** Chaffin-Sloane, The Curling Number Conjecture, arXiv:0912.2382  
**Statement matches intent:** yes  
**Known status:** Open. Verified computationally by Chaffin-Sloane for wide classes of starting sequences; no proof strategy known. No internal PR targets it.  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Definition k via sSup is well-posed: the witness set contains 0 and is bounded by |S| (k*|Y| <= |S| for Y nonempty), so sSup = max and equals the paper's curling number; the extension step and the 'eventually reach 1' claim (exists m with k(S_m)=1) faithfully mirror the conjecture.  
**Next action:** Keep open; no viable attack. Could formalize the known reduction facts (k(S)>=1 for nonempty S) as API only.

## `crystals_components_unique` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/Arxiv/1601.03081/UniqueCrystalComponents.lean:47`  
**Statement:** If an odd number n = ab is a 'crystal' (a,b > 1 and the biharmonic-mean quantity B(a,b) is an integer), then the pair {a,b} is the unique such factorization of n.  
**Source:** Abrate-Barbero-Cerruti-Murru, The Biharmonic mean, arXiv:1601.03081  
**Statement matches intent:** yes  
**Known status:** Open conjecture from the paper; no resolution found; no internal PR targets it.  
**Difficulty:** math 6/10, Lean 7/10 · **Compute:** small · **Confidence:** medium  
**Evidence:** IsCrystalWithComponents encodes B(a,b) in NN as the divisibility 2(a+1)(b+1) | (a+b)^2+(ab+1)^2 (verified on the paper's example 35=5*7, B=15); conclusion {a,b}={c,d} as Finsets correctly handles swapped pairs. Statement is faithful; problem is a niche open conjecture.  
**Flags:** needs literature check (niche 2016 conjecture, resolution would be easy to miss)  
**Next action:** Elementary-number-theory attack plausible: note (a+b)^2+(ab+1)^2 = (a^2+1)(b^2+1)+4ab and study the divisibility 2(a+1)(b+1) | ... ; also worth a computational scan for counterexamples before investing.

## `maximalLength_le_strong` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/Arxiv/1609.08688/sIncreasingrTuples.lean:245`  
**Statement:** The maximal length F(n) of a 2-increasing sequence of triples with entries in [n] satisfies F(n) <= n^{3/2}.  
**Source:** Gowers-Long, The length of an s-increasing sequence of r-tuples, arXiv:1609.08688, CPC 2021 (Conjecture 1.8)  
**Statement matches intent:** suspect — Formalized as the exact bound F(n) <= sqrt(n)^3 for every n. If the paper's Conjecture 1.8 is the asymptotic form F(n) = n^{3/2+o(1)}, the Lean statement is strictly stronger (though consistent with F(4)=8 being exactly 4^{3/2}); could not verify the paper's exact wording within the search budget.  
**Known status:** Open. Gowers-Long proved F(n) <= n^2/exp(Omega(log* n)) and F(n) >= n^{3/2} for squares; the n^{3/2} upper bound (in either exact or asymptotic form) remains open as far as I can determine. No internal PR targets it.  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** maximalLength is well-posed (pairwise lt2 forces distinct triples, so lengths are bounded by n^3 and sSup is a max); Real.sqrt n ^ 3 = n^{3/2} with correct coercions. Lower-bound and log* upper-bound companions in the file are marked research solved, matching the paper.  
**Flags:** exact-vs-asymptotic form of Conjecture 1.8 unverified; needs literature check for post-2021 progress on 2-increasing sequences  
**Next action:** Verify the exact wording of Conjecture 1.8 against the published paper and weaken to the asymptotic form if needed; otherwise keep open.

## `independentDominationEven` — Already solved externally (cat 1)

**File:** `FormalConjectures/Arxiv/2107.00295/IndependentDomination.lean:34`  
**Secondary category:** 5 (Solved mathematically, not yet formalized)  
**Statement:** For every nonempty isolate-free graph with even maximum degree D, the independent domination number satisfies (D+2)^2 i(G) <= (D^2+4) n.  
**Source:** Cho-Choi-Park, On independent domination of regular graphs, arXiv:2107.00295, Conjecture 1.6 (even case); solved by Cho-Kim-Kim-Oum, J. Combin. Theory Ser. B 158 (2023) 341-352, arXiv:2202.09594  
**Statement matches intent:** yes  
**Known status:** Proved externally. Cho-Kim-Kim-Oum (JCTB 2023) prove i(G) <= (1 - D/(floor(D^2/4)+D))(n-1)+1 for connected graphs with D=4 or D>=6 and state the Cho-Choi-Park conjecture as a corollary. Algebraic check: for even D this ratio identity gives exactly (D^2+4)/(D+2)^2 per component (equality on the clique-corona gadget K_{D/2+1} with D/2 pendants per vertex, n_0=(D+2)^2/4), and non-extremal components satisfy the strict (1-a)n bound, so the isolate-free statement follows; the remaining D=2 case is classical (components are paths/cycles, i = ceil(n/3) or n/2 for K2). No Lean proof exists anywhere.  
**Difficulty:** math 3/10, Lean 9/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Constants match the extremal family exactly: K_m with t pendants per vertex, m-1+t=D, m=D/2+1 gives i/n=(1+(m-1)t)/(m(1+t))=(D^2+4)/(D+2)^2. CKKO's bound is tight on exactly this gadget ((1/2)*8+1=5 on n=9 for D=4) and their paper explicitly claims the CCP conjecture as a corollary of Theorem 1.2. indepDominationNumber (sInf over independent dominating Finsets) is the standard i(G) and is attained (maximal independent sets exist).  
**Flags:** formalization effort is large despite external solution  
**Next action:** Reclassify to research solved and port the Cho-Kim-Kim-Oum discharging proof plus the easy D=2 case; large effort (research-scale graph-theory formalization).

## `independentDominationOdd` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/Arxiv/2107.00295/IndependentDomination.lean:47`  
**Statement:** For every nonempty isolate-free graph with odd maximum degree D, the independent domination number satisfies (D+1)(D+3) i(G) <= (D^2+3) n.  
**Source:** Cho-Choi-Park, On independent domination of regular graphs, arXiv:2107.00295, Conjecture 1.6 (odd case)  
**Statement matches intent:** yes  
**Known status:** Open as a whole, but almost entirely resolved: Cho-Kim-Kim-Oum (JCTB 2023, arXiv:2202.09594) prove it for odd D >= 7 (their ratio (D^2-1)/(D^2+4D-1) with the (n-1)+1 correction is tight exactly on the odd clique-corona gadget of size (D+1)(D+3)/4, yielding the conjectured constant); D=1 is trivial (perfect matchings, i=n/2); D=3 reduces to i <= n/2 for isolate-free subcubic graphs (known, cf. Goddard-Henning subcubic literature). The genuinely open case is D=5, explicitly excluded from CKKO's theorem.  
**Difficulty:** math 6/10, Lean 9/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** Same faithfulness analysis as the even case; constants match the odd extremal family (m=(D+3)/2, t=(D-1)/2, i=(D^2+3)/4, n=(D+1)(D+3)/4). CKKO's theorem covers D=4 and D>=6 only, leaving Delta=5 open, so the universally quantified Lean statement is not yet a theorem.  
**Flags:** only Delta=5 stands between this statement and cat 1; needs literature check for a post-2023 Delta=5 resolution  
**Next action:** Track the Delta=5 case in the literature (active area: e.g. the 2025 proof of the 3/8-conjecture for cubic graphs); if/when closed, the full odd statement becomes a porting task.

## `CollatzLike` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Arxiv/2107.12475/CollatzLike.lean:44`  
**Statement:** For every n > 8, the base-3 representation of 2^n contains the digit 2 (equivalently, 2^n is not a sum of distinct powers of 3).  
**Source:** Erdos 1979 (Some Unconventional Problems in Number Theory); Sterin-Woods, Hardness of Busy Beaver Value BB(15), arXiv:2107.12475  
**Statement matches intent:** yes  
**Known status:** Famous open Erdos conjecture; verified computationally to enormous bounds; equivalent to the halting of a 15-state Turing machine (whence BB(15) hardness). Only known exceptions n=0,2,8, matching the n>8 threshold (2^8=256=100111_3 checked in-file).  
**Difficulty:** math 9/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Nat.digits 3 (2^n) is the exact base-3 digit list; membership of 2 is precisely 'not a sum of distinct powers of 3'. Threshold and test case correct.  
**Flags:** related weaker statement exists at FormalConjectures/ErdosProblems/406.lean (finiteness form)  
**Next action:** None; no known approach (would require ternary-digit equidistribution for 2^n). Note the weaker finiteness form is separately formalized as ErdosProblems/406 (not a duplicate).

## `zariski_cancellation_problem` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Arxiv/2208.14736/ZariskiCancellation.lean:44`  
**Statement:** Zariski Cancellation Problem: over a characteristic-0 field k, if B[X] is k-isomorphic to k[x_1..x_n][X] for a finitely generated k-algebra B, then B is isomorphic to the polynomial ring.  
**Source:** Neena Gupta, The Zariski Cancellation Problem and related problems in Affine Algebraic Geometry, arXiv:2208.14736  
**Statement matches intent:** yes  
**Known status:** Major open problem of affine algebraic geometry for n >= 3 in characteristic 0. Known: n=1 (Abhyankar-Eakin-Heinzer), n=2 (Fujita, Miyanishi-Sugie), char p >= 3 counterexamples (Gupta 2014).  
**Difficulty:** math 10/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** IsCancellative quantifies over arbitrary finitely generated commutative k-algebras B with B[X] equiv A[X] implying B equiv A; since B[X] iso to a polynomial ring forces B to be a domain etc., admitting general CommRing B is harmless. Fintype iota covers all finite n including 0 (trivially true case).  
**Flags:** open question stated as positive assertion  
**Next action:** None; keep open. If ever attacked formally, the n<=2 solved variants in this file are the realistic targets.

## `conjecture_1_3` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Arxiv/2303.01089/FurstenbergTimesPTimesQ.lean:76`  
**Statement:** Furstenberg's times-p, times-q conjecture: the only atomless Borel probability measure on the circle invariant under both x -> px and x -> qx (p,q multiplicatively independent) is Lebesgue measure.  
**Source:** Furstenberg 1967; stated as Conjecture 1.3 in Badea-Grivaux, arXiv:2303.01089  
**Statement matches intent:** yes  
**Known status:** Major open problem in ergodic theory. Best known: Rudolph-Johnson (positive entropy case), Einsiedler-Katok-Lindenstrauss circle of results. No internal PR targets it.  
**Difficulty:** math 10/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Multiplicative independence encoded as Irrational(log p / log q) with p,q >= 2 is correct. The custom IsAtomLess class rules out point masses, and the non-ergodic atomless formulation is equivalent to the standard ergodic one: an atomless invariant measure cannot charge the countable set of finite orbits (all supported on rationals), so its ergodic components are a.e. Lebesgue. MeasurePreserving (Tn p) mu mu with Tn n x = n smul x is the correct invariance.  
**Next action:** None; keep open.

## `conjecture_1_1` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/Arxiv/2501.03234/ArithmeticSumS.lean:60`  
**Statement:** For every odd prime k, the theta-function analogue S(k) of the Dedekind-sum aggregate is strictly positive.  
**Source:** Berndt-Bhat-Meyer-Xie-Zaharescu, An Arithmetic Sum Associated with the Classical Theta Function, arXiv:2501.03234; Results in Mathematics (2026), doi:10.1007/s00025-025-02584-2  
**Statement matches intent:** yes  
**Known status:** Open. The published journal version (Results in Mathematics, 2026) still lists these conjectures as open. Values S(3)=2, S(5)=4, S(7)=10 (kernel-verified in-file) are consistent.  
**Difficulty:** math 7/10, Lean 8/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** S' uses Finset.Ico 1 k (j=1..k-1) and Nat.floor of (h*j : QQ)/k, matching the paper's floor(hj/k) for nonnegative arguments; k >= 3 from primality+oddness avoids division-by-zero junk. First 10 values kernel-checked against the paper's table (with the paper's own typo noted in-file).  
**Next action:** Investigate the paper's connection between S(p) and class numbers h(-p) (Dedekind-sum-style reciprocity); a proof likely needs character-sum/L-function positivity input.

## `conjecture_4_1` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/Arxiv/2501.03234/ArithmeticSumS.lean:67`  
**Statement:** For every prime k > 5, S(k) > k.  
**Source:** Berndt-Bhat-Meyer-Xie-Zaharescu, arXiv:2501.03234, Conjecture 4.1; Results in Mathematics (2026)  
**Statement matches intent:** yes  
**Known status:** Open per the 2026 published version.  
**Difficulty:** math 7/10, Lean 8/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** Threshold matches the paper (S(7)=10 > 7 consistent with in-file computed values). Faithful transcription.  
**Next action:** Same class-number/L-function route as Conjecture 1.1; numerically extend verification if useful.

## `conjecture_4_2` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/Arxiv/2501.03234/ArithmeticSumS.lean:74`  
**Statement:** For every prime k > 233, S(k) > 2k.  
**Source:** Berndt-Bhat-Meyer-Xie-Zaharescu, arXiv:2501.03234, Conjecture 4.2; Results in Mathematics (2026)  
**Statement matches intent:** yes  
**Known status:** Open per the 2026 published version.  
**Difficulty:** math 7/10, Lean 8/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** Faithful transcription with the paper's threshold.  
**Next action:** As for 4.1; the explicit thresholds (233, 3119) come from the authors' computations.

## `conjecture_4_3` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/Arxiv/2501.03234/ArithmeticSumS.lean:81`  
**Statement:** For every prime k > 3119, S(k) > 3k.  
**Source:** Berndt-Bhat-Meyer-Xie-Zaharescu, arXiv:2501.03234, Conjecture 4.3; Results in Mathematics (2026)  
**Statement matches intent:** yes  
**Known status:** Open per the 2026 published version.  
**Difficulty:** math 7/10, Lean 8/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** Faithful transcription with the paper's threshold.  
**Next action:** As for 4.1/4.2.

## `conjecture_4_4` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/Arxiv/2501.03234/ArithmeticSumS.lean:89`  
**Statement:** For every fixed n, all sufficiently large odd primes k satisfy S(k) > nk (i.e. S(k)/k tends to infinity along primes).  
**Source:** Berndt-Bhat-Meyer-Xie-Zaharescu, arXiv:2501.03234, Conjecture 4.4; Results in Mathematics (2026)  
**Statement matches intent:** yes  
**Known status:** Open per the 2026 published version. The in-file reduction theorems (4.4 from 1.1/4.1/4.2/4.3 for n=0..3) are already proven Lean-side.  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** Filter.atTop eventually-form with premises inside the eventuality is a faithful rendering of 'for all sufficiently large odd primes'.  
**Next action:** This superlinearity likely hinges on lower bounds for L(1,chi) (Siegel-type, possibly ineffective); treat as research problem.

## `conjecture_1_1` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Arxiv/2504.17644/Margulis.lean:38`  
**Statement:** Margulis's conjecture: for n >= 3, every relatively compact orbit of the diagonal subgroup on SL_n(R)/SL_n(Z) is closed.  
**Source:** Margulis, Problems and conjectures in rigidity theory (2000); stated as Conjecture 1.1 in Huang-Shi, arXiv:2504.17644  
**Statement matches intent:** yes  
**Known status:** Major open problem in homogeneous dynamics (Cassels-Swinnerton-Dyer/Littlewood circle; EKL proved the exceptional set for Littlewood has dimension 0). Huang-Shi disproved the function-field analogue (formalized as the separate research-solved theorem in this file, not in this batch).  
**Difficulty:** math 10/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Quotient SL(n,R)/image of SL(n,Z) with left multiplication action of diagonalSubgroup (defined in FormalConjecturesForMathlib via comap of the GL diagonal subgroup); IsCompact(closure(orbit)) -> IsClosed(orbit) is exactly 'bounded orbits are closed'. Topology instances come from Mathlib's matrix/quotient topology.  
**Next action:** None; keep open.

## `conjecture_2a` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/Arxiv/RestrictedRunTableaux.lean:56`  
**Statement:** Kauers-Zeilberger Conjecture 2a: the number G(n) of standard Young tableaux of shape (n,n,n) with every run of length >= 2 satisfies G(n) ~ C * 8^n / n^4 for some C > 0.  
**Source:** Kauers-Zeilberger, Counting Standard Young Tableaux With Restricted Runs, arXiv:2006.10205, Conjecture 2a  
**Statement matches intent:** yes  
**Known status:** Open. Kauers-Zeilberger state it as an experimentally supported conjecture and further conjecture these sequences are NOT P-recursive for >2 rows (also open per Zeilberger's 2021 follow-up arXiv:2104.01731). Internally: PR #165 (merged 2026-07-23) added the statement only; PRs #138/#158 are reduction scaffolding whose own descriptions say the fixed-endpoint Markov-additive cone local-limit theorem remains open - no proof exists.  
**Difficulty:** math 8/10, Lean 10/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** IsAdmissible = content (n,n,n) + ballot prefixes + no singleton runs over words Fin(3n) -> Fin 3 is the standard SYT encoding; G counts a decidable predicate over a Fintype, well-defined. Tendsto of G(n)*n^4/8^n to a positive constant is equivalent to the stated asymptotic.  
**Flags:** fork-authored encoding, values only partially cross-checked against the paper; needs literature check for a post-2020 proof  
**Next action:** Genuine research: prove a local limit theorem for the associated cone-constrained Markov-additive walk, or find a kernel-method derivation of the asymptotics; formalization would be research-scale.

## `banach_mazur_rotation_problem` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Arxiv/math.0110202/BanachMazurRotation.lean:43`  
**Statement:** Banach-Mazur rotation problem: is every separable Banach space whose linear isometry group acts transitively on the unit sphere linearly isometric to a Hilbert space?  
**Source:** Banach 1932; Randrianantoanina, A note on Banach-Mazur problem, arXiv:math/0110202  
**Statement matches intent:** yes  
**Known status:** Famous open problem (90+ years). Known: finite-dimensional case is yes (Mazur, formalized as the research-solved variant in this file); non-separable transitive non-Hilbert examples exist, so separability is essential and is correctly included.  
**Difficulty:** math 10/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** answer(sorry) <-> forall E [Banach, separable, IsPretransitive of E's linear isometry group on sphere 0 1], E isometric to some real inner-product space: quantifiers and instances are right (completeness + separability + linear isometric transitivity), and the degenerate E = 0 case is benignly true (0-dim Hilbert space). The answer-encoding asks for the actual yes/no, which is faithful for an open question.  
**Next action:** None; keep open.
