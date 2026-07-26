# Audit detail — ErdosProblems

168 research-open declarations. Fields per problem: plain statement, source, category, match, status, action, difficulties, compute, confidence, evidence, flags.

## `erdos_1` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/ErdosProblems/1.lean:45`  
**Statement:** If A is a subset of {1,...,N} with all subset sums distinct and |A| = n, then N >> 2^n, i.e. there is an absolute constant C > 0 with N > C*2^n. Erdos's famous $500 sum-distinct-set problem.  
**Source:** https://www.erdosproblems.com/1 ($500 prize); Erdos-Moser [Er56]; OEIS A276661  
**Statement matches intent:** yes  
**Known status:** Open on erdosproblems.com as of 2026-07-26 ($500). Best known: N >= (sqrt(2/pi) - o(1)) 2^n/sqrt(n) (Elkies-Gleason, formalized as solved variants in the file); the sqrt(n) gap has resisted improvement for ~70 years. No internal PR/campaign targets it.  
**Difficulty:** math 9/10, Lean 9/10 · **Compute:** none · **Confidence:** high  
**Evidence:** IsSumDistinctSet correctly encodes A subseteq Icc 1 N with injective subset-sum map on the powerset subtype. Quantifier order (exists C, forall N A) is the intended absolute-constant form; strict < vs >= only rescales C. The weaker 2^n/n bound is fully proved in-file (variants.weaker), confirming definitions are usable.  
**Next action:** Keep open. No formal action; monitor literature for improvements past 2^n/sqrt(n).

## `erdos_1.variants.real` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/ErdosProblems/1.lean:114`  
**Statement:** Generalization to finite sets A of reals in (0, N] whose subset sums pairwise differ by at least 1: must N >> 2^{|A|}?  
**Source:** https://www.erdosproblems.com/1; [Er73], [ErGr80]  
**Statement matches intent:** yes  
**Known status:** Open; strictly generalizes the $500 integer problem (an integer sum-distinct set has 1-separated subset sums), so at least as hard.  
**Difficulty:** math 9/10, Lean 9/10 · **Compute:** none · **Confidence:** high  
**Evidence:** IsSumDistinctRealSet demands coe A subseteq Ioc 0 N and pairwise (on distinct sub-finsets of the powerset) dist of sums >= 1, which forces all subset sums distinct and 1-separated - the intended real generalization. Restricting to integer sets recovers erdos_1's hypothesis, so implication direction is right.  
**Next action:** Keep open; any resolution of erdos_1 in the negative would need checking here; a proof of this implies erdos_1 up to constants.

## `erdos_10` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/10.lean:39`  
**Statement:** Is there a fixed k such that every integer >= 2 is the sum of a prime and at most k powers of 2? Encoded as answer(sorry) <-> exists k with the representable set equal to univ minus {0,1}.  
**Source:** https://www.erdosproblems.com/10; Gallagher [Ga75]; Granville-Soundararajan [GrSo98]  
**Statement matches intent:** yes  
**Known status:** Open on erdosproblems.com as of 2026-07-26. Gallagher: lower density 1 - eps for k(eps). Erdos suspected the answer is no (covering-congruence heuristics).  
**Difficulty:** math 9/10, Lean 9/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Set equality with univ \ {0,1} is exactly right: representable numbers are >= 2 (p >= 2, powers >= 1... actually >= 0 summands nonneg), and the 'exists k' quantifier makes 'every n >= 2' equivalent to 'every large n' since any n >= 2 equals 2 + (binary rep of n-2), i.e. is representable with <= log2 n powers. Multiset repetitions are harmless (2^a + 2^a merges by carrying to <= as many distinct powers).  
**Flags:** powers of 2 include 2^0 = 1 and may repeat; both are immaterial to the exists-k question but note original sources sometimes restrict to exponent >= 1  
**Next action:** Keep open. A negative answer might come from covering-system constructions; monitor.

## `erdos_10.variants.granville_soundararajan_odd` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/10.lean:62`  
**Statement:** Granville-Soundararajan conjecture: every odd n > 1 is a prime plus at most 3 powers of 2, and every even n != 0 is a prime plus at most 4 powers of 2.  
**Source:** https://www.erdosproblems.com/10; Granville-Soundararajan, A Binary Additive Problem of Erdos and the Order of 2 mod p^2 (1998)  
**Statement matches intent:** yes  
**Known status:** Open conjecture. Consistent with Crocker (infinitely many integers are not p + 2^a + 2^b) and with Grechuk's even example 1117175146 requiring 4 powers.  
**Difficulty:** math 9/10, Lean 9/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** Odd part matches the docstring/site claim; even part follows from odd part plus one extra 2^0, matching the 'hence at most 4' phrasing. Small cases check out (3 = 2+1, 2 = 2 with zero powers), so no vacuity/falsity at the boundary.  
**Next action:** Keep open. Disproof would require a large computational search for an odd counterexample; no certificate path for a proof.

## `erdos_10.variants.grechuk` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/10.lean:91`  
**Statement:** There exist infinitely many even integers that are not the sum of a prime and at most 3 powers of 2 (suggested by Bogdan Grechuk; open).  
**Source:** https://www.erdosproblems.com/10 (additional commentary by B. Grechuk)  
**Statement matches intent:** yes  
**Known status:** Open. The k=2 analogue (two powers) is known and formalized as a solved variant (two_pows) in the same file; one even example for three powers (1117175146) is known.  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** Statement Set.Infinite ({even n} \ sumPrimeAndTwoPows 3) is exactly Grechuk's suggested strengthening; compatible with the GrSo conjecture (even numbers may need 4 powers).  
**Next action:** Keep open. Plausible avenue: Crocker/covering-congruence style arguments extended to three powers; monitor erdosproblems.com/10 commentary.

## `erdos_100` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/100.lean:40`  
**Statement:** Points in the plane with all pairwise distances >= 1 and distinct distances differing by >= 1: must the diameter be >= Cn for some absolute C > 0? Encoded as answer(sorry) <-> exists C, eventually-in-n, all such n-point sets have diameter > Cn.  
**Source:** https://www.erdosproblems.com/100; Guth-Katz Ann. of Math. (2015); Kanold; Piepmeyer example  
**Statement matches intent:** yes  
**Known status:** Open on erdosproblems.com as of 2026-07-26. Known: diam >= n^{3/4} (Kanold), diam >> n/log n (via Guth-Katz distinct distances). Verified via web search that the original hypothesis includes 'all pairwise distances at least 1' in addition to 1-separation of distinct distances.  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** none · **Confidence:** high  
**Evidence:** DistancesSeparated quantifies over possibly-equal points, so comparing with dist p p = 0 forces every distance >= 1; per erdosproblems.com/100 (checked 2026-07-26 via search snippet: 'all pairwise distances are at least 1 and if two distinct distances differ then they differ by at least 1') this is exactly the intended hypothesis, so the encoding is faithful, not an accidental strengthening.  
**Next action:** Keep open. Closing the log n gap requires strengthening distinct-distance counts under the separation hypothesis.

## `erdos_100.variants.strong` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/100.lean:49`  
**Statement:** Strong form: for sufficiently large n, every such separated n-point set has diameter >= n - 1.  
**Source:** https://www.erdosproblems.com/100 ('perhaps even >= n-1')  
**Statement matches intent:** yes  
**Known status:** Open. Tightness witnessed by n equally spaced collinear points (diameter exactly n-1); Piepmeyer's 9-point example with diameter < 5 (formalized separately) shows small-n failures, consistent with the eventually-quantifier.  
**Difficulty:** math 9/10, Lean 9/10 · **Compute:** none · **Confidence:** high  
**Evidence:** n - 1 elaborates at expected type Real, so it is real subtraction of the cast (no Nat truncation). The eventual filter correctly excludes small-n counterexamples like Piepmeyer's 9 points.  
**Next action:** Keep open.

## `erdos_1002` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/1002.lean:39`  
**Statement:** Does f(alpha,n) = (1/log n) * sum_{k<=n} (1/2 - {alpha k}) have an asymptotic distribution function in alpha over (0,1)? Kesten proved the analogous two-variable (alpha,beta) result with a Cauchy law.  
**Source:** https://www.erdosproblems.com/1002; Kesten, Ann. of Math. (1960)  
**Statement matches intent:** yes  
**Known status:** Open on erdosproblems.com as of 2026-07-26. Kesten's 1960 theorem for the shifted average is the natural avenue; the single-variable question remains open.  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** Formalization matches docstring/site phrasing: monotone g with limits 0 at -infty and 1 at +infty and pointwise convergence of the measure of the sublevel set. Int.fract correctly encodes {alpha k}; volume/toReal on (0,1) is right.  
**Flags:** requires convergence at every c, not only at continuity points of g (stronger than the classical notion, but innocuous if the limit law is continuous as in Kesten's theorem); f(alpha,1) uses 1/log 1 = 1/0 = 0 junk; irrelevant to the limit  
**Next action:** Keep open; a proof would likely adapt Kesten's method (substantial analytic work).

## `erdos_1003` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/1003.lean:34`  
**Statement:** Are there infinitely many n with phi(n) = phi(n+1)?  
**Source:** https://www.erdosproblems.com/1003; OEIS A001274; [EPS87]  
**Statement matches intent:** yes  
**Known status:** Open on erdosproblems.com as of 2026-07-26. Known solutions 1, 3, 15, 104, ... ; infinitude follows from standard prime-pattern conjectures (Dickson/Schinzel) but is unconditionally open. EPS87 upper bound on solution counts formalized as solved variant.  
**Difficulty:** math 9/10, Lean 9/10 · **Compute:** none · **Confidence:** high  
**Evidence:** answer(sorry) <-> Set.Infinite {n | phi n = phi (n+1)} is a faithful yes/no encoding; phi is Nat.totient via scoped notation.  
**Next action:** Keep open.

## `erdos_1003.variants.Icc` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/1003.lean:44`  
**Statement:** For every k >= 1, are there infinitely many n with phi(n) = phi(n+1) = ... = phi(n+k)?  
**Source:** https://www.erdosproblems.com/1003; Erdos [Er85e]  
**Statement matches intent:** yes  
**Known status:** Open. Even a single example for k = 3 (four equal consecutive totients) appears to be unknown; k = 2 has n = 5186. Conditional on prime k-tuple type conjectures.  
**Difficulty:** math 9/10, Lean 9/10 · **Compute:** none · **Confidence:** high  
**Evidence:** forall i in Set.Icc 1 k, phi n = phi (n+i) correctly chains the k+1 equal values; k = 1 instance recovers the base problem, so the answer-encoded universal statement matches Erdos's 'presumably for every k'.  
**Next action:** Keep open; small-case searches for k = 3 could add value but are not certificates for the conjecture.

## `erdos_1004` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/1004.lean:38`  
**Statement:** For every fixed c > 0 and all large x, is there n <= x such that phi(n+1), ..., phi(n+floor((log x)^c)) are pairwise distinct?  
**Source:** https://www.erdosproblems.com/1004; Erdos-Pomerance-Sarkozy [EPS87]  
**Statement matches intent:** yes  
**Known status:** Open on erdosproblems.com as of 2026-07-26. EPS87 upper bound K <= n/exp(c (log n)^{1/3}) formalized as solved variant in the same file.  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** IsDistinctTotientRun n K = InjOn totient on Icc (n+1) (n+K) matches 'phi(n+k) distinct for 1 <= k <= K'; floor of (log x)^c is the correct integer threshold; the eventually-atTop and exists n <= x quantifiers mirror the prose.  
**Next action:** Keep open.

## `erdos_101` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/101.lean:50`  
**Statement:** Given n points in the plane with no five collinear, is the maximum number of lines containing exactly four of the points o(n^2)? ($100 prize.)  
**Source:** https://www.erdosproblems.com/101 ($100); related to the orchard problem / Green-Tao (2013)  
**Statement matches intent:** yes  
**Known status:** Open on erdosproblems.com as of 2026-07-26. Green-Tao resolved the 3-point-line orchard problem; the 4-point analogue and this o(n^2) question remain open.  
**Difficulty:** math 9/10, Lean 9/10 · **Compute:** none · **Confidence:** high  
**Evidence:** linesWithPointsFor 4 S counts spanned lines meeting S in exactly 4 points (ncard = 4); with NonCollinearFor 5 (no 5-element subset collinear) 'exactly 4' equals '>= 4'. numLinesWithFourPointMax's sSup is over a nonempty set bounded by C(n,2), so well-defined; S.Finite is a separate binder so infinite-set ncard junk is excluded. The o(n^2) claim is the conjectured direction stated on the site.  
**Next action:** Keep open; formalizing known lower-bound constructions (file TODO) is the only near-term formal work.

## `erdos_1038.parts.i` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/1038.lean:36`  
**Statement:** Determine the infimum, over nonconstant monic real polynomials with all roots in [-1,1], of the Lebesgue measure of {x : |f(x)| < 1}. Encoded as answer(sorry) = the infimum.  
**Source:** https://www.erdosproblems.com/1038; Erdos-Herzog-Piranian; Tao, 'Sublevel sets of logarithmic potentials' (Dec 2025)  
**Statement matches intent:** yes  
**Known status:** Open on erdosproblems.com as of 2026-07-26. Tao (2025) proved the infimum lies in [2^{4/3} - 1, ~1.835) and determined the supremum (2*sqrt(2)); the exact infimum is open (both bounds formalized as solved variants in the file).  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** 'All roots real and in [-1,1]' is encoded by (roots.filter (mem Icc)).card = natDegree, which forces the real-root count with multiplicity to equal the degree - correct. Monic and f != 1 exactly captures nonconstant monic. Index type is nonempty (f = X), so the ENNReal infimum is honest.  
**Flags:** unused binder (n : Nat) in the theorem signature - cosmetic only  
**Next action:** Keep open; the exact constant is a live research question with recent activity (Tao 2025).

## `erdos_1041` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/1041.lean:65`  
**Statement:** For every monic f in C[X] of degree n >= 2 with all roots in the open unit disk, must two roots (with multiplicity) be joined by a path of length < 2 inside the lemniscate {|f(z)| < 1}?  
**Source:** https://www.erdosproblems.com/1041; Erdos-Herzog-Piranian, J. Analyse Math. (1958)  
**Statement matches intent:** yes  
**Known status:** erdosproblems.com state 'falsifiable' = still open as of 2026-07-26. The EHP component lemma (two roots share a component of the sublevel set) is formalized as a solved companion in the file.  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** Multiset ({z1,z2}) <= f.roots correctly requires multiplicity 2 when z1 = z2, so the trivial constant path is available only at genuinely repeated roots, matching 'two roots with multiplicity'. Length as H^1 of the path image is equivalent to arclength < 2 up to extracting an arc from the rectifiable continuum, so no material weakening. Hypotheses (monic, natDegree = n >= 2, rootSet in ball 0 1) are all included via the include block.  
**Flags:** length is H^1 of the image rather than total variation of the path - equivalent for the existence question but worth noting  
**Next action:** Keep open; a counterexample would be an explicit polynomial with a certified length lower bound (hard to certify numerically).

## `erdos_1049` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/ErdosProblems/1049.lean:39`  
**Statement:** For every rational t > 1, is sum_{n>=1} 1/(t^n - 1) irrational? (Chowla's conjecture; Erdos proved it for integer t >= 2.)  
**Source:** https://www.erdosproblems.com/1049; Erdos [Er48]  
**Statement matches intent:** yes  
**Known status:** Open on erdosproblems.com as of 2026-07-26. Erdos's 2-adic method proves integer t >= 2 (solved variant in file); for non-integer rational t (e.g. t = 3/2) no irrationality proof is known to me.  
**Difficulty:** math 9/10, Lean 9/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** The tsum over PNat of 1/((t:R)^n - 1) converges for t > 1 and matches the Lambert series; the file even proves the divisor-sum identity (lambert_series_eq_num_divisor_sum) sorry-free. The answer <-> forall-t encoding matches the site's universally-quantified question.  
**Flags:** needs literature check for partial results on rational non-integer t (Bezivin/Duverney-type q-series methods)  
**Next action:** Keep open; needs a genuinely new irrationality technique for rational non-integer bases.

## `erdos_1052` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/1052.lean:38`  
**Statement:** Are there only finitely many unitary perfect numbers (n equal to the sum of its proper unitary divisors)?  
**Source:** https://www.erdosproblems.com/1052 ($10); OEIS A002827; Subbarao-Warren 1966; Wall 1975  
**Statement matches intent:** yes  
**Known status:** Open on erdosproblems.com as of 2026-07-26. Exactly five unitary perfect numbers known (6, 60, 90, 87360, Wall's 24-digit number - all appear as test lemmas in the file); finiteness is a long-standing open question.  
**Difficulty:** math 9/10, Lean 9/10 · **Compute:** none · **Confidence:** high  
**Evidence:** properUnitaryDivisors = {d in [1,n) : d | n, gcd(d, n/d) = 1} plus sum = n and n > 0 is the standard definition (equivalent to sigma*(n) = 2n); test lemmas for 6, 60, 90 are proved by decide, validating the encoding. answer <-> Set.Finite is a faithful yes/no encoding.  
**Next action:** Keep open.

## `erdos_1054.parts.i` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/1054.lean:38`  
**Statement:** Let f(n) be the least m such that n is the sum of the k smallest divisors of m for some k >= 1. Is f(n) = o(n)?  
**Source:** https://www.erdosproblems.com/1054; OEIS A167485  
**Statement matches intent:** yes  
**Known status:** Open on erdosproblems.com as of 2026-07-26.  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** f uses Nat.find on the existential over m, giving the minimal m - correct reading. Junk value f(n) = 0 at non-representable n (the file itself proves f 2 = 0 and f 5 = 0) only helps the o(n) claim, matching the intended restriction to representable n. Nat.nth junk zeros for k exceeding the divisor count add no new representable values (they reproduce k = d(m)), so no spurious representations.  
**Flags:** junk value 0 at non-representable n; benign for the o(n) direction  
**Next action:** Keep open.

## `erdos_1054.parts.ii` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/1054.lean:44`  
**Statement:** With the same f, is f(n) = o(n) for almost all n (i.e. along a set of density 1)?  
**Source:** https://www.erdosproblems.com/1054  
**Statement matches intent:** yes  
**Known status:** Open on erdosproblems.com as of 2026-07-26.  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** Exists density-1 set A with littleo along the subtype A (atTop on the induced order) is a reasonable encoding of 'for almost all n'; density-1 forces A infinite so the subtype filter is nontrivial.  
**Next action:** Keep open.

## `erdos_1054.parts.iii` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/1054.lean:51`  
**Statement:** With the same f, is limsup_n f(n)/n = infinity?  
**Source:** https://www.erdosproblems.com/1054  
**Statement matches intent:** suspect — The statement wraps the limsup in 'exists A, A.HasDensity 1 and ...' but A never occurs in the limsup (copy-paste from parts.ii). Since Set.univ has density 1, the conjunct is trivially witnessed and the statement is logically equivalent to limsup f(n)/n = top over all n - i.e. the intended question - so this is dead code, not a semantic break.  
**Known status:** Open on erdosproblems.com as of 2026-07-26.  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** The bound variable A is unused in 'atTop.limsup (fun n => (f n : EReal) / n) = top', so the existential collapses to True; EReal division junk at n = 0 and junk f-values 0 at non-representable n cannot lower a limsup, so the reduction to the intended limsup question is exact.  
**Flags:** dead existential conjunct (unused density-1 set A); EReal division at n = 0 is junk but irrelevant  
**Next action:** Suggest upstream cleanup: drop the dead 'exists A, HasDensity 1' conjunct. Mathematically keep open.

## `erdos_1055` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/ErdosProblems/1055.lean:59`  
**Secondary category:** 4 (Vacuously true / accidentally weakened)  
**Statement:** In the Erdos-Selfridge classification (class 1: p+1 has only prime factors 2,3; class r: all prime factors of p+1 of class <= r-1 with equality for one), are there infinitely many primes in each class r?  
**Source:** https://www.erdosproblems.com/1055; OEIS A005113  
**Statement matches intent:** suspect — IsOfClass has a vacuity bug at r = 2: the 'equality for at least one prime factor' clause unfolds to 'forall m <= 1, IsOfClass m q -> m = 1', which is trivially true, so IsOfClass 2 p holds for every prime all of whose p+1-factors are class 1 - including all class-1 primes themselves. Hence the r = 2 instance asserts infinitude of (class 1 union class 2), weaker than the intended 'infinitely many primes of class exactly 2'. For r = 1 and r >= 3 the predicate provably coincides with the intended exact class (the witness clause becomes nontrivial).  
**Known status:** Open on erdosproblems.com as of 2026-07-26. Even the r = 1 instance (infinitude of primes p with p+1 = 2^a 3^b) is a Mersenne-like open problem.  
**Difficulty:** math 9/10, Lean 9/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** Unfolding PNat.caseStrongInductionOn: for r = 2 the second conjunct is 'exists q in (p+1).primeFactors, forall m <= 1, H m q -> m = 1', vacuous because m : PNat with m <= 1 forces m = 1. Concretely IsOfClass 2 2 holds (3 is class 1) even though 2 is class 1, so classes are not exclusive at level 2. By induction the defect does not propagate to r >= 3.  
**Flags:** IsOfClass 2 includes class-1 primes (vacuous exactness clause at r=2): r=2 instance accidentally weakened; r = 1 instance alone is an open Mersenne-like infinitude problem  
**Next action:** Report spec defect upstream: fix the r = 2 clause (e.g. require IsOfClass n q for the witness and non-membership in classes < n). Mathematically keep open.

## `erdos_1055.variants.erdos_limit` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/1055.lean:68`  
**Statement:** With p_r the least prime of class r, Erdos's conjecture that p_r^{1/r} tends to infinity.  
**Source:** https://www.erdosproblems.com/1055; OEIS A005113  
**Statement matches intent:** yes  
**Known status:** Open. Mutually exclusive with the Selfridge variant below - at most one of the two 'research open' statements is true.  
**Difficulty:** math 9/10, Lean 9/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** p r = Nat.find (exists_p r) is the least prime satisfying IsOfClass r; for r >= 3 (and r = 1) IsOfClass matches the intended exact class, so the r -> infinity limit statement is faithful.  
**Flags:** depends on sorried exists_p for well-definedness of Nat.find; contradicts selfridge_limit - the pair cannot both be provable  
**Next action:** Keep open; note the def p depends on the sorried existence theorem exists_p (every class nonempty), itself nontrivial.

## `erdos_1055.variants.selfridge_limit` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/1055.lean:78`  
**Statement:** Selfridge's competing conjecture that p_r^{1/r} is bounded.  
**Source:** https://www.erdosproblems.com/1055; OEIS A005113  
**Statement matches intent:** yes  
**Known status:** Open. Mutually exclusive with erdos_limit.  
**Difficulty:** math 9/10, Lean 9/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** exists M, forall r, (p r)^{1/r} <= M is the boundedness claim; asymptotics dominated by r >= 3 where IsOfClass is exact.  
**Flags:** depends on sorried exists_p; contradicts erdos_limit - the pair cannot both be provable  
**Next action:** Keep open.

## `erdos_1056` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/1056.lean:39`  
**Statement:** For every k >= 2, do there exist a prime p and k consecutive integer intervals I_1,...,I_k (sharing endpoints) with the product over each interval congruent to 1 mod p?  
**Source:** https://www.erdosproblems.com/1056; Guy, Unsolved Problems A15; OEIS A060427  
**Statement matches intent:** yes  
**Known status:** Open on erdosproblems.com as of 2026-07-26. k = 2 (Erdos: 3*4 = 5*6*7 = 1 mod 11) and k = 3 (Makowski mod 17) known and proved by decide in the file.  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Fin arithmetic checked: i.castSucc + 1 in Fin (k+1) never wraps for i : Fin k, so the k intervals [b_i, b_{i+1}) genuinely tile a range; StrictMono makes each interval nonempty; intervals containing 0 or a multiple of p give product = 0 mod p, so no degenerate witnesses. answer <-> forall k >= 2 matches the intended arbitrary-k question.  
**Flags:** docstring typos ('mod n' for 'mod p'; 'I_0,...,I_k' for k intervals) - formal statement is correct  
**Next action:** Keep open. Searching for k = 4 witnesses is a natural computational contribution (a found witness certifies the k = 4 instance by decide) but does not resolve the all-k question.

## `erdos_1056.variants.noll_simmons` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/1056.lean:69`  
**Statement:** Noll-Simmons: for arbitrarily large k, do there exist a prime p and q_1 < ... < q_k < p with q_1! = q_2! = ... = q_k! mod p?  
**Source:** https://www.erdosproblems.com/1056 (Noll-Simmons question)  
**Statement matches intent:** yes  
**Known status:** Open on erdosproblems.com as of 2026-07-26.  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** The Q i < p constraint correctly blocks the trivial loophole q_i >= p (all factorials = 0 mod p). 'Eventually all k' is equivalent to 'arbitrarily large k' since a k-solution restricts to any smaller k. Wilson-type identities (0! = 1! = 1, (p-2)! = 1) give small-k witnesses only, so no trivialization.  
**Flags:** Q i : Nat may be 0 (0! = 1) - at most shifts k by one versus a positive-integer reading; immaterial  
**Next action:** Keep open; computational search for large-k witnesses is possible but only certifies individual k.

## `erdos_1057` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/ErdosProblems/1057.lean:53`  
**Statement:** Is the Carmichael-number counting function C(x) equal to x^{1-o(1)}, i.e. does log C(x)/log x tend to 1?  
**Source:** https://www.erdosproblems.com/1057; Guy UPINT A13; AGP Ann. of Math. 1994  
**Statement matches intent:** yes  
**Known status:** Open (erdosproblems.com state open). Best lower bound C(x) > x^{0.3389} (Lichtman 2022); upper bound x^{1-o(1)} follows from Erdos 1956. The full lower bound x^{1-o(1)} is a recognized hard open problem tied to smooth shifted primes / primes in APs to large moduli.  
**Difficulty:** math 9/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Tendsto (log C(x)/log x) -> 1 is the standard rendering of C(x)=x^{1-o(1)}. carmichaelCounting uses ncard of a finite truncation, well-defined; Real.log junk at small x irrelevant at atTop. Faithful.  
**Next action:** Leave open. answer is believed True but proving it needs a breakthrough in analytic number theory; no formal path.

## `erdos_1057.variants.pomerance` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/ErdosProblems/1057.lean:73`  
**Statement:** Pomerance's refinement: is C(x) = x*exp(-(1+o(1)) log x * logloglog x / loglog x)?  
**Source:** https://www.erdosproblems.com/1057; Pomerance 1989 heuristic  
**Statement matches intent:** yes  
**Known status:** Open; strictly stronger than the main x^{1-o(1)} question (pins the exact second-order term). Only a heuristic supports it.  
**Difficulty:** math 9/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Algebra checks: log(C(x)/x) = -(1+o(1)) log x logloglog x/loglog x iff -(log(C(x)/x)*loglog x)/(log x*logloglog x) -> 1, exactly the formal limit. Junk values (log 0 = 0 for x < 561) occur only on a bounded range, harmless under atTop.  
**Next action:** Leave open; at least as hard as erdos_1057.

## `erdos_1059` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/1059.lean:37`  
**Statement:** Are there infinitely many primes p such that p - k! is composite for every k with 1 <= k! < p?  
**Source:** https://www.erdosproblems.com/1059; OEIS A064152  
**Statement matches intent:** yes  
**Known status:** Open per erdosproblems.com. File includes kernel-checked examples (p=101, 211 qualify; 89 does not), evidencing the definitions behave as intended.  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** none · **Confidence:** high  
**Evidence:** d ranges over factorials < p so Nat subtraction p - d never truncates; d = 1 = 0! included as intended; Nat.Composite = 1 < n and not prime excludes the p = k!+1 edge case (p - k! = 1) exactly as in the prose. Decidable mirror definitions proven equivalent in-file.  
**Next action:** Leave open. Any progress would come from covering-system / sieve constructions; no formal shortcut.

## `erdos_1060.parts.i` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/1060.lean:35`  
**Statement:** The number f(n) of k with k*sigma(k) = n satisfies f(n) <= n^{h(n)} for some h = o(1/loglog n).  
**Source:** https://www.erdosproblems.com/1060; OEIS A327153  
**Statement matches intent:** yes  
**Known status:** Open. Any solution k divides n, so f(n) <= d(n) = n^{O(1/loglog n)} is classical; the conjecture upgrades O to o. Multiplicity f(n) >= 2 really occurs (12*sigma(12) = 14*sigma(14) = 336), so the statement is not degenerate.  
**Difficulty:** math 7/10, Lean 9/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** Existential-h encoding of f(n) = n^{o(1/loglog n)} is faithful: h is unconstrained where f(n) = 0 and can absorb finitely many small n; conjectured direction stated as the theorem, consistent with 'research open'.  
**Next action:** Leave open; would need multiplicative-structure arguments beyond the divisor bound.

## `erdos_1060.parts.ii` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/1060.lean:41`  
**Statement:** The number of k with k*sigma(k) = n is at most polylogarithmic in n: f(n) = O((log n)^C) for some C.  
**Source:** https://www.erdosproblems.com/1060  
**Statement matches intent:** yes  
**Known status:** Open; strictly stronger than parts.i (polylog is far below n^{o(1/loglog n)}). Far beyond current techniques for divisor-multiplicity problems.  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** Straightforward =O formalization; rpow/log junk at n <= 1 is irrelevant since IsBigO at atTop is an eventual bound.  
**Next action:** Leave open.

## `erdos_1061` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/1061.lean:45`  
**Statement:** Is the number of ordered pairs (a,b) with a+b <= x and sigma(a)+sigma(b) = sigma(a+b) asymptotic to c*x for some c > 0?  
**Source:** https://www.erdosproblems.com/1061; Guy UPINT B15; OEIS A110177  
**Statement matches intent:** yes  
**Known status:** Open per erdosproblems.com. Heuristics suggest solutions come mainly from pairs tied to specific divisibility patterns; existence of the asymptotic constant is unproven.  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** S(x) counts ordered pairs in Icc 1 floor(x) with a + b <= x; ordered-vs-unordered only rescales the constant, which is existentially quantified, so the encoding is faithful. IsEquivalent at atTop is the right notion for ~ c*x.  
**Next action:** Leave open. A first milestone would be positive lower density of solutions.

## `erdos_1062.parts.ii` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/1062.lean:46`  
**Statement:** For f(n) = largest fork-free subset of {1..n} (no element divides two distinct other elements), does f(n)/n converge to an irrational limit?  
**Source:** https://www.erdosproblems.com/1062; Lebensold 1976/77 bounds  
**Statement matches intent:** yes  
**Known status:** Open. Lebensold: 0.6725 n <= f(n) <= 0.6736 n for large n (formalized as solved variants in-file); even existence of the limit is unproven, irrationality far beyond reach.  
**Difficulty:** math 9/10, Lean 9/10 · **Compute:** none · **Confidence:** high  
**Evidence:** ForkFree matches 'no element divides two distinct others' via Subsingleton of {b in A \ {a} | a | b}. f via Nat.findGreatest bounded by n is well-defined since any fork-free subset of Icc 1 n has ncard <= n; in-file proved lower bound ceil(2n/3) <= f n sanity-checks the definition.  
**Flags:** compound answer(): existence and irrationality merged into one yes/no  
**Next action:** Leave open; note the compound answer-encoding in any upstream review.

## `erdos_1063.better_upper` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/1063.lean:45`  
**Statement:** Exhibit an explicit upper bound function for n_k (least n >= 2k with all but one of n,...,n-k+1 dividing C(n,k)) that is asymptotically smaller than Cambie's bound k*lcm(1,...,k-1).  
**Source:** https://www.erdosproblems.com/1063; Erdos-Selfridge AMM Problem 6447; Guy B31; OEIS A389360  
**Statement matches intent:** yes  
**Known status:** Open. Known: n_k <= k! (Monier), n_k <= k*lcm(1..k-1) (Cambie, noted on erdosproblems.com), giving exp((1+o(1))k); small values n_2..n_5 = 4,6,9,12 proved by decide in-file. No smaller bound known.  
**Difficulty:** math 7/10, Lean 9/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** Definition demands exactly one non-divisor among n-i, i < k, which matches 'all but one' given the in-file Erdos-Selfridge fact that at least one always fails for n >= 2k, k >= 2. sInf junk value 0 for empty sets only affects k <= 1, irrelevant at atTop. No trivializing witness: any candidate must dominate n_k in Big-O and be o of the Cambie bound.  
**Flags:** answer() asks for a function; well-posedness rests on the =O/=o sandwich, which is genuinely open  
**Next action:** Leave open. The cheapest legitimate route would be proving n_k = o(k*lcm(1..k-1)) directly (then answer := n itself), which is exactly the open content.

## `erdos_1065.parts.i` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/1065.lean:35`  
**Statement:** Are there infinitely many primes p with p = 2^k * q + 1 for some prime q and k >= 0?  
**Source:** https://www.erdosproblems.com/1065; Guy UPINT B46; OEIS A074781  
**Statement matches intent:** yes  
**Known status:** Open per erdosproblems.com. Weaker than (but in the same family as) the infinitude of safe primes, which is itself open; no unconditional result known.  
**Difficulty:** math 8/10, Lean 8/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Set {p | exists q k, p.Prime and q.Prime and p = 2^k*q + 1} is exactly the primes whose predecessor is 2^k times a prime; no truncation or degenerate witnesses (q = 2 gives only Fermat-type primes, a negligible and legitimate subcase).  
**Next action:** Leave open.

## `erdos_1065.parts.ii` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/1065.lean:44`  
**Statement:** Are there infinitely many primes p with p = 2^k * 3^l * q + 1 for some prime q and k, l >= 0?  
**Source:** https://www.erdosproblems.com/1065; OEIS A339465  
**Statement matches intent:** yes  
**Known status:** Open per erdosproblems.com; weaker than parts.i yet still unresolved.  
**Difficulty:** math 7/10, Lean 8/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Direct generalization of parts.i with an extra 3^l factor; formalization mirrors the prose exactly.  
**Next action:** Leave open.

## `erdos_1068` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/1068.lean:33`  
**Statement:** Does every graph with chromatic number aleph_1 contain a countable subgraph that is infinitely connected (infinitely many pairwise internally disjoint paths between any two vertices)?  
**Source:** https://www.erdosproblems.com/1068; Erdos-Hajnal infinite combinatorics  
**Statement matches intent:** yes  
**Known status:** Open per erdosproblems.com. The stronger sibling problem 1067 (subgraph itself of chromatic number aleph_1) is refuted (Thomassen / Bowler-Pitz, formalized externally per 1067.lean metadata); the countable version remains open.  
**Difficulty:** math 9/10, Lean 9/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** 'Countable subgraph' rendered as countable vertex set with induced subgraph; equivalent to arbitrary subgraphs since InfinitelyConnected is monotone under adding edges on a fixed vertex set. InfinitelyConnected requires Nontrivial and infinitely many internally disjoint paths, which rules out finite degenerate witnesses. Type-0 V suffices since aleph_1 <= continuum in ZFC.  
**Next action:** Leave open; set-theoretic methods (elementary submodels, consistency results) are the plausible avenue.

## `erdos_107` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/ErdosProblems/107.lean:46`  
**Statement:** Happy Ending conjecture: the minimum N forcing a convex n-gon among N points in general position is exactly 2^{n-2} + 1 for all n >= 3.  
**Source:** https://www.erdosproblems.com/107 ($500); Erdos-Szekeres 1935/1960; Suk JAMS 2017  
**Statement matches intent:** yes  
**Known status:** Major open problem ($500 prize; erdosproblems state 'falsifiable' = open). Known exactly for n <= 6 (n = 6 via the Szekeres-Peters computation); Suk 2017 gives f(n) <= 2^{n+o(n)}, best current bound 2^{n+O(sqrt(n log n))} (HMPT 2020).  
**Difficulty:** math 9/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** cardSet is upward closed (subsets of general-position sets are general position), so sInf is the intended threshold; in-file tests f(0) = 0, f(3) = 3 validate the definitions. Wikipedia/HappyEndingProblem.lean is only a pointer importing this file, not a duplicate statement.  
**Next action:** Leave open. A negative answer for some specific n would in principle be a (gigantic) finite computation; no feasible path known.

## `erdos_1072.parts.i` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/1072.lean:34`  
**Statement:** With f(p) the least n such that p divides n!+1, are there infinitely many primes with f(p) = p-1 (i.e. Wilson's theorem is first witnessed at n = p-1)?  
**Source:** https://www.erdosproblems.com/1072; OEIS A073944; Hardy-Subbarao AMM 2002  
**Statement matches intent:** yes  
**Known status:** Open per erdosproblems.com. Heuristically the count up to x should be about e^{-1} * pi(x)... in fact Erdos-Hardy-Subbarao believed it is o(x/log x) (see variants.littleo); infinitude unproven.  
**Difficulty:** math 8/10, Lean 8/10 · **Compute:** none · **Confidence:** high  
**Evidence:** sInf set nonempty for prime p by Wilson so f(p) <= p-1; edge case f(2) = 0 (0!+1 = 2) merely excludes p = 2, harmless for an infinitude question. Faithful.  
**Next action:** Leave open.

## `erdos_1072.parts.ii` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/1072.lean:39`  
**Statement:** Does f(p)/p tend to 0 as p tends to infinity along a relative-density-1 subset of the primes?  
**Source:** https://www.erdosproblems.com/1072  
**Statement matches intent:** yes  
**Known status:** Open per erdosproblems.com; would follow from strong equidistribution of factorial residues, which is unavailable.  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Existential density-1 subset P with Tendsto along atTop inf principal P is the standard faithful encoding of 'for almost all primes'; Set.HasDensity uses relative partial densities, matching the intended pi(x)-normalization.  
**Next action:** Leave open.

## `erdos_1072.variants.littleo` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/1072.lean:51`  
**Statement:** The number of primes p <= x with f(p) = p-1 is o(x/log x) (belief of Erdos, Hardy, and Subbarao).  
**Source:** https://www.erdosproblems.com/1072; Hardy-Subbarao AMM 2002  
**Statement matches intent:** yes  
**Known status:** Open; a quantitative strengthening of 'density 0 among primes'. Believed true on heuristic grounds only.  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** none · **Confidence:** high  
**Evidence:** ncard of the truncated set over Icc 0 x is finite; =o against x/log x at atTop avoids the log-junk at small x. Faithful quantitative form.  
**Next action:** Leave open.

## `erdos_1073` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/1073.lean:35`  
**Statement:** Is the number A(x) of composite u < x dividing n!+1 for some n at most x^{o(1)}?  
**Source:** https://www.erdosproblems.com/1073; OEIS A256519  
**Statement matches intent:** yes  
**Known status:** Open per erdosproblems.com. Smallest such composites are 25 | 4!+1, 121 | 5!+1; counting them is tied to Wilson-type congruences with no known technique.  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** Existential o(1)-exponent encoding is faithful: the 'forall x' (rather than eventually) is harmless because o can be chosen freely on any finite initial segment, and rpow junk at x in {0,1} is satisfied since A(0) = A(1) = 0.  
**Next action:** Leave open.

## `erdos_1074.parts.i` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/1074.lean:56`  
**Statement:** Does the natural density of the EHS numbers (m >= 1 such that some prime p not congruent to 1 mod m divides m!+1) exist?  
**Source:** https://www.erdosproblems.com/1074; OEIS A063980; Erdos-Hardy-Subbarao  
**Statement matches intent:** yes  
**Known status:** Open per erdosproblems.com. Erdos-Hardy-Subbarao proved the set is infinite (formalized externally per in-file AlphaProof link); density existence is open, computations up to 2^10 suggest about 0.5.  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** none · **Confidence:** high  
**Evidence:** EHSNumbers definition matches the source (m = 1 auto-excluded since everything is congruent to 1 mod 1, consistent with intent); answer() over 'exists c, HasDensity c' is exactly the existence question.  
**Next action:** Leave open.

## `erdos_1074.parts.ii` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/1074.lean:65`  
**Statement:** What is the value of the natural density of the EHS numbers?  
**Source:** https://www.erdosproblems.com/1074  
**Statement matches intent:** yes  
**Known status:** Open; even existence unknown, numerics suggest about 0.5.  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** Same definitions as parts.i; only the answer-encoding differs (a specific real must be produced and proven to be the density).  
**Flags:** answer() value form presupposes existence of the density  
**Next action:** Leave open; consider guarding the value question on parts.i in an upstream cleanup.

## `erdos_1074.parts.iii` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/1074.lean:75`  
**Statement:** Does the relative density (within the primes) of the Pillai primes exist?  
**Source:** https://www.erdosproblems.com/1074; OEIS A063980  
**Statement matches intent:** yes  
**Known status:** Open per erdosproblems.com. Pillai primes are infinite (Erdos-Hardy-Subbarao, in-file solved variant); density among primes unknown.  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** none · **Confidence:** high  
**Evidence:** HasDensity c {p | p.Prime} gives the pi(x)-normalized relative density, matching |P cap [1,x]|/pi(x). In-file kernel checks (23 in, 2 out) validate the PillaiPrimes definition.  
**Next action:** Leave open.

## `erdos_1074.parts.iv` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/1074.lean:84`  
**Statement:** What is the value of the relative density of the Pillai primes within the primes?  
**Source:** https://www.erdosproblems.com/1074  
**Statement matches intent:** yes  
**Known status:** Open; even existence unknown.  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** Same encoding caveat as parts.ii, otherwise faithful.  
**Flags:** answer() value form presupposes existence of the density  
**Next action:** Leave open.

## `erdos_1074.variants.EHSNumbers_one_half` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/1074.lean:125`  
**Statement:** The EHS numbers have natural density exactly 1/2.  
**Source:** https://www.erdosproblems.com/1074; Hardy-Subbarao computations to 2^10  
**Statement matches intent:** suspect — Hardy-Subbarao only wrote they 'expect [the limit] to be around 0.5, if it exists'; formalizing this as density exactly 1/2 is an over-precise rendering that nobody conjectured and that is quite plausibly false even if a density exists.  
**Known status:** Open as stated, but the exact value 1/2 is speculative; the honest open content is parts.i/ii.  
**Difficulty:** math 9/10, Lean 9/10 · **Compute:** none · **Confidence:** low  
**Evidence:** The docstring itself hedges ('around 0.5, if it exists') while the statement asserts HasDensity (1/2) unconditionally - a precision mismatch between prose and formal statement.  
**Flags:** over-precise formalization of a vague numeric heuristic; needs literature check for any exact-density conjecture  
**Next action:** Recommend demoting or annotating this variant upstream (e.g. as a heuristic target, or an interval claim), rather than a literal density-1/2 conjecture.

## `erdos_108` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/108.lean:35`  
**Statement:** For every r >= 4, k >= 2 is there a finite threshold f(k,r) such that every graph of chromatic number >= f(k,r) contains a subgraph with girth >= r and chromatic number >= k?  
**Source:** https://www.erdosproblems.com/108; Rodl 1977 solved r = 4  
**Statement matches intent:** yes  
**Known status:** Open in general per erdosproblems.com; the triangle-free case r = 4 was proved by Rodl (1977), r >= 5 open. A recognized hard problem in chromatic graph theory.  
**Difficulty:** math 9/10, Lean 9/10 · **Compute:** none · **Confidence:** high  
**Evidence:** girth and chromaticNumber are ENat-valued so comparisons with coerced naturals behave; girth >= r admits acyclic subgraphs (girth = top) only when they also have chromatic number >= k, which forces cycles for k >= 3 but is exactly the intended reading for k = 2 (any forest with an edge works, matching the trivial k = 2 case).  
**Next action:** Leave open. Formalizing the solved r = 4 case (Rodl) would be a meaningful standalone project (noted as TODO in-file).

## `erdos_1082.parts.i` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/1082.lean:32`  
**Statement:** Must n points in the plane with no three collinear determine at least floor(n/2) distinct pairwise distances?  
**Source:** https://www.erdosproblems.com/1082  
**Statement matches intent:** yes  
**Known status:** Open (erdosproblems state 'falsifiable'). Regular n-gons achieve exactly floor(n/2) distances, so the bound is tight; sibling parts.ii (a single point seeing floor(n/2) distances) was refuted by Harborth's 8-point configuration, already recorded as solved in-file.  
**Difficulty:** math 9/10, Lean 9/10 · **Compute:** none · **Confidence:** high  
**Evidence:** distinctDistances = card of image of dist over offDiag, exactly the number of distinct pairwise distances; Nat division A.card / 2 matches floor(n/2); degenerate small cases (n <= 2) hold trivially, so no vacuity or truncation issues.  
**Next action:** Leave open. Any counterexample search would target small general-position multi-distance sets; none known.

## `erdos_1084.variants.triangular_optimal_d2` — Solved mathematically, not yet formalized (cat 5)

**File:** `FormalConjectures/ErdosProblems/1084.lean:66`  
**Statement:** Among 3n^2+3n+1 points in the plane with pairwise distances >= 1, the maximum number of pairs at distance exactly 1 is exactly 9n^2+3n (the hexagonal patch of the triangular lattice is optimal).  
**Source:** https://www.erdosproblems.com/1084 [Er75f]; Harborth, Loesung zu Problem 664A, Elem. Math. 29 (1974), 14-15  
**Statement matches intent:** yes  
**Known status:** SOLVED in the literature despite the 'research open' label: Harborth (1974) proved the maximum number of minimum-distance pairs (= penny graph edges) among n points is floor(3n - sqrt(12n-3)); at n = 3m^2+3m+1 this is exactly 9m^2+3m since 12n-3 = (6m+3)^2. The general Erdos problem 1084 (higher d, growth of f_d) is what remains open. No PR or campaign in this fork targets it; no known Lean formalization.  
**Difficulty:** math 5/10, Lean 9/10 · **Compute:** none · **Confidence:** high  
**Evidence:** f d n is the sup of unitDistNum over 1-separated (edist >= 1, closed condition, so unit distances are allowed) n-point sets - exactly the penny-graph edge count. Harborth's classical formula floor(3n - sqrt(12n-3)) specializes to 9m^2+3m at hexagonal numbers, proving the stated equality for every m (m = 0, 1 check by hand: 0 and 12). Docstring's 'f_2(3n^2+3n+1) < 9n^2+3n' is a typo for '=' (the lattice itself achieves 9n^2+3n, so '<' is impossible).  
**Flags:** mislabeled research open; Harborth 1974 resolves it; docstring inequality '<' contradicts the (correct) '=' in the statement  
**Next action:** Relabel as research solved citing Harborth 1974 and attempt formalization: lower bound from the explicit hexagonal-lattice configuration (medium), upper bound via Harborth's convex-position/boundary induction (large). Overall effort: large.

## `erdos_1085.variants.upper_d3` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/ErdosProblems/1085.lean:58`  
**Statement:** Let f_3(n) be the maximum number of unit-distance pairs among n points in R^3. Is Erdos's lower bound n^{4/3} log log n also an upper bound, i.e. f_3(n) = O(n^{4/3} log log n)?  
**Source:** https://www.erdosproblems.com/1085 (state: open, tags geometry/distances); Erdos unit-distance problem in R^3; best known upper bound O(n^{3/2}) (Kaplan-Matousek-Safernova-Sharir 2012)  
**Statement matches intent:** yes  
**Known status:** Open. Erdos proved f_3(n) = Ω(n^{4/3} log log n) (stated as the solved variant lower_d3 in the same file); matching upper bound is a long-standing open problem. No PR in pr_register.json and no campaign in campaign_register.json touches 1085.  
**Difficulty:** math 9/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Unit distances in R^3: the gap between the Erdos lower bound n^{4/3}loglog n and the KMSS upper bound O(n^{3/2}) is famously open; erdosproblems.com still lists 1085 as open today.  
**Next action:** Leave open. Any progress requires new incidence geometry in R^3; the Lean side additionally needs an entire theory of unitDistNum bounds that Mathlib lacks.

## `erdos_1093.parts.i` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/1093.lean:38`  
**Statement:** For binomial coefficients C(n,k) with n >= 2k all of whose prime factors exceed k, the 'deficiency' counts how many of the k integers n, n-1, ..., n-k+1 are k-smooth. Are there infinitely many such (k,n) with deficiency exactly 1?  
**Source:** https://www.erdosproblems.com/1093 (state: open, tags number theory / binomial coefficients); Ecklund-Erdos-Selfridge circle of problems on prime factors of binomial coefficients  
**Statement matches intent:** suspect — Off-by-one risk in the smoothness threshold. `deficiency n k` uses Mathlib's `Nat.smoothNumbers k`, which is {m ≠ 0 | ∀ p ∈ m.primeFactors, p < k}, i.e. prime factors STRICTLY BELOW k. The complementary condition used in the same statement is `k < p` for primes dividing C(n,k), whose complement is `p ≤ k`; the standard meaning of 'k-smooth' is also 'all prime factors ≤ k'. So the intended set is almost certainly `smoothNumbers (k+1)`. The two differ exactly when k is prime and k | (n-i) — infinitely many relevant cases, and the question is precisely about infinitude, so this could change the answer. ℕ-subtraction `n - i` is safe here because 2k ≤ n and i < k.  
**Known status:** Open. No PR in pr_register.json mentions 1093; no campaign target. File is inherited from upstream google-deepmind/formal-conjectures.  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** Mathlib defines Nat.smoothNumbers n := {m | m ≠ 0 ∧ ∀ p ∈ m.primeFactors, p < n} (strict), which is off by one from the usual 'k-smooth'. Web lookup only echoed the Lean file itself, so the source wording could not be confirmed.  
**Flags:** needs literature check; possible off-by-one: smoothNumbers k (p < k) vs intended p ≤ k  
**Next action:** Confirm the intended smoothness threshold against erdosproblems.com/1093 / [EES74]; if it is 'primes ≤ k', change `smoothNumbers k` to `smoothNumbers (k+1)` in the `deficiency` definition (single-token fix, affects both parts). Then leave as open research.

## `erdos_1093.parts.ii` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/1093.lean:47`  
**Statement:** Same setting: are there only finitely many pairs (k,n) with n >= 2k, all prime factors of C(n,k) greater than k, and deficiency greater than 1?  
**Source:** https://www.erdosproblems.com/1093 (state: open)  
**Statement matches intent:** suspect — Inherits exactly the same `smoothNumbers k` (p < k) vs 'p ≤ k' off-by-one as parts.i. Otherwise faithful: pair encoding is (k, n) = (x.1, x.2), the k=0 and k=1 degenerate cases are automatically excluded because deficiency is 0 there, and the statement is asserted (not answer()-encoded) in the direction Erdos expected.  
**Known status:** Open. No internal or external resolution found.  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** Same definitional analysis as parts.i; the two statements share the single `deficiency` definition at line 32.  
**Flags:** needs literature check; shares off-by-one smoothness threshold with parts.i  
**Next action:** Fix the smoothness threshold jointly with parts.i, then leave open.

## `erdos_1094` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/1094.lean:34`  
**Statement:** For all n >= 2k >= 2, the least prime factor of C(n,k) is at most max(n/k, k), with only finitely many exceptions.  
**Source:** https://www.erdosproblems.com/1094 (state: open); [ELS93] Erdos, Lacampagne, Selfridge, Estimates of the least prime factor of a binomial coefficient, Math. Comp. 61 (1993), 215-224  
**Statement matches intent:** yes  
**Known status:** Open. No PR in pr_register.json mentions 1094; no campaign target; erdosproblems.com lists it open.  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** Careful check that truncated ℕ-division does not alter the statement because minFac ∈ ℕ; positivity hypothesis present; no vacuity.  
**Flags:** needs literature check (exact form of the ELS bound: max(n/k,k) vs max(n/k,29))  
**Next action:** Verify the exact ELS93 constant against the source; otherwise leave open. Progress would need effective bounds on the Erdos-Selfridge function.

## `erdos_1095.variants.log_equivalent` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/1095.lean:74`  
**Secondary category:** 3 (False / refutable as stated)  
**Statement:** Sorenson-Sorenson-Webster's heuristic that log g(k) is of the same order as k / log k.  
**Source:** https://www.erdosproblems.com/1095 (state: open); [SSW20] Sorenson, Sorenson, Webster, An algorithm and estimates for the Erdos-Selfridge function (2020), 371-385  
**Statement matches intent:** no — PROSE/FORMAL MISMATCH. The docstring states log g(k) \asymp k/log k (same ORDER, i.e. Θ / IsTheta), but the Lean uses `~[atTop]`, which is `Asymptotics.IsEquivalent`, i.e. log g(k) / (k/log k) → 1 — an asymptotic EQUALITY with implied constant exactly 1. This is strictly stronger than the cited heuristic and is very likely false if SSW's heuristic constant differs from 1 (their heuristic is of the shape g(k) ≈ exp(c k / log k)). The intended (Θ) version remains open either way.  
**Known status:** Open as intended; as literally written the statement is a stronger, plausibly false claim. No PR or campaign addresses 1095.  
**Difficulty:** math 9/10, Lean 9/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** Docstring uses \asymp; `~[l]` in Mathlib is IsEquivalent (f - g = o(g)), not IsTheta. The two are inequivalent whenever the true constant is not 1.  
**Flags:** prose/formal mismatch: \asymp formalized as IsEquivalent instead of IsTheta; statement stronger than the cited conjecture; may be false as written; needs literature check (SSW20 constant)  
**Next action:** Replace `(fun k ↦ log (g k)) ~[atTop] (fun k ↦ k / log k)` with `(fun k ↦ log (g k)) =Θ[atTop] (fun k ↦ (k : ℝ) / log k)` to match \asymp; then leave as open research. Also check SSW20 for the explicit constant.

## `erdos_1095.variants.lower_conjecture` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/1095.lean:67`  
**Statement:** Erdos-Lacampagne-Selfridge's belief that the Erdos-Selfridge function satisfies g(k) >= exp(c k / log k) for some c > 0 and all large k.  
**Source:** https://www.erdosproblems.com/1095 (state: open); [ELS93] Math. Comp. 61 (1993), 215-224  
**Statement matches intent:** yes  
**Known status:** Open. Konyagin's record (the solved variant lower_solved in the same file) is only g(k) ≫ exp(c (log k)^2), far below exp(ck/log k).  
**Difficulty:** math 9/10, Lean 9/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Statement matches the docstring quote from ELS93; the companion solved variant documents that the current record is exponentially weaker.  
**Next action:** Leave open. The gap between exp(c(log k)^2) and exp(ck/log k) is enormous; no strategy known.

## `erdos_1095.variants.upper_conjecture` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/1095.lean:58`  
**Statement:** Let g(k) be the least n > k+1 such that every prime factor of C(n,k) exceeds k (the Erdos-Selfridge function). Ecklund-Erdos-Selfridge conjectured g(k) <= exp((1+o(1))k).  
**Source:** https://www.erdosproblems.com/1095 (state: open); [EES74] Ecklund, Erdos, Selfridge, Math. Comp. 28 (1974), 647-649  
**Statement matches intent:** yes  
**Known status:** Open. Best known upper bounds are far weaker; Granville-Ramare [GrRa96] and Konyagin [Ko99b] give lower bounds. No PR/campaign hits.  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Definition well-formed; quantifier order (∃ o(1) function, then eventually) is correct; erdosproblems.com state open.  
**Next action:** Leave open. Would need genuinely new analytic number theory.

## `erdos_11` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/ErdosProblems/11.lean:30`  
**Statement:** Is every odd n > 1 the sum of a squarefree number and a power of 2?  
**Source:** https://www.erdosproblems.com/11 (state: open); [GrSo98] Granville and Soundararajan, A binary additive problem of Erdos and the order of 2 mod p^2, Ramanujan J. 2 (1998), 283-298  
**Statement matches intent:** yes  
**Known status:** Open, and provably hard: Granville-Soundararajan [GrSo98] (recorded as the solved variant `granville_soundararajan` in the same file) show a positive answer implies there are infinitely many primes with 2^p ≡ 2 (mod p^2), which is itself an open problem. Verified computationally for n < 2^50 (also recorded in the file). No PR in pr_register.json or campaign register touches Erdos 11.  
**Difficulty:** math 9/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** The file's own solved variant records the Granville-Soundararajan implication, which certifies that erdos_11 is at least as hard as an open problem about 2^p mod p^2.  
**Next action:** Leave open (category 9). Do not attempt: a proof would resolve an open Wieferich-type question.

## `erdos_11.variants.not_four_dvd` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/ErdosProblems/11.lean:39`  
**Statement:** Stronger form Erdos often asked: every n > 1 not divisible by 4 is the sum of a squarefree number and a power of 2.  
**Source:** https://www.erdosproblems.com/11 (state: open)  
**Statement matches intent:** yes  
**Known status:** Open; strictly harder than erdos_11, which is already blocked by an open Wieferich-type question.  
**Difficulty:** math 9/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Logical implication not_four_dvd ⟹ erdos_11 plus the GrSo98 consequence recorded in the same file.  
**Next action:** Leave open. If anything is ever proved here it should be derived from erdos_11 plus the even case, not attacked directly.

## `erdos_11.variants.two_pow_two` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/11.lean:47`  
**Statement:** Is every odd n > 1 the sum of a squarefree number and two powers of 2?  
**Source:** https://www.erdosproblems.com/11 (state: open)  
**Statement matches intent:** yes  
**Known status:** Open. Weaker relaxation of erdos_11; no known proof and no PR/campaign in this fork.  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** Two free powers of 2 give ~ (log n)^2 candidate residues n - 2^l - 2^m, versus ~log n for erdos_11, so the heuristic slack is much larger; still no unconditional argument is known.  
**Flags:** 'two powers of 2' formalized without requiring l ≠ m (weaker but arguably intended)  
**Next action:** Leave open, but this is the most approachable of the three: a sieve/covering argument over n mod small powers of 2 combined with squarefree density in progressions is the natural first attack. First milestone: show a positive-density set of odd n is representable.

## `erdos_1101.parts.i` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/1101.lean:57`  
**Statement:** For a strictly increasing pairwise-coprime sequence u with convergent reciprocal sum, call u 'good' if the gaps in the set of integers divisible by no u_i are eventually below (1+eps) t_x / prod(1 - 1/u_i). Claim: no good sequence grows only polynomially.  
**Source:** https://www.erdosproblems.com/1101 (state: open). Verified verbatim: 'Is there a good sequence such that u_n < n^{O(1)}?' Erdos believed the answer is no.  
**Statement matches intent:** yes  
**Known status:** Open. Erdos proved some good sequence exists (of primes) but believed no polynomially-growing one does. No PR in pr_register.json and no campaign target for 1101.  
**Difficulty:** math 9/10, Lean 9/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Source statement retrieved and compared term by term; all four clauses of IsGood correspond, and every degenerate u is provably not good.  
**Next action:** Leave open. Key obstruction: lower-bounding the largest gap in the u-sieved set for slowly growing u; a first milestone would be formalizing Erdos's construction of a good sequence of primes (currently absent from the file).

## `erdos_1101.parts.ii` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/1101.lean:63`  
**Statement:** There exists a 'good' sequence (same definition) whose growth is sub-exponential, i.e. log u_n = o(n).  
**Source:** https://www.erdosproblems.com/1101 (state: open). Source: 'is there a good sequence such that u_n <= e^{o(n)}?' Erdos believed yes.  
**Statement matches intent:** yes  
**Known status:** Open; Erdos believed the answer yes and proved existence of a good sequence (with no growth control).  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Direct comparison with the retrieved source text; asymptotic encoding is standard and correct.  
**Next action:** Leave open. Natural approach: refine Erdos's prime construction to control growth; first milestone is to formalize IsGood for the primes-based construction at all.

## `erdos_1106.parts.i` — Already solved externally (cat 1)

**File:** `FormalConjectures/ErdosProblems/1106.lean:36`  
**Secondary category:** 5 (Solved mathematically, not yet formalized)  
**Statement:** Let F(n) be the number of distinct primes dividing p(1)p(2)...p(n), where p is the partition function. Does F(n) tend to infinity?  
**Source:** https://www.erdosproblems.com/1106 (page state 'open' because of part ii). Schinzel's note in the Oberwolfach problem book: F(n) → ∞ follows from the asymptotics of p(n) together with a theorem of Tijdeman; details in a paper of Erdos and Ivic. Schinzel and Wirsing proved F(n) ≫ log n. Ono (Ann. of Math. 151 (2000)) proved every prime divides p(n) for some n.  
**Statement matches intent:** yes  
**Known status:** SOLVED EXTERNALLY, yet marked @[category research open] in this repo. Three independent published routes: (a) Schinzel via Tijdeman's theorem on S-smooth sequences plus the Hardy-Ramanujan asymptotic (written up by Erdos-Ivic); (b) Schinzel-Wirsing's stronger F(n) ≫ log n; (c) Ono's theorem that every prime divides some partition value. Only part ii (F(n) > n) remains open, which is why the site's aggregate state reads 'open'.  
**Difficulty:** math 5/10, Lean 9/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Retrieved erdosproblems.com/1106 content: 'Schinzel noted ... that F(n) → ∞ follows from the asymptotic formula for p(n) and a result of Tijdeman'; 'Schinzel and Wirsing have proved that F(n) ≫ log n'. Both settle part i affirmatively.  
**Flags:** MISCATEGORIZED: tagged research open but the mathematical question is settled in the literature; Lean proof remains research-scale (cat 5 secondary)  
**Next action:** Retag as @[category research solved] with answer(True) and cite Schinzel-Wirsing / Erdos-Ivic. Formalizing the proof in Lean is research-scale (needs Tijdeman-type S-unit input or Ono's modular-forms machinery, none of which is in Mathlib), so the honest move is the metadata fix plus a documented citation, not a Lean proof.

## `erdos_1106.parts.ii` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/1106.lean:45`  
**Statement:** With F(n) the number of distinct primes dividing p(1)...p(n), is F(n) > n for all sufficiently large n?  
**Source:** https://www.erdosproblems.com/1106 (state: open); problem asked by Erdos at Oberwolfach 1986  
**Statement matches intent:** yes  
**Known status:** Open. The best published lower bound is Schinzel-Wirsing's F(n) ≫ log n — exponentially short of the required F(n) > n. Ono's theorem gives a positive-density set of n divisible by any fixed prime but no bound of size n on the number of distinct primes.  
**Difficulty:** math 9/10, Lean 9/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Retrieved erdosproblems.com/1106: the only recorded lower bound is F(n) ≫ log n, so F(n) > n is far out of reach.  
**Next action:** Leave open. Key obstruction: converting divisibility results for individual primes into a count of ≥ n distinct primes below the (huge) product; progress would be any bound F(n) ≫ n^c or F(n) ≫ (log n)^A.

## `erdos_1107` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/1107.lean:39`  
**Statement:** For every r >= 2, is every sufficiently large integer the sum of at most r+1 r-powerful numbers (numbers where every prime factor appears to the power at least r)?  
**Source:** https://www.erdosproblems.com/1107 (state: open, tags number theory / powerful); [He88] Heath-Brown, Ternary quadratic forms and sums of three square-full numbers (1988)  
**Statement matches intent:** yes  
**Known status:** Open for r ≥ 3. The r = 2 case is Heath-Brown's theorem, recorded as the solved variant `erdos_1107.variants.two` in the same file. No PR/campaign in this fork touches 1107.  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Definition Nat.Full checked at FormalConjecturesForMathlib/Data/Nat/Full.lean:30; degenerate members 0 and 1 do not weaken the statement because the summand count is capped.  
**Next action:** Leave open. The r = 2 case already required deep work on ternary quadratic forms; general r has no known approach. A worthwhile intermediate Lean target is instead formalizing the trivial direction (density counts showing r+1 summands is the right order).

## `erdos_1108.parts.i` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/1108.lean:44`  
**Statement:** Does the set of all finite sums of distinct factorials contain, for each k >= 2, only finitely many perfect k-th powers?  
**Source:** https://www.erdosproblems.com/1108 (state: open, tags number theory / factorials)  
**Statement matches intent:** yes  
**Known status:** Open. Small squares in A are plentiful (4 = 0!+1!+2!, 9 = 1!+2!+3!, 25 = 0!+4!, 121 = 0!+5!), so the finiteness question is genuine and no elementary obstruction is known. No PR/campaign hits.  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** small · **Confidence:** medium  
**Evidence:** Explicit small solutions found by hand (4, 9, 25, 121) show the set is nonempty and the question non-trivial; the formal statement admits them exactly as the source does.  
**Flags:** 0! = 1! means the index-set encoding admits sums that a 'distinct values' reading would exclude (matches source notation, noted for the record)  
**Next action:** Leave open. First milestone: a computational search for k-th powers in A up to a large bound would sharpen the conjecture; a proof would likely need S-unit/Baker-type methods with no Mathlib support.

## `erdos_1108.parts.ii` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/1108.lean:52`  
**Statement:** Does the set of all finite sums of distinct factorials contain only finitely many powerful numbers (numbers in which every prime factor occurs squared)?  
**Source:** https://www.erdosproblems.com/1108 (state: open)  
**Statement matches intent:** yes  
**Known status:** Open; strictly stronger than parts.i (every k-th power with k ≥ 2 is powerful). No internal or external resolution found.  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** small · **Confidence:** medium  
**Evidence:** Definition-level check of IsPowerful and FactorialSums; implication parts.ii ⟹ parts.i confirms the relative difficulty ordering.  
**Next action:** Leave open. Same obstruction as parts.i.

## `erdos_1113` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/1113.lean:75`  
**Statement:** Do there exist Sierpinski numbers (odd k with k*2^n + 1 always composite) that possess no finite covering set of primes?  
**Source:** https://www.erdosproblems.com/1113 (state: open); [ErGr80] Erdos-Graham; Guy's Unsolved Problems F13; [FFK08] Filaseta, Finch, Kozek, J. Number Theory 128 (2008), 1916-1940  
**Statement matches intent:** yes  
**Known status:** Open. Erdos and Graham conjectured yes. Izotov's argument (detailed by Filaseta-Finch-Kozek) makes m = 734110615000775^4 a candidate Sierpinski number with no covering set — Izotov proved it IS a Sierpinski number, but the absence of a covering set is not proved. No PR in pr_register.json or campaign_register.json touches 1113.  
**Difficulty:** math 9/10, Lean 9/10 · **Compute:** small · **Confidence:** high  
**Evidence:** Retrieved erdosproblems.com/1113: 'An argument of Izotov ... suggests that m = 734110615000775^4 is a Sierpinski number without a covering set, and Izotov proved that this m is indeed a Sierpinski number.' Status is therefore open.  
**Next action:** Leave open. A plausible partial Lean target is formalizing that Izotov's m is a Sierpinski number (algebraic quartic factorization plus a small covering), which is a self-contained finite verification; proving it has no covering set is the open part.

## `erdos_1113.variants.filaseta_finch_kozek` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/ErdosProblems/1113.lean:85`  
**Statement:** Filaseta-Finch-Kozek's revised conjecture: every Sierpinski number is either a perfect power or possesses a finite covering set of primes.  
**Source:** https://www.erdosproblems.com/1113; [FFK08] Filaseta, Finch, Kozek, On powers associated with Sierpinski numbers, Riesel numbers and Polignac's conjecture, J. Number Theory 128 (2008), 1916-1940  
**Statement matches intent:** yes  
**Known status:** Open, and strictly harder than erdos_1113 in the sense that it must classify ALL Sierpinski numbers. No known partial results toward the universal statement.  
**Difficulty:** math 9/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Checked IsPerfectPower for the classic 'every n = n^1' vacuity loophole — the definition requires 1 < m, so no loophole. Conjecture wording confirmed against erdosproblems.com/1113.  
**Next action:** Leave open (category 9). No meaningful strategy exists; the statement quantifies over an infinite family with no structural handle.

## `erdos_1133` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/1133.lean:39`  
**Statement:** For every C > 0 is there eps > 0 such that for large n, for any x_1..x_n in [-1,1] one can pick y_1..y_n in [-1,1] so that any polynomial of degree < (1+eps)n interpolating at least (1-eps)n of the pairs has sup norm exceeding C on [-1,1]?  
**Source:** https://www.erdosproblems.com/1133 (state: open, tags analysis / polynomials); [Er67] Erdos, Problems and results on the convergence and divergence properties of Lagrange interpolation polynomials, Mathematica (Cluj) (1967), 65-73  
**Statement matches intent:** yes  
**Known status:** Open. Erdos proved the weaker statement recorded as `erdos_1133.variants.weaker` in the same file, and remarks in [Er67] that he could not even prove the m = n case of the conjecture.  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** Full quantifier audit against the docstring; the only subtle points (natDegree junk value, repeated nodes, sup rendered as an existential) all fall on the safe side.  
**Next action:** Leave open. Progress requires new extremal results on Chebyshev-type polynomials with a linear number of allowed exceptional nodes; the natural first milestone is formalizing Erdos's weaker theorem.

## `erdos_1135` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/ErdosProblems/1135.lean:42`  
**Statement:** The Collatz conjecture: iterating the 3x+1 map from any positive integer eventually reaches 1.  
**Source:** https://www.erdosproblems.com/1135 (state: open, $500 prize); [La10] Lagarias, The 3x+1 problem: an overview; [La16] Lagarias, Erdos, Klarner, and the 3x+1 problem, Amer. Math. Monthly (2016)  
**Statement matches intent:** yes  
**Known status:** Open, famous, $500 Erdos prize. No PR in pr_register.json and no campaign in campaign_register.json targets Collatz.  
**Difficulty:** math 10/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Collatz is a canonical unsolved problem; the duplication is intentional (the file's module docstring says it points to the canonical formalization).  
**Flags:** duplicate of FormalConjectures/Wikipedia/CollatzConjecture.lean:collatz_conjecture (also sorry)  
**Next action:** Leave open. If the Wikipedia file is ever closed, erdos_1135 closes by `exact CollatzConjecture.collatz_conjecture`; that is the only sensible dependency to record.

## `erdos_1137` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/1137.lean:34`  
**Statement:** With d_n the n-th prime gap, does max_{n<x} d_n d_{n-1} divided by (max_{n<x} d_n)^2 tend to 0, i.e. can two consecutive gaps never both be near-maximal?  
**Source:** https://www.erdosproblems.com/1137 (state: open, tags number theory / primes)  
**Statement matches intent:** yes  
**Known status:** Open. Related to Ford-Green-Konyagin-Maynard-Tao long-gaps work and Ford-Maynard-Tao 'chains of large gaps between primes', which produce many consecutive large gaps but nowhere near the maximum, so the conjecture is untouched. No PR/campaign hits for 1137.  
**Difficulty:** math 9/10, Lean 9/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Definition of primeGap checked at FormalConjecturesForMathlib/NumberTheory/PrimeGap.lean:27; the n-1 truncation contributes only the value 1 to the numerator sup.  
**Flags:** ℕ-subtraction primeGap (n-1) at n = 0 (harmless: contributes the minimal gap); max taken over prime index n < x rather than primes below x  
**Next action:** Leave open. Key obstruction: no upper bound on max_{n<x} d_n is known that is anywhere near the Erdos-Rankin lower bound, so the denominator is uncontrolled.

## `erdos_1139` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/1139.lean:34`  
**Statement:** Let u_1 < u_2 < ... list the positive integers with at most 2 prime factors (counted with multiplicity). Is limsup_k (u_{k+1} - u_k)/log k infinite?  
**Source:** https://www.erdosproblems.com/1139 (state: open, tags number theory / primes)  
**Statement matches intent:** yes  
**Known status:** Open. The counting function of {Ω ≤ 2} up to x is ~ x log log x / log x, so the average gap is ~ log x / log log x; gaps of size ≫ log k require long runs of integers all having at least 3 prime factors, well beyond current sieve technology. No internal or external resolution found.  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** Index-shift and junk-value analysis; density heuristic for Ω ≤ 2 shows the question is genuinely about exceptional runs, not typical behaviour.  
**Flags:** 0-indexed Nat.nth vs 1-indexed source (limsup unaffected)  
**Next action:** Leave open. Key obstruction: constructing long intervals free of primes AND semiprimes; Erdos-Rankin handles primes only. Progress would be any unconditional lower bound limsup (u_{k+1}-u_k)/log k > 0.

## `erdos_1142` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/ErdosProblems/1142.lean:51`  
**Statement:** Are there infinitely many n > 2 such that n - 2^k is prime for every k >= 1 with 2^k < n? (The only known such n are 4, 7, 15, 21, 45, 75, 105.)  
**Source:** https://www.erdosproblems.com/1142 (state: open); OEIS A039669; [MiWe69] Mientka and Weitzenkamp, On f-plentiful numbers, JCT 7 (1969), 374-377  
**Statement matches intent:** yes  
**Known status:** Open; conjecturally the answer is no (105 is believed to be the largest). Mientka-Weitzenkamp verified no further examples up to 2^44 (recorded as a solved variant in the same file). No PR or campaign in this fork targets 1142.  
**Difficulty:** math 9/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Predicate cross-checked against the file's seven test theorems and the A039669 definition; both directions of the infinitude question are beyond current methods.  
**Next action:** Leave open. Neither direction is approachable: proving finiteness needs, for every large n, a k with n - 2^k composite (a covering-congruence style statement not implied by known de Polignac results), and proving infinitude needs simultaneous primality of ~log2(n) shifted values.

## `erdos_357.parts.i` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/357.lean:39`  
**Statement:** Let f(n) be the maximal k such that there exist 1 <= a_1 < ... < a_k <= n with all consecutive-block sums sum_{u<=i<=v} a_i distinct. Is f(n) = o(n)?  
**Source:** https://www.erdosproblems.com/357 (Erdos-Graham); OEIS A364132/A364153  
**Statement matches intent:** yes  
**Known status:** Open on erdosproblems.com as of 2026-07-26. Best known lower bound f(n) >= (2+o(1))sqrt(n) (Weisenberg, forum). Beker 2024 (arXiv:2311.10087, BLMS) resolved a related Erdos-Graham counting question (cn^2 distinct consecutive sums) but not this one.  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Definition f via sSup over {k | exists StrictMono a : Fin k -> Z into Icc 1 n with HasDistinctSums} is faithful: OrdConnected finsets of Fin k are exactly the interval index sets; set is nonempty (k=0) and bounded (k <= n), so sSup is well-defined. Statement asserts the conjectured 'yes' direction, standard for this repo.  
**Next action:** Keep open; monitor erdosproblems.com/357 and follow-ups to Beker 2024 for progress on the o(n) question.

## `erdos_357.parts.ii.bigO_version` — Vacuously true / accidentally weakened (cat 4)

**File:** `FormalConjectures/ErdosProblems/357.lean:57`  
**Secondary category:** 2 (Trivially or easily solvable)  
**Statement:** How does f(n) grow: exhibit g with g = O(f), answer(sorry)-encoded.  
**Source:** https://www.erdosproblems.com/357  
**Statement matches intent:** suspect — answer(sorry)-encoding admits degenerate witnesses: answer := fun n => (f n : R) closes it by isBigO_refl, and answer := 0 by isBigO_zero. The file's own formalisation note (lines 43-52) acknowledges these trivial solutions and appeals to a 'mathematically interesting answer' convention that is not machine-checkable.  
**Known status:** Intended growth-rate question open; formal statement trivially closable.  
**Difficulty:** math 8/10, Lean 1/10 · **Compute:** none · **Confidence:** high  
**Evidence:** answer := (fun n => (f n : R)) with Asymptotics.isBigO_refl is a one-line proof of the formal statement.  
**Flags:** answer-encoding trivializable (acknowledged in-file)  
**Next action:** Tighten the encoding (e.g. require an explicit elementary function with a stated exponent) or accept as convention-guarded; do not count a trivial closure as progress.

## `erdos_357.parts.ii.bigO_version_symm` — Vacuously true / accidentally weakened (cat 4)

**File:** `FormalConjectures/ErdosProblems/357.lean:65`  
**Secondary category:** 2 (Trivially or easily solvable)  
**Statement:** How does f(n) grow: exhibit g with f = O(g), answer(sorry)-encoded.  
**Source:** https://www.erdosproblems.com/357  
**Statement matches intent:** suspect — Degenerate witness answer := fun n => (f n : R) closes it by isBigO_refl; answer := fun n => (n:R) also works after the easy lemma f n <= n. In-file note acknowledges the loophole.  
**Known status:** Intended growth-rate question open; formal statement trivially closable.  
**Difficulty:** math 8/10, Lean 1/10 · **Compute:** none · **Confidence:** high  
**Evidence:** isBigO_refl with answer := f itself is a one-liner.  
**Flags:** answer-encoding trivializable (acknowledged in-file)  
**Next action:** Same as bigO_version: tighten encoding or treat as convention-guarded.

## `erdos_357.parts.ii.bigTheta_version` — Vacuously true / accidentally weakened (cat 4)

**File:** `FormalConjectures/ErdosProblems/357.lean:73`  
**Secondary category:** 2 (Trivially or easily solvable)  
**Statement:** How does f(n) grow: exhibit g with f = Theta(g), answer(sorry)-encoded.  
**Source:** https://www.erdosproblems.com/357  
**Statement matches intent:** suspect — Degenerate witness answer := fun n => (f n : R) closes it by Asymptotics.isTheta_refl. In-file note acknowledges the loophole.  
**Known status:** Intended sharp-growth question open (determining Theta(f) would essentially solve the problem); formal statement trivially closable.  
**Difficulty:** math 9/10, Lean 1/10 · **Compute:** none · **Confidence:** high  
**Evidence:** isTheta_refl gives a one-line closure with the self-referential answer.  
**Flags:** answer-encoding trivializable (acknowledged in-file)  
**Next action:** Same as bigO_version.

## `erdos_357.parts.ii.littleO_version` — Vacuously true / accidentally weakened (cat 4)

**File:** `FormalConjectures/ErdosProblems/357.lean:81`  
**Secondary category:** 2 (Trivially or easily solvable)  
**Statement:** How does f(n) grow: exhibit g with g = o(f), answer(sorry)-encoded.  
**Source:** https://www.erdosproblems.com/357  
**Statement matches intent:** suspect — Degenerate witness answer := 0 closes it: the zero function is little-o of anything (Asymptotics.isLittleO_zero). In-file note explicitly names answer = 0 as a trivial solution.  
**Known status:** Intended lower-growth question open; formal statement trivially closable.  
**Difficulty:** math 8/10, Lean 1/10 · **Compute:** none · **Confidence:** high  
**Evidence:** isLittleO_zero is unconditional; one-line closure.  
**Flags:** answer-encoding trivializable (acknowledged in-file)  
**Next action:** Same as bigO_version.

## `erdos_357.parts.ii.littleO_version_symm` — Vacuously true / accidentally weakened (cat 4)

**File:** `FormalConjectures/ErdosProblems/357.lean:89`  
**Secondary category:** 2 (Trivially or easily solvable)  
**Statement:** How does f(n) grow: exhibit g with f = o(g), answer(sorry)-encoded.  
**Source:** https://www.erdosproblems.com/357  
**Statement matches intent:** suspect — Degenerate witness answer := fun n => (n:R)^2 closes it after the short lemma f n <= n (StrictMono a : Fin k -> Z into Icc 1 n forces k <= n, so the sSup is <= n), since n = o(n^2). Slightly more work than the other variants but still a routine closure.  
**Known status:** Intended upper-growth question open (any g with f = o(g) that beats o(n) would answer parts.i); formal statement easily closable with an overshooting g.  
**Difficulty:** math 8/10, Lean 3/10 · **Compute:** none · **Confidence:** high  
**Evidence:** f n <= n via injectivity of a strictly monotone map into an n-element interval; then f =O n =o n^2.  
**Flags:** answer-encoding trivializable via overshoot (acknowledged in-file)  
**Next action:** Same as bigO_version; note a non-degenerate answer o(n) would resolve parts.i.

## `erdos_357.variants.hegyvari` — Solved mathematically, not yet formalized (cat 5)

**File:** `FormalConjectures/ErdosProblems/357.lean:136`  
**Statement:** Let g(n) be the maximal k such that there exist 1 <= a_1,...,a_k <= n (no order constraint) with all consecutive-block sums distinct; then (1/3+o(1))n <= g(n) <= (2/3+o(1))n.  
**Source:** Hegyvari, On consecutive sums in sequences, Acta Math. Hungar. 48 (1986), 193-200; https://www.erdosproblems.com/357; OEIS A364153  
**Statement matches intent:** yes  
**Known status:** Solved mathematically: Hegyvari (1986) proved both bounds (confirmed via OEIS A364153 / erdosproblems.com quotation). Not formalized anywhere; no PR in pr_register.json targets it.  
**Difficulty:** math 5/10, Lean 7/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Search confirmed: 'If g(n) is the maximal k such that there are 1<=a_1,...,a_k<=n with all consecutive sums distinct, Hegyvari has proved that (1/3+o(1))n <= g(n) <= (2/3+o(1))n' (Acta Math. Hungar. 48 (1986), 193-200). HasDistinctSums forces the a_i pairwise distinct via singleton intervals, consistent with the intended reading.  
**Flags:** mislabeled: tagged research open but is a known 1986 theorem  
**Next action:** Relabel to research solved and formalize Hegyvari's proof; effort medium-large (combinatorial construction for the lower bound plus a counting upper bound).

## `erdos_357.variants.infinite_set_density` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/357.lean:113`  
**Statement:** If A is an infinite strictly increasing sequence of naturals with all finite consecutive-block sums distinct, then A has (natural) density 0.  
**Source:** https://www.erdosproblems.com/357  
**Statement matches intent:** yes  
**Known status:** Open conjecture; the lower-density-0 version is known (in-file variants.infinite_set_lower_density, tagged research solved).  
**Difficulty:** math 7/10, Lean 8/10 · **Compute:** none · **Confidence:** high  
**Evidence:** erdosproblems.com/357 open as of 2026-07-26; density-0 for such sequences is the stated open strengthening of the known lower-density result. HasDistinctSums over ord-connected finsets of N correctly encodes distinct consecutive sums; A 0 = 0 is excluded automatically (empty set vs {0} would collide).  
**Next action:** Keep open; a first step would be formalizing the known lower-density-0 result.

## `erdos_357.variants.infinite_set_sum` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/357.lean:122`  
**Statement:** If A is an infinite strictly increasing sequence of naturals with all finite consecutive-block sums distinct, then sum of 1/A(i) converges.  
**Source:** https://www.erdosproblems.com/357  
**Statement matches intent:** yes  
**Known status:** Open conjecture (stronger than density 0).  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Faithful: division-by-zero junk cannot arise nontrivially since A 0 = 0 contradicts HasDistinctSums and StrictMono forces A i >= 1 for i >= 1. Convergence of reciprocals requires super-linear growth, well beyond known bounds.  
**Next action:** Keep open.

## `erdos_357.variants.monotone.parts.i` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/357.lean:153`  
**Statement:** Let h(n) be the maximal k with 1 <= a_1 <= ... <= a_k <= n (weakly monotone) and all consecutive-block sums distinct. Is h(n) = o(n)?  
**Source:** https://www.erdosproblems.com/357  
**Statement matches intent:** yes  
**Known status:** Equivalent to the open main problem parts.i.  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Monotone a with a i = a j (i<j) forces a i = a (i+1); singleton ord-connected finsets {i}, {i+1} then have equal sums, contradicting InjOn. Hence the defining sets of h and f coincide.  
**Flags:** h provably equals f - monotone variant duplicates parts.i  
**Next action:** Optionally prove h = f as an API lemma to expose the equivalence; otherwise keep open alongside parts.i.

## `erdos_357.variants.monotone.parts.ii.bigO_version` — Vacuously true / accidentally weakened (cat 4)

**File:** `FormalConjectures/ErdosProblems/357.lean:160`  
**Secondary category:** 2 (Trivially or easily solvable)  
**Statement:** Growth of h(n): exhibit g with g = O(h), answer(sorry)-encoded.  
**Source:** https://www.erdosproblems.com/357  
**Statement matches intent:** suspect — Same trivialization as the f-versions: answer := fun n => (h n : R) via isBigO_refl, or answer := 0. Also h = f provably, so this duplicates parts.ii.bigO_version.  
**Known status:** Intended question open; formal statement trivially closable.  
**Difficulty:** math 8/10, Lean 1/10 · **Compute:** none · **Confidence:** high  
**Evidence:** One-line closure by isBigO_refl.  
**Flags:** answer-encoding trivializable (acknowledged in-file); h provably equals f  
**Next action:** Tighten encoding or treat as convention-guarded.

## `erdos_357.variants.monotone.parts.ii.bigO_version_symm` — Vacuously true / accidentally weakened (cat 4)

**File:** `FormalConjectures/ErdosProblems/357.lean:168`  
**Secondary category:** 2 (Trivially or easily solvable)  
**Statement:** Growth of h(n): exhibit g with h = O(g), answer(sorry)-encoded.  
**Source:** https://www.erdosproblems.com/357  
**Statement matches intent:** suspect — answer := fun n => (h n : R) closes it by isBigO_refl. h = f provably.  
**Known status:** Intended question open; formal statement trivially closable.  
**Difficulty:** math 8/10, Lean 1/10 · **Compute:** none · **Confidence:** high  
**Evidence:** One-line closure by isBigO_refl.  
**Flags:** answer-encoding trivializable (acknowledged in-file); h provably equals f  
**Next action:** Tighten encoding or treat as convention-guarded.

## `erdos_357.variants.monotone.parts.ii.bigTheta_version` — Vacuously true / accidentally weakened (cat 4)

**File:** `FormalConjectures/ErdosProblems/357.lean:176`  
**Secondary category:** 2 (Trivially or easily solvable)  
**Statement:** Growth of h(n): exhibit g with h = Theta(g), answer(sorry)-encoded.  
**Source:** https://www.erdosproblems.com/357  
**Statement matches intent:** suspect — answer := fun n => (h n : R) closes it by isTheta_refl. h = f provably.  
**Known status:** Intended question open; formal statement trivially closable.  
**Difficulty:** math 9/10, Lean 1/10 · **Compute:** none · **Confidence:** high  
**Evidence:** One-line closure by isTheta_refl.  
**Flags:** answer-encoding trivializable (acknowledged in-file); h provably equals f  
**Next action:** Tighten encoding or treat as convention-guarded.

## `erdos_357.variants.monotone.parts.ii.littleO_version` — Vacuously true / accidentally weakened (cat 4)

**File:** `FormalConjectures/ErdosProblems/357.lean:184`  
**Secondary category:** 2 (Trivially or easily solvable)  
**Statement:** Growth of h(n): exhibit g with g = o(h), answer(sorry)-encoded.  
**Source:** https://www.erdosproblems.com/357  
**Statement matches intent:** suspect — answer := 0 closes it by isLittleO_zero. h = f provably.  
**Known status:** Intended question open; formal statement trivially closable.  
**Difficulty:** math 8/10, Lean 1/10 · **Compute:** none · **Confidence:** high  
**Evidence:** isLittleO_zero is unconditional.  
**Flags:** answer-encoding trivializable (acknowledged in-file); h provably equals f  
**Next action:** Tighten encoding or treat as convention-guarded.

## `erdos_357.variants.monotone.parts.ii.littleO_version_symm` — Vacuously true / accidentally weakened (cat 4)

**File:** `FormalConjectures/ErdosProblems/357.lean:192`  
**Secondary category:** 2 (Trivially or easily solvable)  
**Statement:** Growth of h(n): exhibit g with h = o(g), answer(sorry)-encoded.  
**Source:** https://www.erdosproblems.com/357  
**Statement matches intent:** suspect — answer := fun n => (n:R)^2 closes it after the short lemma h n <= n (values in Icc 1 n, forced injective, so k <= n). h = f provably.  
**Known status:** Intended question open; formal statement easily closable with an overshooting g.  
**Difficulty:** math 8/10, Lean 3/10 · **Compute:** none · **Confidence:** high  
**Evidence:** h n <= n from injectivity into an n-element interval; then h =O n =o n^2.  
**Flags:** answer-encoding trivializable via overshoot (acknowledged in-file); h provably equals f  
**Next action:** Tighten encoding or treat as convention-guarded.

## `erdos_359.parts.i` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/359.lean:38`  
**Statement:** For the greedy sequence a_1=1 and a_{i+1} = least integer not a sum of consecutive earlier terms (OEIS A002048: 1,2,4,5,8,10,14,15,...), show a_k / k tends to infinity.  
**Source:** https://www.erdosproblems.com/359; OEIS A002048  
**Statement matches intent:** yes  
**Known status:** Open on erdosproblems.com as of 2026-07-26. No PR or duplicate in this repo.  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** none · **Confidence:** high  
**Evidence:** IsGoodFor is faithful: the extra constraint m > A j in the IsLeast set is provably consistent with 'least non-representable integer' (all integers < A(j+1) are consecutive sums by induction, and sums below A j never change when later terms are added), and the empty-interval sum 0 is harmlessly excluded since m > A j >= 1. The sequence exists and is unique, so the hypothesis is non-vacuous. Index shift (A 0 = a_1) does not affect the asymptotics.  
**Next action:** Keep open; small-scale computation of A002048 growth could inform but not resolve.

## `erdos_359.parts.ii` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/359.lean:46`  
**Statement:** For the same greedy sequence, show a_k / k^{1+c} tends to 0 for every fixed c > 0.  
**Source:** https://www.erdosproblems.com/359; OEIS A002048  
**Statement matches intent:** yes  
**Known status:** Open on erdosproblems.com as of 2026-07-26.  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Faithful; real-power division at k=0 is junk-but-irrelevant at atTop. Fixed c > 0 quantification matches 'for any c > 0'.  
**Next action:** Keep open.

## `erdos_359.variants.isGoodFor_1_asymptotic` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/359.lean:62`  
**Statement:** For the same greedy sequence, the conjectured asymptotic a_k ~ k log k / log log k.  
**Source:** https://www.erdosproblems.com/359; OEIS A002048  
**Statement matches intent:** yes  
**Known status:** Open conjecture, strictly stronger than parts i and ii.  
**Difficulty:** math 9/10, Lean 9/10 · **Compute:** none · **Confidence:** high  
**Evidence:** IsEquivalent at atTop; Real.log junk values at small k are irrelevant. Implies both parts i and ii.  
**Next action:** Keep open.

## `erdos_36` — Vacuously true / accidentally weakened (cat 4)

**File:** `FormalConjectures/ErdosProblems/36.lean:256`  
**Secondary category:** 5 (Solved mathematically, not yet formalized)  
**Statement:** Minimum overlap problem: determine the limit of M(N)/N (answer(sorry)-encoded).  
**Source:** https://www.erdosproblems.com/36; Wikipedia: Minimum overlap problem  
**Statement matches intent:** suspect — answer := atTop.liminf MinOverlapQuotient (or Filter.limsup / a lim term) turns the statement into 'the limit exists', which is a known theorem (existence of the limit, in-file variants.exists tagged research solved with the 0.385694 bound, attributed to Haugland). The intended problem - identify the actual constant, only known to lie in (0.379005, 0.380926854) with no closed form - is open.  
**Known status:** Formal statement reduces to formalizing the known limit-existence proof plus a non-informative witness; the intended exact constant is a recognized open problem.  
**Difficulty:** math 9/10, Lean 9/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** Tendsto f (nhds (liminf f)) holds iff the limit exists (for this bounded real sequence); existence is recorded as solved in-file. Exact value unknown in the literature as of Jan 2026.  
**Flags:** answer-encoding admits non-informative witness (liminf); limit-existence attribution (Haugland) taken from in-file solved tag - needs literature check for exact citation  
**Next action:** Tighten encoding (e.g. require a closed-form or high-precision decimal with matching Tendsto proof), or treat closure as 'formalize Haugland's limit-existence theorem' (large effort).

## `erdos_36.variants.lower` — Vacuously true / accidentally weakened (cat 4)

**File:** `FormalConjectures/ErdosProblems/36.lean:233`  
**Secondary category:** 5 (Solved mathematically, not yet formalized)  
**Statement:** Minimum overlap problem: exhibit an explicit c with 0.379005 < c <= liminf M(N)/N, i.e. beat White's 2022 lower bound.  
**Source:** https://www.erdosproblems.com/36; E. P. White, Erdos' minimum overlap problem, arXiv:2201.05704  
**Statement matches intent:** suspect — The answer-encoding admits the degenerate witness c := atTop.liminf MinOverlapQuotient: then 0.379005 < c is exactly White's 2022 theorem (stated strictly in-file as white_2022) and c <= liminf is le_refl. So the formal statement requires no NEW bound, only a formalization of White's known result, whereas the intended problem is to find a genuinely better explicit bound.  
**Known status:** Formal statement mathematically settled by White 2022 + degenerate witness, but formalizing White's proof is research-scale; intended improvement is open. No internal PR targets it (pr_register.json checked).  
**Difficulty:** math 9/10, Lean 9/10 · **Compute:** none · **Confidence:** high  
**Evidence:** liminf of the bounded quotient (0 <= M(N)/N <= 1/2) is a genuine real; witness c := liminf satisfies all three conjuncts given White's strict bound. Definitions Overlap/MaxOverlap/M faithfully encode the classical minimum overlap problem (partition of {1..2n} into equal halves, max number of solutions of a-b=k).  
**Flags:** answer-encoding admits degenerate witness c := liminf  
**Next action:** Either tighten the encoding to demand an explicit decimal strictly above 0.379005, or treat closure as 'formalize White 2022' (large effort).

## `erdos_36.variants.upper` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/36.lean:241`  
**Statement:** Minimum overlap problem: exhibit c strictly below 0.380926853433087 with limsup M(N)/N <= c, i.e. strictly beat Haugland's best upper bound.  
**Source:** https://www.erdosproblems.com/36; J. K. Haugland, https://www.neutreeko.net/mop/index.htm  
**Statement matches intent:** yes  
**Known status:** Genuinely open: the constant 0.380926853433087 equals Haugland's published bound 0.3809268534330870 (same real), so the statement is equivalent to limsup < best-known-bound, which no one has proved. Unlike variants.lower, the degenerate witness c := limsup does NOT close it.  
**Difficulty:** math 9/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Exists c with limsup <= c < B iff limsup < B; current knowledge only gives limsup <= B. Improving the bound requires new constructions/analysis.  
**Flags:** possibly false if Haugland's bound is sharp - truth value itself unknown  
**Next action:** Keep open. Caution: if Haugland's construction-based bound is essentially sharp (the limit is conjectured numerically to be very close to it), this statement could even be false; consider weakening to <= or flagging.

## `erdos_361.bigO` — Vacuously true / accidentally weakened (cat 4)

**File:** `FormalConjectures/ErdosProblems/361.lean:34`  
**Secondary category:** 2 (Trivially or easily solvable)  
**Statement:** Erdos 361: for c > 0, how large can A be inside {1,...,floor(cn)} such that n is NOT a sum of any subset of A? Formalized as an =O growth statement with answer(sorry).  
**Source:** https://www.erdosproblems.com/361  
**Statement matches intent:** no — Two independent defects. (1) The hypothesis 'hA : forall c n, A n = ...' re-binds c, shadowing the outer (c : R) (hc : 0 < c); quantifying over ALL c makes hA unsatisfiable: hA 0 1 forces A 1 = 0 (Icc 1 0 empty, only the empty set survives the filter, sup card = 0) while hA 2 1 forces A 1 = 2 (subsets of {1,2} with total sum != 1 include {1,2}), so the hypothesis is contradictory and the theorem is vacuously provable with ANY answer. (2) Even ignoring the shadowing, the filter condition 'n != sum over B' only excludes sets whose OWN total equals n, not sets having a SUBSET summing to n; the intended extremal function requires 'forall S subseteq B, n != sum S'. As written the sup is trivially about floor(cn), a different (trivial) quantity.  
**Known status:** Intended problem open on erdosproblems.com as of 2026-07-26; formal statement is a vacuous mis-formalization.  
**Difficulty:** math 8/10, Lean 2/10 · **Compute:** none · **Confidence:** high  
**Evidence:** hA 0 1: Icc 1 (floor 0) = empty, powerset = {empty}, empty kept (1 != 0), sup card = 0. hA 2 1: Icc 1 2 = {1,2}, kept sets empty,{2},{1,2}, sup card = 2. 0 != 2 gives False.  
**Flags:** shadowed quantifier makes hypothesis contradictory (vacuous); filter checks only B's own sum, not subset sums - wrong extremal function; outer c and hc unused; answer-encoding weak even after fix  
**Next action:** Fix the statement: remove the inner 'forall c' (use the outer c) and change the filter to exclude all B having a subset summing to n; then re-audit. Current statement closable by deriving False from hA 0 1 and hA 2 1 (decide/norm_num on tiny finsets).

## `erdos_361.bigTheta` — Vacuously true / accidentally weakened (cat 4)

**File:** `FormalConjectures/ErdosProblems/361.lean:48`  
**Secondary category:** 2 (Trivially or easily solvable)  
**Statement:** Same Erdos 361 question formalized as an =Theta growth statement with answer(sorry).  
**Source:** https://www.erdosproblems.com/361  
**Statement matches intent:** no — Identical defects to erdos_361.bigO: inner 'forall c' shadows the outer c making hA contradictory (A 1 = 0 and A 1 = 2), and the filter excludes only sets whose own total sum is n rather than sets with a subset summing to n.  
**Known status:** Intended problem open; formal statement vacuously provable.  
**Difficulty:** math 8/10, Lean 2/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Same computation: hA 0 1 gives A 1 = 0, hA 2 1 gives A 1 = 2.  
**Flags:** shadowed quantifier makes hypothesis contradictory (vacuous); filter checks only B's own sum, not subset sums; outer c and hc unused  
**Next action:** Fix statement as for bigO; current version closable by contradiction from hA 0 1 and hA 2 1.

## `erdos_361.smallO` — Vacuously true / accidentally weakened (cat 4)

**File:** `FormalConjectures/ErdosProblems/361.lean:62`  
**Secondary category:** 2 (Trivially or easily solvable)  
**Statement:** Same Erdos 361 question formalized as an =o growth statement with answer(sorry).  
**Source:** https://www.erdosproblems.com/361  
**Statement matches intent:** no — Identical defects to erdos_361.bigO: contradictory shadowed hypothesis and own-sum-only filter.  
**Known status:** Intended problem open; formal statement vacuously provable.  
**Difficulty:** math 8/10, Lean 2/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Same computation: hA 0 1 gives A 1 = 0, hA 2 1 gives A 1 = 2.  
**Flags:** shadowed quantifier makes hypothesis contradictory (vacuous); filter checks only B's own sum, not subset sums; outer c and hc unused  
**Next action:** Fix statement as for bigO; current version closable by contradiction from hA 0 1 and hA 2 1.

## `erdos_364` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/ErdosProblems/364.lean:30`  
**Statement:** There is no triple of consecutive integers n, n+1, n+2 all of which are powerful (every prime factor appears with exponent >= 2). This is the Erdos-Mollin-Walsh conjecture.  
**Source:** https://www.erdosproblems.com/364  
**Statement matches intent:** yes  
**Known status:** erdosproblems.com state 'verifiable' (open). No PR or campaign in the fork targets it. Verified computationally to very large bounds; abc conjecture would only give finiteness of triples, not nonexistence.  
**Difficulty:** math 9/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Powerful = (2).Full = forall p in primeFactors, p^2 | n. Degenerate cases checked: n=0 gives Powerful 0 and 1 vacuously but Powerful 2 fails, so no junk counterexample. Statement is the exact Erdos-Mollin-Walsh conjecture.  
**Next action:** Leave open; no viable attack. Any claimed counterexample would be checkable via the Decidable instance for Powerful.

## `erdos_364.variants.strong` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/ErdosProblems/364.lean:41`  
**Statement:** Erdos's stronger conjecture: there is c > 0 such that the k-th and (k+2)-nd powerful numbers always differ by more than n_k^c.  
**Source:** https://www.erdosproblems.com/364; Erdos [Er76d]  
**Statement matches intent:** yes  
**Known status:** Open; strictly stronger (asymptotically) than the main triple conjecture. No internal or external progress found.  
**Difficulty:** math 9/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** binrel% elaboration puts the subtraction in R (coercions at leaves), so no Nat-truncation; even Nat-subtraction would be safe since nth is strictly monotone. The 'for all k' form with existential c is equivalent to the intended eventual form: for the finitely many small k the gap is >= 2 while n_k^c < 2 once c is chosen small enough.  
**Flags:** index-shift: 0 counted as powerful by vacuous Full; harmless  
**Next action:** Leave open.

## `erdos_366` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/366.lean:30`  
**Secondary category:** 6 (Computationally solvable with certificate)  
**Statement:** Does there exist n > 0 such that n is 2-full (powerful) and n+1 is 3-full (every prime factor cubed divides)?  
**Source:** https://www.erdosproblems.com/366  
**Statement matches intent:** yes  
**Known status:** erdosproblems.com state 'verifiable' (open): a yes-answer would be a finite checkable witness; none known despite searches. No fork PR targets it.  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** large · **Confidence:** high  
**Evidence:** Full k n := forall p in n.primeFactors, p^k | n, vacuously true at n=0,1. The n>0 guard excludes n=0; n=1 fails since 2 is not 3-full. So no degenerate witness; the answer(sorry) <-> exists encoding is faithful to the yes/no question.  
**Flags:** a yes resolution is certificate-checkable (Decidable Full)  
**Next action:** Leave open; a witness n would close the answer(sorry) side instantly via the Decidable instance for Nat.Full plus decide/norm_num, but searches to large bounds have found none.

## `erdos_366.variants.three_two` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/366.lean:45`  
**Statement:** Are there infinitely many n such that n is 3-full and n+1 is 2-full? (Example: 12167 = 23^3, 12168 = 2^3*3^2*13^2.)  
**Source:** https://www.erdosproblems.com/366  
**Statement matches intent:** yes  
**Known status:** Open; sporadic examples known, infinitude unknown.  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Set {n | (3).Full n and (2).Full (n+1)}.Infinite matches the question; infinitude cannot be faked by the vacuous small cases 0,1 (1 has 2 = n+1 not 2-full... 2 is not 2-full, and 0 is a single junk point).  
**Next action:** Leave open.

## `erdos_366.variants.weaker` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/366.lean:53`  
**Secondary category:** 6 (Computationally solvable with certificate)  
**Statement:** Does there exist a pair of consecutive integers n, n+1 that are both 3-full?  
**Source:** https://www.erdosproblems.com/366  
**Statement matches intent:** yes  
**Known status:** Open; no example known, conjecturally none exist (related to abc-type heuristics).  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** large · **Confidence:** high  
**Evidence:** The n > 0 guard is essential and present: without it n=0 would be a trivial witness since 0 and 1 are vacuously 3-full. n=1 fails (2 not 3-full). Encoding faithful.  
**Flags:** n>0 guard correctly blocks the vacuous 0/1 witness  
**Next action:** Leave open; a witness would be kernel-checkable via Decidable Full.

## `erdos_371` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/371.lean:31`  
**Statement:** The set of n for which the largest prime factor of n+1 exceeds that of n has natural density 1/2.  
**Source:** https://www.erdosproblems.com/371  
**Statement matches intent:** yes  
**Known status:** erdosproblems.com state 'open'. Erdos-Pomerance proved positive-density partial results; the exact density 1/2 (even existence of the density) is open.  
**Difficulty:** math 9/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Set.HasDensity is Tendsto of |S cap Iio n| / |Iio n| to 1/2, the standard natural density; maxPrimeFac = sSup of prime divisors is the intended P(n) for n >= 2.  
**Next action:** Leave open.

## `erdos_373` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/373.lean:41`  
**Statement:** The equation n! = a_1! a_2! ... a_k! with n-1 > a_1 >= ... >= a_k > 1 has only finitely many solutions.  
**Source:** https://www.erdosproblems.com/373  
**Statement matches intent:** yes  
**Known status:** erdosproblems.com state 'open'. Known conditional results (would follow from P(n(n+1))/log n -> infinity) are formalized as separate research-solved variants in the same file.  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Set S audited: empty list excluded (headI = 0 < n-1 forces n >= 2 but then n! != 1); Nat-subtraction in headI < n-1 safe for all n; the a_i > 1 condition correctly kills padding by 1! = 1; per fixed n only finitely many lists, so S.Finite is exactly 'finitely many solutions'.  
**Next action:** Leave open.

## `erdos_373.variants.maximal_solution` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/373.lean:77`  
**Statement:** Hickerson's conjecture: the largest nontrivial solution of n! = a_1!...a_k! is 16! = 14!5!2!.  
**Source:** https://www.erdosproblems.com/373  
**Statement matches intent:** yes  
**Known status:** Open; implies the finiteness conjecture with an explicit bound.  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Checked 16*15 = 240 = 5!*2!, Pairwise >= on [14,5,2], headI 14 < 15, all entries > 1 - the witness half is correct, so the statement is not accidentally false.  
**Next action:** Leave open; the membership conjunct (16,[14,5,2]) in S alone is provable by decide/norm_num (16! = 240*14! = 14!*5!*2!), but the universal bound is the open content.

## `erdos_373.variants.suranyi` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/373.lean:86`  
**Statement:** Suranyi's conjecture: the only nontrivial solution of n! = a! b! (excluding the family (a+1)! = (a+1)*a!) is 10! = 7! 6!.  
**Source:** https://www.erdosproblems.com/373  
**Statement matches intent:** yes  
**Known status:** Open; longstanding.  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Side conditions audited: 1 < a, 1 < b excludes padding by 1!; a+1 != n excludes the trivial family n = a+1 (e.g. 24! = 4!*23! has a = 23, a+1 = 24 = n); b <= a normalizes ordering so the singleton {(10,7,6)} is the right RHS; a >= n impossible since it forces b! <= 1. Faithful.  
**Next action:** Leave open.

## `erdos_375` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/ErdosProblems/375.lean:43`  
**Statement:** Grimm's conjecture: if n+1,...,n+k are all composite then one can choose k distinct primes p_i with p_i | n+i. Encoded as a yes/no answer question.  
**Source:** https://www.erdosproblems.com/375; [RST75]  
**Statement matches intent:** yes  
**Known status:** erdosproblems.com state 'falsifiable' (open). Grimm's conjecture implies prime gaps p_{n+1} - p_n < p_n^{1/2-c}, beyond even RH-conditional technology; both proving and refuting look far out of reach.  
**Difficulty:** math 9/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Erdos375Prop: forall n >= 1, forall k, (forall i < k, not (n+i+1).Prime) -> injective p : Fin k -> N with p i prime dividing n+i+1 - exactly Grimm. n >= 1 and 'not prime' vs 'composite' agree since n+i+1 >= 2. The k <= 2 case is already proved in the file.  
**Flags:** duplicate statement in Wikipedia/Grimm.lean and Subsets/FC100OpenSet1.lean (both still sorry)  
**Next action:** Leave open. Note duplicate open formalizations of the same conjecture at FormalConjectures/Wikipedia/Grimm.lean and FormalConjectures/Subsets/FC100OpenSet1.lean (no proof anywhere).

## `erdos_376` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/376.lean:30`  
**Statement:** Are there infinitely many n such that the central binomial coefficient C(2n,n) is coprime to 105 = 3*5*7?  
**Source:** https://www.erdosproblems.com/376; Erdos-Graham-Ruzsa-Straus [EGRS75]  
**Statement matches intent:** yes  
**Known status:** erdosproblems.com state 'open'. EGRS proved the two-prime analogue (coprime to pq for any two odd primes), formalized as a research-solved variant in the file; the three-prime case is the open problem.  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** none · **Confidence:** high  
**Evidence:** centralBinom n = (2n).choose n; Coprime 105 is exactly 'not divisible by 3, 5, or 7'; Set.Infinite matches 'infinitely many'. No degenerate loophole (n=0,1 members do not affect infinitude).  
**Next action:** Leave open.

## `erdos_377` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/377.lean:45`  
**Statement:** Is there an absolute constant C such that the sum of 1/p over primes p <= n not dividing C(2n,n) is at most C for all n?  
**Source:** https://www.erdosproblems.com/377; [EGRS75]  
**Statement matches intent:** yes  
**Known status:** erdosproblems.com state 'open'. EGRS75 proved the mean value of f(n) is the constant gamma_0 and f(n) = gamma_0 + o(1) for almost all n (research-solved variants in file); uniform boundedness is the open question.  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** none · **Confidence:** high  
**Evidence:** sumInvPrimesNotDvdCentralBinom sums 1/p over p in Icc 1 n with p prime and p not dividing centralBinom n - matches the indicator sum; f >= 0 so requiring C > 0 loses nothing; forall n (not just large n) is fine since finitely many small n are absorbed into C.  
**Next action:** Leave open.

## `erdos_383` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/383.lean:35`  
**Statement:** Is it true that for every k there are infinitely many primes p such that the largest prime factor of (p^2)(p^2+1)...(p^2+k) is p itself, i.e. all prime factors of p^2+i for 1 <= i <= k are < p?  
**Source:** https://www.erdosproblems.com/383  
**Statement matches intent:** yes  
**Known status:** erdosproblems.com state 'open'.  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** Product over Icc 0 k includes the i=0 term p^2, so maxPrimeFac = p correctly encodes 'p is the largest prime factor of the whole product' (for p > k, p cannot divide p^2+i, 1 <= i <= k, so the condition forces all their factors < p). k=0 gives all primes, harmlessly true. Formalization matches the docstring, which matches the site statement.  
**Next action:** Leave open.

## `erdos_385.parts.i` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/385.lean:54`  
**Statement:** With F(n) = max{m + p(m) : m < n composite} (p = least prime factor), is F(n) > n for all sufficiently large n?  
**Source:** https://www.erdosproblems.com/385; Erdos-Eggleton-Selfridge  
**Statement matches intent:** yes  
**Known status:** erdosproblems.com state 'open'.  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** none · **Confidence:** high  
**Evidence:** F uses sSup of {m + m.minFac | m < n, m.Composite}; Composite = 1 < m and not prime, so minFac is genuine least prime factor and F n <= n + sqrt n (proved in file). sSup of empty set = 0 for n <= 4, harmless under the eventually filter.  
**Next action:** Leave open.

## `erdos_385.parts.ii` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/385.lean:60`  
**Statement:** Does F(n) - n tend to infinity?  
**Source:** https://www.erdosproblems.com/385  
**Statement matches intent:** yes  
**Known status:** Open.  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Truncation analysis: truncated difference -> infinity iff integer difference -> infinity, so no semantic drift.  
**Flags:** N-subtraction present but provably harmless here  
**Next action:** Leave open.

## `erdos_385.variants.lb` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/385.lean:66`  
**Statement:** Is F(n) >= n + (1-o(1)) sqrt(n), as Erdos, Eggleton and Selfridge suggested possible?  
**Source:** https://www.erdosproblems.com/385  
**Statement matches intent:** yes  
**Known status:** Open.  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** Verified: for n <= 4 the inequality n + (1 - e n) sqrt n <= F n = 0 is satisfiable by picking e n >= 1 + sqrt n, allowed since =o[atTop] only constrains the tail. So no accidental falsity and no weakening.  
**Flags:** junk F(n)=0 for n<=4 absorbed by existential o(1) function; statement equivalent to intended  
**Next action:** Leave open.

## `erdos_386` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/386.lean:33`  
**Statement:** Is there some k >= 2 such that C(n,k) (with k <= n-2) is a product of consecutive primes for infinitely many n? (E.g. C(21,2) = 210 = 2*3*5*7.)  
**Source:** https://www.erdosproblems.com/386  
**Statement matches intent:** yes  
**Known status:** erdosproblems.com state 'open'.  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** Degenerate-product audit: empty product (q <= p) equals 1, impossible for C(n,k) with 2 <= k <= n-2 (>= 6); single-prime products cannot occur infinitely often for fixed k >= 2 since C(n,2) = n(n-1)/2 is composite for n >= 5. Nat-subtraction in k <= n-2 only excludes small n, harmless under frequently-atTop.  
**Flags:** quantifier ambiguity in source prose, resolved via variants  
**Next action:** Leave open.

## `erdos_386.variants.forall` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/386.lean:43`  
**Statement:** For every k >= 2, is C(n,k) a product of consecutive primes for infinitely many n?  
**Source:** https://www.erdosproblems.com/386  
**Statement matches intent:** yes  
**Known status:** Open; strongest reading of the problem.  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** Same encoding audit as the main statement; forall-k reading.  
**Next action:** Leave open.

## `erdos_386.variants.two` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/386.lean:52`  
**Statement:** Is C(n,2) = n(n-1)/2 a product of consecutive primes for infinitely many n?  
**Source:** https://www.erdosproblems.com/386  
**Statement matches intent:** yes  
**Known status:** Open; the k=2 case highlighted by the example C(21,2) = 210.  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** Faithful; sporadic examples exist (n = 21), infinitude is the open content and cannot be trivialized by empty or singleton prime products.  
**Next action:** Leave open.

## `erdos_387.variants.schinzel` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/387.lean:58`  
**Statement:** Schinzel's conjecture (Guy, UPINT): for every sufficiently large k that is not a prime power, there exists n such that none of n, n-1, ..., n-k+1 divides C(n,k). (Schinzel's classical example: k = 15, n = 99215.)  
**Source:** https://www.erdosproblems.com/387; [Sc58]; Guy UPINT [Gu04]  
**Statement matches intent:** yes  
**Known status:** Main problem 387 was solved (negatively) by Bui-Naprienko-Pratt-Zaharescu, arXiv:2605.21221, and erdosproblems.com marks 387 'solved'; but this Schinzel characterization variant is a distinct sub-conjecture that the 2026-updated file still marks research open. My search found no resolution; post-cutoff status uncertain.  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** Junk-witness audit: n < k gives C(n,k) = 0 and everything divides 0, so such n never witnesses; n = k fails via n-i = 1 | 1; for n > k the values n-i, i < k, are exactly n-k+1..n. Encoding faithful. The file's own native_decide example verifies Schinzel's k=15, n=99215 instance.  
**Flags:** needs literature check (main 387 solved May 2026, after knowledge cutoff; variant status could have moved)  
**Next action:** Check the BNPZ26 paper and recent literature for whether the full Schinzel characterization was settled; otherwise leave open.

## `erdos_389` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/389.lean:33`  
**Statement:** Is it true that for every n >= 1 there is k >= 1 with n(n+1)...(n+k-1) dividing (n+k)...(n+2k-1)?  
**Source:** https://www.erdosproblems.com/389  
**Statement matches intent:** yes  
**Known status:** erdosproblems.com state 'open'. Minimal k computed for 1 <= n <= 18 (Mehta); the n = 4, k = 207 case is proved in-file by native_decide.  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Products over Finset.range k give exactly n...(n+k-1) and (n+k)...(n+2k-1); k >= 1 guard prevents the trivial k = 0 witness (empty product divides empty product would make it vacuous). Faithful.  
**Next action:** Leave open; individual n are decidable but the universal statement needs a proof idea.

## `erdos_39` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/39.lean:34`  
**Statement:** Erdos's $500 problem: does there exist an infinite Sidon set A of naturals whose counting function satisfies |A cap [1,N]| >> N^{1/2-eps} for every eps > 0?  
**Source:** https://www.erdosproblems.com/39  
**Statement matches intent:** yes  
**Known status:** erdosproblems.com state 'open', $500 prize. Best known construction exponent ~ sqrt(2)-1 (Ruzsa) with small later improvements; full problem open.  
**Difficulty:** math 9/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** IsSidon is the standard pairwise-sums condition; the bound is encoded as (fun N => N^(1/2-eps)) =O[atTop] (counting function) for every eps > 0, i.e. counting >>_eps N^{1/2-eps} - exactly the intended lower-bound question. answer(sorry) yes/no encoding faithful.  
**Next action:** Leave open.

## `erdos_390` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/390.lean:46`  
**Statement:** Let f(n) be the least possible largest term when n! is written as a product of distinct integers all > n. Erdos-Guy-Selfridge proved f(n) - 2n = Theta(n/log n); is f(n) - 2n asymptotic to c*n/log n for some constant c?  
**Source:** https://www.erdosproblems.com/390; [EGS82]  
**Statement matches intent:** yes  
**Known status:** erdosproblems.com state 'open'. The Theta result [EGS82] is a separate research-solved variant in the file.  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Definition audit of f: StrictMono f with f 0 > n and f(k-1) = m, product over i < k equals n! - factors distinct, > n, largest m; single-factor representation m = n! keeps the set nonempty for n >= 3. Junk values (f 2 = sInf empty = 0; k = 0 truncation cases at n <= 1) only affect finitely many n, irrelevant to the asymptotic. The subtraction f n - 2n elaborates in R (binop coercion at leaves), so no Nat truncation.  
**Flags:** sInf-empty and k-1 truncation junk at n<=2 only; harmless for asymptotics  
**Next action:** Leave open.

## `erdos_394.parts.i` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/394.lean:44`  
**Statement:** With t_2(n) the least m such that n divides m(m+1), decide whether sum_{n<=x} t_2(n) << x^2/(log x)^c for some c>0.  
**Source:** https://www.erdosproblems.com/394; Erdos-Graham 1980; OEIS A344005  
**Statement matches intent:** yes  
**Known status:** erdosproblems.com state open (2026-07-26). Erdos-Hall 1978 proved sum << x^2 logloglog x/loglog x (in-file hall_bound); the (log x)^{-c} saving is the open question. No internal PR/campaign work found.  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Faithful decision encoding: answer(sorry) <-> exists c>0, IsBigO. The repo's << notation forces domain N -> R, making the floor in Icc 1 |x| a harmless no-op; asymptotics along N are equivalent here.  
**Next action:** Leave open; monitor erdosproblems.com. The t definition (sInf over {m>0 : n | m(m+1)}) is sound for n>=1 and the sum starts at n=1, so no junk values enter.

## `erdos_394.parts.ii` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/394.lean:54`  
**Statement:** Decide whether for every k>=2, sum_{n<=x} t_{k+1}(n) = o(sum_{n<=x} t_k(n)).  
**Source:** https://www.erdosproblems.com/394; Erdos-Graham 1980  
**Statement matches intent:** yes  
**Known status:** Open per erdosproblems.com (2026-07-26). No internal work found.  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Quantifier structure (forall k>=2 inside the decided proposition) matches the docstring and site phrasing; t k n is well-defined and positive for n>=1, k>=1 (witness m=n).  
**Next action:** Leave open. Even the k=2 case (sum t_3 = o(sum t_2)) appears unresolved.

## `erdos_394.variants.factorial_gap_conjecture` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/394.lean:97`  
**Statement:** Decide whether there are infinitely many n such that t_k(n!) < t_{k-1}(n!) - 1 for all k in the stated range (formalized as 2 <= k < n).  
**Source:** https://www.erdosproblems.com/394; Erdos-Graham 1980 (with Selfridge for n=10)  
**Statement matches intent:** suspect — Docstring (and site prose) says 'for all 1 <= k < n' but the formal statement quantifies 2 <= k < n. k=1 would involve the junk value t_0 (sInf of empty set = 0), so the formalizer shifted the range; if the intended reading is pairs (t_{k+1}, t_k) for 1 <= k < n, the top-end comparison t_n(n!) < t_{n-1}(n!) - 1 is silently dropped (off-by-one at the upper boundary).  
**Known status:** Open per erdosproblems.com. The in-file companion factorial_gap_10 uses the same 2 <= k < 10 convention, so the file is internally consistent.  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** N-subtraction in t (k-1) (n!) - 1 is safe: t_{k-1}(n!) >= 1 whenever defined, and the truncated inequality agrees with the integer semantics. Vacuous membership of n <= 2 in the set does not affect infinitude.  
**Flags:** k-range ambiguity vs quoted prose (1<=k vs 2<=k), possible dropped top-end inequality; t_0 is a junk value (sInf empty = 0) but is excluded by the chosen range  
**Next action:** Confirm the exact k-range against the erdosproblems.com prose and fix the boundary if needed; otherwise leave open.

## `erdos_394.variants.hall_conjecture` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/394.lean:77`  
**Statement:** Erdos-Hall conjecture: sum_{n<=x} t_2(n) = o(x^2/(log x)^c) for every c < log 2.  
**Source:** https://www.erdosproblems.com/394; Erdos-Hall, J. Austral. Math. Soc. 1978  
**Statement matches intent:** yes  
**Known status:** Open: it strictly implies parts.i (take any 0<c<log 2), and the main problem is listed open on erdosproblems.com today, so this refinement cannot be proved. No internal work found.  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** Direct statement, no answer() encoding. forall c < log 2 also includes c <= 0, but those cases follow from the proven Erdos-Hall bound, so no weakening or falsification; rpow junk at small x is irrelevant at atTop.  
**Flags:** quantifier ranges over c <= 0 too (harmless, implied by known bound); needs literature check for post-1978 progress on the c < log 2 refinement  
**Next action:** Leave open; a literature check on recent work on A344005/t_2 sums (de la Breteche/Tenenbaum school) would be worthwhile before any future attempt.

## `erdos_396` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/396.lean:32`  
**Statement:** Is it true that for every k there exists n such that n(n-1)...(n-k) divides the central binomial coefficient C(2n,n)?  
**Source:** https://www.erdosproblems.com/396  
**Statement matches intent:** yes  
**Known status:** erdosproblems.com state 'open'.  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** none · **Confidence:** high  
**Evidence:** descFactorial n (k+1) = n(n-1)...(n-k), matching the docstring product over 0 <= i <= k. Degenerate audit: for n <= k the descFactorial is 0 and 0 divides centralBinom n never (centralBinom >= 1), so no junk witness; k = 0 has the honest witness n = 1 (1 | 2), consistent with the intended question.  
**Next action:** Leave open; individual k are searchable but the universal statement is the open content.

## `erdos_398` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/ErdosProblems/398.lean:35`  
**Statement:** Brocard's problem: decide whether the only n with n! + 1 a perfect square are n = 4, 5, 7.  
**Source:** https://www.erdosproblems.com/398; https://en.wikipedia.org/wiki/Brocard%27s_problem; OEIS A146968  
**Statement matches intent:** yes  
**Known status:** Famous open problem (Brocard 1876, Ramanujan 1913). erdosproblems.com state 'falsifiable' = open today. Overholt showed the weak abc conjecture implies finitely many solutions; computations (Berndt-Galway, later extended to ~10^15) found no further solutions. Repo has only a pointer file Wikipedia/BrocardProblem.lean, no duplicate statement.  
**Difficulty:** math 9/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Set-equality encoding over N is exact: n=4,5,7 give 25, 121, 5041 = 5^2, 11^2, 71^2, and small n (0..3, 6) fail, so {n | exists m, n!+1=m^2} = {4,5,7} iff Brocard's conjecture holds. m : N loses nothing since m^2 = (-m)^2.  
**Next action:** None; recognized hard open problem. Any unconditional resolution needs a breakthrough.

## `erdos_40` — Vacuously true / accidentally weakened (cat 4)

**File:** `FormalConjectures/ErdosProblems/40.lean:54`  
**Secondary category:** 9 (Major open problem / currently infeasible)  
**Statement:** For which functions g with g(N) -> infinity does |A cap [1,N]| >> sqrt(N)/g(N) force A+A to represent some integer infinitely often (limsup of the representation function = infinity)?  
**Source:** https://www.erdosproblems.com/40 ($500)  
**Statement matches intent:** no — The open-ended 'for what functions g?' question is encoded as 'Erdos40ForSet answer(sorry)', i.e. exhibit ANY set G of functions for which the implication holds. G := emptyset satisfies Erdos40ForSet vacuously (fun g hg => absurd hg (Set.not_mem_empty g)), as does any set of non-divergent functions. Nothing in the statement demands nontriviality or maximality, so the formal theorem is a one-liner that answers a different (empty) question.  
**Known status:** Intended problem is a $500 Erdos problem, open (site state open today); establishing it for even one g -> infinity would imply a positive answer to the Erdos-Turan-type Problem 28 (the in-file implication erdos_40.variants.implies_erdos_28 is fully proved). No internal PR/campaign work on the main statement.  
**Difficulty:** math 9/10, Lean 1/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Erdos40ForSet G := forall g in G, Tendsto g atTop atTop -> Erdos40For g; membership in the empty set is absurd, so the goal closes vacuously. The answer() elaborator places no semantic restriction on the supplied set.  
**Flags:** answer()-encoding trivializable by G = empty set (major semantic mismatch); open-ended 'characterize the class' question fundamentally hard to capture with answer()  
**Next action:** Report the trivialization upstream: the encoding needs a nontriviality constraint (e.g. require some divergent g in G, or state it for a specific g). As stated, 'exact fun g hg => absurd hg (Set.not_mem_empty g)' with answer := emptyset would close it.

## `erdos_400.parts.i` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/400.lean:41`  
**Statement:** With g_k(n) the max of (a_1+...+a_k) - n over a_1!...a_k! | n!, decide whether sum_{n<=x} g_k(n) ~ c_k x log x for every k>=2 and some constant c_k.  
**Source:** https://www.erdosproblems.com/400; Erdos-Graham 1980  
**Statement matches intent:** yes  
**Known status:** Open per erdosproblems.com (2026-07-26). No internal work found.  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** none · **Confidence:** high  
**Evidence:** g's N-subtraction truncation is harmless: the witness a=(n,1,0,...) puts 1 in the set (proved in-file in g_pos), so sSup equals the true max excess; the set is bounded (also proved in-file), so sSup is well-defined. 'exists c : R' without positivity is harmless: g_k(n) >= 1 forces sum >= x, ruling out c <= 0 in an IsEquivalent. Quantifier order (c depends on k, before nothing else) is correct.  
**Flags:** allows a_i = 0 (0! = 1), which cannot change the max since replacing 0s by 1s only increases the sum  
**Next action:** Leave open.

## `erdos_400.parts.ii` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/400.lean:52`  
**Statement:** Decide whether for every k>=2 there is c_k such that for almost all n <= x, g_k(n) = c_k log x + o(log x) (density-1 concentration).  
**Source:** https://www.erdosproblems.com/400; Erdos-Graham 1980  
**Statement matches intent:** yes  
**Known status:** Open per erdosproblems.com. No internal work found.  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Encoding as exists c, forall eps>0, density of {n <= x : |g_k(n) - c log x| <= eps log x} -> 1 is a standard and faithful reading of 'almost all n < x'; c is fixed before eps, and the comparison uses log x (endpoint), matching the original.  
**Next action:** Leave open.

## `erdos_406` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/406.lean:31`  
**Statement:** Decide whether only finitely many powers of 2 have ternary expansion using only digits 0 and 1 (Erdos: conjecturally just 1, 4, 256).  
**Source:** https://www.erdosproblems.com/406; Erdos 1979  
**Statement matches intent:** yes  
**Known status:** Well-known open problem, related to x2/x3 rigidity questions; Lagarias studied the 3-adic structure but finiteness is wide open. erdosproblems.com state open today. Internal duplicate check: ErdosProblems/125.lean uses the digit-{0,1} set for a different question; no duplicate of this statement.  
**Difficulty:** math 9/10, Lean 9/10 · **Compute:** none · **Confidence:** high  
**Evidence:** List-subset 'Nat.digits 3 n <= [0,1]' correctly says every ternary digit is 0 or 1; n.isPowerOfTwo includes 1 = 2^0 (digits [1]), matching the known members 1, 4, 256. Finiteness encoding is faithful.  
**Next action:** None; genuinely open with no known attack beyond heuristics and Lagarias-style partial structure results.

## `erdos_406.variants.one_two` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/406.lean:39`  
**Statement:** 2^15 = 32768 is the largest power of 2 whose ternary expansion uses only digits 1 and 2 (i.e. omits digit 0).  
**Source:** https://www.erdosproblems.com/406 (remark)  
**Statement matches intent:** yes  
**Known status:** Open; based on numerical observation ('seems to be the largest'). The membership half is a finite check: 32768 = 1122221122_3, all digits in {1,2}.  
**Difficulty:** math 9/10, Lean 9/10 · **Compute:** small · **Confidence:** high  
**Evidence:** Verified by hand: 32768 = 19683+6561+2*2187+2*729+2*243+2*81+27+9+2*3+2, digits (msd to lsd) 1,1,2,2,2,2,1,1,2,2. IsGreatest correctly packages 'member and upper bound'. No degenerate members: digits of 0 is [] but 0 is not a power of two.  
**Flags:** asserts a heuristic observation as a conjecture (IsGreatest), standard for this repo  
**Next action:** The mem half (2^15 in the set) is decidable/by decide; the upper-bound half is the open content. Could split into a solved membership lemma plus the open bound.

## `erdos_409.parts.i` — Vacuously true / accidentally weakened (cat 4)

**File:** `FormalConjectures/ErdosProblems/409.lean:36`  
**Secondary category:** 8 (Deep but approachable research problem)  
**Statement:** For each n > 0, give the least number of iterations of n -> phi(n)+1 needed to reach a prime (IsLeast of the iteration-count set equals answer(sorry)).  
**Source:** https://www.erdosproblems.com/409; OEIS A039651  
**Statement matches intent:** suspect — answer(sorry) elaborates in a context containing n, so answer := sInf {i | Nat.Prime ((phi . + 1)^[i] n)} closes the theorem: the set is nonempty by the fully-proved in-file termination theorem, and IsLeast S (sInf S) follows from Nat.sInf_mem / Nat.sInf_le. This definitional self-answer resolves the formal statement without answering the intended 'how many iterations?' question, for which no closed form or asymptotic is known.  
**Known status:** Intended question open (erdosproblems.com open today). Termination itself is proved in-file (erdos_409.variants.termination, sorry-free).  
**Difficulty:** math 8/10, Lean 2/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Answer elaborator (Util/Answer.lean) elaborates the term in the local context with no semantic guard; AnswerLinter only warns about binders before 'answer(sorry) <->' iff-forms, not IsLeast forms.  
**Flags:** answer()-encoding admits definitional self-answer sInf S; linter does not catch parametrized non-iff answer forms  
**Next action:** Flag upstream that the encoding admits the sInf non-answer; a faithful version should demand a closed form or asymptotic with a nontriviality criterion (as the file's own note admits for the asymptotic variants).

## `erdos_409.parts.i.isBigO` — Vacuously true / accidentally weakened (cat 4)

**File:** `FormalConjectures/ErdosProblems/409.lean:86`  
**Secondary category:** 8 (Deep but approachable research problem)  
**Statement:** Find (the simplest) g with c(n) = O(g(n)) for the phi(n)+1 iteration count c.  
**Source:** https://www.erdosproblems.com/409  
**Statement matches intent:** suspect — answer := fun n => (c n : R) closes it by isBigO_refl; 'simplest g' is prose-only and not enforced by the statement.  
**Known status:** Intended sharp upper bound open.  
**Difficulty:** math 8/10, Lean 1/10 · **Compute:** none · **Confidence:** high  
**Evidence:** IsBigO is reflexive; hypothesis h unused. File note acknowledges the loophole.  
**Flags:** acknowledged trivializable answer()-encoding (isBigO_refl)  
**Next action:** Same as isTheta variant: accept as design-acknowledged placeholder or add a nontriviality spec.

## `erdos_409.parts.i.isLittleO` — Vacuously true / accidentally weakened (cat 4)

**File:** `FormalConjectures/ErdosProblems/409.lean:96`  
**Secondary category:** 8 (Deep but approachable research problem)  
**Statement:** Find (the simplest) g with c(n) = o(g(n)) for the phi(n)+1 iteration count c.  
**Source:** https://www.erdosproblems.com/409  
**Statement matches intent:** suspect — answer := fun n => ((n : R) + 1) * (c n + 1) closes it in a few lines: c n <= eps*(n+1)*(c n + 1) once eps*(n+1) >= 1, so the little-o holds regardless of what c is. No nontriviality is enforced.  
**Known status:** Intended sharp o-bound open.  
**Difficulty:** math 8/10, Lean 2/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Elementary eventual inequality; hypothesis h again unused. File note acknowledges trivial solutions exist.  
**Flags:** acknowledged trivializable answer()-encoding (inflate by a divergent factor)  
**Next action:** Same as the other asymptotic variants.

## `erdos_409.parts.i.isTheta` — Vacuously true / accidentally weakened (cat 4)

**File:** `FormalConjectures/ErdosProblems/409.lean:76`  
**Secondary category:** 8 (Deep but approachable research problem)  
**Statement:** With c(n) the least iteration count of n -> phi(n)+1 to reach a prime, determine Theta(c(n)).  
**Source:** https://www.erdosproblems.com/409  
**Statement matches intent:** suspect — c is a local hypothesis variable, so answer := fun n => (c n : R) closes the goal by Asymptotics.isTheta_refl (well, IsBigO.refl in both directions). The file's own formalisation note concedes that 'trivial or sub-optimal solutions will therefore exist' and appeals to human judgment of non-triviality.  
**Known status:** Intended asymptotic behavior of A039651-type iteration counts is open.  
**Difficulty:** math 8/10, Lean 1/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Reflexivity of IsTheta on (fun n => (c n : R)) requires no use of h at all; consistent with batch-13 treatment of the identical pattern in 357.lean.  
**Flags:** acknowledged trivializable answer()-encoding (isTheta_refl)  
**Next action:** Acknowledge as design-accepted loophole; a real contribution would prove nontrivial bounds (e.g. c(n) << log n type results), which is research-level.

## `erdos_409.parts.ii` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/409.lean:105`  
**Statement:** Decide whether some prime is reached under iteration of n -> phi(n)+1 by infinitely many starting values n.  
**Source:** https://www.erdosproblems.com/409  
**Statement matches intent:** yes  
**Known status:** Open per erdosproblems.com. Primes are fixed points (phi(p)+1 = p), so the iteration partitions N>=1 into basins; whether some basin is infinite is the open question. No internal work found.  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Encoding 'exists prime p with {n | exists i, iterate reaches p} infinite' is faithful; since primes are fixed points, 'reaches p at some i' = 'terminates at p'.  
**Next action:** Leave open; small-case basin computation (A039651) could inform but not settle it.

## `erdos_409.parts.iii` — Vacuously true / accidentally weakened (cat 4)

**File:** `FormalConjectures/ErdosProblems/409.lean:113`  
**Secondary category:** 8 (Deep but approachable research problem)  
**Statement:** For a fixed prime p, determine the natural density of the set of n whose phi(n)+1 iteration reaches p.  
**Source:** https://www.erdosproblems.com/409  
**Statement matches intent:** no — The goal is 'alpha = answer(sorry)' with alpha itself a local hypothesis variable (the assumed density). answer := alpha closes the theorem by rfl, using nothing. Additionally, the statement presupposes the density exists (hypothesis hA), though existence is itself part of the open question, so even the intended reading is conditional/weakened.  
**Known status:** Intended density question open (erdosproblems.com open).  
**Difficulty:** math 8/10, Lean 1/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Answer elaborator uses the local context; 'exact rfl' after answer := alpha. Worst trivialization instance in this batch.  
**Flags:** answer()-encoding trivialized by in-scope witness alpha (rfl); density existence assumed rather than asserted  
**Next action:** Report upstream: answer must be stated as a function of p only (move alpha out of scope, e.g. 'HasDensity (answer p)'), and existence of the density should be part of the claim.

## `erdos_409.variants.sigma` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/409.lean:124`  
**Statement:** For each n > 1, give the least number of iterations of n -> sigma(n)-1 needed to reach a prime.  
**Source:** https://www.erdosproblems.com/409; OEIS A229487  
**Statement matches intent:** suspect — As with parts.i, answer := sInf S is available since n is in scope; but here nonemptiness of S (termination of the sigma-1 iteration) is itself open, so the formal statement is essentially equivalent to sigma_termination: provable via the sInf answer if termination holds, and false for every answer if some n > 1 never reaches a prime.  
**Known status:** Open: reduces to the open termination question (see sigma_termination). erdosproblems.com state open.  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** none · **Confidence:** high  
**Evidence:** sigma(n)-1: N-subtraction safe (sigma >= 1); primes are fixed points (sigma(p)-1 = p); composites strictly increase, so termination is genuinely unclear, exactly as the file's note says.  
**Flags:** answer()-encoding admits sInf self-answer, collapsing content to termination; statement false (for all answers) if termination fails for some n  
**Next action:** Treat jointly with sigma_termination; the extra IsLeast/answer layer adds nothing once the sInf loophole is noted.

## `erdos_409.variants.sigma_isBigO` — Vacuously true / accidentally weakened (cat 4)

**File:** `FormalConjectures/ErdosProblems/409.lean:153`  
**Secondary category:** 8 (Deep but approachable research problem)  
**Statement:** Find g with c(n) = O(g(n)) for the sigma(n)-1 iteration count c.  
**Source:** https://www.erdosproblems.com/409  
**Statement matches intent:** suspect — answer := fun n => (c n : R) via isBigO_refl; also vacuous if termination fails.  
**Known status:** Intended bound open.  
**Difficulty:** math 8/10, Lean 1/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Reflexivity; h unused.  
**Flags:** acknowledged trivializable answer()-encoding; vacuous if sigma termination fails  
**Next action:** Design-acknowledged placeholder.

## `erdos_409.variants.sigma_isLittleO` — Vacuously true / accidentally weakened (cat 4)

**File:** `FormalConjectures/ErdosProblems/409.lean:163`  
**Secondary category:** 8 (Deep but approachable research problem)  
**Statement:** Find g with c(n) = o(g(n)) for the sigma(n)-1 iteration count c.  
**Source:** https://www.erdosproblems.com/409  
**Statement matches intent:** suspect — answer := fun n => ((n : R) + 1) * (c n + 1) closes it (eps*(n+1) >= 1 eventually); also vacuous if termination fails.  
**Known status:** Intended bound open.  
**Difficulty:** math 8/10, Lean 2/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Elementary eventual inequality; h unused.  
**Flags:** acknowledged trivializable answer()-encoding; vacuous if sigma termination fails  
**Next action:** Design-acknowledged placeholder.

## `erdos_409.variants.sigma_isTheta` — Vacuously true / accidentally weakened (cat 4)

**File:** `FormalConjectures/ErdosProblems/409.lean:143`  
**Secondary category:** 8 (Deep but approachable research problem)  
**Statement:** Determine Theta of the least iteration count c(n) of n -> sigma(n)-1 to reach a prime.  
**Source:** https://www.erdosproblems.com/409  
**Statement matches intent:** suspect — answer := fun n => (c n : R) closes it by IsTheta reflexivity without using h. Moreover, if sigma-termination fails, h is unsatisfiable and the theorem is vacuous for every answer — a second independent weakness.  
**Known status:** Intended asymptotics open (and conditional on open termination).  
**Difficulty:** math 8/10, Lean 1/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Same reflexivity trivialization as the phi variants; file note acknowledges it.  
**Flags:** acknowledged trivializable answer()-encoding; vacuous if sigma termination fails (hypothesis h unsatisfiable)  
**Next action:** Design-acknowledged placeholder; treat as spec-weak.

## `erdos_409.variants.sigma_prime_termination` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/409.lean:172`  
**Statement:** Decide whether iterates of n -> sigma(n)-1 always reach a prime (for every n > 1).  
**Source:** https://www.erdosproblems.com/409  
**Statement matches intent:** yes  
**Known status:** Open; exact decision-form duplicate of sigma_termination in the same file.  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** none · **Confidence:** high  
**Evidence:** answer(sorry) <-> forall n > 1, exists i, Prime; RHS identical to sigma_termination's statement.  
**Flags:** internal duplication with sigma_termination (same file, lines 133 vs 173)  
**Next action:** Deduplicate with sigma_termination upstream (one bare form, one answer form of the identical proposition); mathematically leave open.

## `erdos_409.variants.sigma_termination` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/409.lean:132`  
**Statement:** Does iterating n -> sigma(n)-1 from any n > 1 always reach a prime?  
**Source:** https://www.erdosproblems.com/409; OEIS A039654/A229487  
**Statement matches intent:** yes  
**Known status:** Open. Heuristically true (sigma(n)-1 is prime with probability ~1/log n along the strictly increasing orbit, and the harmonic sum diverges) but no proof known; unlike the phi+1 map there is no monotone-decreasing argument. erdosproblems.com state open.  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Direct existential encoding with correct domain n > 1; i = 0 correctly counts prime starting points.  
**Flags:** file marks this 'research open' even though phrased as a bare theorem; content duplicated by sigma_prime_termination in decision form  
**Next action:** Leave open; extending OEIS-style verification for small n is possible but cannot settle it.

## `erdos_41` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/41.lean:43`  
**Statement:** If A is an infinite set of naturals whose triple sums are all distinct (B_3-type condition), is liminf |A cap [1,N]| / N^(1/3) = 0?  
**Source:** https://www.erdosproblems.com/41 ($500)  
**Statement matches intent:** suspect — NtupleCondition quantifies over 3-element Finsets, so only sums of three DISTINCT elements must be distinct; the standard B_3 condition also forbids coincidences with repeated elements (e.g. a+a+b = c+d+e with {a,a,b} != {c,d,e} as multisets). The formal hypothesis is therefore weaker, and the theorem correspondingly stronger than the published conjecture; whether the two versions are equivalent (up to bounded modification of A) is not obvious, so the truth value could in principle differ.  
**Known status:** Open, $500 prize (erdosproblems.com open today). Erdos proved the Sidon (pairwise) analogue, formalized in-file as the solved variant. No internal work found.  
**Difficulty:** math 9/10, Lean 9/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** Definition audit: forall I J : Finset, (subset A and card = n and equal sums) -> I = J; the conjunction-into-implication structure is correct, and Set.Icc/ncard/liminf typing is sound (real rpow 1/3 correctly ascribed).  
**Flags:** Finset (distinct-element) vs multiset triple-sum condition: hypothesis weaker than standard B_3, statement stronger than intended  
**Next action:** Suggest upstream switching NtupleCondition to a multiset/tuple formulation (sorted tuples a1<=a2<=a3) to match B_3[1]; mathematically leave open.

## `erdos_410` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/410.lean:39`  
**Statement:** For iterated sum-of-divisors sigma_k(n), decide whether sigma_k(n)^(1/k) tends to infinity for every n > 1.  
**Source:** https://www.erdosproblems.com/410; Erdos-Granville-Pomerance-Spiro, 'On the normal behavior of the iterates of some arithmetical functions', Analytic Number Theory (1990), problem (iii); OEIS A007497  
**Statement matches intent:** yes  
**Known status:** Open per erdosproblems.com (2026-07-26). EGPS 1990 posed it; growth of sigma-iterates remains poorly understood. No internal work found.  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Decision encoding faithful: forall n > 1 correctly excludes the fixed points n = 0, 1; the k = 0 junk exponent 1/0 = 0 (value 1) is irrelevant in the atTop filter over k.  
**Next action:** Leave open.

## `erdos_412` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/412.lean:35`  
**Statement:** Iterating the sum-of-divisors function sigma, do the trajectories of any two starting values m,n >= 2 eventually meet, i.e. sigma_i(m) = sigma_j(n) for some i,j?  
**Source:** https://www.erdosproblems.com/412  
**Statement matches intent:** yes  
**Known status:** Open per erdosproblems.com (state 'open', 2026-07-26). No internal PR/campaign touches it.  
**Difficulty:** math 9/10, Lean 9/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Formalization faithful: allowing i=j=0 is equivalent to i,j>=1 since applying sigma once to both sides preserves any coincidence. sigma 1 is Mathlib's sum-of-divisors; m,n >= 2 matches source.  
**Next action:** Leave open; no viable proof strategy known for trajectory-merging problems of iterated sigma.

## `erdos_413.parts.i` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/413.lean:43`  
**Statement:** Are there infinitely many n that are 'barriers' for omega, i.e. m + omega(m) <= n for all m < n?  
**Source:** https://www.erdosproblems.com/413  
**Statement matches intent:** yes  
**Known status:** Open per erdosproblems.com. Erdos proved the analogue for the product-of-exponents function (formalized as a solved variant in the same file); Selfridge computed Omega-barriers below 10^5.  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** none · **Confidence:** high  
**Evidence:** IsBarrier def matches source exactly (all m < n, including m=0,1 where omega=0, which is harmless). Real-valued comparison avoids N-subtraction issues.  
**Next action:** Leave open; computational exploration of barriers is possible but a proof of infinitude is out of reach.

## `erdos_413.parts.ii` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/413.lean:71`  
**Statement:** Is there some eps > 0 such that infinitely many n satisfy m + eps*omega(m) <= n for all m < n (relaxed eps-barriers for omega)?  
**Source:** https://www.erdosproblems.com/413  
**Statement matches intent:** yes  
**Known status:** Open per erdosproblems.com (this is the relaxed variant Erdos posed).  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Existential eps scoped correctly outside the infinitude claim; barrier condition with eps-multiplied omega matches the source. Variable shadowing (fun n => eps * omega n) is cosmetic only.  
**Next action:** Leave open; requires control of omega on all of n-1, n-2, ... simultaneously, related to unproven equidistribution of smooth-omega values near n.

## `erdos_413.variants.bigOmega` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/413.lean:59`  
**Statement:** Are there infinitely many barriers for Omega (number of prime factors with multiplicity), i.e. n with m + Omega(m) <= n for all m < n?  
**Source:** https://www.erdosproblems.com/413  
**Statement matches intent:** yes  
**Known status:** Open per erdosproblems.com. Selfridge's computation (largest Omega-barrier below 10^5 is 99840) is recorded as a solved variant in the file.  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Same faithful IsBarrier definition applied to Omega. Statement matches Erdos's belief that infinitely many Omega-barriers exist.  
**Next action:** Leave open.

## `erdos_414` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/414.lean:35`  
**Statement:** For h(n) = n + tau(n) (tau = number of divisors), do the h-iterate trajectories of any two positive starting values m,n eventually meet?  
**Source:** https://www.erdosproblems.com/414  
**Statement matches intent:** yes  
**Known status:** Open per erdosproblems.com.  
**Difficulty:** math 9/10, Lean 9/10 · **Compute:** none · **Confidence:** high  
**Evidence:** h(n) = n + n.divisors.card is correct for n >= 1; m,n > 0 hypotheses exclude the degenerate fixed point h(0)=0. Allowing i=j=0 is equivalent (apply h to both sides).  
**Next action:** Leave open; same trajectory-merging obstruction as problem 412.

## `erdos_416.parts.i` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/416.lean:37`  
**Statement:** With V(x) the number of totient values <= x, does V(2x)/V(x) tend to 2?  
**Source:** https://www.erdosproblems.com/416  
**Statement matches intent:** yes  
**Known status:** Open per erdosproblems.com. Ford's 'The distribution of totients' (1998) determines the order of V(x) (solved variants in the file) but the limit of V(2x)/V(x) remains open.  
**Difficulty:** math 9/10, Lean 9/10 · **Compute:** none · **Confidence:** high  
**Evidence:** V correctly counts n in [1, floor(x)] in the image of totient (includes 1 = phi(1), correct). Statement is asserted positively without answer(): provable only if the conjectured limit 2 is correct, which is the repo convention for yes-conjectured open questions.  
**Flags:** stated positively (no answer elaborator): unprovable if the true answer is 'no'  
**Next action:** Leave open; any progress would come from refining Ford's machinery.

## `erdos_416.parts.ii` — Trivially or easily solvable (cat 2)

**File:** `FormalConjectures/ErdosProblems/416.lean:46`  
**Secondary category:** 4 (Vacuously true / accidentally weakened)  
**Statement:** Is there an asymptotic formula for V(x), the count of totient values up to x? Encoded as: exhibit f with V(x)/f(x) -> 1.  
**Source:** https://www.erdosproblems.com/416  
**Statement matches intent:** no — answer() encoding trivializes the question: nothing constrains f to be a 'formula', so f := V itself is a legal witness.  
**Known status:** Formal statement trivially closable; the intended question (an explicit asymptotic for V, beyond Ford's Theta-result) is genuinely open/ill-posed as a formal statement.  
**Difficulty:** math 9/10, Lean 2/10 · **Compute:** none · **Confidence:** high  
**Evidence:** let f := answer(sorry); Tendsto (V x / f x) atTop (nhds 1). Witness f = V: V x / V x = 1 for all x >= 1 since V x >= 1 there; tendsto_const_nhds + Tendsto.congr' closes it. No condition excludes this degenerate witness.  
**Flags:** answer-encoding admits self-witness f = V (major semantic mismatch); intended 'asymptotic formula' is a meta-question not capturable this way  
**Next action:** Close with answer f := V: for x >= 1, V x >= 1 (1 = phi(1) is counted), so V x / V x is eventually 1 and Tendsto follows by congruence with the constant 1. Alternatively flag upstream for a better encoding.

## `erdos_417.parts.i` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/417.lean:40`  
**Statement:** With V'(x) = #distinct values phi(m) for m <= x and V(x) = #totient values <= x, does lim V(x)/V'(x) exist? (Formalized as existence of lim of the inverse ratio V'/V.)  
**Source:** https://www.erdosproblems.com/417 ; [Er98]  
**Statement matches intent:** yes  
**Known status:** Open per erdosproblems.com.  
**Difficulty:** math 9/10, Lean 9/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** Numerator = ncard of totient image of {1<=m<=x} (= V'), denominator = ncard of totient values <= x (= V, overcounting by 1 because 0 = phi(0) is in Set.range totient - asymptotically irrelevant). Ratio lies in [0,1] so a finite-limit encoding is well-posed.  
**Flags:** denominator includes the junk value 0 via phi(0) (off by 1, harmless); inverse-ratio encoding differs from source if V/V' is unbounded  
**Next action:** Leave open; connected to Ford's totient distribution machinery.

## `erdos_417.parts.ii` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/417.lean:51`  
**Statement:** Is lim V(x)/V'(x) strictly greater than 1? (Encoded: the inverse ratio V'/V tends to some L < 1.)  
**Source:** https://www.erdosproblems.com/417 ; [Er98]  
**Statement matches intent:** yes  
**Known status:** Open per erdosproblems.com.  
**Difficulty:** math 9/10, Lean 9/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** Same V', V encodings as parts.i; existential L bundled with L < 1 matches the strict inequality question given a limit exists.  
**Flags:** same minor 0-value overcount as parts.i  
**Next action:** Leave open.

## `erdos_418.variants.density` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/418.lean:108`  
**Statement:** Does the set of non-cototients (integers not of the form n - phi(n)) have positive density?  
**Source:** https://www.erdosproblems.com/418  
**Statement matches intent:** yes  
**Known status:** The density question is open (file docstring and erdosproblems.com agree). The main problem 418 (infinitude of non-cototients) is solved (Browkin-Schinzel 1995) and already carries a Lean formal proof link (Alexeev/Aristotle) - that solves only the main statement, not this variant. Site state 'proved (Lean)' refers to the main problem. The sigma-analogue (nonaliquots, Erdos 1973) is known and is a separate solved variant in the file.  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Encoding 'exists S with genuine density > 0, S subseteq complement' is the repo's standard positive-lower-density encoding and is equivalent to the complement having positive lower density (thin any set of positive lower density to one with an exact density). Complement is over N with junk values n=0,1 contributing 0 - harmless.  
**Next action:** Leave open; a proof would likely need to show even numbers avoid p+q-1-type representations with positive density, related to Goldbach-type questions.

## `erdos_42.variants.constructive` — Already solved externally (cat 1)

**File:** `FormalConjectures/ErdosProblems/42.lean:54`  
**Secondary category:** 2 (Trivially or easily solvable)  
**Statement:** Skolemized form of Erdos 42: there is a function f such that for all M >= 1 and N >= f(M), every maximal Sidon set A in [1,N] admits a Sidon set B in [N+1,N]...[1,N] of size exactly M with (A-A) cap (B-B) = {0}.  
**Source:** https://www.erdosproblems.com/42 ; formal proof of main statement: https://github.com/Shashi456/erdos-formalizations/blob/main/Erdos/P42/CompactCayley/Proof.lean  
**Statement matches intent:** yes  
**Known status:** Main problem solved: erdosproblems.com state 'solved (Lean)' (2026-07-26); repo's erdos_42 is already answer(True), category research solved, with a formal_proof attribute linking a public Lean proof (attributed to GPT 5.5 Pro, prompted by Sandhu). No internal PR targets the variant.  
**Difficulty:** math 2/10, Lean 5/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** erdos_42 RHS is 'forall M >= 1, eventually-atTop N, P M N'; over N atTop-eventually is 'exists N0, forall N >= N0', so choice yields exactly the variant's f. Conversely trivial. Hence the variant's answer is True given the solved main problem.  
**Flags:** external Lean proof statement match not verifiable offline - check during port; variant is redundant with main statement (classical skolemization)  
**Next action:** Port/import the external Lean proof of erdos_42, set answer(True), and derive f from the atTop-eventually threshold via Classical.choice (f M := witness N0 for M >= 1, arbitrary for M = 0); verify the external proof matches the repo statement during the port.

## `erdos_421` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/421.lean:32`  
**Statement:** Is there a strictly increasing sequence 1 <= d_1 < d_2 < ... of density 1 such that all interval products prod_{u<=i<=v} d_i are pairwise distinct?  
**Source:** https://www.erdosproblems.com/421  
**Statement matches intent:** yes  
**Known status:** Open per erdosproblems.com.  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** none · **Confidence:** high  
**Evidence:** StrictMono + 1 <= d 0 + HasDensity (range d) 1 + InjOn of interval products over {(u,v) : u <= v} matches the source (HasDensity is a genuine limit density). Index base 0 vs 1 is immaterial.  
**Next action:** Leave open.

## `erdos_422` — Cannot classify without correction/clarification (cat 10)

**File:** `FormalConjectures/ErdosProblems/422.lean:46`  
**Statement:** For Hofstadter-style f with f(1)=f(2)=1, f(n)=f(n-f(n-1))+f(n-f(n-2)): does f miss infinitely many integers?  
**Source:** https://www.erdosproblems.com/422  
**Statement matches intent:** no — f is declared with 'partial def', which in Lean 4 produces an opaque constant with NO equational lemmas: the logic cannot prove f 1 = 1 or any value of f. The formal statement is about an arbitrary unspecified function of type PNat -> PNat.  
**Known status:** Intended problem (about Hofstadter's Q-like sequence) open per erdosproblems.com; the formal statement is malformed and independent of Lean's axioms, so neither answer(True) nor answer(False) can be proven.  
**Difficulty:** math 9/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Lean's partial def compiles the body only for runtime; logically f is opaque (justified by Inhabited), so Set.Infinite {n | forall x, f x <> n} has no determined truth value. Additionally the intended recurrence's well-definedness is itself open (docstring admits this), so a total-function formalization cannot be faithful.  
**Flags:** partial def = opaque constant, no equation lemmas: statement independent of axioms; PNat truncated subtraction in the recursion body; well-definedness of the intended f is itself open  
**Next action:** Redefine f before any proof attempt: e.g. an Option-valued/fuel-based total function or an inductively defined graph relation capturing the (possibly partial) recurrence; note PNat subtraction also truncates at 1, which must be handled explicitly. Flag upstream.

## `erdos_422.variants.eventually_const` — Cannot classify without correction/clarification (cat 10)

**File:** `FormalConjectures/ErdosProblems/422.lean:68`  
**Statement:** Does the Hofstadter-style f become eventually constant?  
**Source:** https://www.erdosproblems.com/422  
**Statement matches intent:** no — Same partial-def opacity defect: EventuallyConst f atTop for an opaque constant f is independent of the axioms.  
**Known status:** Intended problem open; formal statement malformed.  
**Difficulty:** math 9/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** No equations for f exist in the logic; neither EventuallyConst nor its negation is provable.  
**Flags:** partial def = opaque constant, no equation lemmas  
**Next action:** Same fix as erdos_422: redefine f, then re-state.

## `erdos_422.variants.growth_rate` — Trivially or easily solvable (cat 2)

**File:** `FormalConjectures/ErdosProblems/422.lean:60`  
**Secondary category:** 4 (Vacuously true / accidentally weakened)  
**Statement:** How fast does the Hofstadter-style f grow? Encoded as: f = O(g) for some answer function g.  
**Source:** https://www.erdosproblems.com/422  
**Statement matches intent:** no — Double defect: (a) f is opaque (partial def), (b) the answer() encoding admits the self-witness g := fun n => (f n : R), which closes the goal by isBigO_refl regardless of what f is.  
**Known status:** Formally trivially closable; the intended growth question for the real Hofstadter-like sequence is open.  
**Difficulty:** math 9/10, Lean 1/10 · **Compute:** none · **Confidence:** high  
**Evidence:** (fun n => (f n : R)) =O[atTop] (fun n => (f n : R)) is isBigO_refl; nothing in the statement excludes this witness, and f's opacity is irrelevant to it.  
**Flags:** answer-encoding admits self-witness (major semantic mismatch); partial def f opaque  
**Next action:** Either close formally with answer g := (fun n => (f n : R)) via Asymptotics.isBigO_refl, or (better) flag upstream: fix the definition of f and use an encoding that forces a nontrivial comparison function.

## `erdos_422.variants.surjective` — Cannot classify without correction/clarification (cat 10)

**File:** `FormalConjectures/ErdosProblems/422.lean:53`  
**Statement:** Is the Hofstadter-style f surjective?  
**Source:** https://www.erdosproblems.com/422  
**Statement matches intent:** no — Same defect: f is a partial-def opaque constant with no defining equations; Function.Surjective f is independent of the axioms.  
**Known status:** Intended problem open; formal statement malformed (unresolvable for either answer).  
**Difficulty:** math 9/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** No equational lemmas exist for partial def f; surjectivity of an opaque PNat -> PNat constant cannot be decided.  
**Flags:** partial def = opaque constant, no equation lemmas  
**Next action:** Same fix as erdos_422: redefine f, then re-state.

## `erdos_424` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/424.lean:54`  
**Statement:** Start with {2,3} and repeatedly adjoin all values x*y - 1 for distinct members x,y. Does the set of integers that eventually appear have positive density?  
**Source:** https://www.erdosproblems.com/424 ; https://oeis.org/A5244 ; Ben Green's Open Problems #63  
**Statement matches intent:** yes  
**Known status:** Open per erdosproblems.com; also Ben Green's open problem 63 (GreensOpenProblems/63.lean is only a pointer file to this canonical formalization, no duplicate decl).  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Generation via distinct values x <> y matches distinct indices in the source (all appearing values are distinct); all elements >= 2 so x*y - 1 never truncates; generatedSet = union of the finitely-iterated closures; HasPosDensity is a genuine limit density (standard repo encoding).  
**Next action:** Leave open; numerical exploration of A005244's density is possible but no proof route is known.

## `erdos_428` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/428.lean:39`  
**Statement:** Is there a set A of positive relative lower density among the primes such that for infinitely many n, n - a is prime for every a in A with 0 < a < n?  
**Source:** https://www.erdosproblems.com/428  
**Statement matches intent:** yes  
**Known status:** Open per erdosproblems.com.  
**Difficulty:** math 9/10, Lean 9/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** Frequently-atTop correctly encodes 'infinitely many n'; n - a is guarded by a < n so no truncation issue; liminf of |A cap [1,n]|/pi(n) > 0 matches (junk division at n = 0,1 does not affect the liminf); finite A automatically fails the density condition, so no degenerate witness.  
**Next action:** Leave open; related to prime tuple/Goldbach-type barriers.

## `erdos_44` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/44.lean:44`  
**Statement:** Can every finite Sidon set A in [1,N] be extended by B in [N+1,M] (for some M) so that A cup B is Sidon in [1,M] of size at least (1-eps)sqrt(M), for every eps > 0?  
**Source:** https://www.erdosproblems.com/44  
**Statement matches intent:** yes  
**Known status:** Open per erdosproblems.com.  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Quantifier order (forall N, A, eps; exists M > N, B) matches the source's M = M(eps) existential; union card and (1-eps)*sqrt(M) bound faithful; disjointness of A and B ranges automatic.  
**Next action:** Leave open; the difficulty is completing an arbitrary (possibly adversarial) Sidon set to near-maximal density.

## `erdos_44.variants.empty_start` — Solved mathematically, not yet formalized (cat 5)

**File:** `FormalConjectures/ErdosProblems/44.lean:53`  
**Statement:** For every eps > 0 and all sufficiently large M, there is a Sidon set in [1,M] of size at least (1-eps)sqrt(M).  
**Source:** Singer (1938), Erdos-Turan (1941), Chowla / Bose-Chowla (1962); see also erdosproblems.com/44 background  
**Statement matches intent:** yes  
**Known status:** This variant is a classical KNOWN theorem, not open: Singer's perfect difference sets (or the Bose-Chowla construction) give Sidon sets of size q+1 in [1, q^2+q+1] for prime powers q, and p_{k+1}/p_k -> 1 (PNT) upgrades this to (1-eps)sqrt(M) for all large M. The repo mislabels it 'research open'.  
**Difficulty:** math 4/10, Lean 8/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Standard textbook result (e.g. Halberstam-Roth, 'Sequences', Ch. II): max Sidon subset of [1,N] has size (1+o(1))sqrt(N); the lower bound is exactly this statement. answer(sorry) should be True.  
**Flags:** mislabeled research open: this variant is a solved classical theorem; formalization blocked on a Sidon construction + PNT-strength prime gaps  
**Next action:** Formalize (large effort): Bose-Chowla Sidon construction over F_{q^2} (discrete logs in the cyclic unit group, quadratic-uniqueness argument) plus prime-ratio-tends-to-1 from PNT (available in Lean via the PrimeNumberTheoremAnd project, not yet in Mathlib core); then answer(True). Effort: large.

## `erdos_445` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/ErdosProblems/445.lean:49`  
**Statement:** For every c > 1/2, is it true that for all sufficiently large primes p and every n >= 0 there are a,b in (n, n + p^c) with ab = 1 mod p?  
**Source:** https://www.erdosproblems.com/445 ; Heath-Brown [He00]  
**Statement matches intent:** yes  
**Known status:** Open per erdosproblems.com. Heilbronn (unpublished) proved it for c near 1; Heath-Brown proved all c > 3/4 via Kloosterman sums (both recorded as solved variants in the file). The range 1/2 < c <= 3/4 is open.  
**Difficulty:** math 9/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Erdos445Prop uses real rpow p^c and strict open-interval bounds, matching the source; eventual-in-p quantifier guarded by primality is faithful; the included small test example sanity-checks the Prop. State-of-the-art (c > 3/4) has stood since 2000.  
**Next action:** Leave open; going below the 3/4 exponent means beating the Weil square-root barrier for Kloosterman-type sums - a recognized hard analytic-number-theory obstruction with no known strategy.

## `erdos_454` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/454.lean:36`  
**Statement:** With f(n) = min over 0 < i < n of (p_{n+i} + p_{n-i}), is limsup_n (f(n) - 2 p_n) infinite?  
**Source:** https://www.erdosproblems.com/454 ; Pomerance [Po79]  
**Statement matches intent:** yes  
**Known status:** Open per erdosproblems.com; Pomerance's prime-number-graph paper gives limsup >= 2 (solved variant in the file).  
**Difficulty:** math 9/10, Lean 9/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Nat.nth Prime is 0-indexed - a uniform index shift immaterial for a limsup-infinite question; the infimum over the nonempty subtype {0 < i < n} is the intended minimum; truncated subtraction into N-infinity only clips negatives to 0, which cannot affect whether the limsup equals top.  
**Flags:** 0-indexed nth prime vs source's 1-indexing (harmless uniform shift); truncated subtraction clips negatives to 0 (irrelevant for limsup = top)  
**Next action:** Leave open; progress would come from quantitative convexity results for the prime sequence.

## `erdos_455` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/455.lean:32`  
**Statement:** If q_1 < q_2 < ... are primes with nondecreasing gaps (q_{n+2}-q_{n+1} >= q_{n+1}-q_n), must q_n/n^2 tend to infinity?  
**Source:** https://www.erdosproblems.com/455 ; Richter [Ri76]  
**Statement matches intent:** yes  
**Known status:** Open per erdosproblems.com; Richter proved liminf q_n/n^2 > 0.352 (solved variant in the file).  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** none · **Confidence:** high  
**Evidence:** StrictMono makes all gaps positive so N-subtraction in the convexity hypothesis never truncates; such sequences exist (greedy construction), so no vacuity; junk division at n = 0 irrelevant to Tendsto atTop.  
**Next action:** Leave open; improving Richter's method toward divergence is the identifiable avenue.

## `erdos_458` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/ErdosProblems/458.lean:37`  
**Statement:** Is lcm(1,...,p_{k+1}-1) < p_k * lcm(1,...,p_k) for every k, i.e. do the prime-power boosts inside any prime gap multiply to less than p_k?  
**Source:** https://www.erdosproblems.com/458  
**Statement matches intent:** yes  
**Known status:** Open per erdosproblems.com (state 'falsifiable': a single counterexample would settle it; none known).  
**Difficulty:** math 9/10, Lean 9/10 · **Compute:** none · **Confidence:** high  
**Evidence:** 0-indexed Nat.nth Prime makes 'forall k : N' exactly the source's 'forall k >= 1' (k=0 gives lcm(1,2)=2 < 2*2). lcm over Finset.Icc 1 n is the intended lcm(1..n); LHS correctly stops at p_{k+1}-1, capturing prime-power (not just prime) jumps of lcm in the gap.  
**Flags:** proof strength: implies a prime between consecutive prime squares (far beyond current technology)  
**Next action:** Leave open. Note the conjecture implies no prime gap (p_k, p_{k+1}) contains two prime squares q^2 < r^2 (their product qr already exceeds p_k), i.e. between consecutive squares of primes there is always a prime - Legendre-tier territory beyond even RH-conditional gap bounds. A refutation search extending known verification is possible but expected fruitless.
