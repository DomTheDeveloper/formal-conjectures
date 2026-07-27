# Audit detail — ErdosProblems

360 research-open declarations. Fields per problem: plain statement, source, category, match, status, action, difficulties, compute, confidence, evidence, flags.

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

## `erdos_1145` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/1145.lean:61`  
**Statement:** If A and B are infinite sets of naturals whose n-th elements satisfy a_n/b_n -> 1 and A+B contains all sufficiently large integers, must the representation function 1_A * 1_B be unbounded (limsup = infinity)?  
**Source:** erdosproblems.com/1145 (Erdos-Sarkozy); related to erdosproblems.com/28  
**Statement matches intent:** yes  
**Known status:** Open on erdosproblems.com (state: open, tags additive combinatorics / additive basis). No PR in the fork register touches 1145; no campaign entry; no duplicate elsewhere in FormalConjectures/. The in-file test `erdos_1145.test_implies_erdos_28` shows Erdos1145Prop implies Erdos 28, which is itself open, so this statement is at least as hard as Erdos 28.  
**Difficulty:** math 9/10, Lean 9/10 · **Compute:** none · **Confidence:** high  
**Evidence:** AdditiveCombinatorics.sumConv (FormalConjecturesForMathlib/Combinatorics/Additive/Convolution.lean:50) is the correct Cauchy-product representation count; limsup in the complete lattice ENat equals top exactly when the counts are unbounded, which is the intended reading. The implication to Erdos 28 is proved (not sorried) in the same file.  
**Flags:** 0-in-A/B convention deliberately left ambiguous by the authors; Nat.nth junk value at index 0 (harmless here)  
**Next action:** Leave open. Any serious attack must first resolve Erdos 28 (A + A = N with bounded representation function). Useful intermediate Lean work: API lemmas relating `sumConv` limsup to `Set.Finite` fibres of the addition map.

## `erdos_1146` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/ErdosProblems/1146.lean:50`  
**Statement:** Is the set of 3-smooth numbers {2^m 3^n} an essential component, i.e. does adding it strictly increase the Schnirelmann density of every set B with 0 < d_s(B) < 1?  
**Source:** erdosproblems.com/1146; Ruzsa, 'Erdos and the Integers', J. Number Theory (1999), 115-163  
**Statement matches intent:** yes  
**Known status:** Open. Ruzsa records that Erdos asked this repeatedly and that he has 'not even a plausible guess'. Known constraints (Ruzsa's lower bound |A ∩ [1,n]| ≫ (log n)^{1+c} for essential components) do not exclude the 3-smooth numbers, whose counting function is ≍ (log n)^2. No PR/campaign/duplicate in this fork.  
**Difficulty:** math 9/10, Lean 9/10 · **Compute:** none · **Confidence:** high  
**Evidence:** The definition matches the standard one (Khintchine/Linnik/Ruzsa) and the file's own docstring explains why the ∪{0} is present. Nothing degenerate: B is universally quantified with both 0 < d_s(B) and d_s(B) < 1 excluded from the trivial ends.  
**Next action:** Leave open. A Lean-tractable sub-goal would be formalizing Ruzsa's necessary density condition for essential components, or Linnik's theorem that essential components of density 0 exist.

## `erdos_1150` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/ErdosProblems/1150.lean:35`  
**Statement:** Is there c > 0 such that every degree-n Littlewood polynomial (all coefficients ±1) has sup-norm on the unit circle greater than (1+c)sqrt(n), for all large n?  
**Source:** erdosproblems.com/1150 (Erdos' flat-polynomial problem)  
**Statement matches intent:** yes  
**Known status:** Open per erdosproblems.com. Known: Parseval gives the trivial bound sqrt(n+1); Balister-Bollobas-Morris-Sahasrabudhe-Tiba (Annals 2020) constructed flat Littlewood polynomials with sup norm ≤ C sqrt(n) for an absolute C > 1, which does not touch the (1+c) lower bound. Fork PR #2 ('Prove the Parseval lower bound for Erdos 1150', merged 2026-07-20, branch agent/erdos1150-parseval-proof) supplies only the textbook variant `erdos_1150.variants.parseval_lower_bound` via FormalConjectures/ErdosProblems/Erdos1150Parseval.lean; PR #1 was an unmerged independent verification of the same lemma. Neither touches the open statement.  
**Difficulty:** math 9/10, Lean 9/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Erdos' conjecture that max|P| ≥ (1+c)sqrt(n) for Littlewood polynomials is a long-standing named open problem; the recent flat-polynomial theorem gives only upper bounds. PR register grep for '1150' returns only the Parseval-lemma PRs.  
**Flags:** merged PR #2 addresses a textbook variant only — must not be read as solving the open theorem  
**Next action:** Leave open. Do not confuse the merged Parseval PR with progress on the main statement. A meaningful next milestone would be formalizing the L4-norm / Rudin-Shapiro upper bound machinery to make the constant explicit.

## `binary_colors` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/1167.lean:75`  
**Secondary category:** 3 (False / refutable as stated)  
**Statement:** Special case of Erdos 1167 with exactly two colour classes (gamma = 2): does 2^lambda -> (kappa_0+1, kappa_1+1)^{r+1} imply lambda -> (kappa_0, kappa_1)^r?  
**Source:** erdosproblems.com/1167, two-colour specialization (repo-authored variant)  
**Statement matches intent:** suspect — Inherits the cardinal-vs-ordinal '+1' problem from `erdos_1167`: for infinite kappa_alpha the '+1' disappears entirely, so the hypothesis is weaker than in the classical two-colour stepping-up lemma and the asserted implication becomes a stronger (possibly false) claim. Also stated as a bare theorem rather than an answer()-question.  
**Known status:** Open; specialization of the open problem. Danger instance: lambda = aleph_1, kappa_0 = kappa_1 = aleph_1, r = 2. The conclusion aleph_1 -> (aleph_1)^2_2 is refutable in ZFC (Sierpinski, via 2^{aleph_0} -/-> (aleph_1)^2_2 and aleph_1 ≤ 2^{aleph_0}), so this variant is true only if 2^{aleph_1} -/-> (aleph_1)^3_2 — which Erdos-Rado does not deliver (ER gives beth_2^+ -> (aleph_1)^3_{aleph_0}) and which I could not confirm.  
**Difficulty:** math 9/10, Lean 9/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** Cardinal.add_one_of_aleph0_le makes (fun α => κ α + 1) = κ for infinite κ; the file itself relies on this identity at line 166.  
**Flags:** needs literature check (2^{aleph_1} -/-> (aleph_1)^3_2 ?); possible falsity under the cardinal-addition reading  
**Next action:** Resolve the '+1' convention first; then check the aleph_1 instance against the literature on negative relations for triples with two colours before spending proof effort.

## `erdos_1167` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/1167.lean:48`  
**Secondary category:** 3 (False / refutable as stated)  
**Statement:** Does the partition relation 2^lambda -> (kappa_alpha + 1)^{r+1} for alpha < gamma always imply lambda -> (kappa_alpha)^r? (Erdos-Hajnal-Rado 'stepping down' question.)  
**Source:** erdosproblems.com/1167; Erdos-Hajnal(-Rado) unsolved-problems-in-set-theory list  
**Statement matches intent:** suspect — Two concerns. (1) The '+1' is formalized as CARDINAL addition (the docstring says so explicitly), which makes it a no-op whenever kappa_alpha is infinite, since cardinalPartitionRel only constrains the CARDINALITY of the homogeneous set. In classical partition calculus (and in the Erdos-Rado theorem (2^kappa)^+ -> (kappa^+ + 1)^2_kappa, and in the negative stepping-up lemma of which this question is the converse) 'kappa + 1' denotes the ORDER TYPE kappa+1. Under the ordinal reading the hypothesis is strictly stronger, so the formalized statement is strictly stronger than the intended one and could be false while the original stays open. (2) The original list's side condition kappa_alpha > r is dropped; this only adds instances where the conclusion is vacuously true (a homogeneous set of size < r has no r-subsets), so it is harmless.  
**Known status:** Open on erdosproblems.com. Could not retrieve the verbatim statement: erdosproblems.com returns HTTP 403 to WebFetch and targeted web search did not surface the page text — hence 'needs literature check' on the +1 convention. No PR, campaign entry, or duplicate in this repo. Note the potentially dangerous instance lambda = kappa_alpha = aleph_1, gamma = 2, r = 2: the conclusion aleph_1 -> (aleph_1)^2_2 is a ZFC-refutable relation (Sierpinski), so under the cardinal reading the formal statement forces 2^{aleph_1} -/-> (aleph_1)^3_2, which is not obviously a theorem.  
**Difficulty:** math 9/10, Lean 9/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** cardinalPartitionRel (FormalConjecturesForMathlib/Combinatorics/SetTheory/PartitionRelation.lean:56) asks only for #H = nu i, so no order type is expressible; with cardinal addition (fun α => κ α + 1) = κ whenever κ is infinite (Cardinal.add_one_of_aleph0_le, used in the file's own counterexample proof at line 166). The negative stepping-up lemma 'lambda -/-> (kappa)^r implies 2^lambda -/-> (kappa+1)^{r+1}' is the exact contrapositive of this question and is classically stated with ORDINAL +1.  
**Flags:** needs literature check (ordinal vs cardinal '+1'); possible major semantic mismatch: formal statement strictly stronger than intended, may be refutable; dropped side condition kappa_alpha > r (benign)  
**Next action:** Before any proof attempt, confirm against erdosproblems.com/1167 (or the Erdos-Hajnal list) whether kappa_alpha + 1 is ordinal or cardinal addition; if ordinal, the ForMathlib definition must be extended to order-type-homogeneous sets and the statement rewritten. Then leave open.

## `finite_targets` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/1167.lean:64`  
**Statement:** Special case of Erdos 1167 with all targets kappa_alpha finite: does 2^lambda -> (n_alpha + 1)^{r+1} imply lambda -> (n_alpha)^r?  
**Source:** erdosproblems.com/1167, finite-target specialization (repo-authored variant)  
**Statement matches intent:** yes  
**Known status:** Open; a specialization of the open Erdos 1167. No PR, campaign entry or duplicate. Note the natural attempted counterexample (lambda = aleph_0, gamma = omega, n_alpha = 3, r = 2, conclusion aleph_0 -/-> (3)^2_omega by rainbow-colouring pairs of N) fails, because the premise 2^{aleph_0} -> (4)^3_omega is also false: from a Sierpinski pair-colouring of 2^omega with no monochromatic triangle (colour {f,g} by the least coordinate of disagreement) one builds a triple-colouring {x<y<z} |-> (d(x,y),d(y,z),d(x,z)) with no monochromatic 4-set. So no cheap refutation.  
**Difficulty:** math 9/10, Lean 9/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** Checked explicitly that the missing 'n_alpha > r' condition is harmless (H with #H < r has no r-subsets, so the conclusion is vacuously satisfiable) and that the obvious rainbow-colouring counterexample is blocked by the stepped-up Sierpinski colouring described above.  
**Flags:** stated as a theorem, not an answer()-question — presumes the answer is yes for finite targets  
**Next action:** Leave open; if attacked, start from the finite-colour case (gamma finite), where both sides follow from the infinite Ramsey theorem and the statement is provable — that would be a good first Lean milestone.

## `infinite_targets` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/1167.lean:92`  
**Secondary category:** 3 (False / refutable as stated)  
**Statement:** Special case of Erdos 1167 where all targets are infinite and bounded by lambda: does 2^lambda -> (kappa_alpha)^{r+1} imply lambda -> (kappa_alpha)^r?  
**Source:** erdosproblems.com/1167, infinite-target specialization (repo-authored variant)  
**Statement matches intent:** suspect — This variant drops '+1' entirely (correctly, under the cardinal reading), so it is a 'pure' stepping-down assertion. But that is exactly the reading that is suspect: under the classical ORDER-TYPE reading the hypothesis would be 2^lambda -> (kappa_alpha + 1)^{r+1}, which is strictly stronger. The added bound kappa_alpha ≤ lambda is genuinely needed and the file proves so (`infinite_targets_needs_bound`).  
**Known status:** Open; no PR/campaign/duplicate. Same danger instance as `binary_colors`: lambda = kappa = aleph_1, gamma = 2, r = 2 satisfies ℵ₀ ≤ κ ≤ λ, and the conclusion aleph_1 -> (aleph_1)^2_2 is ZFC-false, so the variant is true only if 2^{aleph_1} -/-> (aleph_1)^3_2.  
**Difficulty:** math 9/10, Lean 9/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** Sierpinski's 2^kappa -/-> (kappa^+)^2_2 instantiated at kappa = aleph_0 refutes aleph_1 -> (aleph_1)^2_2, so the implication's conclusion is outright false at that instance; the only escape is failure of the premise.  
**Flags:** needs literature check; possible falsity as stated (concrete danger instance identified); stated as a theorem, not an answer()-question  
**Next action:** Check the literature (Erdos-Hajnal-Mate-Rado, Combinatorial Set Theory, negative relations for triples) for 2^{kappa^+} -/-> (kappa^+)^3_2; if that fails the variant is refutable and should be restated with order types or with an extra hypothesis.

## `r_eq_two` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/1167.lean:106`  
**Secondary category:** 3 (False / refutable as stated)  
**Statement:** Special case of Erdos 1167 with r = 2: does 2^lambda -> (kappa_alpha + 1)^3 imply lambda -> (kappa_alpha)^2?  
**Source:** erdosproblems.com/1167, r = 2 specialization (repo-authored variant)  
**Statement matches intent:** suspect — Same cardinal-vs-ordinal '+1' issue as `erdos_1167`, and here it bites hardest: for infinite kappa the hypothesis reduces to 2^lambda -> (kappa)^3 while the classical stepping-up lemma is stated with the order type kappa+1.  
**Known status:** Open; specialization of the open problem. Explicit danger instance: gamma = 2, kappa ≡ aleph_1, lambda = aleph_1, giving conclusion aleph_1 -> (aleph_1)^2_2 which is ZFC-false; the variant therefore requires 2^{aleph_1} -/-> (aleph_1)^3_2, unverified.  
**Difficulty:** math 9/10, Lean 9/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** Instantiating the theorem statement with gamma = 2 and constant kappa = aleph_1 gives a conclusion that Mathlib-level Sierpinski arguments refute, so truth hinges entirely on failure of the premise.  
**Flags:** needs literature check; possible falsity as stated; stated as a theorem, not an answer()-question  
**Next action:** Same as `binary_colors`: settle the '+1' convention and the aleph_1 instance before attempting a proof; consider restating with order types once the ForMathlib partition-relation API supports them.

## `erdos_1175` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/1175.lean:48`  
**Statement:** For every uncountable cardinal kappa, is there a cardinal mu such that every graph of chromatic number mu contains a triangle-free subgraph of chromatic number kappa?  
**Source:** erdosproblems.com/1175 (Erdos-Hajnal); Shelah's consistency result for kappa = lambda = aleph_1  
**Statement matches intent:** suspect — The hypothesis is `G.chromaticCardinal = mu` (exact equality) rather than the usual `≥ mu`; the file itself notes this and provides the `threshold_formulation` variant plus a test showing threshold ⟹ exact. Exact equality is a weaker (easier) statement. Also the conclusion demands `H.coe.chromaticCardinal = kappa` exactly rather than `≥ kappa`. No vacuity loophole: every cardinal in the ambient universe is realized as the chromatic cardinal of a complete graph, so no choice of mu makes the hypothesis unsatisfiable.  
**Known status:** Open on erdosproblems.com. Shelah proved that a negative answer is consistent for kappa = mu = aleph_1 (recorded in the file as `shelah_consistency`, itself an answer(sorry) placeholder), but the ∃mu makes the general question open. No PR, campaign entry, or duplicate in this repo.  
**Difficulty:** math 9/10, Lean 10/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** chromaticCardinal is sInf over cardinals admitting a proper colouring (FormalConjecturesForMathlib/Combinatorics/SimpleGraph/Coloring.lean:140); the set is always nonempty (identity colouring), so no junk sInf. `Type*` inside the ∀ binder fixes a single universe, so the statement is universe-parametric rather than genuinely universe-quantified — a mild weakening worth noting.  
**Flags:** exact-equality rather than threshold hypothesis (weaker than intended); single fixed universe for V; conclusion asks chromaticCardinal = kappa rather than ≥ kappa  
**Next action:** Leave open. The set-theoretic content (Shelah forcing, Erdos-Hajnal triangle-free graphs of large chromatic number) is far beyond current Mathlib; a realistic milestone is formalizing existence of triangle-free graphs of chromatic number kappa for every kappa.

## `erdos_1175.variants.threshold_formulation` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/1175.lean:86`  
**Statement:** Threshold form of Erdos 1175: for every uncountable kappa is there mu such that every graph with chromatic number at least mu has a triangle-free subgraph of chromatic number kappa?  
**Source:** erdosproblems.com/1175, threshold reformulation (repo-authored variant)  
**Statement matches intent:** yes  
**Known status:** Open, and strictly stronger than `erdos_1175`, which is itself open. Shelah's consistency result blocks the mu = kappa = aleph_1 instance. No PR/campaign/duplicate.  
**Difficulty:** math 9/10, Lean 10/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** `erdos_1175.test.threshold_implies_exact` is a completed (non-sorry) proof in the file, confirming the intended strength ordering.  
**Flags:** single fixed universe for V; conclusion asks chromaticCardinal = kappa rather than ≥ kappa  
**Next action:** Leave open; prefer this formulation over `erdos_1175` when citing the problem.

## `erdos_1176` — Already solved externally (cat 1)

**File:** `FormalConjectures/ErdosProblems/1176.lean:36`  
**Secondary category:** 10 (Cannot classify without correction/clarification)  
**Statement:** If G has chromatic number aleph_1, can its edges be coloured with aleph_1 colours so that every countable vertex colouring has a colour class whose induced edges realize all aleph_1 edge colours?  
**Source:** erdosproblems.com/1176 (Erdos-Galvin-Hajnal); consistency proved by Hajnal and Komjath  
**Statement matches intent:** suspect — The statement itself is a faithful rendering (edge colour type of size aleph_1, vertex colour type countable, a vertex colour class containing edges of every edge colour). The defect is structural: erdosproblems.com records this as 'not disprovable', i.e. Hajnal-Komjath showed the positive answer is consistent with ZFC, so `answer(sorry)` cannot be discharged inside Lean's ZFC-like ambient theory — there is no truth value to supply unless the statement is also provable. The 1175 file handles the analogous situation by explicitly labelling its consistency statement a placeholder; 1176 does not.  
**Known status:** erdosproblems.com state: 'not disprovable' (a consistency result exists — Hajnal-Komjath), which per the batch convention counts as resolved outside this repo. It is NOT a ZFC theorem, so the Lean `answer(sorry) ↔ P` shape is not closable without an added axiom or a relativisation to a forcing extension. No PR, campaign entry, or duplicate in the repo.  
**Difficulty:** math 9/10, Lean 10/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** Batch metadata gives erdosproblems.com state 'not disprovable'. The Lean statement additionally pins EColor to `Type 0` while V is universe-polymorphic; harmless (a set of size aleph_1 exists in Type 0) but stylistically inconsistent with `G.chromaticCardinal = aleph 1 : Cardinal.{u}`.  
**Flags:** answer() encoding cannot be discharged for a statement that is only known consistent; consistency vs ZFC-theorem confusion — mirror the 1175 placeholder convention; EColor forced into Type 0  
**Next action:** Restate as a consistency/independence statement (as `erdos_1175.variants.shelah_consistency` does, with an explicit placeholder note), or drop the answer() wrapper; do not attempt to prove the current form. Verify the exact Hajnal-Komjath statement before relabelling.

## `erdos_119.parts.iii` — Already solved externally (cat 1)

**File:** `FormalConjectures/ErdosProblems/119.lean:76`  
**Secondary category:** 5 (Solved mathematically, not yet formalized)  
**Statement:** For unit-modulus z_1, z_2, ... and M_n = max_{|z|=1} |prod_{i<=n} (z - z_i)|, is there c > 0 with sum_{k<=n} M_k > n^{1+c} for all large n?  
**Source:** erdosproblems.com/119 ($100; Wagner 1980, Beck Annals 1991); third question reported resolved in July 2026 by M. Korsky with GPT-5.6, sum_{k<=n} M_k >> n^{5/4}/sqrt(log n)  
**Statement matches intent:** suspect — Quantifier order is weakened: the file states ∀ z, ∃ c > 0, ∀ᶠ n, ... whereas the natural reading of the question (and of Beck's theorem, which the file's parts i/ii mirror) uses an absolute constant, ∃ c > 0, ∀ z, ∀ᶠ n. The reported solution supplies an absolute c (any c < 1/4), so it implies the weaker formal statement — but the formalization is not the sharp question. Minor off-by-one: `∑ k ∈ range n` is sum over k ≤ n-1 rather than k ≤ n; asymptotically irrelevant. M z 0 = 1 (empty product), fine.  
**Known status:** erdosproblems.com state for problem 119 is now 'solved' (batch metadata, 2026-07-26); as of 2026-07-20 the site still listed the third question unresolved, and the new resolution (Korsky + GPT-5.6, sum_{k<=n} M_k >> n^{5/4}/sqrt(log n), which also yields M_n > n^{1/4-o(1)} infinitely often) was still being verified in public discussion. Parts i and ii are already marked research solved in-file (Wagner 1980, Beck 1991). No PR/campaign/duplicate in this repo.  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** Web search confirms a July-2026 claimed resolution of the third question of Erdos 119 with the bound n^{5/4}/sqrt(log n) (> n^{1+c} for any c < 1/4), attributed to GPT-5.6 and Korsky, and notes the site page was edited 19-20 July 2026; batch metadata now records state 'solved'.  
**Flags:** needs literature check (very recent, verification status was still open as of 2026-07-20); quantifier order ∀z ∃c is weaker than the intended absolute constant; range n off-by-one (harmless)  
**Next action:** Confirm the site's current status and the Korsky/GPT-5.6 write-up, then set answer(True) and either cite the paper as a `research solved` reference or begin the (substantial) formalization; note that a full Lean proof needs Beck-style potential-theory machinery not in Mathlib. Effort: large.

## `erdos_1192` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/1192.lean:93`  
**Statement:** For every r >= 2, is there a basis A of order r (f_r(n) > 0 for large n) whose representation function satisfies sum_{n<=x} f_r(n)^2 = O(x)?  
**Source:** erdosproblems.com/1192; Ruzsa, 'A just basis', Monatsh. Math. (1990), 145-151; Erdos survey [Er80]  
**Statement matches intent:** yes  
**Known status:** Open for r ≥ 3; Ruzsa [Ru90] solved r = 2 (recorded as `erdos_1192.variants.ruzsa`, sorried). Erdos-Renyi's probabilistic construction is recorded as `variants.renyi`. No PR/campaign/duplicate in the fork.  
**Difficulty:** math 9/10, Lean 9/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Four in-file test lemmas (f_r_zero_zero, f_r_empty, f_r_singleton_self, f_r_no_rep) are proved and pin down the counting convention correctly; no degenerate A is admitted since the basis condition ∀ᶠ n, f_r A r n > 0 excludes trivial choices.  
**Flags:** ordered vs unordered representation counting (immaterial for the O(x) statement)  
**Next action:** Leave open. Checked that the obvious cheap reduction fails: adjoining 0 to Ruzsa's order-2 just basis does NOT give an order-r just basis, since the r-fold ordered counts pick up the much larger g_r contributions. First Lean milestone would be formalizing the Cauchy-Schwarz lower bound sum_{n<=x} f_r(n)^2 >> x showing the bound is tight.

## `erdos_1199` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/ErdosProblems/1199.lean:39`  
**Statement:** Must every 2-colouring of the naturals admit an infinite set A with A+A monochromatic?  
**Source:** erdosproblems.com/1199; Owings, E2494, Amer. Math. Monthly (1974) 902; Hindman, JCTA (1979) 19-32 (false for 3 colours)  
**Statement matches intent:** suspect — `A + A` (Set.Pointwise) is {a+b : a,b ∈ A}, which INCLUDES the doubles 2a. Some statements of Owings' problem use {a+b : a ≠ b}. Requiring the doubles to share the colour is a stronger demand on A, hence a stronger conjecture; if the intended version excludes a = b, the formal statement is strictly stronger than the source. Also A ⊆ ℕ may contain 0, which is harmless.  
**Known status:** Open on erdosproblems.com (a well-known open problem: Hindman showed the analogue fails for 3 colours; the 2-colour case remains unresolved, and is not implied by Moreira-Richter-Robertson's B+C theorem, which produces two different infinite sets). No PR/campaign/duplicate in this repo.  
**Difficulty:** math 10/10, Lean 10/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** Repo docstring matches the site wording 'all elements of A+A are the same colour'; the Pointwise sumset in Mathlib includes a = b, which is the only faithfulness question here.  
**Flags:** needs literature check (a = b included in A+A?); companion `variants.three` (Hindman) is also sorried  
**Next action:** Verify against erdosproblems.com/1199 whether A+A is meant to include a = b; if not, restate with distinct summands. Otherwise leave open.

## `erdos_12.parts.iii` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/12.lean:81`  
**Statement:** If A is infinite and no distinct a,b,c in A satisfy a | b+c with b,c > a, must the sum of reciprocals of A converge?  
**Source:** erdosproblems.com/12; Erdos-Sarkozy, Proc. LMS (1970) 97-101  
**Statement matches intent:** yes  
**Known status:** Open. Parts i and ii of the same problem are recorded as solved by the DeepMind prover agent (with upstream formal_proof links to mo271/formal-conjectures), part iii is not. Checked that part ii's disproof (for every c > 0 there is a good A with |A ∩ [1,N]| ≥ N^{1-c} eventually) does NOT refute part iii: partial summation gives sum_{n∈A} 1/n ≤ O(1/c) < ∞ for each such A. Likewise `variants.erdos_sarkozy` gives only infinitely-often density, which does not force divergence. No PR/campaign/duplicate for part iii.  
**Difficulty:** math 9/10, Lean 9/10 · **Compute:** none · **Confidence:** high  
**Evidence:** The other parts of the file carry `formal_proof using formal_conjectures at ...` attributes; part iii carries none, and the in-file solved results are consistent with (do not decide) convergence.  
**Flags:** 1/0 = 0 junk if 0 ∈ A (harmless)  
**Next action:** Leave open. A plausible Lean-side warm-up is the Erdos-Sarkozy density-0 theorem (`erdos_12.variants.erdos_sarkozy_density_0`), currently sorried.

## `erdos_120` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/ErdosProblems/120.lean:44`  
**Statement:** Erdos similarity problem: for every infinite A ⊆ R, is there a set E of positive measure containing no affine copy aA+b (a ≠ 0)?  
**Source:** erdosproblems.com/120 ($100); Steinhaus, Fund. Math. (1920) 93-104 (finite case)  
**Statement matches intent:** yes  
**Known status:** Open on erdosproblems.com (this is the famous Erdos similarity conjecture, still unsolved despite substantial recent partial progress on 'sub-lacunary' and structured sets). Steinhaus/Lebesgue density gives the finite case, recorded as `variants.finite_set` (sorried). No PR, campaign entry, or duplicate in this repo.  
**Difficulty:** math 10/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Classical named open problem with a standing $100 prize; batch metadata confirms erdosproblems.com state 'open' with prize $100 as of 2026-07-26.  
**Next action:** Leave open (cat 9). A reasonable Lean milestone is `erdos_120.variants.finite_set` itself, which follows from the Lebesgue density theorem / Steinhaus theorem and is within Mathlib's reach.

## `erdos_1201` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/1201.lean:43`  
**Statement:** For all eps, eta > 0 is there k such that the set of n with P(n(n+1)...(n+k)) > n^{1-eps} has lower density at least 1-eta, where P is the largest prime factor?  
**Source:** erdosproblems.com/1201  
**Statement matches intent:** yes  
**Known status:** Open on erdosproblems.com. Erdos wrote that he could prove the eps = 1/2 case, recorded as `variants.epsilon_half` (sorried). No PR, campaign entry, or duplicate.  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** Checked the sSup junk case explicitly: for n = 0 the product ∏_{i<k+1} i is 0 and every prime divides it, so the set is unbounded and Nat.sSup = 0, failing `0 > 0^{1-eps} = 0`. For n ≥ 1 the divisor set is finite and sSup is the max.  
**Flags:** Nat.sSup junk value at n = 0 (harmless); lower density via liminf rather than an assumed-existing density (reasonable)  
**Next action:** Leave open. First milestone: the eps = 1/2 variant, which follows from standard results on the largest prime factor of n(n+1)...(n+k) but needs sieve infrastructure absent from Mathlib.

## `erdos_1203` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/1203.lean:41`  
**Secondary category:** 10 (Cannot classify without correction/clarification)  
**Statement:** With omega(n) the number of distinct prime factors and F(n) = max_k omega(n+k) loglog k / log k, does F(n) tend to infinity?  
**Source:** erdosproblems.com/1203  
**Statement matches intent:** suspect — The range of the max is not specified in the source snippet and the file takes ⨆ over ALL k : ℕ. This drags in junk terms: k = 0 and k = 1 give Real.log = 0 hence a 0/0 = 0 division junk value, and k = 2 gives a NEGATIVE weight (log log 2 < 0). None of these lowers a supremum that is ≥ 1, so the definition is probably harmless, but that the iSup is even bounded (so not Real.sSup junk = 0) relies on the nontrivial fact max_{m≤x} omega(m) ~ log x/loglog x. If Erdos intended k restricted (e.g. 1 ≤ k ≤ n), the formalization is a different function.  
**Known status:** Open on erdosproblems.com. The easy lower bound F(n) ≥ 1 - o(1) is recorded as `variants.lower_bound` (sorried). No PR, campaign entry, or duplicate.  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** Real.log 0 = Real.log 1 = 0 and x/0 = 0 in Lean, so the k ∈ {0,1} terms are 0; log log 2 ≈ -0.366 makes the k = 2 term negative. Boundedness of the family in k for fixed n follows from omega(m) ≤ (1+o(1)) log m/loglog m together with sup_k loglog k/log k = 1/e.  
**Flags:** unspecified range of the max over k; iSup well-definedness (boundedness) is not established in-file; negative/junk terms at k ≤ 2  
**Next action:** Confirm the intended range of k in the source (all k ≥ 1? k ≤ n?) and add the corresponding restriction plus a boundedness lemma so the ⨆ is provably not a junk value; then leave open.

## `erdos_1209.parts.iii.b` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/1209.lean:85`  
**Statement:** Is there an n such that n + 2^(2^k) is squarefree for every k?  
**Source:** erdosproblems.com/1209; Erdos, survey [Er80]  
**Statement matches intent:** yes  
**Known status:** Open on erdosproblems.com. The prime analogue (iii.a) is disproved (ebarschkis/GPT, with a Lean formalization linked in the file). The squarefree analogue resists the same argument, which used primality of n + 2^{2^K} to get a divisor; getting p^2 | n + 2^{2^k} for all large k would need a covering-system style construction modulo p^2. No PR/campaign/duplicate.  
**Difficulty:** math 9/10, Lean 9/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** iii.a's disproof relies essentially on primality (order of 2^{2^k} mod p), so it does not transfer; nothing in the file or the register indicates progress on iii.b.  
**Next action:** Leave open. A plausible line of attack (and a good Lean sub-target) is: for each odd prime p, 2^(2^k) mod p^2 is eventually periodic in k, so 'p^2 divides n + 2^(2^k) for some k' is a congruence condition on n; deciding whether these conditions cover all n is the crux.

## `erdos_1209.parts.iii.c` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/ErdosProblems/1209.lean:93`  
**Statement:** Is there an n such that n + 2^(2^k) is prime for infinitely many k?  
**Source:** erdosproblems.com/1209; Erdos, survey [Er80]  
**Statement matches intent:** yes  
**Known status:** Open on erdosproblems.com. Proving the answer 'yes' means exhibiting infinitely many primes in a doubly-exponentially sparse sequence — beyond all current technology (the n = 1 instance is the Fermat-prime problem, where the expectation is that only finitely many exist). Proving 'no' for every n would need a covering-congruence argument stronger than the one that settles iii.a. No PR/campaign/duplicate.  
**Difficulty:** math 10/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Erdos himself wrote of this family that 'unless I overlook a trivial way of getting a counterexample these questions are quite hopeless' (quoted in the file's iii/parts.i docstring); the positive direction subsumes Fermat-prime-type questions.  
**Next action:** Leave open (cat 9). Do not attempt.

## `erdos_1209.parts.iii.d` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/1209.lean:101`  
**Statement:** Is there an n such that n + 2^(2^k) is squarefree for infinitely many k?  
**Source:** erdosproblems.com/1209; Erdos, survey [Er80]  
**Statement matches intent:** yes  
**Known status:** Open on erdosproblems.com. Squarefreeness of values of exponential sequences is notoriously hard (even 'infinitely many squarefree Fermat numbers' is unknown); the obstruction is that p^2 | n + 2^(2^k) is governed by the eventual period of 2^k mod ord_{p^2}(2), and one must avoid all p simultaneously along an infinite set of k. No PR/campaign/duplicate.  
**Difficulty:** math 9/10, Lean 9/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** Weakest of the iii-family and still marked open on the site; no known technique gives squarefree values of doubly-exponential sequences infinitely often.  
**Next action:** Leave open. The most likely route to a positive answer is an averaging/counting argument over n rather than an explicit n; a Lean-side warm-up is the eventual periodicity of k ↦ 2^(2^k) mod m.

## `erdos_1210` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/1210.lean:38`  
**Statement:** For pairwise coprime A ⊆ [1,n), is sum_{a in A} 1/(n-a) at most sum_{p<n} 1/p + O(1), with an absolute implied constant?  
**Source:** erdosproblems.com/1210; Erdos [Er77c], [Er80]  
**Statement matches intent:** yes  
**Known status:** Open on erdosproblems.com. No PR, campaign entry, or duplicate in this repo. `(range n).filter Prime` uses the general `_root_.Prime` predicate, which on ℕ is equivalent to Nat.Prime, so the right-hand sum is sum over primes p < n of 1/p (note p = 0, 1 are not prime so no 1/0 junk).  
**Difficulty:** math 8/10, Lean 8/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** Statement structure (∃C ∀n ∀A) matches 'O(1)' with an absolute constant. No degenerate A is admitted; the pairwise coprimality is the only structural constraint, as in the source.  
**Next action:** Leave open. A tractable first step is the trivial bound sum_{a∈A} 1/(n-a) ≪ log n and the matching Mertens estimate sum_{p<n} 1/p = loglog n + O(1), which would at least locate the difficulty.

## `erdos_1210.variants.er80_correction` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/1210.lean:52`  
**Statement:** Erdos' [Er77c] version: if q_1 < ... < q_k are the primes in (n,m], is sum 1/(q_i - n) < sum_{p < m-n} 1/p + O(1)?  
**Source:** erdosproblems.com/1210; Erdos [Er77c] as corrected in [Er80]  
**Statement matches intent:** yes  
**Known status:** Open on erdosproblems.com. Erdos himself said he 'did not state this quite correctly' in [Er77c], which is exactly why the repo records both forms. Heuristic warning worth recording: for n a primorial the density of primes in n + [1, D] is boosted by ∏_{p|n} p/(p-1) ≍ e^gamma loglog n for small D, which suggests the left side may exceed loglog(m-n) by a constant factor rather than a constant — i.e. this variant may be FALSE as stated. I could not verify this against the literature.  
**Difficulty:** math 8/10, Lean 8/10 · **Compute:** none · **Confidence:** low  
**Evidence:** Heuristic computation: with n primorial and m - n ≍ n, sum_{n<q≤m} 1/(q-n) is plausibly ≍ e^gamma loglog n while sum_{p<m-n} 1/p ≍ loglog n, so the inequality with an additive O(1) would fail. This is a heuristic only, not a proof.  
**Flags:** needs literature check; possible falsity for primorial n (heuristic only)  
**Next action:** Check the literature (and erdosproblems.com/1210 comments) for whether the [Er77c] form is known false for primorial n; if it is, this should be re-categorised as cat 3 with the primorial counterexample. Otherwise leave open.

## `erdos_1212` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/1212.lean:63`  
**Statement:** In the graph on coprime lattice points (x,y) with edges between points differing by 1 in one coordinate, is there an infinite path all of whose vertices have min(x,y) > 1 and at least one composite coordinate?  
**Source:** erdosproblems.com/1212; Erdos [Er80] p. 114 (weaker version solved by C. Stewart)  
**Statement matches intent:** yes  
**Known status:** Open on erdosproblems.com. The weaker version (min(x,y) > 1 only) was solved by C. Stewart with the prime-pair path (p_k, p_{k+1}) → (p_{k+1}, p_{k+2}); the compositeness condition forbids exactly those anchors. The file records genuine machine-checked API lemmas (vertical_leg_valid, horizontal_leg_valid, anchor_coprime_of_short_leg, right/left_neighbor_witness_free) but no progress on the main statement. No PR or campaign entry for 1212.  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** Derived the parity constraint directly from the adjacency + coprimality conditions (y(y±1) is always even, so the anchor must be odd), and the leg-length constraint from `anchor_coprime_of_short_leg` in the file; the resulting growth recursion t → t + t^{1/3} does reach infinity, so the construction is not obstructed — only the analytic input is missing.  
**Flags:** redundant Tendsto conjunct (implied by injectivity)  
**Next action:** Leave open. Concrete strategy worth recording: every move (a,y) → (a,y±1) forces the fixed coordinate a to be coprime to y(y+1) hence ODD, so the path must be a staircase of L-shaped legs anchored at odd composites; a leg from anchor a has length < P^-(a), so one needs, in each interval of length about t^{1/3} near t, a composite with smallest prime factor ≫ t^{1/3} (an almost-prime in a short interval). That reduces the problem to an almost-primes-in-short-intervals input that is currently out of reach.

## `erdos_123` — Already solved externally (cat 1)

**File:** `FormalConjectures/ErdosProblems/123.lean:74`  
**Statement:** For pairwise coprime a,b,c > 1, is every sufficiently large integer a sum of distinct numbers of the form a^k b^l c^m, none of which divides another (i.e. is that set d-complete)?  
**Source:** erdosproblems.com/123 (state today: 'proved (Lean)', $250); [ErLe96] Erdős–Lewin, d-complete sequences of integers, Math. Comp. (1996); 2026 resolution with a complete Lean 4 formalization (StarFleetMath project, per web search)  
**Statement matches intent:** yes  
**Known status:** Solved externally in 2026: the affirmative answer is proved for every pairwise coprime triple a,b,c>1, and erdosproblems.com marks the problem 'proved (Lean)', i.e. a public formal Lean proof exists. No fork PR or campaign targets this file (pr_register.json / campaign_register.json contain nothing for Erdős 123).  
**Difficulty:** math 8/10, Lean 4/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Batch metadata gives today's erdosproblems.com state as 'proved (Lean)'. Web search confirms a 2026 result: 'for every pairwise-coprime triple a,b,c>1, every sufficiently large integer is a sum of distinct terms a^i b^j c^k such that no selected term divides another', formalized sorry-free in Lean 4. That statement is literally the RHS of erdos_123, so answer := True.  
**Flags:** fastest import in this batch: public Lean proof already exists; canonical file still says answer(sorry) / research open  
**Next action:** Set answer(True) and import/port the public Lean 4 proof of the d-completeness theorem, adapting it to this file's IsDComplete + Submonoid.powers formulation; then verify the build (lake not runnable here).

## `erdos_123.variants.powers_2_3_5_snug` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/123.lean:109`  
**Statement:** For every ε>0, can every sufficiently large n be written as a sum of distinct numbers of the form 2^k 3^l 5^j whose largest summand is < (1+ε) times the smallest?  
**Source:** erdosproblems.com/123 (stronger conjecture listed on the page); [Er92b] Erdős, Some of my favourite problems…, Matematiche (Catania) (1992)  
**Statement matches intent:** yes  
**Known status:** Open. The 2026 resolution of the main problem (pairwise-coprime d-completeness) does not give the snug/almost-equal-summands strengthening; no formal proof or PR found in the fork (pr_register.json, campaign_register.json have no Erdős 123 entry).  
**Difficulty:** math 8/10, Lean 8/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** Erdős called the plain 2^k3^l case 'nice and difficult' though it has a two-line induction; the snug variant adds a strong window constraint and is stated separately on the problem page as an unresolved strengthening. Nothing in the fork targets it.  
**Flags:** needs literature check: whether the 2026 proof of Erdős 123 also covers the (1+ε)-snug 2,3,5 variant  
**Next action:** Attempt the density heuristic: the 5-smooth numbers in [x,(1+ε)x] number ≍_ε (log x)^2, and a greedy/subset-sum argument over that window plus a multiplicative-scaling induction (n even → halve; n odd → subtract a suitable 3^k5^j) is the natural first milestone. First check the 2026 Erdős-123 literature for whether the snug variant was also settled.

## `erdos124.ne_zero` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/124.lean:57`  
**Statement:** For fixed k ≠ 0 and integers 3 ≤ d_1 < … < d_r with gcd 1 and Σ 1/(d_i−1) ≥ 1, can every sufficiently large integer be written as Σ c_i a_i with c_i ∈ {0,1}, where a_i is divisible by d_i^k and has only digits 0,1 in base d_i?  
**Source:** erdosproblems.com/124 (state today: open); [BEGL96] Burr, Erdős, Graham, Li, Complete sequences of sets of integer powers, Acta Arith. (1996)  
**Statement matches intent:** yes  
**Known status:** Open per erdosproblems.com. The k = 0 case in the same file (erdos124.zero) is recorded as solved (Boris Alexeev, via Aristotle), and the special case D = {3,4,7} with k ≠ 0 is BEGL96's theorem (erdos124.ne_zero_three_four_seven, also sorry in-repo). No fork PR/campaign touches problem 124.  
**Difficulty:** math 8/10, Lean 8/10 · **Compute:** small · **Confidence:** medium  
**Evidence:** Statement matches the BEGL96 conjecture verbatim including the gcd-1 side condition that is needed once d_i^k | a_i is imposed; no known resolution, and the k = 0 analogue only fell in 2025/26.  
**Flags:** worth a small search over (D,k) for a candidate counterexample, since answer(False) is a live possibility  
**Next action:** Treat as open: first formalize the BEGL96 {3,4,7} case as a template, then look for the general covering/base-representation argument; alternatively probe for a counterexample family (large k with minimal admissible D) before committing to answer(True).

## `erdos_125.variants.positive_upper_density` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/125.lean:84`  
**Statement:** With A = integers using only digits 0,1 in base 3 and B = integers using only digits 0,1 in base 4, does A+B have positive upper density?  
**Source:** erdosproblems.com/125 (page state today: 'disproved (Lean)' — that refers to the positive-(lower)-density question); Burr–Erdős–Graham–Li; Erdős letter to Soundararajan (1995)  
**Statement matches intent:** yes  
**Known status:** Open. Its companion erdos_125.variants.positive_lower_density is recorded as answer(False) with a public formal proof link (mo271/formal-conjectures), i.e. lowerDensity(A+B) = 0 is established. What remains unresolved is exactly the sign of upperDensity(A+B).  
**Difficulty:** math 8/10, Lean 8/10 · **Compute:** small · **Confidence:** medium  
**Evidence:** The three open declarations in this file collapse to a single unknown bit once lowerDensity = 0 is used: positive_upper_density ⟺ zero_lower_positive_upper_density ⟺ ¬zero_density. Counting heuristics strongly favour positive upper density but the disproof of positive lower density shows the sumset is genuinely irregular.  
**Flags:** logically equivalent to erdos_125.variants.zero_lower_positive_upper_density given the already-proved lowerDensity = 0; needs literature check on whether upper density was settled alongside the 2025/26 disproof  
**Next action:** Try to prove upperDensity > 0 directly: |A∩[0,x]| ≍ x^{log2/log3} ≈ x^{0.631} and |B∩[0,x]| ≍ x^{1/2}, so the product of counts is ≫ x^{1.13}; a second-moment/energy bound on the number of representations along a sparse sequence x = 4^m would give positive upper density. Milestone: bound the additive energy of (A∩[0,x], B∩[0,x]).

## `erdos_125.variants.zero_density` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/125.lean:93`  
**Statement:** Does A+B (A = base-3 digits 0/1, B = base-4 digits 0/1) have both zero upper and zero lower density?  
**Source:** erdosproblems.com/125 (case 1 of the four density possibilities enumerated in the module docstring)  
**Statement matches intent:** yes  
**Known status:** Open, and exactly the negation of erdos_125.variants.zero_lower_positive_upper_density: one of the two must get answer(True) and the other answer(False). Half of the conjunction (lower density 0) is already proved upstream.  
**Difficulty:** math 8/10, Lean 8/10 · **Compute:** small · **Confidence:** medium  
**Evidence:** Given the established lowerDensity = 0, zero_density ⟺ upperDensity = 0 and zero_lower_positive_upper_density ⟺ upperDensity > 0; these two declarations are exact complements, so they encode one bit twice.  
**Flags:** duplicate/complementary encoding: exact negation of zero_lower_positive_upper_density (mod the proved lowerDensity = 0); counting heuristic (x^{0.631}·x^{0.5} ≫ x) makes answer(False) the likely outcome here  
**Next action:** Resolve the single open bit sign(upperDensity(A+B)); then both this and the complementary declaration close simultaneously. Also add the in-repo lemma lowerDensity(A+B) = 0 so this reduces to upperDensity = 0.

## `erdos_125.variants.zero_lower_positive_upper_density` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/125.lean:102`  
**Statement:** Does A+B have zero lower density but positive upper density (so that its density does not exist)?  
**Source:** erdosproblems.com/125 (case 2 of the four density possibilities)  
**Statement matches intent:** yes  
**Known status:** Open. lowerDensity(A+B) = 0 has a linked formal proof (mo271/formal-conjectures, referenced from erdos_125.variants.positive_lower_density); the outstanding content is 0 < upperDensity(A+B).  
**Difficulty:** math 8/10, Lean 8/10 · **Compute:** small · **Confidence:** medium  
**Evidence:** Same single unknown bit as the two sibling declarations; the fork already owns half the statement.  
**Flags:** half of the statement is already proved externally/upstream — only 0 < upperDensity is open; equivalent to erdos_125.variants.positive_upper_density  
**Next action:** Prove upperDensity(A+B) > 0 (energy/second-moment bound along x = 4^m or 12^m), then combine with the existing lower-density-zero proof; answer would be True.

## `erdos_126` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/ErdosProblems/126.lean:40`  
**Statement:** Let f(n) be the largest m such that every n-element set A of naturals has ∏_{a≠b∈A}(a+b) with at least m distinct prime factors. Is f(n)/log n → ∞?  
**Source:** erdosproblems.com/126 (state today: open, $250); [ErTu34] Erdős–Turán, On a Problem in the Elementary Theory of Numbers, Amer. Math. Monthly (1934)  
**Statement matches intent:** yes  
**Known status:** Open since 1934 (Erdős–Turán proved log n ≪ f(n) ≪ n/log n, recorded as erdos_126.variants.IsBigO in the same file). $250 prize. No fork PR or campaign.  
**Difficulty:** math 9/10, Lean 9/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Ninety-year-old prize problem with no improvement past the original Erdős–Turán bounds; the formal statement matches it.  
**Flags:** minor spec issue: 0 ∈ ℕ is allowed in A, shifting small values of f but not the asymptotic question  
**Next action:** Do not attempt a resolution; at most formalize the Erdős–Turán lower bound f(n) ≫ log n (the solved sibling) to build infrastructure. Any progress on f(n)/log n → ∞ is research-scale.

## `erdos_126.variants.isLittleO` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/ErdosProblems/126.lean:64`  
**Statement:** With the same f, is f(n) = o(n/log n)?  
**Source:** erdosproblems.com/126 ('Erdős says that f(n) = o(n/log n) has never been proved'); [ErTu34]  
**Statement matches intent:** yes  
**Known status:** Open; explicitly flagged by Erdős as never proved. The trivial upper bound f(n) ≤ π(2n) ≍ n/log n is all that is known.  
**Difficulty:** math 9/10, Lean 9/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Erdős's own remark on the problem page that this has never been proved; nothing in the fork addresses it.  
**Flags:** stated as a bare theorem rather than an answer() question — no escape hatch if the truth value is False  
**Next action:** Leave open. A first milestone would be any nontrivial saving, e.g. f(n) ≤ (1−δ)·2n/log n for the extremal A, which already requires new sieve input.

## `erdos_128` — Vacuously true / accidentally weakened (cat 4)

**File:** `FormalConjectures/ErdosProblems/128.lean:33`  
**Secondary category:** 3 (False / refutable as stated)  
**Statement:** If every induced subgraph of an n-vertex graph G on at least n/2 vertices has more than n²/50 edges, must G contain a triangle?  
**Source:** erdosproblems.com/128 (state today: falsifiable, i.e. still open; $250)  
**Statement matches intent:** no — MAJOR quantifier-scope defect: V' is universally quantified together with the conclusion, so the RHS reads 'for every graph G and every vertex subset V' with 2|V'|+1 ≥ n and 50·e(G[V']) > n², G has a triangle' — i.e. a single dense large induced subgraph is required to force a triangle. The intended hypothesis is that EVERY such V' is dense (the ∀ V' must sit inside the hypothesis). Secondary off-by-one: 2*V'.ncard + 1 ≥ Fintype.card V encodes |V'| ≥ (n−1)/2 rather than |V'| ≥ n/2.  
**Known status:** As written the RHS is plainly false, so the declaration is closable with answer(False) plus a tiny counterexample; the INTENDED Erdős problem remains open ($250).  
**Difficulty:** math 8/10, Lean 3/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Explicit counterexample to the current RHS: take V = Fin 2, G = ⊤ (one edge), V' = univ. Then Fintype.card V = 2, 2·2+1 = 5 ≥ 2, and 50·1 = 50 > 2² = 4, yet a 2-vertex graph is triangle-free, so ¬G.CliqueFree 3 fails. (Asymptotic version: K_{n/2,n/2} with V' = univ has n²/4 > n²/50 edges and no triangle.) Hence answer := False and the theorem becomes a small finite computation.  
**Flags:** quantifier order / witness scope loophole — different problem from the intended one; off-by-one in the |V'| ≥ n/2 threshold; trivialised: provable by a Fin 2 counterexample once answer(False) is filled in  
**Next action:** Fix the statement to: answer(sorry) ↔ ∀ V [Fintype V] (G), (∀ V' : Set V, 2 * V'.ncard ≥ Fintype.card V → 50 * (G.induce V').edgeSet.ncard > Fintype.card V ^ 2) → ¬ G.CliqueFree 3. Do not 'solve' the current version — flag it as a formalization bug and repair it.

## `erdos_13.variants.general` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/13.lean:54`  
**Statement:** For fixed r, if A ⊆ {1,…,N} contains no a and b_1,…,b_r ∈ A with a < min b_i and a | (b_1+…+b_r), is |A| ≤ N/(r+1) + O(1)?  
**Source:** erdosproblems.com/13 (page state 'proved', $100 — that refers to the r = 2 case); [Be23] Bedert, arXiv:2301.07065 (r = 2, |A| ≤ ⌊N/3⌋+1); general r asked by Erdős–Sárközy  
**Statement matches intent:** yes  
**Known status:** Open for r ≥ 3. Bedert (2023) settled r = 2 (recorded as the solved theorem erdos_13 in the same file, still sorry in-repo). Web search confirms the general-r version is still open in the literature.  
**Difficulty:** math 8/10, Lean 8/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Search on Bedert's paper confirms only r = 2 is resolved; the general |A| ≤ N/(r+1)+O(1) question is described as remaining open.  
**Flags:** r = 0 branch is vacuous (a ∣ 0 always), a harmless degenerate case in the ∀ r quantifier  
**Next action:** Two independent tracks: (a) formalize the easy tight construction A = (rN/(r+1), N] to show the bound cannot be improved; (b) attempt r = 3 by adapting Bedert's Fourier/structure argument — research-scale. Meanwhile the easiest legitimate in-repo work is the r ≤ 1 sanity lemmas.

## `erdos_137` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/137.lean:32`  
**Statement:** For k ≥ 3, can the product of k consecutive integers ever be a powerful number (every prime divisor appearing squared)?  
**Source:** erdosproblems.com/137 (state today: open); related: [ES75] Erdős–Selfridge, The product of consecutive integers is never a power  
**Statement matches intent:** yes  
**Known status:** Open. Erdős–Selfridge settled the weaker 'never a perfect power'; whether such a product can be powerful is unresolved.  
**Difficulty:** math 9/10, Lean 9/10 · **Compute:** small · **Confidence:** medium  
**Evidence:** erdosproblems.com lists it open; the statement is a clean and faithful rendering, with no junk-value or truncation issues. The k = 1 case of the sibling variant in the same file implies this for large k, showing the two are of comparable depth.  
**Next action:** Formalize the partial results first (e.g. a prime p with k < p ≤ n+k dividing exactly one factor to the first power handles all n,k outside a prime-gap-controlled range); the residual cases require genuinely new input. Also run a finite search over small n,k to confirm answer(True) is the right target.

## `erdos_137.variants.multiple_powerful_factors` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/137.lean:55`  
**Statement:** For fixed k, for all sufficiently long runs of consecutive integers and every starting point m, are there at least k distinct primes dividing the product exactly to the first power?  
**Source:** erdosproblems.com/137; [Er82c] Erdős, Miscellaneous problems in number theory, Congr. Numer. (1982)  
**Statement matches intent:** suspect — Off-by-one: the docstring says N = m(m+1)⋯(m+n) but the Lean product ∏ x ∈ Finset.Ioc m (m+n) equals (m+1)⋯(m+n) (n factors, starting at m+1). Since the statement is 'eventually in n, for all m ≥ 1', the two families of products essentially coincide, so this is a cosmetic rather than semantic defect. 'At least k primes' is correctly encoded as ∃ P : Finset ℕ with P.card = k of such primes.  
**Known status:** Open (Erdős 1982 conjecture). Note it is a strengthening of erdos_137: its k = 1 instance already says the product of n consecutive integers is not powerful for all large n.  
**Difficulty:** math 9/10, Lean 9/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** The declaration implies the eventual-n form of the main open problem in the same file, hence is at least as hard; no literature resolution known.  
**Flags:** docstring/statement off-by-one on the product range (m vs m+1 as the first factor); unused named binder hm : 0 < m is fine but the positivity is redundant given Ioc  
**Next action:** Leave open; a milestone is the k = 1 case for large n (equivalently the eventual form of erdos_137), via primes in (n, n+…] dividing exactly one factor once.

## `erdos_138` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/ErdosProblems/138.lean:83`  
**Statement:** Does the van der Waerden number W(k) (2 colours, k-term monochromatic AP) satisfy W(k)^{1/k} → ∞?  
**Source:** erdosproblems.com/138 (state today: open, $500); [Er80] Erdős, A survey of problems in combinatorial number theory, Ann. Discrete Math. (1980)  
**Statement matches intent:** yes  
**Known status:** Open and hard. Best known general lower bound is of the shape W(k) ≥ 2^k/(2ek) (LLL) with Berlekamp's W(p+1) > p·2^p only along primes; upper bounds are Gowers-tower. W(k)^{1/k} → ∞ is far beyond current technology.  
**Difficulty:** math 10/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** This is the classical 'is W(k) superexponential' question; even W(k) ≥ 4^k is unknown. Implied by variants.quotient and implies variants.dvd_two_pow, so the three open declarations in this file form a strict implication chain.  
**Flags:** docstring of the (solved) sibling variants.prime says W(p+1) ≥ p^{2^p} while the Lean statement says p·2^p — the Lean version matches Berlekamp; docstring typo, not in scope of this batch  
**Next action:** Do not attempt. If any work is done here, formalize the Berlekamp lower bound (erdos_138.variants.prime) or the vdW existence theorem instead.

## `erdos_138.variants.dvd_two_pow` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/ErdosProblems/138.lean:124`  
**Statement:** Does W(k)/2^k → ∞ for the 2-colour van der Waerden numbers?  
**Source:** erdosproblems.com/138; [Er80] Erdős, A survey of problems in combinatorial number theory (1980); [Be68] Berlekamp  
**Statement matches intent:** yes  
**Known status:** Open, the weakest of the three. Berlekamp gives W(p+1) > p·2^p, so the ratio → ∞ along k = p+1 with p prime; but transferring to all k via monotonicity loses 2^{k−p}, and even with the best prime-gap results (p ≥ k − k^{0.525}) the bound degrades to p·2^{−k^{0.525}} → 0. The best unconditional general bound W(k) ≥ 2^k/(2ek) gives ratio → 0.  
**Difficulty:** math 10/10, Lean 9/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Explicit gap analysis above: prime-only lower bounds cannot be interpolated to all k with the current toolkit; this is precisely why Erdős listed it separately from W(k)^{1/k} → ∞.  
**Flags:** declaration name 'dvd_two_pow' does not describe the statement (a quotient, not divisibility)  
**Next action:** Leave open; the concrete milestone is a Berlekamp-type construction valid for all k (not just prime+1), which alone would settle this declaration.

## `erdos_138.variants.quotient` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/ErdosProblems/138.lean:105`  
**Statement:** Does W(k+1)/W(k) → ∞ for the 2-colour van der Waerden numbers?  
**Source:** erdosproblems.com/138; [Er81] Erdős, On the combinatorial problems which I would most like to see solved, Combinatorica (1981)  
**Statement matches intent:** yes  
**Known status:** Open, and the strongest of the three open questions in the file: W(k+1)/W(k) → ∞ implies W(k)^{1/k} → ∞ (Stolz–Cesàro), which implies W(k)/2^k → ∞. Even W(k+1) > 2W(k) is unknown; monotonicity of W is essentially all that is provable today.  
**Difficulty:** math 10/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** No nontrivial lower bound on consecutive vdW ratios is known; the sibling variants.difference (W(k+1) − W(k) → ∞) is the only one of the four that has been proved, and only because it follows from W being unbounded and eventually strictly increasing.  
**Next action:** Do not attempt. A genuinely useful in-repo contribution is the monotonicity lemma W k ≤ W (k+1) and the (solved) Berlekamp/Gowers bounds.

## `erdos_14.parts.i` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/14.lean:50`  
**Statement:** For every A ⊆ ℕ, letting B be the integers with exactly one representation as a sum of two elements of A, is |{1,…,N} \ B| ≫_ε N^{1/2−ε} for every ε > 0?  
**Source:** erdosproblems.com/14 (state today: open; tags Sidon sets, additive combinatorics)  
**Statement matches intent:** yes  
**Known status:** Open. Closely tied to Erdős–Fuchs-type lower bounds for representation functions; no resolution known.  
**Difficulty:** math 9/10, Lean 9/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** Erdős problem 14 remains open per erdosproblems.com; the formalization is a faithful ≫_ε statement with the correct quantifier order and no truncation or junk-value issues.  
**Next action:** Leave open. A useful first milestone is the trivial bound (count ≫ N^{1/3} or similar) via counting the ≤ N pairs contributing to unique sums, formalized as a warm-up lemma.

## `erdos_14.parts.ii` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/14.lean:57`  
**Statement:** Is there a set A ⊆ ℕ for which the count of integers in {1,…,N} NOT uniquely representable as a sum of two elements of A is o(N^{1/2})?  
**Source:** erdosproblems.com/14 (second half of the problem)  
**Statement matches intent:** yes  
**Known status:** Open. Answering True requires an explicit near-perfect-difference-set-like construction; answering False requires the ≫ N^{1/2} lower bound (stronger than parts.i).  
**Difficulty:** math 9/10, Lean 9/10 · **Compute:** small · **Confidence:** medium  
**Evidence:** Both halves of Erdős 14 are listed open; the formal statement is faithful and non-degenerate (A = ∅ gives count = N, so a real construction is needed).  
**Next action:** Attempt a probabilistic/greedy construction (perfect difference sets modulo q give near-unique representation structure) as the candidate witness; milestone is a Lean-usable construction with a counting bound.

## `erdos_141` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/ErdosProblems/141.lean:74`  
**Statement:** For every k ≥ 3, are there k consecutive primes in arithmetic progression?  
**Source:** erdosproblems.com/141 (state today: open); Wikipedia, Primes in AP — consecutive primes in AP (CPAP records)  
**Statement matches intent:** yes  
**Known status:** Open. Existence is verified only for k ≤ 10 (CPAP-10, Toplic 1998, recorded as the solved variants.first_cases); the general statement is expected to follow from Dickson/Hardy–Littlewood-type conjectures but is unconditionally out of reach (Green–Tao gives APs of primes, not of *consecutive* primes).  
**Difficulty:** math 10/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Consecutive-prime APs of unbounded length are a well-known unconditionally hopeless target; the strongest known technology (Green–Tao, Maynard–Tao) does not control primality of the intervening integers.  
**Next action:** Do not attempt. Formalizable in-repo work is limited to small explicit examples (the file already has k = 3).

## `erdos_141.variants.eleven` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/141.lean:90`  
**Secondary category:** 6 (Computationally solvable with certificate)  
**Statement:** Are there 11 consecutive primes in arithmetic progression?  
**Source:** erdosproblems.com/141; CPAP records (largest known is CPAP-10, found 1998)  
**Statement matches intent:** yes  
**Known status:** Open but 'verifiable': it is expected to be True, and a single explicit witness would settle it. No CPAP-11 is known as of the last records I can confirm; the common difference must be divisible by every prime ≤ 11 (so 2310 | d up to small exceptions), and heuristics put the smallest example far beyond the CPAP-10 search (which was already a large distributed computation).  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** large · **Confidence:** medium  
**Evidence:** Sieving-plus-primality search; the certificate is finite and kernel-checkable in principle (Pratt/ECPP certificates for the primes, factor witnesses for the gaps), but the search space is far beyond laptop scale.  
**Flags:** needs literature check on the current CPAP record (post-cutoff results unknown)  
**Next action:** If a CPAP-11 is ever published, importing it is still nontrivial in Lean: one needs primality certificates for the 11 terms plus compositeness witnesses for every integer strictly between consecutive terms (≈ 10·d numbers). Track the CPAP record rather than searching from scratch.

## `erdos_141.variants.infinite_general_case` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/ErdosProblems/141.lean:112`  
**Statement:** For every k ≥ 3, are there infinitely many arithmetic progressions of k consecutive primes?  
**Source:** erdosproblems.com/141  
**Statement matches intent:** yes  
**Known status:** Open; strictly harder than the two sibling open declarations, which are themselves out of reach.  
**Difficulty:** math 10/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Implies both erdos_141 and variants.infinite_three, each already hopeless unconditionally.  
**Flags:** implication chain: infinite_general_case ⇒ erdos_141 and ⇒ infinite_three  
**Next action:** Do not attempt.

## `erdos_141.variants.infinite_three` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/ErdosProblems/141.lean:104`  
**Statement:** Are there infinitely many triples of consecutive primes in arithmetic progression?  
**Source:** erdosproblems.com/141 ('open even for k = 3')  
**Statement matches intent:** yes  
**Known status:** Open, of twin-prime difficulty: infinitude of CPAP-3 requires controlling the primality of p, p+d, p+2d together with the absence of primes in between, which no current sieve can do unconditionally.  
**Difficulty:** math 10/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** The problem page states this is open even for k = 3; parity-barrier-type obstructions apply.  
**Next action:** Do not attempt.

## `erdos_142` — Vacuously true / accidentally weakened (cat 4)

**File:** `FormalConjectures/ErdosProblems/142.lean:36`  
**Secondary category:** 9 (Major open problem / currently infeasible)  
**Statement:** Find an asymptotic formula (up to Theta) for r_k(N), the largest size of a subset of {1,...,N} containing no non-trivial k-term arithmetic progression.  
**Source:** https://www.erdosproblems.com/142 ($10000 Erdos prize problem)  
**Statement matches intent:** suspect — The `answer(sorry)` slot is an unconstrained function N -> R and appears on the right of `=Theta[atTop]`. Since `answer` elaborates in postpone mode (FormalConjectures/Util/Answer.lean:117), a solver may legitimately instantiate it with `fun N => (r k N : R)` and close the goal with `Asymptotics.isTheta_refl _ _`. Nothing in the statement forces the answer to be a closed form independent of r, so the formal statement does not encode 'prove an asymptotic formula'.  
**Known status:** Open. Best known for k=3: Behrend lower bound N*exp(-c*sqrt(log N)) and Kelley-Meka upper bound N*exp(-c(log N)^{1/11}); no matching asymptotic is known for any k >= 3.  
**Difficulty:** math 10/10, Lean 1/10 · **Compute:** none · **Confidence:** high  
**Evidence:** r := Set.IsAPOfLengthFree.maxCard (FormalConjecturesForMathlib/Combinatorics/AP/Basic.lean:220) is a faithful definition of r_k(N) (sSup of cards of AP-free subsets of Icc 1 N; IsAPOfLengthFree excludes only trivial length<=1 APs). The defect is purely in the answer-encoding, not in r.  
**Flags:** answer()-loophole: isTheta_refl with answer := r k closes the goal; no constraint tying the answer to an explicit/elementary function  
**Next action:** Add a well-formedness side condition to the answer slot (e.g. require the answer to be built from elementary functions, or state two separate O/Omega bounds with explicit constants) before treating this as a research target; otherwise the statement is closable by self-reference.

## `erdos_142.variants.lower` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/ErdosProblems/142.lean:44`  
**Statement:** For every k > 1, the largest k-AP-free subset of {1,...,N} has size o(N / log N).  
**Source:** https://www.erdosproblems.com/142 (Erdos' $10000 conjecture)  
**Statement matches intent:** yes  
**Known status:** Open. For k=2 trivial (r_2(N)=1). For k=3 it is already a theorem: Bloom-Sisask (2020) give r_3(N) << N/(log N)^{1+c} and Kelley-Meka (2023) give N*exp(-c(log N)^{1/11}), both o(N/log N). For k >= 4 the best bound (Leng-Sah-Sawhney 2024, N*exp(-(log log N)^{c_k}) with c_k < 1) is far from o(N/log N), so the statement is open exactly for k >= 4.  
**Difficulty:** math 10/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** No answer() slot here, so no loophole; the statement is a clean o-bound. hk : 1 < k correctly excludes the degenerate k<=1 case where r_k(N)=N (maxCard_zero/maxCard_one in AP/Basic.lean).  
**Next action:** Leave open. A realistic sub-target is to add the k=3 case as a separate `research solved` variant citing Kelley-Meka / Bloom-Sisask.

## `erdos_142.variants.three` — Vacuously true / accidentally weakened (cat 4)

**File:** `FormalConjectures/ErdosProblems/142.lean:66`  
**Secondary category:** 9 (Major open problem / currently infeasible)  
**Statement:** Find an asymptotic formula (up to Theta) for r_3(N), the largest 3-AP-free subset of {1,...,N}.  
**Source:** https://www.erdosproblems.com/142  
**Statement matches intent:** suspect — Same answer()-loophole as erdos_142: answer := `fun N => (r 3 N : R)` plus `isTheta_refl` closes the goal. Mathematically the intended question (matching upper and lower bounds for r_3) is one of the best-known open problems in additive combinatorics.  
**Known status:** Open: Behrend's N*exp(-c*sqrt(log N)) lower bound vs Kelley-Meka's N*exp(-c(log N)^{1/11}) upper bound; no Theta-formula known.  
**Difficulty:** math 10/10, Lean 1/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Identical structure to erdos_142 with k fixed to 3.  
**Flags:** answer()-loophole: isTheta_refl  
**Next action:** Constrain the answer slot (explicit closed form) or split into a stated conjecture such as r_3(N) = N^{1-o(1)}-type bounds; then re-audit.

## `erdos_142.variants.upper` — Vacuously true / accidentally weakened (cat 4)

**File:** `FormalConjectures/ErdosProblems/142.lean:54`  
**Secondary category:** 2 (Trivially or easily solvable)  
**Statement:** Find a function f_k with r_k(N) = O(f_k(N)).  
**Source:** https://www.erdosproblems.com/142  
**Statement matches intent:** no — Completely degenerate as formalised: the goal is `(fun N => (r k N : R)) =O[atTop] (answer(sorry) : N -> R)` with no further constraint on the answer. Instantiating answer := `fun N => (r k N : R)` and applying `Asymptotics.isBigO_refl _ _` proves it in one line. Unlike erdos_160.better_upper there is no second conjunct forcing the bound to be an improvement, so the statement carries no mathematical content.  
**Known status:** The intended problem (good explicit upper bounds for r_k) is open for k >= 3; the formal statement is vacuously closable.  
**Difficulty:** math 9/10, Lean 1/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Answer.lean default mode is `.postpone` (line 117), so the answer term is elaborated in the local context and may mention `k` and even `r`; nothing rejects self-referential answers.  
**Flags:** major answer()-loophole: one-line proof by isBigO_refl; statement weaker than intended (different problem)  
**Next action:** Restate as e.g. `exists f, r_k =O f and f =o (known bound)` mirroring erdos_160.better_upper, or fix an explicit target bound; then re-audit.

## `erdos_143.parts.i` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/143.lean:44`  
**Statement:** If A ⊆ (1,∞) is infinite with |kx − y| ≥ 1 for all distinct x,y ∈ A and all integers k ≥ 1, must liminf_{x→∞} |A ∩ [1,x]|/x = 0?  
**Source:** erdosproblems.com/143 (state today: open, $500; tagged primitive sets)  
**Statement matches intent:** yes  
**Known status:** Open ($500). This is the real-valued 'primitive-like set' problem; no resolution known.  
**Difficulty:** math 8/10, Lean 8/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** erdosproblems.com lists 143 as open; the formalization has no truncation/junk-value defects and the degenerate cases (finite A) are excluded by Set.Infinite A.  
**Next action:** Leave open; a reasonable first milestone is the easy bound limsup |A ∩ [1,x]|/x ≤ 1 and the analysis of the k-dilate structure (each x ∈ A forbids a neighbourhood of every kx), which is also the natural route to parts.ii.

## `erdos_143.parts.ii` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/143.lean:55`  
**Statement:** For the same well-separated sets A ⊆ (1,∞), is Σ_{x∈A} 1/(x log x) finite?  
**Source:** erdosproblems.com/143 (second alternative question on the page)  
**Statement matches intent:** yes  
**Known status:** Open; the Erdős–Sárközy/Behrend-type analogue for primitive sets (Erdős's theorem Σ 1/(n log n) < ∞ for primitive integer sets) suggests the intended proof route, but the real-valued dilate condition is weaker than divisibility.  
**Difficulty:** math 8/10, Lean 8/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** Listed open on erdosproblems.com; formalization is faithful and non-vacuous (WellSeparatedSet is satisfiable, e.g. by lacunary sets).  
**Flags:** asserted as a bare theorem with no answer() — unprovable if the truth value turns out to be False  
**Next action:** Try to adapt Erdős's 1935 primitive-set argument (assign to each x ∈ A the multiples interval and use a density/measure argument on the dilates kx) to the real setting; milestone: a Behrend-type inequality for well-separated real sets.

## `erdos_145` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/145.lean:45`  
**Statement:** For the increasing sequence s_1 < s_2 < … of squarefree numbers and any α ≥ 0, does (1/x)·Σ_{s_n ≤ x}(s_{n+1} − s_n)^α converge as x → ∞?  
**Source:** erdosproblems.com/145 (state today: open); [Er51] Erdős (α ≤ 2), [Ho73] Hooley (α ≤ 3), [GHH97] Greaves–Harman–Huxley (α ≤ 11/3)  
**Statement matches intent:** yes  
**Known status:** Open for α > 11/3. Known for 0 ≤ α ≤ 11/3 (Greaves–Harman–Huxley 1997), with Erdős (α ≤ 2) and Hooley (α ≤ 3) as earlier steps; all three are recorded as solved-but-sorry variants in the same file.  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** The file itself records three successive partial results ending at α ≤ 11/3, and erdosproblems.com still lists the problem open, so only large α remains; the formalization is faithful and free of coercion defects.  
**Flags:** needs literature check: whether the admissible range beyond 11/3 has been extended since 1997  
**Next action:** The highest-value in-repo work is formalizing the α ≤ 2 case (Erdős 1951), which is elementary sieve counting; the general α is a research problem tied to gaps between squarefree numbers (max gap ≍ x^{1/5} territory). Estimate: large for the general case, medium for α ≤ 2.

## `erdos_15` — Vacuously true / accidentally weakened (cat 4)

**File:** `FormalConjectures/ErdosProblems/15.lean:36`  
**Secondary category:** 2 (Trivially or easily solvable)  
**Statement:** Does the alternating series sum_{n>=1} (-1)^n n / p_n converge, where p_n is the n-th prime?  
**Source:** https://www.erdosproblems.com/15  
**Statement matches intent:** no — Mathlib's `Summable f` means the NET of finite partial sums converges (unconditional summability), which for a real/rational series is equivalent to absolute summability. The Erdos question is about conditional convergence of the ordered partial sums sum_{n<=N}. Since sum_n n/p_n diverges (n/p_n ~ 1/log n), `Summable` is provably FALSE here, so the formal statement collapses to `answer := False` and is decidable today with elementary Mathlib input, while the actual open question is untouched. Additionally the series is stated in Q, where the limit of a convergent real series need not even exist.  
**Known status:** The intended problem is open (erdosproblems.com/15 lists it open). The formal statement is refutable: the answer slot must be False and the content is ¬Summable.  
**Difficulty:** math 8/10, Lean 4/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Mathlib `Summable f := exists a, HasSum f a` and `HasSum f a := Tendsto (fun s : Finset i => sum over s) atTop (nhds a)` — order-independent, hence never satisfied by a conditionally convergent series. The docstring explicitly asks about convergence, not summability.  
**Flags:** major semantic mismatch: Summable (unconditional) used for a conditional-convergence question; series stated over Q, whose completion issues make even the intended reading wrong; as stated the answer is forced to False  
**Next action:** Rewrite as `answer(sorry) <-> exists L : R, Tendsto (fun N => sum_{k in Finset.range N} (-1)^(k+1)*(k+1)/(nth Prime k)) atTop (nhds L)` over R (not Q). Meanwhile the current statement can be discharged: |f k| = (k+1)/p_k >= 1/p_k, and Mathlib's `Nat.Primes.not_summable_indicator_one_div_natCast` (sum of prime reciprocals diverges) plus `Real.summable_abs_iff` gives ¬Summable; a Q-summable family would also be R-summable via the continuous embedding.

## `erdos_153` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/153.lean:44`  
**Statement:** For a finite Sidon set A with sumset A+A = {s_1<...<s_t}, does the mean square gap (1/t) sum_{1<=i<t}(s_{i+1}-s_i)^2 tend to infinity as |A| -> infinity?  
**Source:** https://www.erdosproblems.com/153; [ESS94] Erdos-Sarkozy-Sos, On sum sets of Sidon sets I, J. Number Theory 47 (1994) 329-347  
**Statement matches intent:** yes  
**Known status:** Open per erdosproblems.com. Cauchy-Schwarz only gives the trivial bound (1/t)sum(Delta)^2 >= ((s_t-s_1)/t)^2, which is O(1) for perfect-difference-set Sidon sets, so the question has real content.  
**Difficulty:** math 8/10, Lean 8/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** Read def f (153.lean:37-39) carefully: (A.1 + A) is the pointwise sumset Finset, orderIsoOfFin rfl gives the increasing enumeration, and s(i) > s(i-1) so any Nat-subtraction is non-truncating.  
**Next action:** First milestone: formalise the trivial Cauchy-Schwarz lower bound and the t ~ n^2/2 count for Sidon sets, then look for the ESS94 partial results.

## `erdos_155` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/155.lean:41`  
**Statement:** Let F(N) be the size of the largest Sidon subset of {1,...,N}. Is it true that for each fixed k >= 1, F(N+k) <= F(N)+1 for all sufficiently large N?  
**Source:** https://www.erdosproblems.com/155  
**Statement matches intent:** yes  
**Known status:** Open per erdosproblems.com. F(N) ~ sqrt(N) (Erdos-Turan / Singer), so heuristically F increases by 1 only every ~2sqrt(N) steps and two jumps within k consecutive integers should not recur; no proof known.  
**Difficulty:** math 8/10, Lean 8/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** F = Finset.maxSidonSubsetCard (Icc 1 N) (FormalConjecturesForMathlib/Combinatorics/Basic.lean:153) = sup of cards of Sidon subsets — correct. No degenerate-object or truncation issues (F N + 1 is in N and both sides are cardinalities).  
**Flags:** needs literature check: exact wording of the k-quantifier on erdosproblems.com/155 not verified  
**Next action:** Formalise F monotone and F(N+1) <= F(N)+1 as API lemmas first (easy), then attempt k=2 via structure of near-extremal Sidon sets.

## `erdos_156` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/156.lean:45`  
**Statement:** Is there, for every N, a maximal (i.e. non-extendable) Sidon subset of {1,...,N} of size O(N^{1/3})?  
**Source:** https://www.erdosproblems.com/156; [ESS94]; [Ru98b] Ruzsa, A small maximal Sidon set, Ramanujan J. 2 (1998) 55-58  
**Statement matches intent:** yes  
**Known status:** Open. Greedy gives >> N^{1/3} (stated as a solved variant in the file), Ruzsa gives a maximal Sidon set of size << (N log N)^{1/3}; closing the log^{1/3} gap is the question.  
**Difficulty:** math 8/10, Lean 8/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** Definitions read in full; the two `research solved` variants in the same file correctly bracket the open question.  
**Next action:** Medium-term: formalise Ruzsa's probabilistic construction as the `ruzsa_upper_bound` variant first; the N^{1/3} question stays open.

## `erdos_158` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/158.lean:55`  
**Statement:** Must every infinite B_2[2] set A (every n has at most 2 representations n=a+a' with a<=a') satisfy liminf_N |A ∩ [0,N)| N^{-1/2} = 0?  
**Source:** https://www.erdosproblems.com/158; [ESS94]  
**Statement matches intent:** yes  
**Known status:** Open. The Sidon (B_2[1]) analogue is proved in [ESS94] and is present in the file as `erdos_158.variants.isSidon'` / `isSidon` (the latter already has a complete Lean derivation from the former).  
**Difficulty:** math 8/10, Lean 8/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** `- 1 / 2` parses as -(1/2); the exponent is correct. The ENNReal formulation used in the solved variants shows the authors were aware of liminf junk-value issues.  
**Next action:** Attempt to push the [ESS94] Sidon argument (liminf |A ∩ [1,N]| N^{-1/2} (log N)^{1/2} < infinity) to B_2[2]; first milestone is formalising isSidon'.

## `erdos_160.better_lower` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/160.lean:64`  
**Statement:** Improve the lower bound h(n) >> exp(c (log n)^{1/12}) for the same colouring function h.  
**Source:** https://www.erdosproblems.com/160; https://mathoverflow.net/q/410808 (Zachary Hunter) + Kelley-Meka arXiv:2302.05537  
**Statement matches intent:** suspect — The second conjunct is malformed: `forall c > 0, (exp(c log n^{1/12}) =O h -> forall c > 0, exp(c log n^{1/12}) =o lower_bound)` shadows the binder c, so it is logically equivalent to `(exists c > 0, exp(c L) =O h) -> (forall c > 0, exp(c L) =o lower_bound)`. The inner hypothesis is then unusable for the intended purpose (one only ever gets it for the single outer c) and the first conjunct `lower_bound =O h` sits outside the implication. The statement still requires a real improvement (so it is not trivialised), but the intended meaning is obscured and should be rewritten.  
**Known status:** Open; only the exp(c(log n)^{1/12}) lower bound is known.  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** Checked exploitability: answer := h makes conjunct 1 trivial but leaves `forall c>0, exp(c L) = o(h)` unprovable from the single available hypothesis instance; answer := exp((log n)^{1/6}) makes conjunct 2 trivial but conjunct 1 becomes an unproved improvement. So no loophole, only a specification defect.  
**Flags:** shadowed `forall c > 0` binder makes the implication vestigial; spec defect (minor): statement should be a plain conjunction  
**Next action:** Rewrite as `exists lb, lb =O h and (forall c>0, exp(c (log n)^{1/12}) =o lb)` with no vestigial implication, then re-audit.

## `erdos_160.better_upper` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/160.lean:54`  
**Statement:** Improve the upper bound h(n) << n^{2/3}, where h(n) is the least number of colours needed to colour {1,...,n} so that every 4-term AP receives at least 3 distinct colours.  
**Source:** https://www.erdosproblems.com/160; MathOverflow answer https://mathoverflow.net/a/410815 (leechlattice)  
**Statement matches intent:** yes  
**Known status:** Open. Known n^{2/3} upper bound (MathOverflow) and exp(c (log n)^{1/12}) lower bound (Hunter + Kelley-Meka), both stated as solved variants in the file.  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** h is defined as sInf over k of colourings Icc 1 n -> Fin k such that every 4-term AP inside Icc 1 n gets >= 3 colours; the set is nonempty (k = n works) so sInf is not junk.  
**Flags:** meta-statement ('find a better bound') — solvable only by a genuine improvement, so acceptable, but not a fixed mathematical proposition  
**Next action:** Research-level. A concrete first milestone is formalising the n^{2/3} colouring (erdos_160.known_upper) so that any improvement can be stated against a proved baseline.

## `erdos_168.parts.i` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/168.lean:89`  
**Statement:** Determine lim_{N->infinity} F(N)/N, where F(N) is the largest subset of {1,...,N} containing no n with n, 2n, 3n all present.  
**Source:** https://www.erdosproblems.com/168; limit existence due to Graham-Spencer-Witsenhausen  
**Statement matches intent:** yes  
**Known status:** Open: the limit is known to exist but its exact value is not known (rigorous numerical bounds only).  
**Difficulty:** math 8/10, Lean 8/10 · **Compute:** small · **Confidence:** medium  
**Evidence:** F N is a Finset.sup over a decidable filter, so small values are computable by `decide`/`rfl` (F_0..F_3 already are).  
**Flags:** answer()-loophole (mild): answer := limUnder ... reduces the statement to limit existence  
**Next action:** Compute F(N) for moderate N via the existing decidable definition to pin down numeric bounds, and formalise the GSW existence proof (erdos_168.variants.limit_exists) as the enabling step.

## `erdos_168.parts.ii` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/ErdosProblems/168.lean:95`  
**Statement:** Is lim F(N)/N irrational, for the same n,2n,3n-free maximal density F?  
**Source:** https://www.erdosproblems.com/168  
**Statement matches intent:** suspect — Uses `Filter.atTop.limsup (fun N => F N / N)` rather than the limit. This is semantically harmless because the limit is known to exist (so limsup = lim, and F N / N in [0,1] so no limsup junk value), but the repo has not proved existence (erdos_168.variants.limit_exists is sorry), so the two formulations are not yet interchangeable in Lean.  
**Known status:** Open, and no avenue is known: the constant has no known closed form, so its irrationality is out of reach of current techniques.  
**Difficulty:** math 9/10, Lean 10/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** Irrationality proofs require a closed form or an effective Diophantine handle on the constant; none exists here.  
**Flags:** limsup vs lim mismatch (harmless mathematically, not yet bridged in Lean)  
**Next action:** Do not attempt directly. Prerequisite: determine or characterise the constant (parts.i).

## `erdos_17` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/17.lean:38`  
**Statement:** Are there infinitely many cluster primes, i.e. primes p such that every even n <= p-3 is a difference of two primes <= p?  
**Source:** https://www.erdosproblems.com/17; [BES99] Blecksmith-Erdos-Selfridge, Cluster primes, Amer. Math. Monthly 106 (1999) 43-48; [El03] Elsholtz, Acta Arith. 109 (2003) 281-284  
**Statement matches intent:** yes  
**Known status:** Open. Density results only: BES99 give pi^C(x) << x (log x)^{-A}, Elsholtz gives x exp(-c (log log x)^2); infinitude (or finiteness) is unknown.  
**Difficulty:** math 9/10, Lean 9/10 · **Compute:** none · **Confidence:** high  
**Evidence:** The 97 test theorem is a strong sanity check on the definition; convention for small p (2 and 3 vacuously/trivially cluster) matches the standard one.  
**Next action:** Leave open. The two `research solved` variants (BES99, Elsholtz upper bounds) are the realistic formalisation targets.

## `erdos170` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/170.lean:57`  
**Statement:** Determine lim F(N)/sqrt(N), where F(N) is the least number of marks on a ruler of length N that measures every integer distance 1..N (restricted difference basis).  
**Source:** https://www.erdosproblems.com/170; [ErGa48] Erdos-Gal; [Le56] Leech; [Wi63] Wichmann  
**Statement matches intent:** yes  
**Known status:** Open: the limit exists (Erdos-Gal 1948) and lies in [1.5578..., sqrt 3] (Leech lower bound, Wichmann upper bound); the exact constant is unknown.  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** small · **Confidence:** high  
**Evidence:** F N is computable for small N by exhaustive search over subsets of {0,...,N} (though exponential); the numeric bracket 1.5578..1.7320 is a long-standing gap.  
**Flags:** answer()-loophole (mild): answer := limUnder ... reduces the statement to limit existence  
**Next action:** Formalise Erdos-Gal existence and the Wichmann construction first (erdos170.existing_bounds); determining the constant is research-scale.

## `erdos_172` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/ErdosProblems/172.lean:31`  
**Statement:** In any finite colouring of N, are there arbitrarily large finite sets A all of whose sums and products of distinct elements have the same colour?  
**Source:** https://www.erdosproblems.com/172  
**Statement matches intent:** suspect — The inner quantifier ranges over every nonempty S : Finset A, including singletons, so the statement also forces every element of A itself to have colour c (A monochromatic). The usual reading of 'sums and products of distinct elements' takes |S| >= 2. This is a strengthening of the conjecture: if the strengthened form is false while the standard one is true, the forced `answer` value flips. Allowing 0,1 in A is harmless since A is existentially quantified.  
**Known status:** Open. Related progress: Bowen (2022) and Bowen-Sabok obtained monochromatic {x,y,x+y,xy} for 2-colourings of N and of Q, but the arbitrarily-large-A version for arbitrary finite colourings is wide open.  
**Difficulty:** math 10/10, Lean 10/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** `forall (S : Finset A), S.Nonempty -> ...` with S = {x} gives color x = c for all x in A.  
**Flags:** singleton subsets included: silently strengthens the conjecture to 'A monochromatic'; needs literature check on the canonical wording  
**Next action:** Restate with `2 <= S.card` (or add the monochromatic-A requirement explicitly in the docstring) so the formal and intended statements agree; leave the mathematics open.

## `erdos_18a` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/18.lean:219`  
**Statement:** Are there infinitely many practical numbers m with h(m) < (log log m)^{O(1)}, where h(m) is the max over 1<=k<=m of the least number of distinct divisors of m summing to k?  
**Source:** https://www.erdosproblems.com/18; [ErGr80]; [Vo85] Vose, Egyptian fractions, Bull. LMS 17 (1985) 21-24  
**Statement matches intent:** yes  
**Known status:** Open. Vose proved the weaker h(m) << (log m)^{1/2} infinitely often (stated in the file as erdos_18_vose); (log log m)^{O(1)} is far stronger.  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** Read the definition and all four numeric test theorems; no truncation, division-by-zero or quantifier defects.  
**Next action:** Formalise Vose's construction first (erdos_18_vose); the (log log)^{O(1)} strengthening stays open.

## `erdos_18b` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/18.lean:230`  
**Statement:** Is h(n!) < n^{o(1)}, i.e. for every eps>0 is h(n!) < n^eps for large n?  
**Source:** https://www.erdosproblems.com/18  
**Statement matches intent:** yes  
**Known status:** Open. Only Erdos' h(n!) < n is known (erdos_18_upper_bound in the file, still sorry).  
**Difficulty:** math 8/10, Lean 8/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** factorial_isPractical is fully proved in-file (lines 168-208), removing the main degeneracy risk.  
**Next action:** First milestone: formalise the elementary h(n!) < n bound; then attack n^{o(1)} via greedy/Egyptian-fraction arguments.

## `erdos_18c` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/18.lean:241`  
**Statement:** Is h(n!) < (log n)^{O(1)}? (Erdos offered $250.)  
**Source:** https://www.erdosproblems.com/18 ($250 problem)  
**Statement matches intent:** yes  
**Known status:** Open, $250 prize; nothing beyond h(n!) < n is known.  
**Difficulty:** math 9/10, Lean 9/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** Since log log(n!) ~ log n, 18c is the strongest of the three conjectures in the file.  
**Next action:** Same as 18b; treat as the hardest of the three.

## `erdos_184` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/ErdosProblems/184.lean:52`  
**Statement:** Can the edges of every n-vertex graph be decomposed into O(n) edge-disjoint cycles and single edges? (Erdos-Gallai cycle decomposition conjecture.)  
**Source:** https://www.erdosproblems.com/184; [Er71]; [BM22] Bucic-Montgomery arXiv:2211.07689; [CFS14] Conlon-Fox-Sudakov  
**Statement matches intent:** yes  
**Known status:** Open (erdosproblems.com/184 still open today). Best known O(n log* n) (Bucic-Montgomery 2022/STOC 2023); lower bound (1+c)n from K_{3,n-3}.  
**Difficulty:** math 9/10, Lean 10/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** Statement quantifies over all Fintype V in one universe with a single f; no loophole (f must be O(n) and work for every graph on n vertices).  
**Flags:** needs literature check: arXiv:2509.01901 may improve the decomposition bound  
**Next action:** Do not attempt the full conjecture. Realistic: formalise the Erdos-Gallai O(n log n) bound (variants.n_log_n) or the K_{3,n-3} lower bound. Also check arXiv:2509.01901 ('Tight Bounds for Cycle-Edge Decompositions and Covers') for whether it changes the state of the art.

## `erdos_184.variants.covering` — Already solved externally (cat 1)

**File:** `FormalConjectures/ErdosProblems/184.lean:95`  
**Secondary category:** 5 (Solved mathematically, not yet formalized)  
**Statement:** Can the edges of every n-vertex graph be COVERED (not necessarily disjointly) by at most n-1 cycles and single edges?  
**Source:** Pyber, L., 'An Erdos-Gallai conjecture', Combinatorica 5 (1985) 67-79 — https://link.springer.com/article/10.1007/BF02579444 ; see also arXiv:2509.01901 'Tight Bounds for Cycle-Edge Decompositions and Covers'  
**Statement matches intent:** yes  
**Known status:** SOLVED EXTERNALLY (positively) by Pyber in 1985 — the covering version of the Erdos-Gallai conjecture is a theorem; only the edge-disjoint DECOMPOSITION version (erdos_184 above) remains open. The file nevertheless tags this `@[category research open]`, which is a mislabel.  
**Difficulty:** math 6/10, Lean 9/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** Web search confirmed: 'In 1985, Pyber proved the covering version of the Erdos-Gallai conjecture, showing that the edges of any n-vertex graph can be covered with n-1 cycles and edges', contrasted explicitly with the still-open decomposition version (best bound O(n log* n)).  
**Flags:** MISLABELLED: tagged research open although the underlying question is a 1985 theorem; answer slot should be True  
**Next action:** Reclassify to `@[category research solved]` with answer(True) and the Pyber 1985 citation. Formalising Pyber's proof in Lean is a substantial project (large), so keep the `sorry` but fix the category and docstring.

## `erdos_188` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/188.lean:44`  
**Statement:** What is the least k such that the plane can be 2-coloured with no two red points at distance 1 and no k-term arithmetic progression of blue points with common difference of length 1?  
**Source:** https://www.erdosproblems.com/188; [EGMRSS75] Euclidean Ramsey theorems II; [Ts17] Tsaturian, Electron. J. Combin. 24 (2017)  
**Statement matches intent:** yes  
**Known status:** Open: the file's own solved variants record only 5 <= k <= 10^7; the exact minimum is unknown.  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** IsLeast s (answer) forces both membership and minimality, so no one-sided loophole; the answer is a natural number that is genuinely unknown.  
**Flags:** needs literature check: whether [Ts17] narrowed the 5 <= k <= 10^7 window  
**Next action:** Formalise the two bracketing variants (nonempty, estimate) first; determining the exact k is research-scale and would need a fresh construction plus a matching Ramsey-type lower bound.

## `erdos_189.variants.parallelogram` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/189.lean:77`  
**Statement:** Is there a finite colouring of the plane in which no colour class contains the vertices of a parallelogram of every positive area?  
**Source:** https://www.erdosproblems.com/189; Kovac, 'Coloring and density theorems for configurations of a given volume', arXiv:2309.09973 / Proc. LMS (2026) — solves the RECTANGLE case  
**Statement matches intent:** suspect — The theorem commits to one direction (`¬ Erdos189For ...`) of a question the docstring itself calls open, instead of using the repo's `answer(sorry) <->` convention as the solved rectangle case (erdos_189) does. If the parallelogram question turns out to have the opposite answer, this `research open` theorem is simply false. Otherwise the encoding is faithful: convex ccw quadrilateral with ab || cd and ad || bc, area |ab|*|bc|*sin(angle abc).  
**Known status:** Open. Kovac's 25-colour Jordan-measurable colouring kills rectangles of unit area (Erdos 189 proper, formalised in Lean by Alexeev-Kovac and already marked solved in this file), but a parallelogram is a strictly more general configuration and the parallelogram version is reported as still unsolved.  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** Web search: Kovac's result is stated for rectangles of unit area; the parallelogram analogue is explicitly described as still open. Note erdosproblems.com lists problem 189 itself as 'disproved (Lean)', which refers to the rectangle statement (erdos_189 in this file), not to this variant.  
**Flags:** one-directional statement of an open question (no answer() slot) — falsifiable if the answer is positive; needs literature check: post-2025 extensions of Kovac's construction  
**Next action:** Change to `answer(sorry) <-> Erdos189For ...` to match the repo convention, then investigate whether Kovac's invariant-based construction extends from rectangles to parallelograms (the natural first attempt).

## `erdos_193` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/193.lean:47`  
**Statement:** If S is a finite subset of Z^3 and a_1,a_2,... is an infinite walk with all steps a_{i+1}-a_i in S, must the walk visit three collinear points?  
**Source:** https://www.erdosproblems.com/193; [GeRa79] Gerver-Ramsey, On certain sequences of lattice points, Pacific J. Math. 83 (1979) 357-363  
**Statement matches intent:** yes  
**Known status:** Open for Z^3. Gerver-Ramsey proved the Z^2 case (present as erdos_193_z2) and constructed a Z^3 walk with no 4 collinear points, which does not settle the 3-point question.  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** Read IsSWalk and HasCollinearTriple in full; the only quantifier subtlety (S may be empty, making the walk hypothesis unsatisfiable) is vacuous and harmless.  
**Next action:** Formalise the Z^2 case (erdos_193_z2) as the accessible target; Z^3 remains open.

## `erdos_195` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/195.lean:36`  
**Statement:** What is the largest k such that every permutation of the integers Z must contain a monotone k-term arithmetic progression (indices increasing, values in AP)?  
**Source:** erdosproblems.com/195; Geneson, Discrete Math. (2019) 1489-1491; Adenwalla, arXiv:2211.04451 (2022)  
**Statement matches intent:** yes  
**Known status:** erdosproblems.com: open. Known: every permutation of Z contains a monotone 3-AP; Geneson gives sSup ≤ 5, Adenwalla improves to sSup ≤ 4. So the answer is 3 or 4 and is undecided. No PR in DomTheDeveloper/formal-conjectures and no campaign entry touches 195.  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Read whole file plus FormalConjecturesForMathlib/Combinatorics/AP/Basic.lean:248 (HasMonotoneAP) and List.IsAPOfLengthWith at line 51. No duplicate statement elsewhere in FormalConjectures/. campaign_register.json has no entry for any ErdosProblems/195-243 file.  
**Flags:** answer(sorry) is a numeric answer, so closing it requires knowing the exact value (3 or 4), not just a bound  
**Next action:** Leave open. The realistic first milestone is formalizing Adenwalla's explicit permutation of Z with no monotone 5-term AP (gives the ≤ 4 variant); resolving erdos_195 itself needs the missing 3-vs-4 case from the literature.

## `erdos_196` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/196.lean:27`  
**Statement:** Must every permutation of the natural numbers contain a monotone 4-term arithmetic progression?  
**Source:** erdosproblems.com/196 (Davis-Entringer-Graham-Simmons 1977)  
**Statement matches intent:** yes  
**Known status:** erdosproblems.com: open. Known: every permutation of N contains a monotone 3-AP, and there is a permutation of N with no monotone 5-term AP (DEGS 1977); the 4-term case is exactly the open question. No fork PR or campaign targets this file.  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** none · **Confidence:** high  
**Evidence:** answer(sorry) ↔ ∀ f : ℕ ≃ ℕ, HasMonotoneAP f 4 is a faithful rendering; injectivity of the Equiv rules out the d = 0 degeneracy allowed by List.IsAPOfLengthWith.  
**Next action:** Leave open (cat 8). A tractable side project is formalizing the DEGS permutation avoiding monotone 5-APs as a new variant; that does not close erdos_196.

## `erdos_197` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/197.lean:33`  
**Statement:** Can N be split into two complementary sets A and B such that each can be enumerated (permuted) so as to contain no monotone 3-term arithmetic progression?  
**Source:** erdosproblems.com/197 (Davis-Entringer-Graham-Simmons)  
**Statement matches intent:** yes  
**Known status:** erdosproblems.com: open. Contrast with the single-permutation case, where every permutation of N contains a monotone 3-AP; the question is whether a 2-colouring evades this. No fork PR / campaign entry.  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** File read in full; HasMonotoneAP semantics checked against FormalConjecturesForMathlib/Combinatorics/AP/Basic.lean.  
**Next action:** Leave open. If one believes the answer is yes, the formal path is an explicit interleaved construction of A, B plus enumerations, with a 3-AP-free invariant; that is real research.

## `erdos_20` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/ErdosProblems/20.lean:50`  
**Statement:** Sunflower conjecture: is the minimum size f(n,k) forcing a k-sunflower in an n-uniform set family bounded by c_k^n for some constant c_k?  
**Source:** erdosproblems.com/20 ($1000 prize); Erdős-Rado, J. London Math. Soc. 35 (1960) 85-90  
**Statement matches intent:** yes  
**Known status:** Famous open problem with a $1000 Erdős prize. Best known: Alweiss-Lovett-Wu-Zhang (2019/2021) give f(n,k) ≤ (C k log n)^n, i.e. still n^{o(n)} away from c_k^n. Duplicate entry point FormalConjectures/Wikipedia/ErdosRadoSunflowerConjecture.lean merely re-references this file (no proof). No fork PR / campaign entry.  
**Difficulty:** math 10/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Checked the noncomputable def f and FormalConjecturesForMathlib/Combinatorics/SetFamily/Sunflower.lean (IsSunflower = F.Pairwise (A ∩ B = S)); the sInf set is upward closed so sInf is the true threshold.  
**Flags:** Set.ncard = 0 for infinite families hides infinite F from the definition of f (value unaffected)  
**Next action:** Do not attempt. At most, formalize the Erdős-Rado (k-1)^n n! bound (the sibling variant erdos_20.variants.erdos_rado_bound), which is a genuine but standard double-counting induction.

## `erdos_200` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/200.lean:38`  
**Statement:** Is the length of the longest arithmetic progression consisting of primes inside {1,...,N} of size o(log N)?  
**Source:** erdosproblems.com/200  
**Statement matches intent:** yes  
**Known status:** erdosproblems.com: open. The (1+o(1)) log N upper bound (recorded as erdos_200.variants.upper) follows from the fact that the common difference must be divisible by every prime below the length, plus PNT. Improving log N to o(log N) is unresolved. No fork PR / campaign entry.  
**Difficulty:** math 9/10, Lean 9/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** Definition longestPrimeArithmeticProgressions checked against Set.IsAPOfLengthWith (ENat.card s = l ∧ s = {a + n•d | n < l}) in FormalConjecturesForMathlib/Combinatorics/AP/Basic.lean.  
**Next action:** Leave open (cat 8). A worthwhile intermediate formalization is variants.upper: d must be divisible by the primorial of the length, so length ≪ log N.

## `erdos_203` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/203.lean:31`  
**Secondary category:** 6 (Computationally solvable with certificate)  
**Statement:** Is there an integer m coprime to 6 such that 2^k·3^l·m + 1 is composite for all k, l ≥ 0?  
**Source:** erdosproblems.com/203  
**Statement matches intent:** yes  
**Known status:** erdosproblems.com: open. The 1-parameter analogue (2^k·m + 1 never prime) is solved by Sierpiński numbers via a covering system; the 2-parameter version needs a covering of the (k,l) exponent lattice and is not known. No fork PR / campaign entry.  
**Difficulty:** math 8/10, Lean 8/10 · **Compute:** medium · **Confidence:** medium  
**Evidence:** Statement is a bare existential over m with no hidden weakening; the whole difficulty is the mathematics of covering systems.  
**Flags:** needs literature check on whether a 2-dimensional covering construction is already known  
**Next action:** Leave open, but this is the most computationally attackable item in the batch: search for a finite covering of Z² of exponent-pairs by pairs (order of 2 mod p, order of 3 mod p) and lift by CRT. If found, the Lean certificate is a finite `decide`-style check plus a CRT argument; encode as `∀ k l, ∃ p ∈ S, p ∣ 2^k 3^l m + 1 ∧ p < 2^k 3^l m + 1`.

## `erdos_208.parts.i` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/208.lean:37`  
**Statement:** For the increasing sequence s_n of squarefree numbers, is s_{n+1} - s_n bounded by O_ε(s_n^ε) for every ε > 0?  
**Source:** erdosproblems.com/208; Erdős, Math. Mag. 52 (1979) 67-70  
**Statement matches intent:** yes  
**Known status:** erdosproblems.com: open. Best known: Filaseta-Trifonov give s_{n+1} - s_n ≪ s_n^{1/5} log s_n; getting every ε > 0 is open. No fork PR / campaign entry.  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Whole file read; erdos208.s = Nat.nth Squarefree checked.  
**Next action:** Leave open (cat 8). Formalizing even the classical O(x^{1/3}) gap bound would be a substantial standalone Mathlib-level project (squarefree sieve + Roth/Halász-type counting).

## `erdos_208.parts.ii` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/ErdosProblems/208.lean:45`  
**Statement:** Is the gap between consecutive squarefree numbers at most (1+o(1))·(π²/6)·log(s_n)/log log(s_n)?  
**Source:** erdosproblems.com/208; Erdős, Math. Mag. 52 (1979) 67-70  
**Statement matches intent:** yes  
**Known status:** erdosproblems.com: open. This is a sharp maximal-gap conjecture with the exact constant π²/6 = 1/ζ(2)^{-1}; nothing anywhere close is known (best upper bounds are power-of-s_n, cf. parts.i). No fork PR / campaign entry.  
**Difficulty:** math 10/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Statement compared with the Erdős 1979 formulation quoted in the module docstring.  
**Next action:** Do not attempt. Strictly harder than parts.i.

## `erdos_208.variants.log_bound` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/ErdosProblems/208.lean:55`  
**Statement:** Are the gaps between consecutive squarefree numbers O(log s_n)?  
**Source:** erdosproblems.com/208; [Er79] Erdős, Some unconventional problems in number theory, Math. Mag. (1979) 67-70  
**Statement matches intent:** suspect — The file's own docstring records that Erdős proposed this bound but was 'very doubtful' about it. It is nevertheless asserted here as a bare theorem (no answer(sorry) wrapper), so the repo is committing to a direction the source explicitly doubts. If the bound is false — which is the source's own expectation — this declaration can never be closed and should be restated as `answer(sorry) ↔ ...` like parts.i/ii.  
**Known status:** Open in both directions. Known: gaps of size ≫ log s_n / log log s_n occur infinitely often (Erdős), which is consistent with but does not contradict an O(log) bound; and no unconditional o(s^{1/5}) improvement is close to log. No fork PR / campaign entry.  
**Difficulty:** math 9/10, Lean 10/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** Docstring at 208.lean:51 says Erdős 'is very doubtful'; the declaration at line 56-57 asserts the bound unconditionally rather than asking for its truth value.  
**Flags:** directional risk: statement asserts a bound its own cited source doubts; inconsistent encoding with parts.i/parts.ii in the same file (those use answer(sorry) ↔)  
**Next action:** Recommend a statement fix upstream: convert to `answer(sorry) ↔ (fun n ↦ ...) =O[atTop] fun n ↦ log (s n)` so that a negative resolution is expressible. Then leave open.

## `erdos_212` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/212.lean:31`  
**Statement:** Erdős-Ulam problem: is there a dense subset of the plane all of whose pairwise distances are rational?  
**Source:** erdosproblems.com/212  
**Statement matches intent:** yes  
**Known status:** erdosproblems.com: open unconditionally. Conditional resolutions exist: Shaffaf and (independently) Tao showed no dense rational-distance set exists assuming the Bombieri-Lang conjecture; Ascher-Braune-Turchet derived it from Lang's conjecture; Solymosi-de Zeeuw showed an infinite rational-distance set on an algebraic curve forces a line or circle. No fork PR / campaign entry. Related but distinct: FormalConjectures/Wikipedia/RationalDistanceProblem.lean is the unit-square 4-corner question, not this.  
**Difficulty:** math 9/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** File read in full; grep over FormalConjectures/ found no duplicate of the dense-rational-distance statement.  
**Next action:** Leave open (cat 8). The only identifiable formal route is the conditional one: state and prove 'Bombieri-Lang ⇒ no dense rational-distance set', which needs arithmetic geometry Mathlib does not have.

## `erdos_213` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/213.lean:43`  
**Statement:** For every n ≥ 4, are there n points in the plane, no three collinear and no four concyclic, with all pairwise distances integers?  
**Source:** erdosproblems.com/213; Kreisel-Kurz (2008) for the n = 7 construction  
**Statement matches intent:** yes  
**Known status:** erdosproblems.com: open. Best construction is still n = 7 (Kreisel-Kurz 2008), recorded as erdos_213.variants.KK08. Greenfeld-Iliopoulou-Peluse, 'On integer distance sets' (arXiv:2401.10821, 2024) prove a strong upper bound on the size of an integer distance set inside [-N,N]² with no three collinear and no four concyclic — but the bound grows with the diameter N, so it does not bound n absolutely and 213 stays open. No fork PR / campaign entry.  
**Difficulty:** math 9/10, Lean 8/10 · **Compute:** small · **Confidence:** high  
**Evidence:** File read in full; NonTrilinear checked at FormalConjecturesForMathlib/Geometry/2d.lean:59. GIP 2024 confirmed by web search (arXiv:2401.10821): they deduce 'a strong upper bound on the size of any integer distance set in [-N,N]² with no three points on a line and no four points on a circle'.  
**Next action:** Leave open (cat 8). The concrete, finite sub-goal is erdos_213.variants.KK08: formalize the explicit 7-point Kreisel-Kurz configuration — exact rational/algebraic coordinates, then decide collinearity and concyclicity by determinant computations. That is a real but bounded Lean project.

## `erdos_218.variants.ge` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/ErdosProblems/218.lean:39`  
**Statement:** Does the set of indices n for which the prime gap d_{n+1} is at most d_n have natural density 1/2?  
**Source:** erdosproblems.com/218  
**Statement matches intent:** suspect — Same ≤ vs < issue as variants.le; the two together force the equality set to have density 0.  
**Known status:** erdosproblems.com: open; entirely out of reach of current prime-gap technology. No fork PR / campaign entry.  
**Difficulty:** math 10/10, Lean 10/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** Symmetric counterpart of variants.le in the same file.  
**Flags:** ≤ vs < mismatch with the prose/source  
**Next action:** Do not attempt.

## `erdos_218.variants.infinite_equal_prime_gap` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/ErdosProblems/218.lean:48`  
**Statement:** Are there infinitely many n with d_n = d_{n+1}, i.e. infinitely many triples of consecutive primes in arithmetic progression?  
**Source:** erdosproblems.com/218 (cf. erdosproblems.com/141)  
**Statement matches intent:** yes  
**Known status:** Open. This repo's own FormalConjectures/ErdosProblems/141.lean states at erdos_141.variants.infinite_three: 'It is open, even for k=3, whether there are infinitely many such progressions', which is consistent with erdosproblems.com. Post-Zhang/Maynard work (e.g. Banks-Freiberg-Turnage-Butterbaugh on consecutive primes in tuples) gives conditional/related results but does not settle infinitude of consecutive 3-term prime APs unconditionally. No fork PR / campaign entry.  
**Difficulty:** math 9/10, Lean 10/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** Cross-checked against FormalConjectures/ErdosProblems/141.lean (Set.IsAPAndPrimeProgressionOfLength, variants.infinite_three marked research open).  
**Flags:** needs literature check on whether any unconditional infinitude result for consecutive 3-term prime APs has appeared  
**Next action:** Leave open. If ever attacked, route through erdos_141.variants.infinite_three and prove the equivalence lemma between the two formulations first (that lemma is genuinely provable and would be a useful repo contribution).

## `erdos_218.variants.le` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/ErdosProblems/218.lean:31`  
**Statement:** Does the set of indices n for which the prime gap d_n is at most the next gap d_{n+1} have natural density 1/2?  
**Source:** erdosproblems.com/218  
**Statement matches intent:** suspect — The docstring and the source phrase this with a strict comparison (d_n < d_{n+1}); the Lean statement uses ≤. Because the same file also asserts the ≥ version with density 1/2, and d(≤) + d(≥) = 1 + d(=), the pair of statements is equivalent to 'd(<) = d(>) = 1/2 and d(=) = 0'. That is arguably the intended content, but d(=) = 0 is itself unproven, so neither variant is individually equivalent to the strict form. Also note 1/2 elaborates in ℝ (HasDensity takes α : ℝ), so there is no ℕ-division-to-0 bug.  
**Known status:** erdosproblems.com: open. Nothing is known about the distribution of consecutive prime gaps at this resolution; even d(=) = 0 is open. No fork PR / campaign entry.  
**Difficulty:** math 10/10, Lean 10/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** primeGap defined at FormalConjecturesForMathlib/NumberTheory/PrimeGap.lean:27 as (n+1).nth Nat.Prime - n.nth Nat.Prime (0-indexed, primeGap 0 = 1); HasDensity at FormalConjecturesForMathlib/Data/Set/Density.lean:91 is the natural density relative to univ.  
**Flags:** ≤ vs < mismatch with the prose/source  
**Next action:** Do not attempt. Optionally file an upstream note to state the < version explicitly alongside the ≤ version.

## `erdos_23` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/23.lean:100`  
**Statement:** Can every triangle-free graph on 5n vertices be made bipartite by deleting at most n² edges?  
**Source:** erdosproblems.com/23; Balogh-Clemen-Lidický, Max cuts in triangle-free graphs (arXiv:2103.14179); OEIS A389646  
**Statement matches intent:** yes  
**Known status:** erdosproblems.com: state 'falsifiable', i.e. still open. The C₅ blow-up (blowupC5 in this file) shows n² is the right extremal value. The file records the n = 5 case (25 vertices) as research solved via Balogh-Clemen-Lidický plus McKay's 23-vertex catalogue. No fork PR / campaign entry targets 23.lean.  
**Difficulty:** math 9/10, Lean 10/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** Whole file read, including the blowupC5 tightness witness. No duplicate statement elsewhere in the repo.  
**Next action:** Leave open (cat 8). The realistic finite sub-goal is erdos_23.variants.n1 / n1_tight on 5 vertices, which is a genuinely decidable finite check but still costly in Lean (all graphs on Fin 5, all bipartite subgraphs).

## `erdos_233` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/ErdosProblems/233.lean:36`  
**Statement:** Heath-Brown's conjecture: is the sum of the squares of the first N prime gaps O(N (log N)²)?  
**Source:** erdosproblems.com/233; Cramér; OEIS A74741  
**Statement matches intent:** yes  
**Known status:** erdosproblems.com: open. Even on RH only O(N (log N)^4) is known (recorded as erdos_233.variants.upper_bound); the matching lower bound ≫ N(log N)² from PNT is recorded with an AlphaProof formal proof link at mzhorvath1/formal-conjectures commit 032848c. That external link covers only the lower bound variant, NOT this declaration. No fork PR / campaign entry.  
**Difficulty:** math 10/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** File read in full; the formal_proof attribute at line 55 attaches only to erdos_233.variants.lower_bound.  
**Next action:** Do not attempt the main statement. The realistic import is the already-formalized lower_bound variant from the linked AlphaProof proof — that is a different declaration in the same file, and porting it would need a build check.

## `erdos_234` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/ErdosProblems/234.lean:34`  
**Statement:** For every c ≥ 0, does the natural density f(c) of integers n with (p_{n+1}-p_n)/log n < c exist, and is f a continuous function of c?  
**Source:** erdosproblems.com/234  
**Statement matches intent:** yes  
**Known status:** erdosproblems.com: open. Existence of the density even for a single c is open; it would follow from strong uniform Hardy-Littlewood/Gallagher-type equidistribution of prime gaps. No fork PR / campaign entry.  
**Difficulty:** math 10/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** File read in full; HasDensity semantics checked in FormalConjecturesForMathlib/Data/Set/Density.lean.  
**Next action:** Do not attempt.

## `erdos_236` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/236.lean:38`  
**Statement:** Let f(n) be the number of ways to write n = p + 2^k with p prime and k ≥ 0. Is f(n) = o(log n)?  
**Source:** erdosproblems.com/236  
**Statement matches intent:** yes  
**Known status:** erdosproblems.com: open. Known lower bounds show f(n) is unbounded (f(n) ≫ log log n infinitely often); the trivial upper bound is f(n) ≤ log₂ n + 1, and shaving that to o(log n) is unresolved. No fork PR / campaign entry.  
**Difficulty:** math 9/10, Lean 9/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** Definition f at 236.lean:32-33 audited term by term against Nat.log2 semantics (log2 0 = log2 1 = 0, log2 n = ⌊log₂ n⌋).  
**Next action:** Leave open (cat 8). The cheap first milestone is the trivial bound f n ≤ Nat.log2 n + 1 (immediate from List.length_filter_le), stated as a variant — it does not close erdos_236 but is a legitimate contribution.

## `erdos_238` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/238.lean:34`  
**Statement:** For all c₁, c₂ > 0 and all large x, are there more than c₁ log x consecutive primes below x whose consecutive differences all exceed c₂?  
**Source:** erdosproblems.com/238  
**Statement matches intent:** yes  
**Known status:** erdosproblems.com: open. The small-c₁ regime is classical (recorded as erdos_238.variants.small_c1). Heuristically the statement is true for every c₁, c₂ because P(gap > c₂) ≈ exp(-c₂/log x) → 1, so a run of c₁ log x such gaps has constant probability — but making that rigorous needs unproved uniform prime-gap distribution. No fork PR / campaign entry.  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** File read in full; the ∃ f : Fin k → ℕ is redundant given m but harmless — its only content is p_{m+i} ≤ x.  
**Next action:** Leave open (cat 8). First milestone would be the c₂ < 2 case, which is trivially true (all gaps above p=2 are ≥ 2) and would sanity-check the encoding.

## `erdos_241` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/ErdosProblems/241.lean:57`  
**Statement:** Let f(N) be the largest size of a subset of {1,...,N} whose 3-fold sums are all distinct up to reordering (a B₃ set). Is f(N) asymptotic to N^{1/3}?  
**Source:** erdosproblems.com/241 ($100 prize); Bose-Chowla, Comment. Math. Helv. (1962/63) 141-147; Green, Acta Arith. (2001) 365-390; Guy UPINT C11  
**Statement matches intent:** yes  
**Known status:** erdosproblems.com: open, $100 prize. Bose-Chowla give f(N) ≥ (1+o(1))N^{1/3}; Green gives f(N) ≤ ((7/2)^{1/3}+o(1))N^{1/3} ≈ 1.519 N^{1/3}. The gap between 1 and 1.519 is the whole problem. No fork PR / campaign entry.  
**Difficulty:** math 9/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Definition f at 241.lean:42-48 audited; matches the B₃-set formulation quoted in the docstring.  
**Next action:** Do not attempt the asymptotic. The Bose-Chowla lower bound (variants.lower_bound) is the only realistically formalizable piece and needs finite-field Singer-difference-set machinery Mathlib lacks.

## `erdos_241.variants.generalization` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/ErdosProblems/241.lean:93`  
**Statement:** Bose-Chowla conjecture: for every r ≥ 2, the largest B_r subset of {1,...,N} has size asymptotic to N^{1/r}.  
**Source:** erdosproblems.com/241; Bose-Chowla, Comment. Math. Helv. (1962/63) 141-147  
**Statement matches intent:** yes  
**Known status:** Open for every r ≥ 3 (r = 2 is a theorem). Strictly stronger than erdos_241. No fork PR / campaign entry.  
**Difficulty:** math 9/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** BoseChowlaConjecture def at 241.lean:85-86 specializes correctly at r = 3 to erdos_241's right-hand side.  
**Next action:** Do not attempt. If any piece is to be done, do variants.r_eq_2 first (Sidon sets, Erdős-Turán upper bound + Singer construction).

## `erdos_242` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/ErdosProblems/242.lean:36`  
**Statement:** Erdős-Straus conjecture: for every n > 2 there are distinct positive integers x < y < z with 4/n = 1/x + 1/y + 1/z.  
**Source:** erdosproblems.com/242  
**Statement matches intent:** yes  
**Known status:** erdosproblems.com: state 'falsifiable', i.e. still open. Verified computationally for all n up to ~10^17; covering-congruence arguments settle all n outside a thin set of residue classes mod 840 (essentially n ≡ 1, 11^2, 13^2, 17^2, 19^2, 23^2 mod 840). No fork PR / campaign entry.  
**Difficulty:** math 9/10, Lean 9/10 · **Compute:** none · **Confidence:** high  
**Evidence:** File read in full; distinctness constraint checked against small n by hand.  
**Flags:** distinctness (x<y<z) is stronger than the classical Erdős-Straus statement; harmless here but worth a formalization note  
**Next action:** Do not attempt in full. A legitimate partial contribution is a Lean lemma covering the easy residue classes (e.g. n ≡ 0, 2, 3 mod 4 and n ≡ 2 mod 3) by explicit polynomial identities in n — that is a real, finite, decidable piece of work.

## `erdos_242.variants.schinzel_generalization` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/ErdosProblems/242.lean:47`  
**Statement:** Schinzel's generalization: for every fixed a > 0 and all sufficiently large n, there are distinct 1 ≤ x < y < z with a/n = 1/x + 1/y + 1/z.  
**Source:** erdosproblems.com/242; Sierpiński, Mathesis (1956) 16-32 (attributing the conjecture to Schinzel)  
**Statement matches intent:** yes  
**Known status:** Open. Strictly implies Erdős-Straus for all large n (take a = 4), so it is at least as hard as erdos_242. No fork PR / campaign entry.  
**Difficulty:** math 9/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Specializing a = 4 recovers the eventual form of the Erdős-Straus conjecture, confirming the statement is not accidentally weaker.  
**Next action:** Do not attempt.

## `erdos_243` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/243.lean:37`  
**Statement:** If a strictly increasing integer sequence satisfies a_n/a_{n-1}² → 1 and the sum of reciprocals is rational, must a_n = a_{n-1}² - a_{n-1} + 1 for all sufficiently large n?  
**Source:** erdosproblems.com/243  
**Statement matches intent:** yes  
**Known status:** erdosproblems.com: open. This is the rigidity direction of the Sylvester/Kellogg-type sequence a_n = a_{n-1}² - a_{n-1} + 1 (whose reciprocal sum is exactly rational); the converse characterisation is what is asked. No fork PR / campaign entry.  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** File read in full; Summable-in-ℚ semantics reasoned out (ℚ is a topological field with the ℝ subspace topology, so unconditional convergence of a nonnegative series in ℚ ⟺ rational real sum).  
**Flags:** the rationality hypothesis is encoded indirectly via Summable in ℚ; correct but non-obvious, deserves a formalization note in the file  
**Next action:** Leave open (cat 8). Identifiable avenue: prove the easy direction first (the Sylvester recurrence does give a rational sum and satisfies a_n/a_{n-1}² → 1) as a sanity variant, then attack the rigidity via a tail-estimate argument bounding a_n between a_{n-1}²-a_{n-1}+1 and a_{n-1}²+O(a_{n-1}).

## `erdos_244` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/244.lean:29`  
**Statement:** For every real C > 1, does the set of integers of the form p + floor(C^k) (p prime, k >= 0) have positive density?  
**Source:** https://www.erdosproblems.com/244 ; Romanoff, Über einige Sätze der additiven Zahlentheorie, Math. Ann. 1934 (integer C case, cited in file)  
**Statement matches intent:** yes  
**Known status:** erdosproblems.com state = open (batch metadata, 2026-07-26). Romanoff (1934) settles integer C (stated in-file as erdos_244.variants.Romanoff, itself sorry). No PR in pr_register.json touches problems 244-279 or 25/28; no campaign entry; no duplicate elsewhere in FormalConjectures/.  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** Romanoff's method uses the multiplicative order of C mod d to bound the number of representations; ⌊C^k⌋ for non-integer C has no such multiplicative structure, which is exactly the open obstruction. Statement is faithful, no junk-value or truncation issues (Nat.floor of a positive real, ℕ addition).  
**Next action:** Attempt the Romanoff route: formalize the L^2/representation-count argument for the sumset of primes with a sparse set. First milestone: formalize Romanoff's theorem (the `variants.Romanoff` sorry) for integer C, which is a prerequisite for any attack on real C.

## `erdos_247` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/ErdosProblems/247.lean:40`  
**Secondary category:** 8 (Deep but approachable research problem)  
**Statement:** If n_1 < n_2 < ... are integers with limsup n_k/k = infinity, must sum 1/2^{n_k} be transcendental?  
**Source:** https://www.erdosproblems.com/247 ; [ErGr80] Erdős–Graham, Old and new problems and results in combinatorial number theory (1980)  
**Statement matches intent:** yes  
**Known status:** erdosproblems.com state = open. Erdős's partial result (limsup n_k/k^t = ∞ for all t ≥ 1) is recorded in-file as erdos_247.variants.strong_condition (sorry). No repo/PR work found.  
**Difficulty:** math 9/10, Lean 10/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** Irrationality under the hypothesis is easy (eventual periodicity of the binary expansion forces n_k/k bounded), but transcendence needs Diophantine approximation machinery absent from Mathlib. The gap between limsup n_k/k = ∞ and Erdős's limsup n_k/k^t = ∞ is exactly the unresolved part.  
**Next action:** Do not attempt directly. If pursued, the only identifiable avenue is a combinatorial transcendence criterion (Ridout / Adamczewski–Bugeaud) applied to the binary expansion; formalizing Ridout's theorem alone is research-scale in Lean.

## `erdos_249` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/ErdosProblems/249.lean:34`  
**Statement:** Is the sum over n of phi(n)/2^n (phi = Euler totient) irrational?  
**Source:** https://www.erdosproblems.com/249  
**Statement matches intent:** yes  
**Known status:** erdosproblems.com state = open. Contrast with the divisor-function analogue ∑ d(n)/2^n, proved irrational by Erdős 1948 (recorded in 257.lean as erdos_257.variants.tsum_top). No repo/PR work found.  
**Difficulty:** math 9/10, Lean 9/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** ∑ d(n)/2^n is a Lambert series (= ∑ 1/(2^n-1)), which is what makes Erdős's 1948 argument work; ∑ φ(n)/2^n is not, so the standard denominator/approximation argument does not apply. Statement is clean and faithful.  
**Next action:** No realistic Lean path. Would first require formalizing the Erdős/Lambert-series irrationality technique (see 257.lean, whose `tsum_top` is still sorry) and then extending it to a non-Lambert series.

## `erdos_25` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/25.lean:35`  
**Statement:** Given any strictly increasing sequence of moduli n_i with residues a_i, let A be the set of n that avoid every congruence a_i mod n_i with n_i <= n. Must A have a logarithmic density?  
**Source:** https://www.erdosproblems.com/25  
**Statement matches intent:** yes  
**Known status:** erdosproblems.com state = open. Related classical background: Davenport–Erdős proved logarithmic density exists for sets of multiples, and Besicovitch showed natural density can fail; the general congruence version is the open case. No PR/campaign/duplicate found.  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** Formalization is faithful; the k = 0 term in HasLogDensity uses (0:ℝ)⁻¹ = 0, harmless. The mathematical obstruction is that partial log-densities need not converge without a Davenport–Erdős-style monotonicity structure.  
**Next action:** Milestone-first approach: prove the easy direction that A always has an upper/lower logarithmic density and formalize the sets-of-multiples special case (Davenport–Erdős) as a warm-up; the general case is open research.

## `erdos_251` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/ErdosProblems/251.lean:30`  
**Statement:** Is sum_{n>=1} p_n/2^n irrational, where p_n is the n-th prime?  
**Source:** https://www.erdosproblems.com/251  
**Statement matches intent:** suspect — Index shift: Nat.nth Nat.Prime n is 0-indexed (nth 0 = 2) but the exponent is also n, so the Lean value is ∑_{n≥0} p_{n+1}/2^n = 2·(intended ∑_{n≥1} p_n/2^n). Irrationality of x and 2x are equivalent, so the truth value is unchanged, but the constant formalized is literally twice the one in the docstring.  
**Known status:** erdosproblems.com state = open. No PR/campaign/duplicate found in this repo.  
**Difficulty:** math 9/10, Lean 9/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** Sum elaborates in ℝ (Irrational forces it), so no ℕ division. No junk values (2^n ≠ 0). The only defect is the off-by-one between the 0-indexed Nat.nth and the exponent.  
**Flags:** off-by-one indexing: formal constant is 2× the docstring constant (harmless for irrationality)  
**Next action:** Leave open; if desired, fix the cosmetic mismatch by using 2^(n+1) in the denominator so the Lean constant equals the constant in the docstring. Resolution itself is research-scale.

## `erdos_252` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/252.lean:47`  
**Statement:** Is sum_n sigma_k(n)/n! irrational for every k >= 1 (sigma_k = sum of k-th powers of divisors)?  
**Source:** https://www.erdosproblems.com/252 ; [ErSt71], [ErSt74], [ErKa54], [ScPu06], [FLC07], [Pr22] (all cited in file)  
**Statement matches intent:** yes  
**Known status:** erdosproblems.com state = open. Known: k=0 [ErSt71], k=1 [ErSt74], k=2 [ErKa54], k=3 [ScPu06]/[FLC07], k=4 [Pr22]; all k conditional on Schinzel's hypothesis [ScPu06] or prime k-tuples [FLC07]. No PR/campaign work in this fork.  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** none · **Confidence:** high  
**Evidence:** The file itself records that every k ≤ 4 is settled and that the general case follows from Schinzel's hypothesis, so the remaining content is exactly the open k ≥ 5 range. Statement is faithful; no junk/truncation issues.  
**Flags:** logically duplicates erdos_252.variants.k_ge_five given the in-file solved k ≤ 4 variants  
**Next action:** Not resolvable unconditionally today. The pragmatic Lean target is the conditional theorem erdos_252.variants.schinzel (Schinzel ⇒ irrational for all k); that is a substantial but well-defined formalization (medium-large).

## `erdos_252.variants.k_ge_five` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/252.lean:79`  
**Statement:** Is sum_n sigma_k(n)/n! irrational for every fixed k >= 5?  
**Source:** https://www.erdosproblems.com/252 ; [Pr22] Pratt, arXiv:2209.11124 (k=4)  
**Statement matches intent:** yes  
**Known status:** erdosproblems.com state = open. Each successive k has been settled by increasingly refined sieve/prime-tuple inputs; k ≥ 5 unresolved. No PR/campaign work.  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Duplicate-in-substance of erdos_252 (given in-file solved variants for k ≤ 4); no formalization defect found.  
**Flags:** logically equivalent to erdos_252 given in-file solved variants  
**Next action:** Same as erdos_252: pursue the conditional Schinzel/prime-k-tuples implication rather than the unconditional statement.

## `erdos_254` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/254.lean:44`  
**Statement:** If A ⊆ N satisfies |A∩[1,2x]| - |A∩[1,x]| → ∞ and sum_{n∈A} ||θn|| = ∞ for all θ in (0,1), then every sufficiently large integer is a sum of distinct elements of A.  
**Source:** https://www.erdosproblems.com/254 ; [Ca60] Cassels, Acta Sci. Math. (Szeged) 1960 (weaker hypotheses, in-file variant)  
**Statement matches intent:** yes  
**Known status:** erdosproblems.com state = open. Cassels [Ca60] proved the statement under stronger hypotheses (recorded in-file as erdos_254.variants.cassels, sorry). No PR/campaign/duplicate.  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** Checked the standard failure mode: A = multiples of 2 has |A∩[1,2x]|-|A∩[1,x]| → ∞ but is killed by θ = 1/2 (||θn|| ≡ 0, summable), so the second hypothesis is doing the right work and the statement is not falsified by structured A. Stated as an unconditional theorem (no answer()), which is the correct encoding of a conjecture.  
**Next action:** First milestone: formalize Cassels' theorem (the weaker in-file variant) — that is the only known result and would be a large but bounded project; the Erdős strengthening is open research.

## `erdos_257` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/257.lean:34`  
**Statement:** For every infinite set A of natural numbers, is sum_{n in A} 1/(2^n - 1) irrational?  
**Source:** https://www.erdosproblems.com/257 ; [Er48] Erdős, On arithmetical properties of Lambert series (the A = N case)  
**Statement matches intent:** suspect — If 0 ∈ A the term is 1/(2^0-1) = 1/0 = 0 (Lean junk value) rather than undefined; the intended A ⊆ positive integers. Harmless: A\{0} is still infinite and the sum equals the intended one, so neither direction is affected. Otherwise faithful.  
**Known status:** erdosproblems.com state = open. Known: A = N is Erdős 1948 (in-file erdos_257.variants.tsum_top, sorry); the Lambert identity ∑ 1/(2^n-1) = ∑ d(n)/2^n is actually PROVED in-file (erdos_257.variants.tsum_top_eq, sorry-free). Erdős problem 69 (∑ ω(n)/2^n) is recorded as the special case A = primes (69.lean).  
**Difficulty:** math 9/10, Lean 9/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** The universal quantifier over all infinite A makes a negative answer plausible via an explicit construction (cf. Kovač–Tao's counterexamples for neighbouring Ahmes-series problems 263/264), which is the identifiable avenue.  
**Flags:** division-by-zero junk value when 0 ∈ A (benign)  
**Next action:** Target the special cases first (A = N, A = primes) using the already-proved Lambert identity; the universal statement over all infinite A likely needs a Kovač–Tao-style counterexample construction if the answer is 'no'.

## `erdos_260` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/260.lean:33`  
**Statement:** If a_1 < a_2 < ... is increasing with a_n/n → ∞, must sum_n a_n/2^{a_n} be irrational?  
**Source:** https://www.erdosproblems.com/260 (statement confirmed by web search: 'for every increasing sequence a_1<a_2<... with a_n/n → ∞, is ∑_{n>1} a_n/2^{a_n} irrational?')  
**Statement matches intent:** yes  
**Known status:** erdosproblems.com state = open (batch metadata). Recent (post-cutoff) partial progress: arXiv:2606.24972 'Positive dyadic density for rational weighted binary expansions' obtains a structural/density theorem for this exact problem (if ∑ n·d_n·2^{-n} is rational and {n : d_n = 1} is infinite, that set has positive density in each dyadic block [X,2X]). Could not fetch the abstract (erdosproblems.com and arxiv.org both returned 403 here).  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** Web search confirmed the formal statement matches the source problem exactly. The in-file TODOs correctly record the two known sufficient conditions (a_{n+1}-a_n → ∞, and a_n ≫ n√(log n log log n)).  
**Flags:** needs literature check: arXiv:2606.24972 (2026) may supersede the 'open' status  
**Next action:** Verify whether arXiv:2606.24972 fully resolves 260 before investing; if it is only a partial density theorem (as the search snippet indicates), formalizing that density statement is the natural first milestone.

## `erdos_263.parts.i` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/263.lean:47`  
**Statement:** Is a_n = 2^(2^n) an irrationality sequence, i.e. does every sequence of positive integers b_n with a_n/b_n → 1 have sum 1/b_n irrational?  
**Source:** https://www.erdosproblems.com/263 ; [KoTa24] Kovač–Tao, On several irrationality problems for Ahmes series, arXiv:2406.17593  
**Statement matches intent:** yes  
**Known status:** erdosproblems.com state = open. Kovač–Tao [KoTa24] settle the sub-doubly-exponential regime (a_{n+1}/a_n^2 → 0 ⇒ not an irrationality sequence, in-file variant, also referenced from FC100SolvedSet1.lean) and the folklore result covers liminf a_{n+1}/a_n^{2+ε} > 0. a_n = 2^(2^n) has a_{n+1}/a_n^2 ≡ 1, i.e. it sits exactly on the boundary between the two known regimes.  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** none · **Confidence:** high  
**Evidence:** a_{n+1}/a_n^2 = 2^{2^{n+1}}/2^{2·2^n} = 1, so neither erdos_263.variants.sub_doubly_exponential (needs → 0) nor variants.super_doubly_exponential (needs exponent 2+ε) applies: the boundary case is genuinely the open one. No repo/PR/campaign work on 263.  
**Next action:** Compute/verify that a_n = 2^(2^n) is the exact critical case (a_{n+1}/a_n^2 = 1) and look for a Kovač–Tao-style perturbation b_n = a_n + O(1) argument; formalizing either known regime theorem is the realistic first milestone.

## `erdos_264.parts.ii` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/264.lean:58`  
**Statement:** Is a_n = n! an irrationality sequence in Erdős's second sense: for every bounded integer sequence b_n with b_n ≠ 0 and a_n + b_n ≠ 0, is sum 1/(a_n+b_n) irrational?  
**Source:** https://www.erdosproblems.com/264 ; [KoTa24] Kovač–Tao, arXiv:2406.17593  
**Statement matches intent:** yes  
**Known status:** erdosproblems.com state = open. Known: 2^n is not an irrationality sequence [KoTa24] (parts.i); 2^(2^n) is one (variants.example); general negative criterion via liminf a_n^2 ∑_{k>n} 1/a_k^2 > 0 (variants.ko_tao_neg). n! is not covered by either criterion. No PR/campaign work.  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** The definitional sanity check above (b ≡ 0 would trivialize parts.i) confirms the b_n ≠ 0 condition is intended rather than an accidental strengthening. Factorial growth falls strictly between the two Kovač–Tao regimes.  
**Next action:** Check whether n! satisfies the Kovač–Tao liminf criterion: a_n^2 ∑_{k>n} a_k^{-2} for a_n = n! is ≈ (n!)^2/((n+1)!)^2 = 1/(n+1)^2 → 0, so the negative criterion does not apply and the problem is genuinely open; no near-term Lean action.

## `erdos_267` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/267.lean:32`  
**Statement:** If n_1 < n_2 < ... satisfies n_{k+1}/n_k >= c > 1, must sum_k 1/F_{n_k} be irrational (F = Fibonacci)?  
**Source:** https://www.erdosproblems.com/267 ; [Go74] Good, [BiHo76] Hoggatt–Bicknell (the n_k = 2^k case); André-Jeannin (∑1/F_n)  
**Statement matches intent:** yes  
**Known status:** erdosproblems.com state = open. Known special cases: ∑ 1/F_{2^k} irrational (Good; Hoggatt–Bicknell; an AlphaProof formal proof is linked upstream for erdos_267.variants.specialization_pow_two) and ∑ 1/F_n irrational (André-Jeannin). No PR/campaign work in this fork.  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** Nat.fib matches the F_1 = F_2 = 1 convention in the docstring. The known identity ∑ 1/F_{2^k} = (7-√5)/2 gives an irrational value, consistent with a 'yes' answer; no rational example is known.  
**Next action:** Port the upstream AlphaProof proof of erdos_267.variants.specialization_pow_two into this fork and verify the build; the general lacunary case remains open research.

## `erdos_267.variants.generalisation_ratio_limit_to_infinity` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/267.lean:42`  
**Statement:** If n_1 < n_2 < ... satisfies n_k/k → infinity, must sum_k 1/F_{n_k} be irrational?  
**Source:** https://www.erdosproblems.com/267 (generalisation stated on the problem page)  
**Statement matches intent:** suspect — Two cosmetic mismatches: (a) the docstring says n_k/k → ∞ but the formal condition is n(k+1)/(k+1) → ∞ — equivalent, since it is the same sequence reindexed and the limit is a tail property; (b) unlike erdos_267 there is no ratio hypothesis excluding n 0 = 0, in which case Nat.fib 0 = 0 makes the k = 0 term 1/0 = 0 (junk) — this merely drops one term and yields another legitimate instance, so no falsification.  
**Known status:** erdosproblems.com state = open. Strictly generalises erdos_267 (a lacunary sequence has n_k/k → ∞), so it is at least as hard.  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** The Tendsto is over ℝ (explicit ascription), so no ℕ division truncation. Statement is strictly stronger than erdos_267, which is itself open.  
**Flags:** fib 0 = 0 junk-value branch when n 0 = 0 (benign); docstring/formal index shift (equivalent)  
**Next action:** Same as erdos_267. Optionally tighten by requiring 0 < n k to remove the fib 0 junk-value branch.

## `erdos_269.variants.irrational` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/269.lean:72`  
**Statement:** For every finite set P of at least 2 primes, is sum_n 1/lcm(a_1,...,a_n) irrational (a_i = the P-smooth positive integers in increasing order)?  
**Source:** https://www.erdosproblems.com/269  
**Statement matches intent:** suspect — Same off-by-one as erdos_269.variants.rational (the n = 0 term contributes 1/lcm(∅) = 1). Note also that this and the 'rational' variant are not exact negations: both are ∀P statements, so if the answer depends on P then BOTH answer(sorry) values are False without the problem being resolved in the intended sense.  
**Known status:** erdosproblems.com state = open. Companion in-file result erdos_269.variants.infinite claims irrationality when P is infinite (sorry). Listed in FormalConjectures/Subsets/FC100OpenSet1.lean (the 'rational' variant) as a curated open problem.  
**Difficulty:** math 8/10, Lean 8/10 · **Compute:** small · **Confidence:** medium  
**Evidence:** Two ∀-quantified answer() statements about the same family can both be refuted by different P without resolving the underlying question — a genuine (if mild) encoding weakness.  
**Flags:** rational/irrational variants can both be False without resolving the problem; series is intended-value + 1  
**Next action:** Same as the rational variant; additionally consider restating as a single ∀P, (Irrational ∨ rational) decision to avoid the both-False degeneracy.

## `erdos_269.variants.rational` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/269.lean:59`  
**Statement:** For every finite set P of at least 2 primes, with a_1<a_2<... the positive integers all of whose prime factors lie in P, is sum_n 1/lcm(a_1,...,a_n) rational?  
**Source:** https://www.erdosproblems.com/269  
**Statement matches intent:** suspect — `series P` = ∑_{n≥0} 1/partialLcm P n and partialLcm P 0 = Finset.lcm ∅ = 1, so the Lean value is 1 + (intended ∑_{n≥1} 1/[a_1..a_n]). Adding 1 preserves rationality/irrationality, so the truth value is unchanged, but the constant is off by 1. The in-file comment on partialLcm ('lcm of {a P 0, ..., a P n}') is also wrong — Finset.range n is {0,...,n-1}; the code is right, the comment is not.  
**Known status:** erdosproblems.com state = open. The |P| = 1 case is trivially rational (a_n = p^{n-1}, sum = p/(p-1)), which is why |P| ≥ 2 is imposed. The P infinite case is asserted irrational in-file (erdos_269.variants.infinite, sorry). No PR/campaign/duplicate.  
**Difficulty:** math 8/10, Lean 8/10 · **Compute:** small · **Confidence:** medium  
**Evidence:** HasPrimeFactorsIn P n := n > 0 ∧ (all prime divisors in P) correctly makes a_1 = 1; Nat.nth is well-defined since the predicate holds infinitely often for P nonempty. For P = {2,3}, lcm of the first n smooth numbers grows only like exp(c√n), so the sum is far from lacunary and neither rationality nor irrationality is forced by a trivial argument.  
**Flags:** series is intended-value + 1 (extra n = 0 term); benign for (ir)rationality; misleading code comment on partialLcm  
**Next action:** Numerically explore P = {2,3}: compute lcm(a_1..a_n) (which is p^α q^β with α,β the largest exponents seen) and the partial sums to high precision to guess the answer, then attempt an explicit closed form. First milestone: prove partialLcm P n = ∏_{p∈P} p^{v_p(a_n)} for the |P| = 2 case.

## `erdos_272` — Already solved externally (cat 1)

**File:** `FormalConjectures/ErdosProblems/272.lean:47`  
**Secondary category:** 4 (Vacuously true / accidentally weakened)  
**Statement:** Determine the asymptotics of the largest t such that there are t distinct subsets A_1,...,A_t of {1,...,N} with every pairwise intersection a non-empty arithmetic progression.  
**Source:** https://www.erdosproblems.com/272 ; Szabo's theorem (t = N^2/2 + O(N^{5/3} log^3 N)), stated in the same file as erdos_272.variants.szabo [category research solved]  
**Statement matches intent:** suspect — The formal statement only asks for an asymptotic equivalence maxArithInterCard N ~ f(N), which is strictly weaker than 'what is the largest t?'. That weaker question is ALREADY ANSWERED by the file's own solved variant erdos_272.variants.szabo: maxArithInterCard N - N^2/2 = O(N^{5/3} log^3 N) implies maxArithInterCard N ~ N^2/2, since N^{5/3} log^3 N = o(N^2). So answer(sorry) := fun N => (N:ℝ)^2/2 and the statement is a known theorem, yet it is tagged @[category research open].  
**Known status:** Solved in the literature (Szabo). The genuinely open part of erdosproblems.com/272 is the error term, which is captured separately by erdos_272.variants.szabo_strong. The categorisation of erdos_272 as 'research open' is inconsistent with the file's own 'research solved' szabo variant.  
**Difficulty:** math 6/10, Lean 8/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** Asymptotics.IsEquivalent f g means (f - g) =o[atTop] g; szabo gives (f - N^2/2) = O(N^{5/3} log^3 N) ⊆ o(N^2), hence f ~ N^2/2 immediately. maxArithInterCard is well-defined (sSup of a bounded nonempty subset of ℕ: A ⊆ powerset of Icc 1 N; A = ∅ witnesses nonemptiness), and Finset (Finset ℕ) correctly forces the A_i to be distinct (without distinctness t would be unbounded by repetition).  
**Flags:** MISLABELLED: research open statement is implied by an in-file research solved statement; answer() encoding (asymptotic equivalence) is weaker than the source question 'what is the largest t'  
**Next action:** Fill in answer := fun N => (N:ℝ)^2/2 and retag erdos_272 as research solved, deriving it from erdos_272.variants.szabo via Asymptotics.IsEquivalent (an easy o(N^2) comparison once szabo is available). The remaining real work is formalizing Szabo's theorem itself (large). Verify the build afterwards — lake cannot be run in this container.

## `erdos_272.variants.szabo_strong` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/272.lean:76`  
**Statement:** Is the maximum number t of subsets of {1,...,N} with pairwise non-empty-AP intersections equal to N^2/2 + O(N)?  
**Source:** https://www.erdosproblems.com/272 (question attributed to Szabo)  
**Statement matches intent:** yes  
**Known status:** erdosproblems.com state = open; this is the real open content of problem 272. Curated in FormalConjectures/Subsets/FC100OpenSet1.lean. No PR/campaign work.  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** Improving O(N^{5/3} log^3 N) to O(N) requires a genuinely sharper extremal argument; no partial results beyond Szabo are recorded.  
**Next action:** Out of reach until Szabo's theorem is formalized. Interim milestone: formalize the lower-bound construction giving t ≥ N^2/2 - O(N), which is the elementary half.

## `erdos_273` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/273.lean:29`  
**Secondary category:** 6 (Computationally solvable with certificate)  
**Statement:** Is there a covering system of the integers all of whose (distinct) moduli have the form p-1 for primes p >= 5?  
**Source:** https://www.erdosproblems.com/273 ; covering-system notion as in [ErGr80]  
**Statement matches intent:** yes  
**Known status:** erdosproblems.com state = open. The p ≥ 3 relaxation is asserted answer(True) in-file (erdos_273.variants.three, sorry, with a TODO asking for a reference). No PR/campaign work; FormalConjectures/ErdosProblems/7.lean and 40.lean also use CoveringSystem but state different problems.  
**Difficulty:** math 8/10, Lean 7/10 · **Compute:** medium · **Confidence:** medium  
**Evidence:** Sum of 1/(p-1) over primes p ≥ 5 diverges, so no elementary density obstruction rules a covering out; this is a search problem in the YES direction, hence the cat2 = 6. Note the sibling variant erdos_273.variants.three uses StrictCoveringSystem ℕ (ideals of the semiring ℕ) while erdos_273 uses ℤ — an inconsistency worth fixing, though it does not affect the audited declaration.  
**Flags:** sibling variant erdos_273.variants.three is stated over ℕ rather than ℤ (inconsistent, likely a defect in that variant)  
**Next action:** Two-sided: (a) run a computer search over covering systems with moduli drawn from {4,6,10,12,16,18,22,...} — a positive answer yields a finite, kernel-checkable certificate (check coverage of Z/lcm by `decide`); (b) if no system exists, the negative direction needs Hough/Balister–Bollobás–Morris-style density machinery.

## `erdos_274` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/274.lean:59`  
**Statement:** In any exact covering (partition) of a group by more than one coset of subgroups, must two of the subgroups have the same cardinality?  
**Source:** https://www.erdosproblems.com/274 ; Herzog–Schönheim conjecture (Wikipedia, arXiv:1803.08301 etc., cited in file)  
**Statement matches intent:** suspect — The conclusion is equality of subgroup CARDINALITIES (#(P.parts i)), whereas Herzog–Schönheim is about equality of INDICES. For finite G the two coincide; for infinite G they do not, and the cardinality version is trivially true there: by B. H. Neumann's lemma, in a partition of G by finitely many cosets every subgroup has finite index, hence cardinality |G|, so any two parts have equal cardinality. Net effect: erdos_274 is truth-equivalent to Herzog–Schönheim for finite groups (hence to HS in general, via the normal-core reduction), but its infinite-G content is vacuous.  
**Known status:** erdosproblems.com state = open. The abelian case is recorded as solved in-file (erdos_274.variants.abelian, sorry). The index version is stated separately in the same file as `herzog_schonheim`. No PR/campaign work.  
**Difficulty:** math 9/10, Lean 9/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** Group.ExactCovering encodes disjointness (PairwiseDisjoint on univ) plus covering (⋃ = univ), correctly allowing the same subgroup with different representatives (e.g. 1 mod 4 and 3 mod 4). The `nonempty` field is redundant (subgroups always contain 1). Hypotheses 1 < ENat.card G and 1 < Fintype.card ι rule out the degenerate one-part covering.  
**Flags:** cardinality-vs-index mismatch: infinite-group instances are vacuously true; near-duplicate of `herzog_schonheim` in the same file  
**Next action:** Restate the conclusion with Subgroup.index (i.e. merge with `herzog_schonheim`) so the infinite-group case is not vacuous, then attack the finite abelian case first (a clean, formalizable classical proof).

## `herzog_schonheim` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/274.lean:85`  
**Secondary category:** 9 (Major open problem / currently infeasible)  
**Statement:** Herzog-Schönheim conjecture: if finitely many (more than one) left cosets of subgroups partition a group, then two of the subgroups have the same index.  
**Source:** https://en.wikipedia.org/wiki/Herzog–Schönheim_conjecture ; Herzog & Schönheim 1974; erdosproblems.com/274  
**Statement matches intent:** yes  
**Known status:** Recognized open conjecture since 1974. Known partial results: nilpotent/pyramidal groups, groups whose order has few prime factors, and several 2018 arXiv papers cited in the file header (1803.08301, 1803.03569, 1804.11103). No PR/campaign work in this fork.  
**Difficulty:** math 9/10, Lean 9/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Well-known long-standing open problem; the formalization matches the standard statement exactly. Duplicates erdos_274 in substance (see that entry).  
**Flags:** near-duplicate of erdos_274 in the same file (index vs cardinality)  
**Next action:** Formalize the classical finite abelian / cyclic case first (via the density-of-cosets argument on Z/n), i.e. prove erdos_274.variants.abelian; the general conjecture is research-scale.

## `erdos_276` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/276.lean:45`  
**Statement:** Is there a Fibonacci-like sequence a_{n+2}=a_{n+1}+a_n of natural numbers with every term composite, such that no integer > 1 shares a factor with every term?  
**Source:** https://www.erdosproblems.com/276 ; cf. R. L. Graham, A Fibonacci-like sequence of composite numbers (1964)  
**Statement matches intent:** yes  
**Known status:** erdosproblems.com state = open. Graham (1964) constructed a Fibonacci-like sequence of composites with coprime initial terms, but that construction is driven by a covering system of primes, so the product of those primes DOES share a factor with every term — i.e. Graham's sequence does not answer the stronger question formalized here. No PR/campaign/duplicate.  
**Difficulty:** math 8/10, Lean 8/10 · **Compute:** small · **Confidence:** medium  
**Evidence:** The distinction between 'no prime divides every term' (Graham, solved) and 'no integer shares a factor with every term' (this statement) is exactly what keeps the problem open, and the Lean statement encodes the strong version.  
**Next action:** No cheap path. Explore whether a finite prime set must always exist (which would give answer(False)): a first milestone is to prove that if the sequence avoids being eventually covered by a finite prime set then some term is prime, for restricted classes of sequences.

## `erdos_279` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/279.lean:31`  
**Statement:** For each k >= 3, is there a choice of residue a_p mod p for every prime p such that every sufficiently large n can be written as a_p + t*p with p prime and t >= k?  
**Source:** https://www.erdosproblems.com/279  
**Statement matches intent:** yes  
**Known status:** erdosproblems.com state = open. This is an infinite-covering-system question with distinct prime moduli; the t ≥ k constraint means only primes p ≲ n/k may be used to cover n. No PR/campaign/duplicate.  
**Difficulty:** math 8/10, Lean 8/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** Checked the obvious trivialization: a_p ≡ 0 covers every composite n ≥ k^2 (a factor p ≤ √n ≤ n/k exists), so only prime n and one residue class remain — the statement is not trivially true and not trivially false. The profinite/compactness argument gives an uncovered element of Ẑ but not of ℤ, which is the standard obstruction.  
**Next action:** First reduce: setting a_2 ∈ {0,1} already covers one residue class mod 2 for all large n, so the problem reduces to covering the other class by residues mod distinct odd primes p ≤ n/k. Formalize that reduction as a warm-up lemma; the residual question is open research.

## `erdos_28` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/ErdosProblems/28.lean:35`  
**Statement:** Erdős–Turán additive basis conjecture (h=2): if A+A contains all but finitely many naturals, then the number of representations n = a+b is unbounded.  
**Source:** https://www.erdosproblems.com/28 ($500 prize); Erdős–Turán 1941  
**Statement matches intent:** yes  
**Known status:** Recognized major open problem with a $500 Erdős prize (batch metadata confirms prize = $500, state = open). Two in-file implications elsewhere in the repo: erdos_40.variants.implies_erdos_28 and erdos_1145.test_implies_erdos_28 both reduce erdos_28 to other (also open) statements. No PR/campaign proof.  
**Difficulty:** math 10/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** This is the Erdős–Turán conjecture on additive bases, open since 1941 and one of Erdős's best-known prize problems. The formalization is faithful and free of junk-value or truncation issues.  
**Next action:** Do not attempt. Only meaningful contribution would be formalizing known partial results (e.g. Erdős–Fuchs on the error term in the counting function), which is a separate large project.

## `erdos_282` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/ErdosProblems/282.lean:69`  
**Secondary category:** 8 (Deep but approachable research problem)  
**Statement:** Run the greedy Egyptian-fraction algorithm on a rational x in (0,1) with odd denominator, always subtracting 1/n for the least odd n with n >= 1/x. Does the process always reach 0 (the 'odd greedy algorithm' conjecture)?  
**Source:** erdosproblems.com/282 (state: open); Erdos-Graham 'Old and new problems...'; Guy, UPINT D11 (odd greedy expansions); Stewart 1954; Graham 1964  
**Statement matches intent:** suspect — `greedyUnitFractionRem` re-selects the least element of A at every step and never excludes already-used denominators, so it does NOT in general produce *distinct* unit fractions (contrary to the definition's docstring). Concrete instance inside the conjecture's hypotheses: x = 5/7 (odd denominator, in (0,1)) gives 5/7 - 1/3 = 8/21, and 1/(8/21) = 2.625, so the least odd n >= 1/x is 3 again: the model outputs 5/7 = 1/3 + 1/3 + 1/21. The literal wording on erdosproblems.com ('choose the minimal n in A with n >= 1/x') matches the Lean code, but the classical odd-greedy algorithm takes the least *unused* odd denominator, so the formal statement may be a strictly weaker termination question.  
**Known status:** Open. No PR in pr_register.json and no entry in campaign_register.json touches Erdos 282; no duplicate statement elsewhere in FormalConjectures/. Only the trivial `test` lemmas in the file are proved.  
**Difficulty:** math 9/10, Lean 10/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** The odd greedy expansion conjecture is a well-known unresolved problem: remainders' denominators grow doubly exponentially and no method is known to prove termination even for a single infinite family; only numerical verification exists. `answer` is not used here, so the theorem literally asserts termination.  
**Flags:** definition admits repeated denominators; docstring's 'distinct unit fractions' claim is false for general A; sInf on Set N returns junk 0 when the candidate set is empty (irrelevant for A = odds, relevant for the general variant); needs literature check on the exact erdosproblems.com phrasing (fetch returned HTTP 403)  
**Next action:** Before any proof attempt, fix the definition to forbid repeated denominators (e.g. carry the used Finset, or require the next denominator > previous) and re-check the docstring claim; then treat as a long-term research target (no known approach to proving termination of the odd greedy algorithm).

## `erdos_282.variants.general` — Cannot classify without correction/clarification (cat 10)

**File:** `FormalConjectures/ErdosProblems/282.lean:75`  
**Secondary category:** 4 (Vacuously true / accidentally weakened)  
**Statement:** Classify all pairs (x, A) for which the greedy unit-fraction process with denominators from A terminates on x.  
**Source:** erdosproblems.com/282 ('More generally, for which pairs x and A does this process terminate?')  
**Statement matches intent:** no — Three problems. (1) The target is an `answer(sorry) : Set (Q x Set N)`; under the repo's default `alwaysTrue` answer setting a non-Prop `answer(sorry)` elaborates to an opaque `sorryAx`, so the compiled statement is unprovable as it stands; under `postpone`/`withAuxiliary` it is trivially closable by supplying the tautological set `{p | greedyUnitFractionRem p.2 p.1 =^f[atTop] 0}` and `Iff.rfl`. (2) The hypothesis 'A infinite' from the problem text is dropped: A = empty gives sInf = 0 and 1/0 = 0, so the remainder is constant and the answer set is polluted by degenerate A. (3) x is unrestricted, so all x <= 0 vacuously 'terminate' (remainder goes negative and the `prev <= 0` branch clamps to 0 at step 1), whereas the source restricts to x in (0,1).  
**Known status:** Open-ended classification question with no known closed-form answer; no relevant PR or campaign.  
**Difficulty:** math 9/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Read of FormalConjectures/Util/Answer.lean: `answer(sorry)` at non-Prop expected type produces a canonical `sorryAx` (mode alwaysTrue) or a user-supplied auxiliary definition (mode withAuxiliary), which admits the identity-set cheat. The prose question is a research programme, not a decidable statement.  
**Flags:** answer-set encoding trivializable by the tautological set; missing hypothesis A.Infinite and x in Ioo 0 1; degenerate objects admitted (empty A, x <= 0)  
**Next action:** Rewrite as a family of concrete conjectures (A = odds, A = a mod d, A = squares) or add hypotheses `A.Infinite`, `x in Ioo 0 1` and a non-tautological answer format; do not attempt as stated.

## `erdos_282.variants.graham` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/282.lean:93`  
**Statement:** Graham characterised when m/n is a sum of distinct unit fractions with denominators congruent to a mod d. In exactly those cases, does the greedy algorithm restricted to that residue class always terminate?  
**Source:** erdosproblems.com/282; R. L. Graham, 'On finite sums of unit fractions', Proc. LMS (1964)  
**Statement matches intent:** suspect — Graham's arithmetic condition is transcribed correctly (Nat divisions x.den / gcd(x.den, gcd(a,d)) and d / gcd(a,d) are exact, so no truncation). Same repeated-denominator defect as `erdos_282`: the modelled process may reuse a denominator, so 'terminates' is not equivalent to 'is a sum of distinct unit fractions from the class'. Also, x is not required to be in lowest terms beyond Rat's normalisation (fine) and a is unrestricted mod d (harmless).  
**Known status:** Open. Graham's representability criterion is a theorem; the greedy-termination question in those cases is not settled. No PR/campaign coverage.  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** `answer(sorry)` here has expected type Prop, so under the default setting it elaborates to `True`, and the theorem asserts termination for every x, a, d meeting Graham's condition. This is strictly more general than `erdos_282` (which is the case a = 1, d = 2), hence at least as hard.  
**Flags:** inherits the repeated-denominator defect of greedyUnitFractionRem; no hypothesis that gcd(a,d) constraints make the residue class nonempty/infinite (harmless since d > 1)  
**Next action:** Fix the greedy definition (distinct denominators), then attack the arithmetic-progression case a = 1, d = 2 (odd denominators) first, i.e. reduce to `erdos_282`.

## `erdos_282.variants.sq` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/282.lean:115`  
**Statement:** Graham showed x is a sum of distinct unit fractions with square denominators exactly when x is in [0, pi^2/6 - 1) or [1, pi^2/6). Does the greedy algorithm with square denominators terminate for every such x? (Erdos and Graham expect not.)  
**Source:** erdosproblems.com/282; Graham, 'On finite sums of reciprocals of distinct nth powers', Pacific J. Math (1964)  
**Statement matches intent:** suspect — The membership range for Graham's theorem is transcribed correctly. But the repeated-denominator defect is severe here: for x = 1/2 (which lies in [0, pi^2/6 - 1) since pi^2/6 - 1 ~ 0.6449) the modelled greedy gives 1/2 - 1/4 = 1/4 and then picks 4 again, terminating with 1/2 = 1/4 + 1/4, which is not a representation by *distinct* squares. So the formal 'terminates' predicate is strictly weaker than the intended one and the expected answer (False) could in principle flip.  
**Known status:** Open; Erdos and Graham conjectured non-termination, possibly almost always. No PR/campaign coverage.  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** small · **Confidence:** medium  
**Evidence:** Hand-computation of the modelled orbit of 1/3 with squares: 1/3 -> 1/12 -> 1/48 -> 1/2352 -> 1/115248 ...; the remainder stays a unit fraction whose denominator is never a square, illustrating the expected non-termination, but proving 'never a square' forever is an infinite statement with no known handle.  
**Flags:** repeated denominators allowed: explicit witness 1/2 = 1/4 + 1/4; answer(sorry) defaults to True, so the compiled statement asserts the direction Erdos/Graham believe is false  
**Next action:** Repair the definition to use distinct denominators; then a disproof needs a certified non-terminating orbit (e.g. show the remainder is always 1/n with n never a perfect square along an invariant family) - this is the realistic first milestone.

## `erdos_287` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/287.lean:38`  
**Secondary category:** 6 (Computationally solvable with certificate)  
**Statement:** If 1 = 1/n_1 + ... + 1/n_k with 1 < n_1 < ... < n_k, must some consecutive gap n_{i+1} - n_i be at least 3?  
**Source:** erdosproblems.com/287 (state: falsifiable, i.e. still open); Erdos [Er32] for the gap >= 2 case  
**Statement matches intent:** yes  
**Known status:** Open. The file's `gap_at_least_two` (Erdos 1932, sum of reciprocals of consecutive integers is never 1) and `prime_conjecture_implies` are stated but sorry'd. No PR or campaign targets Erdos 287.  
**Difficulty:** math 7/10, Lean 8/10 · **Compute:** medium · **Confidence:** medium  
**Evidence:** `max_gap` uses truncated Nat subtraction, but under `StrictMono s` every s(i+1) - s(i) >= 1 so no truncation occurs; the index type Fin (k-1) is nonempty for k >= 2 and the hypothesis 1 < s 0 correctly excludes n_i = 1. Statement is a faithful transcription. The `answer(sorry) : Prop` defaults to True, so it asserts the conjecture.  
**Next action:** Two tracks: (a) formalise the conditional reduction `prime_conjecture_implies` (Egyptian-fraction bookkeeping plus Bertrand); (b) run an exhaustive search over Egyptian representations of 1 with all gaps <= 2 (bounded k, bounded n_1) to build confidence / find a counterexample.

## `erdos_287.variants.prime_conjecture` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/ErdosProblems/287.lean:84`  
**Statement:** For all large N there is a prime p in [N, 2N] with (p+1)/2 also prime (equivalently, a prime q with 2q-1 prime in every dyadic range).  
**Source:** erdosproblems.com/287 (auxiliary conjecture noted there); Dickson/Hardy-Littlewood prime k-tuple heuristics  
**Statement matches intent:** yes  
**Known status:** Open, and of twin-prime strength: no unconditional method produces two simultaneous primes in a linear pattern, let alone in every dyadic interval. Sieve theory gives only almost-prime substitutes (Chen-type).  
**Difficulty:** math 9/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Nat division (p+1)/2 is exact for odd p and yields 1 (non-prime) for p = 2, so no junk-value loophole. The parity/prime-pattern obstruction is the same one that blocks the twin prime conjecture.  
**Next action:** Do not attempt; keep as a recorded auxiliary open conjecture. If desired, formalise the Hardy-Littlewood heuristic count as a separate variant.

## `erdos_288` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/288.lean:33`  
**Statement:** Are there only finitely many pairs of integer intervals I1, I2 with sum of 1/n over I1 plus sum of 1/n over I2 an integer?  
**Source:** erdosproblems.com/288 (state: open); Erdos-Graham  
**Statement matches intent:** yes  
**Known status:** Open. The one-interval case (no interval sum of reciprocals other than [1,1] is an integer) is the classical Kurschak/Erdos theorem; the two-interval case is open because 2-adic valuations can cancel between the two intervals. No PR/campaign coverage.  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** Sum notation over `Set.Icc` on N+ resolves through the LocallyFiniteOrder/Fintype instance; `(n^-1 : Q)` elaborates as the inverse of the coercion, so no junk value (N+ has no zero). The mathematical obstruction (cancellation of p-adic valuations across the two intervals) is exactly why the problem is open.  
**Flags:** existential quantifier nested inside the forall j (harmless but should be hoisted for readability)  
**Next action:** First formalise the single-interval theorem (unique maximal power of 2 in an interval gives negative 2-adic valuation) as reusable API; then attack pairs via a p-adic/Bertrand argument.

## `erdos_288.variants.exists_k_gt_2` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/288.lean:59`  
**Secondary category:** 10 (Cannot classify without correction/clarification)  
**Statement:** Is there at least one k > 2 for which only finitely many k-tuples of intervals have integer combined reciprocal sum?  
**Source:** erdosproblems.com/288 (remark about k > 2)  
**Statement matches intent:** suspect — The docstring reads 'Is it true for any k > 2 that only finitely many ...', which in mathematical English normally means 'for every k > 2' - but the Lean uses `exists k > 2`. If the source sentence is 'this is not known for any k > 2', the existential reading is right; if it is 'is it true for every k > 2', the statement is strictly weaker than intended (and then it is also redundant with `k_intervals`). erdosproblems.com could not be fetched (HTTP 403) to adjudicate.  
**Known status:** Open under either reading; no k > 2 case is known to be finite. No PR/campaign coverage.  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** none · **Confidence:** low  
**Evidence:** Formally the statement is strictly weaker than `k_intervals` (one witness k suffices) yet no witness is known, so it is not trivially closable; the risk here is prose/formal mismatch, not a proof loophole.  
**Flags:** quantifier reading ambiguity: 'for any k > 2' formalised as exists, not forall; needs literature check (erdosproblems.com fetch blocked)  
**Next action:** Confirm the source wording, then either keep the existential (documenting 'not known for any k > 2') or change to a universal statement; mathematically, prove finiteness for one concrete k (k = 3) first.

## `erdos_288.variants.i2_card_eq_1` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/288.lean:42`  
**Statement:** Same question when the second interval is a single integer: are there only finitely many pairs (I, n2) with (sum of 1/n over I) + 1/n2 an integer?  
**Source:** erdosproblems.com/288 ('this is still open even if |I_2| = 1')  
**Statement matches intent:** yes  
**Known status:** Open per the problem page; a special case of `erdos_288` and therefore no harder, but still unresolved.  
**Difficulty:** math 7/10, Lean 8/10 · **Compute:** small · **Confidence:** medium  
**Evidence:** Faithful transcription (N+ everywhere, so no division-by-zero or empty-interval degeneracies; I.1 <= I.2 keeps intervals nonempty). Strictly weaker than the main statement, so it is the right entry point.  
**Next action:** Attack this case first: sum over [a,b] plus 1/n2 in N forces strong p-adic constraints on n2; a proof here would be the natural first milestone for Erdos 288.

## `erdos_288.variants.k_intervals` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/288.lean:50`  
**Statement:** For every k, are there only finitely many k-tuples of intervals whose combined reciprocal sum is an integer?  
**Source:** erdosproblems.com/288 ('perhaps true with two intervals replaced by any k intervals')  
**Statement matches intent:** yes  
**Known status:** Open; strictly implies `erdos_288`, which is itself open.  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** Same encoding as erdos_288 with Fin k; the nested existential is again harmless for k >= 1 and for k = 0 the constraint set is a singleton function type, so no vacuous-truth issue arises that would weaken the k >= 2 content.  
**Next action:** Deprioritise relative to `i2_card_eq_1`/`erdos_288`; nothing is gained by attacking the uniform-in-k form first.

## `erdos_289` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/289.lean:34`  
**Secondary category:** 6 (Computationally solvable with certificate)  
**Statement:** For all sufficiently large k, can 1 be written as the sum of reciprocals over k pairwise disjoint integer intervals, each containing at least two integers?  
**Source:** erdosproblems.com/289 (state: open); Erdos-Graham  
**Statement matches intent:** suspect — Faithful except for a junk-value hole: the intervals live in N and (0 : Q)^-1 = 0, so an interval [0,1] has 'length 2' but contributes exactly 1. This makes the k = 1 instance true for a spurious reason (intended k = 1 is impossible by the Kurschak/Erdos theorem). Since only one interval can contain 0 and every other interval has positive sum, the loophole cannot help any k >= 2, and the statement is about large k, so the mathematical content is unaffected.  
**Known status:** Open. No PR or campaign entry; PR #148 matched on the string '289' only via 'WorldCup7' noise and is unrelated.  
**Difficulty:** math 7/10, Lean 8/10 · **Compute:** medium · **Confidence:** medium  
**Evidence:** Disjointness is encoded correctly ((I i).2 < (I j).1 or (I j).2 < (I i).1 for i != j), and (I i).1 < (I i).2 gives |I_i| >= 2. The eventual-in-k form `forall^f k in atTop` matches 'for all sufficiently large k'.  
**Flags:** 1/0 = 0 junk value lets [0,1] act as the singleton {1} (affects only k = 1)  
**Next action:** Search computationally for interval decompositions of 1 for k = 2..12 (each interval [a,b] with b > a); a repeatable splitting identity turning a valid k-decomposition into a (k+1)-decomposition would give the whole conjecture by induction and is the right milestone.

## `erdos_291.parts.i` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/291.lean:59`  
**Statement:** Writing H_n = a_n / L_n with L_n = lcm(1..n), is gcd(a_n, L_n) = 1 for infinitely many n?  
**Source:** erdosproblems.com/291 (state: open); [ErGr80, p.34]; Shiu, arXiv:1607.02863; Wu-Yan, C. R. Acad. Sci. Paris (2022)  
**Statement matches intent:** yes  
**Known status:** Open. The complementary question (gcd > 1 infinitely often) is trivially yes (Steinerberger); the heuristic predicts ~ x/log x such n up to x. No PR/campaign coverage.  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** small · **Confidence:** medium  
**Evidence:** `a n = sum_{k=1..n} L n / k` uses Nat division, which is exact because k | L n for k <= n, so a n is genuinely the numerator over L n. Statement is faithful. The obstruction is that avoiding p | (a_n, L_n) for all p <= n simultaneously requires unproved independence of base-p leading digits.  
**Next action:** Attack via the file's own `steinerberger_generalization`: gcd(a_n, L_n) = 1 iff for every prime p <= n, p does not divide the numerator of H_k with k the leading base-p digit of n. Producing infinitely many n avoiding all these conditions simultaneously is a covering/sieve problem - formalise the criterion first, then attempt an explicit construction.

## `erdos_291.variants.shiu_heuristic_asymptotic` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/ErdosProblems/291.lean:95`  
**Statement:** The number of n <= x with gcd(a_n, L_n) = 1 is of order x / log x.  
**Source:** erdosproblems.com/291; P. Shiu, 'The denominators of harmonic numbers', arXiv:1607.02863 (2016) - heuristic only  
**Statement matches intent:** yes  
**Known status:** Only a heuristic prediction; no proof of even the infinitude (part i), let alone the order of magnitude. Strictly stronger than `erdos_291.parts.i`.  
**Difficulty:** math 9/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** The statement implies infinitude (part i, open) and additionally a matching upper bound; the underlying heuristic assumes independence of the base-p leading-digit conditions across all primes p <= n, which is exactly what cannot currently be proved.  
**Flags:** labelled 'research open' but is a heuristic prediction, not a stated conjecture of Erdos - severity: documentation only  
**Next action:** Do not attempt; record as a heuristic. Any progress would first require part (i).

## `erdos_291.variants.shiu_heuristic_density_zero` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/291.lean:106`  
**Statement:** The set of n with gcd(a_n, L_n) = 1 has natural density zero.  
**Source:** erdosproblems.com/291; Shiu (heuristic); Wu-Yan, C. R. Acad. Sci. Paris (2022) proved (conditionally on Q-linear independence of 1/log p, a consequence of Schanuel) that {n : gcd > 1} has upper density 1  
**Statement matches intent:** yes  
**Known status:** Open unconditionally. Wu-Yan give upper density 1 for the complement conditionally on Schanuel-type independence, which is weaker than the lower density 1 needed here.  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** Density zero of {gcd = 1} is equivalent to density one of {gcd > 1}; the file itself records only the conditional upper-density-1 result (`wu_yan`), so a genuine gap remains, but that result is an identifiable avenue (hence 8, not 9).  
**Next action:** Formalise the Steinerberger criterion, then try to upgrade the Wu-Yan argument from upper density to density; medium-to-large effort even conditionally.

## `erdos_295` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/295.lean:52`  
**Statement:** Let k(N) be the least number of terms in a representation 1 = 1/n_1 + ... + 1/n_k with N <= n_1 < ... < n_k. Does k(N) - (e-1)N tend to infinity?  
**Source:** erdosproblems.com/295 (state: open); Erdos-Straus bounds -c < k(N) - (e-1)N << N/log N  
**Statement matches intent:** suspect — Off-by-one: `k N := Nat.find (exists_k N)` searches over k such that there is a representation indexed by `Fin k.succ`, so `k N` equals (true minimal number of terms) - 1. Since the question is whether k(N) - (e-1)N -> infinity, a fixed shift by 1 does not change the truth value (and likewise is absorbed by the constant c in the Erdos-Straus variant), but the definition does not literally match the docstring.  
**Known status:** Open. Erdos and Straus proved the two-sided bound recorded in the file (also sorry'd); whether the difference is unbounded is unresolved. No PR/campaign coverage.  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** The limit is taken in R (`rexp 1` forces the coercion of k N), so there is no Nat-subtraction truncation. `Filter.atTop.Tendsto f atTop` correctly means Tendsto f atTop atTop. The mathematical difficulty is the lower-order term in the Erdos-Straus analysis of greedy-type Egyptian representations starting above N.  
**Flags:** k N is off by one from the documented k(N) (harmless for the limit, but should be corrected); the definition of k depends on the sorry'd lemma exists_k  
**Next action:** Fix the Fin k.succ off-by-one; first formalise the helper `exists_k` (currently sorry'd), e.g. via a greedy construction with denominators >= N, since everything downstream depends on it.

## `erdos_3` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/ErdosProblems/3.lean:31`  
**Statement:** If a set A of naturals has divergent sum of reciprocals, must A contain arbitrarily long arithmetic progressions? (Erdos' $5000 conjecture on APs.)  
**Source:** erdosproblems.com/3 (state: open, prize $5000); Erdos-Turan; Green-Tao (primes case)  
**Statement matches intent:** yes  
**Known status:** Famous open problem; the k = 3 case (Bloom-Sisask 2020: sets of density >> 1/(log N)^{1+c} contain 3-APs) is known, longer progressions are open. No PR/campaign coverage; not duplicated elsewhere in the repo.  
**Difficulty:** math 10/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** `Set.IsAPOfLength` unfolds via `IsAPOfLengthWith`, which requires `ENat.card s = l`, so degenerate common difference 0 (a singleton) cannot masquerade as a long progression; the `exists^f k in atTop` form correctly says 'arbitrarily long'. Non-summability of 1/a over the subtype is the right divergence condition (0 in A contributes the harmless term 0).  
**Next action:** Do not attempt. If desired, add the known partial results (Behrend lower bound, Bloom-Sisask) as variants, per the file's own TODO.

## `erdos_30` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/ErdosProblems/30.lean:38`  
**Statement:** Is the maximum size h(N) of a Sidon set in {1,...,N} equal to sqrt(N) + O(N^eps) for every eps > 0? ($1000 problem.)  
**Source:** erdosproblems.com/30 (state: open, prize $1000); Erdos-Turan 1941; Lindstrom  
**Statement matches intent:** yes  
**Known status:** Famous open problem; best known is h(N) = sqrt(N) + O(N^{1/4}) (Lindstrom), and even h(N) = sqrt(N) + O(N^{1/4 - c}) is unknown. No PR/campaign coverage; ErdosProblems/43, /44, /155 and GreensOpenProblems/31 reuse `maxSidonSubsetCard` but state different questions, so no duplicate.  
**Difficulty:** math 9/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** `h N - (N : R).sqrt` elaborates in R (the Real sqrt forces a coercion of the Nat cardinality), so there is no truncated subtraction; the eps-quantifier is outside the IsBigO as intended. `maxSidonSubsetCard A = sup over Sidon subsets of A of card` (FormalConjecturesForMathlib/Combinatorics/Basic.lean:153) is the right notion.  
**Next action:** Do not attempt. Adding the Lindstrom upper bound h(N) <= sqrt(N) + N^{1/4} + 1 as a variant (the file's TODO) is the useful contribution; ErdosProblems/44 already has a weak version (<= 2 sqrt N).

## `upper_bound` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/304.lean:172`  
**Statement:** Let N(a,b) be the least number of distinct unit fractions summing to a/b and N(b) its maximum over 1 <= a < b. Is N(b) << log log b?  
**Source:** erdosproblems.com/304 (state: open); Erdos [Er50c] (loglog b << N(b) << log b/loglog b); Vose 1985 (N(b) << sqrt(log b))  
**Statement matches intent:** yes  
**Known status:** Open; Vose's sqrt(log b) is the record upper bound and matching the loglog b lower bound is the conjecture. No PR/campaign coverage.  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** `unitFractionExpressible` uses a Finset (hence distinct denominators) with all n > 1 and `(a / b : Q)` is genuine rational division, so there is no Nat-division junk. `smallestCollection = sInf` would return the junk value 0 for a non-expressible a/b, but every 0 < a/b is expressible (Fibonacci greedy), and `smallestCollectionTo` takes sSup over the finite index set Ico 1 b, so both are well behaved.  
**Flags:** declaration not namespaced as erdos_304.* (cosmetic); sInf junk value 0 if some a/b were inexpressible - benign but the file itself notes nonemptiness is unproved  
**Next action:** Formalising Vose's bound (variant `upper_1985`) is the realistic target; the conjecture itself needs a new idea beyond Vose's probabilistic/greedy hybrid.

## `erdos_306` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/306.lean:35`  
**Statement:** Is every positive rational with squarefree denominator a sum of distinct unit fractions whose denominators are each a product of two distinct primes?  
**Source:** erdosproblems.com/306 (state: open); Erdos-Graham  
**Statement matches intent:** yes  
**Known status:** Open; the companion result for products of three distinct primes representing integers is known (recorded as a solved variant in the same file, also sorry'd). No PR/campaign coverage.  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** Faithful transcription of the source question, including the squarefree condition on q.den and strict increase of the denominators. Difficulty is genuine Egyptian-fraction research (control of denominators restricted to semiprimes).  
**Flags:** sentinel-index encoding (n 0 = 1 plus Icc 1 (Fin.last k)) is fragile and hard to read, though correct here  
**Next action:** Milestone: formalise the density/greedy machinery for sums of 1/(pq) (the relevant series diverges), then attempt the squarefree-denominator case by induction on the denominator's prime factors.

## `erdos_307` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/307.lean:41`  
**Secondary category:** 6 (Computationally solvable with certificate)  
**Statement:** Are there finite sets of primes P and Q with (sum of 1/p over P) times (sum of 1/q over Q) = 1?  
**Source:** erdosproblems.com/307 (state: verifiable, i.e. still open); asked by Barbeau [Ba76]  
**Statement matches intent:** yes  
**Known status:** Open. The same file records a machine-checked barrier (Bonfioli 2026, external Lean repo github.com/ElVec1o/erdos307 at v1.0.0): any solution with Q nonempty needs >= 59 primes and prod P >= 2*10^56 - so no small witness exists. That barrier theorem is itself still `sorry` in this repo. No PR/campaign in this fork targets it.  
**Difficulty:** math 8/10, Lean 8/10 · **Compute:** large · **Confidence:** medium  
**Evidence:** Statement is a faithful, fully explicit existential over Finsets of primes (empty P or Q gives product 0 != 1, so no degenerate witness). 'verifiable' status means a witness would settle it, but the 59-prime / 2*10^56 barrier rules out brute force.  
**Flags:** erdos_307.barrier is marked 'research solved' with an external formal_proof link but is sorry in this repo - importable, high value  
**Next action:** Two options: (a) port the external barrier proof (Closed.lean) to discharge `erdos_307.barrier` here and verify the build; (b) for the main question, a positive answer would need a search far beyond the 10^56 barrier, so the realistic direction is a non-existence proof via p-adic valuation constraints.

## `erdos_307.variants.coprime_one_notMem` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/307.lean:70`  
**Secondary category:** 6 (Computationally solvable with certificate)  
**Statement:** Weaken 'primes' to 'pairwise coprime integers' but forbid the element 1: are there sets P, Q (each of size > 1) of pairwise coprime integers with (sum 1/p)(sum 1/q) = 1?  
**Source:** erdosproblems.com/307 remark; Cambie's examples all use 1 in P (e.g. (1 + 1/5)(1/2 + 1/3) = 1, (1 + 1/41)(1/2 + 1/3 + 1/7) = 1)  
**Statement matches intent:** yes  
**Known status:** Open in the sense that no example is known; a single explicit example would close it immediately in Lean. No PR/campaign coverage.  
**Difficulty:** math 6/10, Lean 3/10 · **Compute:** medium · **Confidence:** medium  
**Evidence:** Known solutions rely essentially on 1 (the factor 1 + 1/n = (n+1)/n cancels a sum of the shape n/(n+1)); without 1, both factors are < 1 unless a set has many small pairwise coprime elements, which is heavily constrained (e.g. P = {2,3} forces sum Q = 6/5, and the 6-adic obstruction kills the natural candidates). ldiff is low *if* a witness exists.  
**Flags:** 0 notin (P inter Q) should probably be 0 notin (P union Q) - currently harmless because of the coprimality and card conditions  
**Next action:** Run a bounded computer search over pairwise-coprime sets with elements in [2, 10^4] and small cardinalities; if a witness appears, the Lean proof is `use P, Q; norm_num +decide`. Otherwise leave open and record the search bound.

## `erdos_312` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/312.lean:32`  
**Statement:** Is there c > 0 such that for every K > 1, any (sufficiently large) finite multiset A of integers with sum of 1/n over A greater than K has a sub-multiset S with 1 - e^{-cK} < sum of 1/n over S <= 1?  
**Source:** erdosproblems.com/312 (state: open); Erdos-Graham  
**Statement matches intent:** suspect — Two encoding issues. (1) Elements are drawn from N, and (0 : R)^-1 = 0, so the multiset may be padded with arbitrarily many zeros without changing any subset sum; this makes the 'sufficiently large' hypothesis (n >= N_0) vacuous and silently strengthens the statement to 'for every finite multiset'. (2) 'Sufficiently large finite multiset' is ambiguous in the source (large cardinality vs. large elements); the Lean picks cardinality. Both matter for the truth value if the intended relaxation was essential.  
**Known status:** Open. No PR/campaign coverage.  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** The quantifier order (c first, then K, then N_0, then the multiset) is correct and blocks the cheat of shrinking c, since for fixed c the threshold 1 - e^{-cK} tends to 1 as K grows. The empty S is never a witness because 1 - e^{-cK} > 0.  
**Flags:** 1/0 = 0 junk value lets zero-padding neuter the 'sufficiently large' hypothesis; needs literature check on the meaning of 'sufficiently large' in the source  
**Next action:** Require a i >= 1 (or use a multiset of positive integers) so that the n >= N_0 hypothesis has real content, and check the source for what 'sufficiently large' means; then attack via a greedy/exchange argument giving the exponential approximation rate.

## `erdos_313` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/ErdosProblems/313.lean:42`  
**Statement:** Are there infinitely many pairs (m, P) with m >= 2 and P a finite set of distinct primes such that the sum of 1/p over P equals 1 - 1/m? (Equivalently, infinitely many primary pseudoperfect numbers.)  
**Source:** erdosproblems.com/313 (state: open); OEIS A054377 (2, 6, 42, 1806, 47058, 2214502422, 52495396602, 8490421583559688410706771261086)  
**Statement matches intent:** yes  
**Known status:** Open; only 8 primary pseudoperfect numbers are known (none since 1999 despite extensive search), and no heuristic even predicts infinitude convincingly. No PR/campaign coverage (register hits on '313' were all OEIS A263135 noise).  
**Difficulty:** math 9/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** The Sylvester-like recursion generating these numbers must produce a prime at every step, and no mechanism is known to guarantee this infinitely often; the eighth term (31 digits) was found by exhaustive search in 1999 and none has been found since.  
**Next action:** Do not attempt the infinitude claim. Useful nearby work: formalise the m = prod P lemma sketched above (short gcd argument, genuinely provable) as API.

## `erdos_313.variants.primary_pseudoperfect_are_infinite` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/ErdosProblems/313.lean:63`  
**Statement:** There are infinitely many primary pseudoperfect numbers (integers n = p_1...p_k with 1/n + sum 1/p_i = 1).  
**Source:** erdosproblems.com/313; OEIS A054377; Butske-Jaje-Mayernik, Math. Comp. (2000)  
**Statement matches intent:** yes  
**Known status:** Open, and asserted here unconditionally (no answer() escape hatch), so this declaration is a full conjecture. The file already proves >= 8 such numbers exist (`exists_at_least_eight_primary_pseudoperfect`, using native_decide).  
**Difficulty:** math 9/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Same obstruction as erdos_313: infinitude would require an unbounded Sylvester-type sequence in which every step yields a prime; nothing in current technology addresses this.  
**Flags:** duplicate of erdos_313 up to a trivial equivalence  
**Next action:** Do not attempt; consider merging with `erdos_313` or documenting the equivalence, since the two declarations state the same open problem.

## `erdos_317` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/317.lean:33`  
**Statement:** Is there a constant c>0 such that for every n>=1 one can choose signs delta_k in {-1,0,1} making 0 < |sum_{k<=n} delta_k/k| < c/2^n?  
**Source:** https://www.erdosproblems.com/317 (Erdos-Graham, unit fractions); erdosproblems.com state = open (2026-07-26)  
**Statement matches intent:** yes  
**Known status:** Open on erdosproblems.com. No PR in this fork (pr_register.json has no 317 entry apart from unrelated OEIS A317940 PRs #32/#43/#152) and no campaign entry. Trivial lower bound: any nonzero such sum is >= 1/lcm(1..n) ~ e^{-n}, which is below 2^{-n}, so no easy obstruction exists.  
**Difficulty:** math 9/10, Lean 9/10 · **Compute:** small · **Confidence:** high  
**Evidence:** Exhaustive DP over all 3^n sign patterns for n<=16 (scaled by lcm(1..16)) gives min-nonzero-|sum| * 2^n = 2.0, 2.0, 1.33, 1.33, 1.07, 2.13, 1.22, 2.13, 0.81, 1.22, 0.89, 1.77, 0.20, 0.41, 0.82, 1.64 for n=1..16 — bounded, so the conjecture looks TRUE, but nothing in the range gives a proof idea. Pigeonhole cannot work: the number of distinct subsums of {1,...,1/n} is exp(o(n)) (Bleicher-Erdos, cf. problem 320/321), far fewer than 2^n.  
**Next action:** Treat as genuinely open. First milestone: formalize the computational evidence (min nonzero |sum| times 2^n) or the 1/lcm lower bound `claim2_inequality`; do not attempt the full statement.

## `erdos_317.variants.claim2` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/317.lean:46`  
**Statement:** For all sufficiently large n and any signs delta_k in {-1,0,1}, is |sum_{k<=n} delta_k/k| > 1/lcm(1,...,n) whenever the sum is nonzero?  
**Source:** https://www.erdosproblems.com/317 (second question on the page); state = open  
**Statement matches intent:** yes  
**Known status:** Open. The non-strict inequality is immediate (all sums are integer multiples of 1/lcm(1..n)); only strictness is at stake, and it genuinely fails for small n (1/2-1/3-1/4 = -1/12 with lcm(1..4)=12), which is why `∀ᶠ n in atTop` is used.  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** small · **Confidence:** high  
**Evidence:** Exhaustive computation of min nonzero |sum| * lcm(1..n) for n=1..16: 1,1,1,1,2,2,4,7,4,3,12,12,9,9,9,18. Equality (value 1) occurs exactly for n<=4, and the minimum is >=2 for 5<=n<=16, so the answer is plausibly True with threshold n>=5. Proving it for all large n is open.  
**Next action:** Open research statement. Useful intermediate work: formalize `claim2_inequality` (divide through by lcm and use integrality) and extend the finite verification.

## `erdos_319` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/ErdosProblems/319.lean:41`  
**Statement:** What is the largest size of A ⊆ {1,...,N} admitting signs delta_n = ±1 with sum_{n in A} delta_n/n = 0 but no nonempty proper subset of A summing to 0?  
**Source:** https://www.erdosproblems.com/319; state = open. Lower bound (1-1/e+o(1))N via Croot [Cr01] recorded as `erdos_319.variants.lb`.  
**Statement matches intent:** yes  
**Known status:** Open: only (1-1/e+o(1))N <= c(N) <= N is known. No internal PR or campaign touches 319.  
**Difficulty:** math 9/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** The formal statement demands the exact extremal value for every N; even the asymptotic constant is unknown (gap between 1-1/e ≈ 0.632 and 1).  
**Flags:** answer(sorry) for an exact extremal function admits a degenerate 'answer' equal to the sSup of the same set — a filled answer must be an independent closed form  
**Next action:** Leave open; the realistic target in this file is `variants.lb` (Croot), not the exact maximum.

## `erdos_319.variants.isBigO` — Vacuously true / accidentally weakened (cat 4)

**File:** `FormalConjectures/ErdosProblems/319.lean:84`  
**Secondary category:** 2 (Trivially or easily solvable)  
**Statement:** Find g with c(N) = O(g(N)) for the Erdos 319 extremal function c.  
**Source:** https://www.erdosproblems.com/319  
**Statement matches intent:** suspect — Accidentally weakened: any g growing at least linearly is a valid answer, so the statement carries no information about the actual problem. Explicitly acknowledged by the formalisation note at lines 49-54.  
**Known status:** Not a real open problem in this form; closable now.  
**Difficulty:** math 1/10, Lean 3/10 · **Compute:** none · **Confidence:** high  
**Evidence:** h : ∀ N, IsGreatest S (c N) gives c N ∈ S, i.e. c N = (#A : ℝ) for some A ⊆ Finset.Icc 1 N; Finset.card_le_card gives #A <= N. Hence |c N| <= 1 * |N| for all N.  
**Flags:** trivially satisfiable answer() — does not certify optimality  
**Next action:** Fill `answer := fun N => (N : ℝ)` and prove: from h N obtain A ⊆ Icc 1 N with c N = #A, so c N <= #(Icc 1 N) = N; conclude with `Asymptotics.isBigO_of_le`. Then verify the build (lake cannot be run in this container).

## `erdos_319.variants.isLittleO` — Vacuously true / accidentally weakened (cat 4)

**File:** `FormalConjectures/ErdosProblems/319.lean:103`  
**Secondary category:** 2 (Trivially or easily solvable)  
**Statement:** Find g with c(N) = o(g(N)) for the Erdos 319 extremal function c.  
**Source:** https://www.erdosproblems.com/319  
**Statement matches intent:** suspect — Same escape-hatch weakening as isBigO: any super-linear g works, e.g. N^2.  
**Known status:** Not a real open problem in this form; closable now.  
**Difficulty:** math 1/10, Lean 4/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Same derivation of c N <= N from h; N = o(N^2) at atTop.  
**Flags:** trivially satisfiable answer() — does not certify optimality  
**Next action:** Fill `answer := fun N => (N : ℝ)^2` and prove from c N <= N that c N / N^2 → 0 (`Asymptotics.isLittleO_of_tendsto` / `isBigO.trans_isLittleO`). Verify the build afterwards.

## `erdos_319.variants.isTheta` — Solved mathematically, not yet formalized (cat 5)

**File:** `FormalConjectures/ErdosProblems/319.lean:65`  
**Secondary category:** 4 (Vacuously true / accidentally weakened)  
**Statement:** Determine the order of growth Theta(c(N)) of the maximal size c(N) from Erdos 319.  
**Source:** https://www.erdosproblems.com/319; Croot [Cr01] lower bound via Adenwalla, as cited in the same file.  
**Statement matches intent:** suspect — Θ only pins the answer up to constants, so `answer := fun N => (N : ℝ)` is the correct and complete answer — much weaker than the actual question (the extremal constant). The file's own formalisation note admits this.  
**Known status:** Mathematically settled: c(N) <= N trivially and c(N) >= (1-1/e+o(1))N by Croot's short-interval unit-fraction theorem, so c =Θ[atTop] id. Not formalized: Croot's theorem is not in Mathlib.  
**Difficulty:** math 5/10, Lean 9/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** Hypothesis h gives c N ∈ {#A | A ⊆ Icc 1 N ∧ ...}, hence c N <= N, giving the O half immediately; the Ω half is exactly `erdos_319.variants.lb` which is stated (with sorry) in the same file as research solved.  
**Flags:** asymptotic-variant escape hatch: correct answer is trivially 'N', so this does not capture Erdos 319  
**Next action:** Fill answer with `fun N => (N : ℝ)`; the O-direction follows from h in a few lines (members of the set are #A <= N). The Ω-direction needs Croot [Cr01] — research-scale formalization; alternatively find a cheaper explicit linear-size construction.

## `erdos_32` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/32.lean:68`  
**Statement:** Is there a set A ⊆ ℕ with |A ∩ [1,N]| = o((log N)^2) such that every sufficiently large integer is p + a with p prime and a in A?  
**Source:** https://www.erdosproblems.com/32; [Erd54] Erdos, Some results on additive number theory (1954); [Ru98c] Ruzsa (1998). erdosproblems.com state = open.  
**Statement matches intent:** yes  
**Known status:** Open. Erdos [Erd54] gives an O((log N)^2) complement (recorded as variants.log_squared); Ruzsa's e^gamma liminf lower bound (variants.ruzsa) is the only obstruction known. No fork PR or campaign touches problem 32.  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** Both directions are plausible; the only known constraints are A(N) >> log N (Ruzsa) from below and (log N)^2 from above, leaving the whole range in between unresolved.  
**Flags:** needs literature check: could not reach erdosproblems.com (HTTP 403 through the proxy); relying on the batch's state=open and on [Ru98c]/[Erd54] as cited in the file  
**Next action:** Genuinely open; the tractable target in this file is Erdos' O((log N)^2) construction (variants.log_squared), a medium-large formalization (probabilistic/greedy construction plus prime counting).

## `erdos_32.variants.log_bound` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/ErdosProblems/32.lean:79`  
**Statement:** Is there an additive complement A to the primes with |A ∩ [1,N]| = O(log N)? (Erdos offered $50.)  
**Source:** https://www.erdosproblems.com/32; [Guy04] Guy, Unsolved Problems in Number Theory; Ruzsa [Ru98c]. State = open.  
**Statement matches intent:** yes  
**Known status:** Open, prize problem. Ruzsa's liminf >= e^gamma shows the constant cannot be beaten below e^gamma, but existence at the log N scale is untouched.  
**Difficulty:** math 9/10, Lean 10/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** Advertised prize problem in [Guy04]; the gap between the known O((log N)^2) construction and the Omega(log N) barrier has stood since 1954.  
**Flags:** needs literature check: erdosproblems.com unreachable from this container  
**Next action:** Do not attempt. If any work is done in this file, do Ruzsa's lower bound (variants.ruzsa) or Erdos' construction instead.

## `erdos_321` — Already solved externally (cat 1)

**File:** `FormalConjectures/ErdosProblems/321.lean:43`  
**Secondary category:** 8 (Deep but approachable research problem)  
**Statement:** Let R(N) be the largest size of A ⊆ {1,...,N} such that all subset sums of {1/n : n in A} are distinct. What is R(N)?  
**Source:** https://www.erdosproblems.com/321; [BlEr75], [BlEr76b] Bleicher-Erdos. Batch metadata: erdosproblems.com state = 'solved' as of 2026-07-26.  
**Statement matches intent:** suspect — The formal statement demands an exact closed form R N = answer for EVERY N. A solution recorded on erdosproblems.com for this kind of question is almost certainly asymptotic (the Bleicher-Erdos bounds in the same file are asymptotic with iterated logs), so the external solution probably does not close this exact-value form. The `R` definition itself is faithful (sSup over A ⊆ Icc 1 N with InjOn of S ↦ sum_{n in S} 1/n on A.powerset; nonempty since A = ∅ qualifies, bounded by N).  
**Known status:** Marked solved externally on erdosproblems.com (batch metadata). I could NOT retrieve the solution: erdosproblems.com returns 403 through this container's proxy, and targeted web searches surfaced only related unit-fraction work (e.g. Korsky, 'A Stretched-Exponential Bound for an Erdos-Graham Unit-Fraction Problem', arXiv:2607.04157, which concerns a different problem). No internal PR/campaign for 321.  
**Difficulty:** math 6/10, Lean 9/10 · **Compute:** none · **Confidence:** low  
**Evidence:** Batch-supplied authoritative status 'solved'; unverified independently. The file still records only the 1975/1976 Bleicher-Erdos upper and lower bounds (both with sorry), which differ by an iterated-log factor.  
**Flags:** needs literature check — external solution not confirmed, cited only from batch metadata; exact-value formalization may not correspond to what was solved  
**Next action:** Retrieve erdosproblems.com/321 (and its cited paper) from a network that can reach it; then decide whether the resolution gives an exact formula (fills this statement) or only an asymptotic (in which case restate as the isTheta variant and re-file this one).

## `erdos_321.variants.isBigO` — Vacuously true / accidentally weakened (cat 4)

**File:** `FormalConjectures/ErdosProblems/321.lean:69`  
**Secondary category:** 2 (Trivially or easily solvable)  
**Statement:** Find g with R(N) = O(g(N)) for the Erdos 321 extremal function R.  
**Source:** https://www.erdosproblems.com/321 (formalisation-note variant, lines 48-55)  
**Statement matches intent:** suspect — Accidentally weakened: g(N) = N is a valid answer since R N <= N by definition, so the statement says nothing about the problem. The file's own formalisation note concedes that trivial solutions exist.  
**Known status:** Closable now regardless of the external status of 321.  
**Difficulty:** math 1/10, Lean 3/10 · **Compute:** none · **Confidence:** high  
**Evidence:** R is defined as sSup of a set of naturals each of the form #A with A ⊆ Finset.Icc 1 N; Finset.card_le_card and Nat.card_Icc give the bound N.  
**Flags:** trivially satisfiable answer()  
**Next action:** Fill `answer := fun N => (N : ℝ)`; prove R N <= N by `Nat.sSup_le` (every member is #A with A ⊆ Finset.Icc 1 N, so #A <= N), then `Asymptotics.isBigO_of_le`. Verify the build.

## `erdos_321.variants.isLittleO` — Vacuously true / accidentally weakened (cat 4)

**File:** `FormalConjectures/ErdosProblems/321.lean:77`  
**Secondary category:** 2 (Trivially or easily solvable)  
**Statement:** Find g with R(N) = o(g(N)) for the Erdos 321 extremal function R.  
**Source:** https://www.erdosproblems.com/321 (formalisation-note variant, lines 48-55)  
**Statement matches intent:** suspect — Same escape-hatch weakening: g(N) = N^2 works trivially.  
**Known status:** Closable now regardless of the external status of 321.  
**Difficulty:** math 1/10, Lean 4/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Same R N <= N bound as isBigO.  
**Flags:** trivially satisfiable answer()  
**Next action:** Fill `answer := fun N => (N : ℝ)^2`, reuse R N <= N, conclude via `Asymptotics.IsBigO.trans_isLittleO` with N = o(N^2). Verify the build.

## `erdos_321.variants.isTheta` — Already solved externally (cat 1)

**File:** `FormalConjectures/ErdosProblems/321.lean:61`  
**Secondary category:** 5 (Solved mathematically, not yet formalized)  
**Statement:** Determine Theta(R(N)) for the Erdos 321 extremal function R.  
**Source:** https://www.erdosproblems.com/321; Bleicher-Erdos [BlEr75],[BlEr76b]. Batch metadata: state = 'solved'.  
**Statement matches intent:** suspect — answer() up to constants; the Bleicher-Erdos bounds in the same file differ by a log_r N factor, so a Theta statement is exactly what a solution would provide — but the placeholder does not force optimality.  
**Known status:** Presumed determined by the external solution (state 'solved'); unverified here. Formalizing whichever bound is needed (N/log N times iterated logs) is substantial and not in Mathlib.  
**Difficulty:** math 6/10, Lean 9/10 · **Compute:** none · **Confidence:** low  
**Evidence:** Same as erdos_321: authoritative status from batch metadata only.  
**Flags:** needs literature check; answer() placeholder permits a sub-optimal Theta if paired with a wrong R bound  
**Next action:** Get the exact asymptotic from erdosproblems.com/321, fill answer, then formalize the matching upper and lower bounds (variants.lower / variants.upper in the same file are the natural stepping stones).

## `erdos_323.parts.i` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/ErdosProblems/323.lean:43`  
**Statement:** Is f_{k,k}(x), the number of integers <= x that are a sum of k nonnegative k-th powers, at least x^{1-eps} (up to constants) for every eps>0?  
**Source:** https://www.erdosproblems.com/323 (Erdos-Graham: 'unattackable by the methods at our disposal'); Landau for k=2. State = open.  
**Statement matches intent:** yes  
**Known status:** Open; would have significant consequences for Waring's problem, per Erdos-Graham. Best known for k=3 is Wooley's x^{0.917} (recorded in 325.lean). No fork PR or campaign.  
**Difficulty:** math 10/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Erdos and Graham explicitly describe this as unattackable; the k=3 case alone is only known down to exponent 0.917 after decades of work on sums of three cubes.  
**Next action:** Do not attempt. If the file is to be advanced, target `variants.k_eq_2` (Landau's theorem on sums of two squares) — itself a large Mathlib gap.

## `erdos_323.parts.ii` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/ErdosProblems/323.lean:52`  
**Statement:** For m < k, is the number of integers <= x that are sums of m nonnegative k-th powers at least of order x^{m/k}?  
**Source:** https://www.erdosproblems.com/323. State = open.  
**Statement matches intent:** yes  
**Known status:** Open. The trivial upper bound f_{k,m}(x) << x^{m/k} is easy; the matching lower bound requires controlling solutions of a_1^k+...+a_m^k = b_1^k+...+b_m^k, which for m=2, k=3 is already Hooley-level (giving only x^{2/k-eps}).  
**Difficulty:** math 9/10, Lean 10/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** The ∀ over all 1 <= m < k makes the statement at least as hard as its hardest instance; even m=2 needs sharp bounds on the number of coincidences a^k+b^k=c^k+d^k.  
**Next action:** Do not attempt in full. A meaningful partial step would be the m=1 case (f_{k,1}(x) = floor(x^{1/k})+1) or an eps-loss version via Cauchy-Schwarz plus a known bound on equal sums of k-th powers.

## `erdos_323.variants.k_gt_2` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/ErdosProblems/323.lean:71`  
**Statement:** For every k>2, is the number of integers <= x that are sums of k nonnegative k-th powers o(x) (i.e. density zero)?  
**Source:** https://www.erdosproblems.com/323 ('For k>2 it is not known if f_{k,k}(x)=o(x)'). State = open.  
**Statement matches intent:** yes  
**Known status:** Open. Only the trivial bound f_{k,k}(x) <= (Gamma(1+1/k)^k + o(1)) x < x is known; the k=2 analogue is Landau's x/sqrt(log x).  
**Difficulty:** math 9/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Deciding this for k=3 is equivalent to settling whether sums of three nonnegative cubes have density zero — a long-standing open problem; Wooley's x^{0.917} is the state of the art.  
**Flags:** interacts with 325.lean:erdos_325 — the k=3 instance there (f_{3,3}(x) >> x) is essentially the negation of this statement's k=3 case; both are answer(sorry), so an inconsistent pair of filled answers is possible  
**Next action:** Do not attempt. The natural (still open) route is to show a positive proportion of integers are sums of three nonnegative cubes.

## `erdos_324` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/ErdosProblems/324.lean:33`  
**Statement:** Does there exist an integer polynomial f such that all sums f(a)+f(b) with 0 <= a < b are distinct?  
**Source:** https://www.erdosproblems.com/324 (Erdos-Graham). State = open.  
**Statement matches intent:** yes  
**Known status:** Open; no polynomial is known to have the property, and no proof that none exists. No fork PR or campaign.  
**Difficulty:** math 9/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** A positive answer needs a Diophantine non-existence theorem of the shape 'f(a)+f(b)=f(c)+f(d) has only trivial solutions', which is not available for any known polynomial of degree >= 3.  
**Next action:** Do not attempt directly; it reduces to the quintic variant below (f = X^5), which is itself hopeless with current technology.

## `erdos_324.variants.quintic` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/ErdosProblems/324.lean:42`  
**Statement:** Are all sums a^5+b^5 with 0 <= a < b distinct (i.e. a^5+b^5 = c^5+d^5 has no nontrivial solutions)?  
**Source:** https://www.erdosproblems.com/324 ('probably x^5 works'). State = open.  
**Statement matches intent:** suspect — Stated as a positive theorem rather than an answer()-encoded question, so a refutation could not be recorded without rewriting the declaration. Mathematically the statement itself is the intended conjecture.  
**Known status:** Open. No solution to a^5+b^5 = c^5+d^5 in distinct pairs is known despite extensive search, but non-existence is far beyond current methods (contrast Euler's 133^4+134^4 = 158^4+59^4 for the quartic analogue).  
**Difficulty:** math 10/10, Lean 10/10 · **Compute:** medium · **Confidence:** high  
**Evidence:** The quartic analogue is false by Euler's identity, so no soft/parity argument can work for degree 5; only heuristics support the conjecture.  
**Flags:** conjecture asserted positively under @[category research open]; if it is false the declaration is unprovable as written  
**Next action:** Do not attempt. A defensible small contribution is a certified search bound (no solutions with max <= B) as a separate lemma.

## `erdos_325` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/ErdosProblems/325.lean:39`  
**Statement:** Is f_{k,3}(x), the number of integers <= x that are sums of three nonnegative k-th powers, at least of order x^{3/k} for every k >= 3?  
**Source:** https://www.erdosproblems.com/325; [Wo15] Wooley, Sums of three cubes II (2015). State = open.  
**Statement matches intent:** yes  
**Known status:** Open even for k=3, where the claim f_{3,3}(x) >> x (positive density of sums of three nonnegative cubes) is believed but only x^{0.917} is known (Wooley, recorded as variants.wooley).  
**Difficulty:** math 9/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** For k=3 the statement asserts positive density of sums of three cubes; the best unconditional exponent after decades is 0.9179.  
**Flags:** k=3 instance is essentially the negation of 323.variants.k_gt_2's k=3 case; keep the two answer() fills consistent  
**Next action:** Do not attempt. The realistic file target is Wooley's bound, which is a research-scale formalization.

## `erdos_325.variants.weaker` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/ErdosProblems/325.lean:49`  
**Statement:** Weakened form: is f_{k,3}(x) at least of order x^{3/k - eps} for every eps > 0 and every k >= 3?  
**Source:** https://www.erdosproblems.com/325. State = open.  
**Statement matches intent:** yes  
**Known status:** Open even for k=3: Wooley's exponent 0.917 falls short of 1-eps for eps < 0.083.  
**Difficulty:** math 9/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** The eps-weakened statement for k=3 is precisely 'sums of three cubes have exponent 1', still unproven; Wooley 2015 gives 0.9179.  
**Next action:** Do not attempt; formalizing Wooley's circle-method argument is the only credible partial step and is research-scale.

## `erdos_326` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/326.lean:37`  
**Secondary category:** 4 (Vacuously true / accidentally weakened)  
**Statement:** If A is an additive basis of order 2, must it contain a subset B = {b_1 < b_2 < ...} that is still a basis and for which lim_k b_k/k^2 does not exist?  
**Source:** https://www.erdosproblems.com/326 (Erdos; the A = B version was disproved by Cassels). State = open.  
**Statement matches intent:** suspect — Two issues. (1) B is only required to satisfy `(Set.range b).IsAddBasis` — a basis of SOME order — whereas the source (and the Cassels context, where a_k/k^2 has a finite limit) intends a basis of order 2. Under the weaker reading one may take B so sparse that b_k/k^2 → ∞, and then `∀ x : ℝ, ¬Tendsto ... (𝓝 x)` holds automatically; so the whole question can be dodged by exhibiting a thin higher-order basis inside A. (2) Cosmetic: `∀ n, b n ∈ A ∧ (Set.range b).IsAddBasis ∧ ∀ x, ...` puts the last two conjuncts under the ∀ n; harmless since ℕ is inhabited, but misleading.  
**Known status:** Open in the intended (order-2) reading. The weakened reading reduces to 'every basis of order 2 contains a much thinner basis of higher order', which is itself not obviously true but is a different and likely easier question. No fork PR or campaign for 326.  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** If B is a basis of order h > 2 then only B(x) >> x^{1/h} is forced, so b_k can grow like k^h and b_k/k^2 → ∞, making the non-existence-of-limit clause vacuous. With B a basis of order 2 one has b_k ≍ k^2 and the clause is the real content, matching the Cassels counterexample discussed in variants.eq.  
**Flags:** major: 'basis' of unspecified order weakens the target and can make the limit clause vacuous; minor: quantifier scoping of ∀ n over non-n-dependent conjuncts  
**Next action:** Fix the specification first: replace `(Set.range b).IsAddBasis` by `(Set.range b).IsAddBasisOfOrder 2` and hoist the two conjuncts out of `∀ n` (use `Set.range b ⊆ A`). Then treat as open.

## `erdos_329` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/ErdosProblems/329.lean:49`  
**Statement:** How large can limsup_N |A ∩ [1,N]|/sqrt(N) be for a Sidon set A ⊆ ℕ?  
**Source:** https://www.erdosproblems.com/329; [ErTu41] Erdos-Turan upper bound 1; [Kr61] Kruckeberg lower bound 1/sqrt 2. State = open.  
**Statement matches intent:** yes  
**Known status:** Open: the answer lies in [1/sqrt 2, 1] and it is not known whether 1 is attained. Alexeev-Mixon (arXiv:2510.19804) removed the perfect-difference-set route.  
**Difficulty:** math 9/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Classical prize-adjacent Erdos problem, open since 1941/1961; the file itself records only the two bounding results as sorry'd 'research solved'.  
**Next action:** Do not attempt the exact value. Kruckeberg's 1/sqrt 2 construction (variants.kruckeberg_1961) is the realistic file target.

## `erdos_329.variants.converse_implication` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/329.lean:93`  
**Secondary category:** 4 (Vacuously true / accidentally weakened)  
**Statement:** If the maximal Sidon upper density equals 1, then every finite Sidon set embeds in a perfect difference set — which, since the conclusion is false, amounts to asserting that the maximal density is not 1.  
**Source:** https://www.erdosproblems.com/329; [Ha47] Hall, Cyclic projective planes; [AlMi25] Alexeev-Mixon, arXiv:2510.19804 (2025).  
**Statement matches intent:** suspect — Degenerate encoding, as the docstring itself admits: with the consequent known false, the implication is logically equivalent to `sSup ≠ 1`. So the declaration silently asserts one specific answer to the open problem rather than posing a question — and it is FALSE if the true supremum turns out to be 1. It is also not really a 'converse' of anything provable here.  
**Known status:** Open and one-directional. The only route to a proof is refuting the antecedent, i.e. showing the maximal Sidon upper density is < 1, which is exactly the open problem 329.  
**Difficulty:** math 9/10, Lean 10/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** IsPerfectDifferenceSet is defined via a BijOn of D.offDiag onto the nonzero classes of ZMod n (the subtraction is genuine ZMod subtraction, not truncated ℕ subtraction), so the consequent is the intended embedding statement; Hall [Ha47] and Alexeev-Mixon [AlMi25] falsify it.  
**Flags:** statement is provable only by resolving 329 in one particular direction; it is false as stated if the supremum is 1; needs literature check on whether the expected answer is 1 or 1/sqrt 2  
**Next action:** Restate as `answer(sorry) ↔ (sSup {...} = 1)` (or as the implication in the sound direction, consequent → sSup = 1, which is the classically known one). Then treat as open.

## `erdos_33` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/ErdosProblems/33.lean:41`  
**Statement:** Over all sets A ⊆ ℕ such that every integer is a + n^2 with a in A, what is the smallest possible value of limsup_N |A ∩ [1,N]|/sqrt(N)?  
**Source:** https://www.erdosproblems.com/33; van Doorn's upper bound 2*phi^{5/2} ≈ 6.66 recorded as variants.vanDoorn. State = open.  
**Statement matches intent:** yes  
**Known status:** Open: known only to lie in (1, 2*phi^{5/2}]. No fork PR or campaign for problem 33.  
**Difficulty:** math 9/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Asking for an exact extremal constant with a factor-6 gap between the known bounds; no method is known to close such constants.  
**Flags:** sibling declaration erdos_33.variants.one_mem_lowerBounds (line 50, research solved, not in this batch) states ∃ A with limsup > 1, which is trivially true (take A = ℕ, limsup = ∞) and does NOT express Erdos' observation that the infimum exceeds 1 — should be a ∀  
**Next action:** Do not attempt the exact constant. The tractable target is van Doorn's construction (variants.vanDoorn).

## `erdos_330_statement` — Already solved externally (cat 1)

**File:** `FormalConjectures/ErdosProblems/330.lean:49`  
**Statement:** Is there a minimal asymptotic additive basis A of positive density such that, for every n in A, the set of integers not representable without using n also has positive density?  
**Source:** https://www.erdosproblems.com/330. Batch metadata: state = 'proved (Lean)' as of 2026-07-26, i.e. solved externally with a public formal Lean proof.  
**Statement matches intent:** suspect — Two spec risks against the prose. (1) `Set.HasPosDensity` (FormalConjecturesForMathlib/Data/Set/Density.lean:100) requires the natural density to EXIST and be positive, whereas the docstring says '(upper) density ... is positive'; this makes the ∃-statement strictly stronger than intended. (2) `Rep A m h` uses 'sum of at most h elements' (∃ k ≤ h, f : Fin k → ℕ), while `MinAsymptoticAddBasisOfOrder` is phrased via Mathlib's IsAsymptoticAddBasisOfOrder (exactly-h convention); if 0 ∉ A the two notions of representability differ, shrinking UnrepWithout. Both push the same way (harder), so a proof of the Lean statement still answers the problem affirmatively, but a ported external proof may not match term-for-term.  
**Known status:** Solved externally per erdosproblems.com ('proved (Lean)'), so a public formal proof exists and is the fastest import. Nothing internal: no PR in pr_register.json and no campaign_register.json entry mentions 330; a GitHub code search for `erdos_330` returned nothing accessible from this session (upstream google-deepmind/formal-conjectures is not attached to this session).  
**Difficulty:** math 4/10, Lean 4/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** Batch-supplied authoritative erdosproblems.com status 'proved (Lean)'; the '(Lean)' suffix indicates a public formal proof exists. Direct verification was impossible: erdosproblems.com returns HTTP 403 through this container's proxy.  
**Flags:** highest-value import in this batch; HasPosDensity requires the density to converge — stronger than 'upper density positive'; 'at most h' vs 'exactly h' summand convention mismatch between Rep and IsAsymptoticAddBasisOfOrder; needs literature check to identify the external Lean proof  
**Next action:** Fetch the Lean proof linked from erdosproblems.com/330, adapt it to this file's `Rep`/`HasPosDensity` definitions (or relax HasPosDensity to positive upper density first), fill answer(True) presumably, and verify the build.

## `erdos_331.variants.ruzsa` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/331.lean:59`  
**Statement:** If A,B ⊆ ℕ satisfy the sharper counting asymptotics |A∩[1,N]| ~ c_A·N^{1/2} and |B∩[1,N]| ~ c_B·N^{1/2} (c_A,c_B>0), must there be infinitely many quadruples with a₁−a₂ = b₁−b₂ ≠ 0?  
**Source:** https://www.erdosproblems.com/331 (Ruzsa's remark on the stronger normalisation); main problem 331 is disproved, Lean proof by van Doorn at https://github.com/Woett/Lean-files/blob/main/ErdosProblem%23331.lean  
**Statement matches intent:** yes  
**Known status:** The ≫N^{1/2} version (erdos_331 in the same file) is disproved by Ruzsa's even/odd-binary-digit construction and already has an external Lean proof; this normalised variant is untouched. No PR in the fork register (262 PRs grepped) and no campaign targets 331.  
**Difficulty:** math 8/10, Lean 8/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** Ruzsa's set A (nonzero binary digits only in even places) has |A∩[1,4^k]| = 2^k = √N but |A∩[1,2·4^k]| = 2^{k+1} = √2·√(2·4^k), so count/√N oscillates between 1 and √2 and A is NOT ~ c√N — hence the known counterexample does not settle the variant, confirming it is genuinely open. In Ruzsa's example there are literally zero nontrivial solutions (unique representation n = a+b forces a₁=a₂, b₁=b₂), so the question is exactly whether the extra regularity destroys that.  
**Flags:** answer(sorry) in Prop position compiles to True under the default `alwaysTrue` setting, so the file currently asserts the ∀-statement itself; a 'solution' must replace it with answer(True)/answer(False) — human-judged, not machine-checked  
**Next action:** Attack the refutation side: try to smooth Ruzsa's construction (which has count A n /√n oscillating in [1,√2]) into one with a genuine limit, e.g. by randomising the digit blocks or taking unions of dilates; a counterexample would give answer(False). No Lean work is worthwhile before the mathematics is settled.

## `erdos_332` — Vacuously true / accidentally weakened (cat 4)

**File:** `FormalConjectures/ErdosProblems/332.lean:50`  
**Secondary category:** 5 (Solved mathematically, not yet formalized)  
**Statement:** Find conditions on A ⊆ ℕ that guarantee that D(A) — the set of integers occurring infinitely often as a difference a₁−a₂ of elements of A — is syndetic (has bounded gaps).  
**Source:** https://www.erdosproblems.com/332  
**Statement matches intent:** suspect — The statement is `(answer(sorry) : Set ℕ → Prop) A → HasBoundedGaps (D_A A)` — a bare sufficient-condition implication. Filling the answer slot with `fun _ ↦ False` (or any unsatisfiable predicate) makes the theorem vacuously true with a one-line proof and answers nothing. The file's own docstring concedes 'If the condition is a solution to the problem is up to human judgement.' This is not a yes/no question and admits no faithful single formal statement.  
**Known status:** Open on erdosproblems.com. No fork PR or campaign touches 332. Mathematically there IS a classical sufficient condition in the literature: if A has positive upper Banach density then A−A contains a Bohr set (Bogolyubov/Følner) and is therefore syndetic, and the same argument gives it for differences occurring infinitely often.  
**Difficulty:** math 5/10, Lean 8/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** Loophole is immediate: with answer := fun _ ↦ False the goal becomes `False → HasBoundedGaps (D_A A)`, closed by `exact fun h ↦ h.elim`. Definitions themselves are fine: D_A A is the set of d ∈ ℤ realised by infinitely many pairs, HasBoundedGaps is the standard syndeticity predicate (∃ M>0, every interval [z, z+M) meets S).  
**Flags:** vacuous-answer loophole: `fun _ ↦ False` closes the theorem; problem is a 'find conditions' question, not a proposition — arguably belongs in category 10 as unformalisable in this shape; needs literature check on whether erdosproblems.com records a specific intended sufficient condition  
**Next action:** Either (a) restate as a concrete named implication, e.g. `0 < upperDensity A → HasBoundedGaps (D_A A)`, and formalise the Følner/Bogolyubov argument (A−A ⊇ Bohr set ⇒ syndetic) — a substantial Mathlib gap; or (b) keep the answer slot but add a nontriviality guard (e.g. require the condition to be satisfied by some explicit A). Recommend (a).

## `erdos_340` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/ErdosProblems/340.lean:71`  
**Statement:** For the greedy Sidon (Mian–Chowla) sequence 1,2,4,8,13,21,31,45,66,81,97,…, is |A∩[1,N]| ≫ N^{1/2−ε} for every ε>0?  
**Source:** https://www.erdosproblems.com/340; Erdős–Graham, Old and new problems and results in combinatorial number theory (1980); OEIS A005282  
**Statement matches intent:** yes  
**Known status:** Open; a long-standing Erdős problem with a monetary prize attached in the original sources. Only the trivial ≫N^{1/3} bound is known (recorded in the same file as `variants.third`, still sorry, and in ErdosProblems/156.lean as `greedy_lower_bound`). No fork PR/campaign.  
**Difficulty:** math 9/10, Lean 9/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Numerically a(50)≈4262 ≈ 50^{2.14}, consistent with the conjectured a(n)=n^{2+o(1)} (equivalently |A∩[1,N]| = N^{1/2−o(1)}); the only proved bound in either direction is the trivial |A∩[1,N]| ≫ N^{1/3}. No technique is known to beat the cube-root bound for the greedy Sidon set.  
**Next action:** Do not attempt. If any work is done, target the recorded-but-unproved trivial bound `erdos_340.variants.third` (N^{1/3}) first: it follows from the fact that a greedy Sidon set below N is maximal, so every m ≤ N is blocked by some a+b−c with a,b,c in the set, giving |A∩[1,N]|³ ≫ N.

## `erdos_340.variants._33_mem_sub` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/340.lean:128`  
**Secondary category:** 6 (Computationally solvable with certificate)  
**Statement:** Is 33 a difference of two elements of the greedy Sidon (Mian–Chowla) sequence? It is stated to be the smallest integer whose membership in A−A is unknown.  
**Source:** https://www.erdosproblems.com/340; Erdős–Graham [ErGr80]  
**Statement matches intent:** yes  
**Known status:** Open (per the file's own docstring, 33 is the smallest integer not known to be in A−A). The companion `_22_mem_sub` in the same file is closed with the explicit witness greedySidon 14 − greedySidon 13 = 22 via `decide +native`.  
**Difficulty:** math 8/10, Lean 4/10 · **Compute:** medium · **Confidence:** medium  
**Evidence:** If 33 were realised at a small index, extensive published computation of A005282 would have found it; the persistence of 33 as 'smallest unknown' after such searches is weak evidence that any witness lies very deep or does not exist, in which case only a structural theorem (currently unavailable) can decide it.  
**Flags:** a `yes` answer would need greedySidon evaluated far beyond the file's `decide +native` tests; kernel-checkable evaluation at large index is itself nontrivial  
**Next action:** Asymmetric problem: a positive answer is a one-line witness `greedySidon i − greedySidon j = 33` IF such a pair exists in computable range — worth an out-of-Lean search over ~10^5–10^6 terms of A005282 first (cheap, laptop-minutes). A negative answer is an infinitary statement about the greedy set with no known approach. Note the existing `_22_mem_sub` relies on `decide +native`, which is outside the kernel; a witness for 33 at a large index would need a reflection-friendly computation of greedySidon.

## `erdos_340.variants.co_density_zero_sub` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/ErdosProblems/340.lean:148`  
**Statement:** Do almost all natural numbers (all outside a set of density zero) lie in A−A for the greedy Sidon (Mian–Chowla) sequence?  
**Source:** https://www.erdosproblems.com/340; Erdős–Graham [ErGr80]  
**Statement matches intent:** yes  
**Known status:** Open; weaker than `cofinite_sub` but strictly stronger than `sub_hasPosDensity` (which is open).  
**Difficulty:** math 9/10, Lean 9/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Density-1 coverage of A−A would in particular give |A∩[1,N]| ≫ N^{1/2−o(1)} up to constants (a Sidon set has at most |A|² differences below N), i.e. it implies the prize problem erdos_340. That reduction makes this at least as hard as the main problem.  
**Flags:** implies the main prize question erdos_340, so it cannot be easier  
**Next action:** Same blocker as the other A−A variants: no structural handle on the greedy Sidon set. Not a target.

## `erdos_340.variants.cofinite_sub` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/ErdosProblems/340.lean:140`  
**Statement:** Are all but finitely many natural numbers differences of two elements of the greedy Sidon (Mian–Chowla) sequence?  
**Source:** https://www.erdosproblems.com/340; Erdős–Graham [ErGr80] ('all or almost all integers are in A−A')  
**Statement matches intent:** yes  
**Known status:** Open, and strictly stronger than `sub_hasPosDensity`, which is itself open. Contradicted-in-spirit by nothing known; 33 is not even known to be in A−A, so cofiniteness is far out of reach.  
**Difficulty:** math 9/10, Lean 9/10 · **Compute:** none · **Confidence:** high  
**Evidence:** The statement implies membership of every sufficiently large integer, hence in particular resolves infinitely many instances of the currently-undecided membership questions of which 33 is the smallest; no technique is known.  
**Next action:** Blocked behind `_33_mem_sub`: cofiniteness implies 33 ∈ A−A for the trivial reason that only finitely many exceptions are allowed and 33 would have to be checked directly. Nothing to attempt formally.

## `erdos_340.variants.isTheta` — Vacuously true / accidentally weakened (cat 4)

**File:** `FormalConjectures/ErdosProblems/340.lean:84`  
**Secondary category:** 9 (Major open problem / currently infeasible)  
**Statement:** Determine the exact order of growth of |A∩[1,N]| for the greedy Sidon (Mian–Chowla) sequence, as a Θ-asymptotic.  
**Source:** https://www.erdosproblems.com/340  
**Statement matches intent:** suspect — Two defects. (1) The answer slot has type ℕ → ℝ and IsTheta is reflexive, so filling it with the left-hand function itself, `fun n ↦ ((Set.range greedySidon ∩ Set.Icc 1 n).ncard : ℝ)`, closes the theorem by `IsTheta.refl` while saying nothing. (2) The hypotheses (ε : ℝ) (hε : ε > 0) are copied from erdos_340 and are completely unused, so the statement is ε-independent and the docstring (which is a verbatim copy of erdos_340's) does not describe it.  
**Known status:** Open, and in fact no Θ-asymptotic for the greedy Sidon sequence is even conjectured with confidence — the conjecture is only N^{1/2−o(1)}, which is not a Θ statement. So no legitimate answer is currently available.  
**Difficulty:** math 9/10, Lean 1/10 · **Compute:** none · **Confidence:** high  
**Evidence:** IsTheta.refl gives a one-line 'solution' once the answer slot is filled with the LHS; the currently compiled statement uses a sorryAx-valued function so it is not provable as-is, but nothing in the answer mechanism prevents the tautological fill (FormalConjectures/Util/Answer.lean:136-149 shows answer() is a bare annotation with no well-formedness check).  
**Flags:** tautological-answer loophole (IsTheta is reflexive); unused hypotheses ε, hε; docstring duplicated from erdos_340 and does not describe the Θ formulation  
**Next action:** Delete or restate. A defensible replacement is `∀ ε > 0, (fun n ↦ (n:ℝ)^(1/2−ε)) =O[atTop] card ∧ card =O[atTop] (fun n ↦ (n:ℝ)^(1/2))`, or drop the variant entirely and keep erdos_340. If kept, at minimum remove the unused ε hypotheses.

## `erdos_340.variants.sub_hasPosDensity` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/340.lean:106`  
**Statement:** Does the difference set A−A of the greedy Sidon (Mian–Chowla) sequence have positive density?  
**Source:** https://www.erdosproblems.com/340; Erdős–Graham [ErGr80]  
**Statement matches intent:** yes  
**Known status:** Open. Erdős and Graham asked it in [ErGr80]; only sporadic membership facts are known (the file proves 22 ∈ A−A by explicit witness and records 33 as the smallest unknown). No fork PR/campaign.  
**Difficulty:** math 8/10, Lean 8/10 · **Compute:** small · **Confidence:** medium  
**Evidence:** Positive density of A−A is at least as hard as understanding the counting function of A: a Sidon set with |A∩[1,N]| ≍ N^{1/3} has only ~N^{2/3} differences below N, so positive density of A−A already forces strong lower bounds on |A∩[1,N]|. So this variant is entangled with the main (prize) problem.  
**Flags:** ℕ pointwise subtraction truncates, but harmlessly (difference set is symmetric)  
**Next action:** Compute a long prefix of A005282 (say 10^5 terms) and measure the density of realised differences below N to see whether the empirical density is bounded away from 0 — this at least tells you which way to aim. A proof in either direction looks to need real information about the greedy set's structure, which is exactly what erdos_340 lacks.

## `erdos_341` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/341.lean:39`  
**Statement:** Start from a finite set of integers and repeatedly append the least integer larger than the current maximum that is not a sum aᵢ+aⱼ of two earlier terms. Is the resulting difference sequence a_{m+1}−a_m always eventually periodic?  
**Source:** https://www.erdosproblems.com/341; Ben Green, Open Problems list, Problem 7  
**Statement matches intent:** yes  
**Known status:** Open; listed as Problem 7 on Green's open-problems list. No fork PR/campaign; no duplicate in the repo (GreensOpenProblems/7.lean is about the Ulam sequence, i.e. Erdős 342, not this one).  
**Difficulty:** math 9/10, Lean 9/10 · **Compute:** small · **Confidence:** medium  
**Evidence:** The greedy rule is 'local' once the sequence is far above the initial set (only sums involving recent terms can obstruct), which is why eventual periodicity is plausible and is observed numerically; but making the state space provably finite is exactly the open obstruction, as it is for the closely related Ulam sequence (Erdős 342 part ii).  
**Flags:** the sum set {aᵢ+aⱼ | i ≤ n, j ≤ n} allows i = j; the source's 'aᵢ+aⱼ with i,j ≤ n' also allows it, but some formulations require i<j — a convention worth double-checking against erdosproblems.com  
**Next action:** Generate the sequence for many starting sets and test the observed periods (cheap); a single starting set with provably non-periodic differences would give answer(False). For a positive answer one would need an invariant/automaton argument showing the state (the finite window of relevant forbidden sums) is eventually finite — that is the natural avenue and would be the first milestone.

## `erdos_342.parts.i` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/342.lean:110`  
**Statement:** Does Ulam's sequence 1,2,3,4,6,8,11,13,16,18,… (each term the least integer with a unique representation as a sum of two distinct earlier terms) contain infinitely many pairs of terms differing by 2?  
**Source:** https://www.erdosproblems.com/342; Guy, Unsolved Problems in Number Theory (2004); OEIS A002858  
**Statement matches intent:** yes  
**Known status:** Open. Empirically pairs differing by 2 keep occurring (1&3, 2&4, 6&8, 11&13, 16&18, 26&28, 36&38, 97&99, …). No fork PR/campaign.  
**Difficulty:** math 9/10, Lean 9/10 · **Compute:** small · **Confidence:** medium  
**Evidence:** The Ulam sequence has resisted all structural analysis apart from Steinerberger's empirical 'hidden signal' (a near-periodicity with respect to a mysterious constant λ ≈ 2.5714); no proof technique is known for any qualitative statement about its terms, including the 2-gap question.  
**Flags:** the statement is ∀ a, IsUlamSequence a → …; the repo never proves that any such a exists, so the 'True' side could in principle be discharged vacuously if the definition were ever found unsatisfiable (it is satisfiable, but this is unverified in Lean)  
**Next action:** Nothing formal is worthwhile until someone first proves in Lean that an Ulam sequence exists (the definition is currently only used hypothetically — see flags). That existence proof (the greedy step always succeeds, because a_{n−2}+a_{n−1} always has a unique representation) is a genuinely useful, self-contained milestone of moderate size.

## `erdos_342.parts.ii` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/ErdosProblems/342.lean:120`  
**Statement:** Are the consecutive differences a(n+1)−a(n) of Ulam's sequence eventually periodic?  
**Source:** https://www.erdosproblems.com/342; Guy, Unsolved Problems in Number Theory (2004); OEIS A002858  
**Statement matches intent:** yes  
**Known status:** Open and widely believed false — the observed difference sequence of A002858 shows no periodicity out to millions of terms, and Steinerberger's Fourier analysis suggests quasi-periodic rather than periodic structure. No fork PR/campaign.  
**Difficulty:** math 10/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Nothing whatsoever is proved about the asymptotic structure of the Ulam sequence; even the far weaker density question (part iii) is open, and eventual periodicity of the differences would essentially determine the sequence completely.  
**Flags:** same vacuity caveat as parts.i: existence of an Ulam sequence is never established in the repo  
**Next action:** Do not attempt. Disproof requires a genuine theorem about A002858, of which none exist.

## `erdos_342.parts.iii` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/ErdosProblems/342.lean:131`  
**Statement:** Does Ulam's sequence have density zero?  
**Source:** https://www.erdosproblems.com/342; Ben Green, Open Problems list, Problem 7  
**Statement matches intent:** yes  
**Known status:** Open; empirically the density is ≈ 0.07398, so the expected answer is answer(False), but proving positive density is exactly Green's Open Problem 7. DUPLICATE in this repo: FormalConjectures/GreensOpenProblems/7.lean:green_7.variants.positive_density states the negation (`upperDensity > 0`) over the same IsUlamSequence predicate — the two are mutually exclusive and both are tagged research open.  
**Difficulty:** math 9/10, Lean 9/10 · **Compute:** small · **Confidence:** high  
**Evidence:** The numerical density of A002858 is stable around 0.074 over millions of terms, so the formal statement is presumably false; but no lower bound on the density of the Ulam sequence is known, which is precisely why Green lists it as an open problem.  
**Flags:** duplicate/complement of FormalConjectures/GreensOpenProblems/7.lean:green_7.variants.positive_density; same vacuity caveat as parts.i  
**Next action:** Deduplicate: link 342.parts.iii and green_7.variants.positive_density so that answering one is recorded against the other (they are complementary, not independent). Mathematically, do not attempt.

## `erdos_346` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/346.lean:36`  
**Statement:** If A is a lacunary, strongly complete sequence that stops being complete as soon as infinitely many terms are deleted, must A(n+1)/A(n) converge to the golden ratio?  
**Source:** https://www.erdosproblems.com/346; Graham, A property of Fibonacci numbers, Fibonacci Quart. (1964); Erdős–Graham [ErGr80]  
**Statement matches intent:** yes  
**Known status:** Open. Graham's f(n) = fib(n) − (−1)ⁿ is the motivating example and the file records (still sorry) that it is lacunary, strongly complete, and destroyed by deleting infinitely many terms. Erdős–Graham's remark that ratio > φ forces the deletion property is also recorded. No fork PR/campaign.  
**Difficulty:** math 8/10, Lean 8/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** Consistency check on the file: `variants.example` claims very irregular sequences with limsup A(n+1)/A(n) = ⊤ satisfying the same two properties; such a sequence cannot be lacunary, since lacunarity (ratio ≥ c>1) plus completeness forces A(n+1) ≤ 1 + Σ_{i≤n} A i ≤ A n·c/(c−1) + 1, a bounded ratio. So the example does not refute erdos_346 and the statement is coherent.  
**Next action:** Best first milestone is the already-stated but unproved `erdos_346.variants.gt_goldenRatio_not_IsAddComplete`: if A(n+1) > φ·A(n) then deleting an infinite subset destroys completeness — a Brown-criterion-style counting argument (the surviving terms have partial sums too small to cover the next term) that is genuinely formalisable. That is also the natural first half of any attack on erdos_346.

## `erdos_348` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/348.lean:35`  
**Statement:** Determine the set of pairs 0 ≤ m < n for which there is a complete sequence of integers that remains complete after deleting any m terms but fails to be complete after deleting any n terms.  
**Source:** https://www.erdosproblems.com/348  
**Statement matches intent:** suspect — Two issues. (1) Deletion is modelled by `Function.updateFinset a s 0` (zeroing m indices) and completeness by `IsAddComplete (Set.range …)`, i.e. subset sums of the SET of values. Erdős writes A = {a₁ ≤ a₂ ≤ …} with repetitions allowed, and completeness of a sequence with repeated values should use sums over distinct INDICES (the repo's own `subseqSums'`/IsAddCompleteNatSeq'). Since only `Monotone a` is required, constant or repeating sequences are admitted and their multiplicities are silently collapsed, so the LHS set may be smaller than intended. (2) `= answer(sorry)` on a Set (ℕ×ℕ) can be 'answered' by restating the left-hand side.  
**Known status:** Open. No fork PR/campaign; no duplicate elsewhere in the repo.  
**Difficulty:** math 8/10, Lean 8/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** The subtlety is real: with `Monotone a` the constant sequence a ≡ 1 is complete as a multiset (every n is a sum of n distinct indices) but its range {1} has subset sums {0,1}, so the two notions genuinely disagree on admissible objects.  
**Flags:** Set.range collapses repeated terms although Erdős's A = {a₁ ≤ a₂ ≤ …} allows them; tautological-answer loophole on `= answer(sorry)`; 'not complete after removing any n elements' read as ∀ t; the alternative ∃ t reading is defensible — needs literature check against erdosproblems.com  
**Next action:** First fix the model: replace `IsAddComplete (Set.range (updateFinset a s 0))` by an index-based completeness predicate (IsAddCompleteNatSeq' on the zeroed sequence), or require StrictMono a so that range and multiset agree. Then attack small cases: decide whether (0,1) is in the set (a sequence complete after any single deletion but destroyed by any two), which is the natural first milestone and is where the literature on complete/strongly complete sequences (Graham 1964) is most informative.

## `complete_for_alpha_in_Ioo_one_to_goldenRatio` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/349.lean:49`  
**Secondary category:** 7 (Plausibly solvable with moderate formal work)  
**Statement:** For every t > 0 and every 1 < α < (1+√5)/2, is the sequence ⌊t·αⁿ⌋ complete?  
**Source:** https://www.erdosproblems.com/349 ('It seems likely that the sequence is complete for all t>0 and all 1 < α < φ')  
**Statement matches intent:** yes  
**Known status:** Conjectural per the source ('it seems likely'), i.e. not a theorem. It is the most tractable open statement in this file, and the golden-ratio threshold is exactly the Fibonacci-type condition a_{n+1} ≤ a_n + a_{n−1}.  
**Difficulty:** math 6/10, Lean 8/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** Why φ and not 2: the naive Brown criterion b_{k+1} ≤ 1 + Σ_{i≤k} b_i holds for all α < 2, but it is not sufficient for EVENTUAL completeness — the surviving subset-sum set is symmetric, so a small non-representable value r propagates to non-representable values s_n − r arbitrarily high, and the intervals only merge under the stronger Fibonacci condition b_{k+1} ≤ b_k + b_{k−1}, i.e. α < φ. Concrete illustration: for t=1, α=1.9 the value set {1,3,6,13,24,47,…} misses 2, 5 and 49, and one must argue the gaps eventually close — which is exactly the open part.  
**Flags:** a genuine Lean-tractable target, unlike the rest of this file — recommend prioritising  
**Next action:** Plausible attack with moderate formal work: (1) show that for 1 < α < φ the distinct values b₀ < b₁ < … of ⌊tαⁿ⌋ eventually satisfy b_{k+1} ≤ b_k + b_{k−1} (floor errors are O(1) against exponentially growing terms); (2) prove the Brown/Zeckendorf-style interval invariant — if [L, R] ⊆ subsetSums and b_{k+1} ≤ R − L + 1 then [L, R + b_{k+1}] ⊆ subsetSums — by induction; (3) conclude IsAddComplete. Milestone (2) as a standalone Mathlib-style lemma about `subsetSums` is the right first deliverable and is reusable for 346, 348 and 354.

## `erdos_349` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/ErdosProblems/349.lean:40`  
**Statement:** Determine all pairs (t, α) of positive reals for which the sequence ⌊t·αⁿ⌋ is complete (every sufficiently large integer is a sum of distinct terms).  
**Source:** https://www.erdosproblems.com/349  
**Statement matches intent:** suspect — Mathematically faithful — IsGoodPair uses IsAddComplete on `Set.range (fun n ↦ ⌊t·αⁿ⌋)`, i.e. subset sums of DISTINCT values, matching 'sum of distinct integers of the form ⌊tαⁿ⌋'. The suspect flag is only for the answer slot: `{…} = answer(sorry)` can be discharged by restating the left-hand side, and no clean closed form for this set is known or expected.  
**Known status:** Open. The file records substantial partial results as `research solved` with external formal_proof links to branches of a third-party fork (cepadugato/formal-conjectures): α > 2 fails, 0 < α ≤ 1 fails, (1,2) is good, (1/2^k, 2) is good, integer t ≥ 2 fails, and the full characterisation on positive integer pairs (good ⟺ (t,α)=(1,2)). None of those proofs are in this repo — every one of them is still `sorry` here.  
**Difficulty:** math 10/10, Lean 9/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** The known partial results pin the boundary at α = 2 (α > 2 fails by Brown-criterion counting: Σ_{i≤n} tα^i ≈ tα^{n+1}/(α−1) < tα^{n+1}), but the fibre α = 2 depends on t in a complicated arithmetic way and the range (φ, 2) is not understood at all, so no closed form for the full set is plausible.  
**Flags:** tautological-answer loophole on `= answer(sorry)`; six sibling theorems in the same file are tagged `research solved` but carry `sorry` bodies with proofs only on external fork branches — provenance is unverified in this repo  
**Next action:** Do not target the characterisation. Instead, import the six partial results whose proofs already exist on the cepadugato branches and verify them against the canonical statements — that is concrete, and it is the only tractable work in this file.

## `erdos_349.variants.floor_3_halves_even` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/ErdosProblems/349.lean:78`  
**Statement:** Are there infinitely many n with ⌊(3/2)ⁿ⌋ even?  
**Source:** https://www.erdosproblems.com/349 (remark); classical, related to Mahler's Z-numbers  
**Statement matches intent:** yes  
**Known status:** Open; same classical obstruction as the odd variant. No fork PR/campaign.  
**Difficulty:** math 9/10, Lean 9/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Identical to the odd case: the parity is governed by binary digits of 3ⁿ near position n, about which nothing is provable with current technology.  
**Flags:** trivial partial observation: `Odd`-infinite ∨ `Even`-infinite is provable (pigeonhole on ℕ), so a solver must be careful not to present that as evidence for either individual statement  
**Next action:** Do not attempt.

## `erdos_349.variants.floor_3_halves_odd` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/ErdosProblems/349.lean:70`  
**Statement:** Are there infinitely many n with ⌊(3/2)ⁿ⌋ odd?  
**Source:** https://www.erdosproblems.com/349 (remark); classical, related to Mahler's Z-numbers and the 3ⁿ mod 2ⁿ problem  
**Statement matches intent:** yes  
**Known status:** Open, and a notoriously hard classical question: nothing is proved about the parity distribution of ⌊(3/2)ⁿ⌋. No fork PR/campaign.  
**Difficulty:** math 9/10, Lean 9/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Parity of ⌊(3/2)ⁿ⌋ = parity of ⌊3ⁿ/2ⁿ⌋ depends on the binary digits of 3ⁿ just above position n; no non-trivial information about those digits is known — the same obstruction that leaves ‖(3/2)ⁿ‖ > c^n open.  
**Next action:** Do not attempt. Any progress would bear directly on the distribution of {(3/2)ⁿ} mod 1, the central obstruction in Mahler's Z-number problem and in Waring's problem for the g(k) formula.

## `erdos_352` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/352.lean:34`  
**Statement:** Is there a constant c > 0 such that every measurable subset of the plane with Lebesgue measure at least c contains three points forming a triangle of area exactly 1?  
**Source:** https://www.erdosproblems.com/352  
**Statement matches intent:** yes  
**Known status:** Open. No fork PR/campaign; the same `triangle_area` machinery is reused in ErdosProblems/507.lean, which is a different question (minimum triangle area).  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** The statement is scale-sensitive rather than scale-invariant (area is fixed at 1 while the measure threshold is fixed at c), so neither a compactness argument nor a direct measure-theoretic pigeonhole applies; this is what makes it genuinely open rather than routine.  
**Flags:** `ℙ A ≥ c.toEReal` compares an ℝ≥0∞ measure with an EReal via coercion — typechecks, but a plain `ENNReal.ofReal c ≤ ℙ A` would be cleaner and less error-prone  
**Next action:** Look for the refutation direction first: construct, for each c, a measurable set of measure ≥ c avoiding area-1 triangles (e.g. a union of thin neighbourhoods of a lacunary family of lines, where all realisable areas concentrate away from 1). If no such construction exists, the positive direction plausibly needs a density-increment/Fourier argument on the affine group, which is far beyond current Mathlib.

## `erdos_354.parts.i` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/354.lean:39`  
**Statement:** For α, β > 0 with α/β irrational, is the union {⌊α⌋,⌊2α⌋,⌊4α⌋,…} ∪ {⌊β⌋,⌊2β⌋,⌊4β⌋,…} complete, i.e. is every sufficiently large integer a sum of distinct terms?  
**Source:** https://www.erdosproblems.com/354; Erdős–Graham. Related: N. Hegyvári (non-representability for α ≥ 2, β = 2ⁿα); 'On a problem of Erdős and Graham', Acta Math. Hungar. (2025), doi 10.1007/s10474-025-01515-5  
**Statement matches intent:** yes  
**Known status:** Open per erdosproblems.com. Hegyvári's known partial result (infinitely many non-representable integers for α ≥ 2, β = 2ⁿα) does not apply, since then α/β = 2^{−n} is rational. A 2025 Acta Math. Hungar. paper titled 'On a problem of Erdős and Graham' addresses this circle of problems and may contain relevant progress — not verified.  
**Difficulty:** math 8/10, Lean 8/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** A single ratio-2 sequence ⌊2ᵏα⌋ is exactly borderline for completeness (Σ_{i<k} ≈ 2ᵏα − k, next term ≈ 2ᵏα), so the union of two such sequences has roughly twice the needed mass; the whole difficulty is that the deficit is only linear in k while the phases of α and β can conspire, and this is precisely what irrationality of α/β is meant to prevent.  
**Flags:** needs literature check: 'On a problem of Erdős and Graham', Acta Math. Hungar. (2025) may already resolve this; IsAddCompleteNatSeq' sums over indices, so a value shared by both subsequences can be used twice (minor deviation from 'distinct terms of the set')  
**Next action:** Check the 2025 Acta Math. Hungar. paper before investing; if the problem is still open, the tractable direction is the Brown-criterion computation: the two interleaved ratio-2 sequences have Σ of previous terms ≈ 2× the next term, so the interval-merging invariant (see 349:complete_for_alpha_in_Ioo_one_to_goldenRatio) nearly closes — the obstruction is controlling the floor errors and the relative phase of α and β, which is where the irrationality hypothesis must enter.

## `erdos_354.parts.ii` — Vacuously true / accidentally weakened (cat 4)

**File:** `FormalConjectures/ErdosProblems/354.lean:47`  
**Secondary category:** 10 (Cannot classify without correction/clarification)  
**Statement:** Intended (apparently): is there some ratio γ strictly between 1 and 2 for which the interleaved union {⌊γᵏα⌋} ∪ {⌊γᵏβ⌋} is complete whenever α, β > 0 and α/β is irrational?  
**Source:** https://www.erdosproblems.com/354; Erdős–Graham  
**Statement matches intent:** no — BUG: the bound variable γ never appears in the body. The statement reads `∃ γ ∈ Set.Ioo (1:ℝ) 2, ∀ α>0, ∀ β>0, Irrational (α/β) → IsAddCompleteNatSeq' (FloorMultiples.interleave α β 2)` — the last argument is the literal `2`, not γ. Since Set.Ioo (1:ℝ) 2 is provably nonempty (e.g. 3/2), the whole statement is logically equivalent to erdos_354.parts.i. The two docstrings are also verbatim identical, reinforcing that this is a copy-paste error: the third argument should be γ.  
**Known status:** Not a distinct problem as written — it is parts.i in disguise. The intended part (ii) (whichever γ-range erdosproblems.com asks about) is untouched. No fork PR/campaign.  
**Difficulty:** math 8/10, Lean 2/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Purely syntactic and airtight: `∃ γ ∈ S, P` with γ ∉ FV(P) and S nonempty is equivalent to P, and here P is exactly the body of parts.i. So `parts.ii` is closed by `⟨3/2, by norm_num, h⟩` given any proof h of parts.i, and conversely.  
**Flags:** unused bound variable γ — statement collapses to parts.i; docstring copy-pasted from parts.i; needs literature check to recover the intended γ range  
**Next action:** Fix the statement: replace `FloorMultiples.interleave α β 2` by `FloorMultiples.interleave α β γ` in parts.ii, and rewrite the docstring so it states the γ-quantified question rather than duplicating part (i). Until then this declaration should not be counted as an open problem. Verify the intended γ range against erdosproblems.com/354 before committing.

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

## `erdos_358.variants.one_le` — Already solved externally (cat 1)

**File:** `FormalConjectures/ErdosProblems/358.lean:113`  
**Secondary category:** 5 (Solved mathematically, not yet formalized)  
**Statement:** Is there a strictly increasing sequence of positive integers such that every sufficiently large n is a sum of at least two consecutive terms?  
**Source:** https://www.erdosproblems.com/358 (state: proved); T. Tao, 'Erdős problem 358' (2026), https://terrytao.wordpress.com/wp-content/uploads/2026/02/erdos-358-2.pdf  
**Statement matches intent:** yes  
**Known status:** SOLVED EXTERNALLY, but mis-tagged `research open` in this file. Tao [Ta26] constructs a strictly increasing A with f(n) ≫ log n for all large n — the very construction cited in the same file's `erdos_358.parts.i` and `parts.ii`, which are already tagged `research solved` with answer(True). erdosproblems.com records 358 as proved.  
**Difficulty:** math 3/10, Lean 8/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Immediate corollary of parts.ii: for n ≥ 1, a representation with u = v means n = A u, and StrictMono A makes such u unique, so at most one of the f A n representations is trivial. Hence f A n ≥ 2 ⇒ g A n ≥ 1. Tao's sequence has f(n) ≫ log n eventually, so eventually f ≥ 2 and therefore g ≥ 1. Nothing in the variant is harder than parts.i/parts.ii, both of which the file already classifies as solved.  
**Flags:** MIS-TAGGED: `research open` although it follows immediately from the [Ta26] result cited three declarations above in the same file; 0 < u means A 0 is never used by f or g; irrelevant here because A is existentially quantified  
**Next action:** Retag as research solved (citing [Ta26]) and record the two-line derivation from parts.ii. Formally: prove the reduction lemma `StrictMono A → 2 ≤ f A n → 1 ≤ g A n` (cheap), then it remains only to formalise Tao's construction, which is the real work — port or write it, then verify the build. Effort: medium-to-large for Tao's construction; the reduction itself is small.

## `erdos_358.variants.prime_set` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/ErdosProblems/358.lean:94`  
**Statement:** For the sequence of primes, is the limsup over n of the number of ways to write n as a sum of consecutive primes infinite?  
**Source:** https://www.erdosproblems.com/358 (variant); Erdős–Graham  
**Statement matches intent:** suspect — Off-by-one: `intervalRepresentations` requires 0 < u, but `Nat.nth Nat.Prime` is 0-indexed (nth Prime 0 = 2), so the prime 2 is never used — the statement is about sums of consecutive ODD primes. This does not plausibly affect the truth of a limsup-infinite statement, but it is a genuine index-convention slip relative to 'a₁ < a₂ < …' 1-indexed sources. Otherwise faithful: limsup in ℕ∞ equal to ⊤ is the correct 'infinitely often, unboundedly many'.  
**Known status:** Open (the main problem 358 is proved — Tao [Ta26] — but this prime variant is not). No fork PR/campaign.  
**Difficulty:** math 9/10, Lean 9/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** Counting: the number of (u,k) with p_u + … + p_{u+k−1} ≤ x is ≈ Σ_{k ≤ √(x/log x)} π(x/k) ≈ x·log 2 ≈ 0.69x, i.e. fewer than x representations in total below x. So the average multiplicity is < 1 and no averaging/pigeonhole argument can produce even multiplicity 2 infinitely often, let alone unbounded multiplicity.  
**Flags:** 0 < u excludes A 0 = 2, so the prime 2 never participates (indexing slip)  
**Next action:** Do not attempt. Note the heuristic count below: the total number of representations up to x is ≈ x·log 2, so pigeonhole gives nothing and a genuine input about prime gaps is required.

## `erdos_358.variants.prime_set_density_representation` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/ErdosProblems/358.lean:103`  
**Statement:** Does the set of integers expressible as a sum of consecutive primes have positive upper density?  
**Source:** https://www.erdosproblems.com/358 (variant); Erdős–Graham  
**Statement matches intent:** suspect — Uses `intervalRepresentations` (which allows u = v, i.e. a single prime) rather than `intervalRepresentationsNonTrivial`; the intended conjecture is normally about sums of at least two consecutive primes. Harmless for the density claim (the primes themselves have density 0) but it should have used g/nonTrivial for consistency with the neighbouring `one_le`. Also inherits the 0 < u indexing slip that drops the prime 2, and the degenerate pair (2,1) with Icc 2 1 = ∅ puts 0 in the set (a single point, no density effect).  
**Known status:** Open. No fork PR/campaign.  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** small · **Confidence:** medium  
**Evidence:** The first-moment count (≈0.69x representations below x) is Θ(x), so positive density is plausible, but it is compatible with all representations concentrating on a density-zero set; ruling that out needs an upper bound on Σ f(n)² over the primes, i.e. control of coincidences among sums of consecutive primes — no such bound is known.  
**Flags:** single-term representations (u = v) are counted, unlike the neighbouring nontrivial-g variant; 0 < u excludes the prime 2  
**Next action:** Cheap and worthwhile first step: compute the density of representable n below 10^7 to see the empirical constant. A proof requires a second-moment/variance bound on the number of representations, which is where the difficulty lies; not a Lean target.

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
