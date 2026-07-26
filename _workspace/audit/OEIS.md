# Audit detail — OEIS

21 research-open declarations. Fields per problem: plain statement, source, category, match, status, action, difficulties, compute, confidence, evidence, flags.

## `a.infinite` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/OEIS/228828.lean:63`  
**Statement:** The sequence of numbers n such that n^2 + pi(n) is prime (pi = prime counting function) is infinite.  
**Source:** https://oeis.org/A228828  
**Statement matches intent:** yes  
**Known status:** Open. Landau-tier: infinitude of primes in a sparse polynomial-type sequence (analogous to n^2+1 primes, open since 1912). Test lemmas confirm a(0)=2, a(1)=3, a(2)=7 consistent with OEIS. Nat.nth junk (returns 0 for large n if set finite) does not distort the statement: range of nth is infinite iff the predicate set is infinite.  
**Difficulty:** math 9/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Predicate-set infinitude of n^2+pi(n) prime is far beyond current analytic number theory (no equidistribution tool produces primes in such sparse irregular sequences). No PR/campaign/duplicate hits in pr_register.json or campaign_register.json.  
**Next action:** No viable strategy; leave open. Do not attempt.

## `conjecture` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/OEIS/231201.lean:50`  
**Statement:** Zhi-Wei Sun's $1000 conjecture: every n > 1 can be written n = x + y with x, y > 0 such that 2^x + y is prime.  
**Source:** https://oeis.org/A231201; Sun arXiv:1402.6641  
**Statement matches intent:** yes  
**Known status:** Open; $1000 prize by Sun. Verified locally here for all 2 <= n <= 1500 (no failures); OEIS verification goes much further.  
**Difficulty:** math 9/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Formalization faithful: x,y > 0, n = x+y, (2^x+y).Prime, hypothesis 1 < n matches OEIS a(n) > 0 conjecture for n > 1. Local Miller-Rabin check to 1500 passed. No internal PR/campaign work found.  
**Next action:** Leave open. Producing primes of the form 2^x + y in every additive decomposition is Crocker/Sierpinski-adjacent territory with no known method.

## `conjecture` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/OEIS/232174.lean:58`  
**Statement:** Zhi-Wei Sun's $200 conjecture: every n > 1 can be written n = x + y with x, y > 0 such that x + ny and x^2 + ny^2 are both prime.  
**Source:** https://oeis.org/A232174; Sun arXiv:1211.1588  
**Statement matches intent:** yes  
**Known status:** Open; $200 prize. Verified locally for all 2 <= n <= 3000 (no failures).  
**Difficulty:** math 9/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Formal statement matches OEIS/Sun exactly (x,y>0, both primality conditions). Local check to 3000 passed. No internal or external resolution found.  
**Next action:** Leave open. Requires simultaneous prime values of a linear and a quadratic form in every additive decomposition; beyond current sieve/circle-method technology.

## `conjecture` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/OEIS/239957.lean:37`  
**Statement:** Zhi-Wei Sun's conjecture (RMB 2000 prize): every prime p has a primitive root g with 0 < g < p of the form k^2 + 1.  
**Source:** https://oeis.org/A239957; Sun arXiv:1405.0290  
**Statement matches intent:** yes  
**Known status:** Open. Verified locally for all primes p < 20000 (every prime has a primitive root k^2+1 < p); Sun verified much further.  
**Difficulty:** math 9/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Encoding checked: k : Z with k^2+1 < p and orderOf (k^2+1 : ZMod p) = p-1 is exactly 'primitive root 0 < g < p of the form k^2+1'; p=2,3 edge cases work (g=1 has order 1 = 2-1). Nat subtraction p-1 harmless since p >= 2. No prior work found.  
**Next action:** Leave open. Even under GRH, forcing a primitive root inside the sparse set {k^2+1} below p is out of reach (character sums over sparse sequences).

## `conjecture` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/OEIS/280831.lean:56`  
**Statement:** Sun's 1680-conjecture: every nonnegative integer is x^2+y^2+z^2+w^2 with nonnegative x,y,z,w such that x^4 + 1680*y^3*z is a perfect square.  
**Source:** https://oeis.org/A280831; Sun, J. Number Theory 175 (2017) 167-190  
**Statement matches intent:** yes  
**Known status:** Open; RMB 1680 prize. Internal partial work: fork PR #261 (open, unmerged) 'Develop parametric families for A280831' explicitly records only kernel-verified algebraic partial families and leaves the conjecture open; campaign register lists it as branch-only/still sorry on main.  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Statement faithful; the y=0/z=0 degenerate branch (x^4 automatically square) is present in Sun's original formulation too, and only n not expressible as three squares carry real content. Test cases in file verified by hand (95 = 6^2+3^2+1^2+7^2, 6^4+1680*27 = 216^2). PR #261 is partial, not a solution.  
**Flags:** internal partial PR #261 (unmerged, non-solving)  
**Next action:** Research problem. Possible avenue: quaternion techniques of Machiavelo-Tsopanidis (which proved Sun's 1-3-5 conjecture) adapted to the quartic condition; first milestone would be handling n = 4^a(8b+7) where all of x,y,z,w are forced nonzero.

## `conjecture` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/OEIS/281976.lean:66`  
**Statement:** Sun's x+24y conjecture ($2400 prize): every n >= 0 is x^2+y^2+z^2+w^2 with nonnegative x,y,z,w, z <= w, such that x and x+24y are both perfect squares.  
**Source:** https://oeis.org/A281976; Sun, J. Number Theory 175 (2017); arXiv:1701.05868  
**Statement matches intent:** yes  
**Known status:** Open but active: Wu-She, 'On restricted sums of four squares and Zhi-Wei Sun's x+24y conjecture' (arXiv:2511.23223, Nov 2025) proves via ternary quadratic form theory that ax+by can be made a square for all sufficiently large n with bounded 2-adic valuation - explicit partial progress, not a full proof (the full conjecture also requires x itself square, and all n). Internal fork PR #15 (closed, unmerged) added sorry-free parameter-family constructors and P(n) -> P(16n) scaling, explicitly leaving the conjecture open.  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Web check (2 lookups used batch-wide) confirmed the Nov 2025 Wu-She preprint gives only asymptotic/restricted progress. PR register: PR #15 'Formalize exact A281976 parameter families and 16-scaling' is explicitly partial. Formal statement matches docstring and OEIS.  
**Flags:** active recent literature (arXiv:2511.23223) - recheck status periodically; internal partial PR #15 (unmerged, non-solving)  
**Next action:** Track Wu-She arXiv:2511.23223 and successors; a future full proof would make this cat 5 with large formalization effort (ternary form spinor genus theory not in Mathlib). Sources: https://arxiv.org/abs/2511.23223

## `conjecture` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/OEIS/287616.lean:64`  
**Statement:** Sun's $135 conjecture: every nonnegative integer is x(x+1)/2 + y(3y+1)/2 + z(5z+1)/2 with x, y, z nonnegative integers.  
**Source:** https://oeis.org/A287616; Sun arXiv:1502.03056  
**Statement matches intent:** yes  
**Known status:** Open. Verified locally here: every n <= 10^6 is representable with x,y,z >= 0 (no misses), so the N-restricted formal statement is consistent with data and with Sun's formulation.  
**Difficulty:** math 7/10, Lean 9/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** Nat division is exact for all three terms (x(x+1), y(3y+1), z(5z+1) always even), so no truncation loophole. Exhaustive check to 10^6 passed. No PR/campaign resolution; campaign register lists only branch-scoped non-solving activity.  
**Flags:** needs literature check (universal ternary triples of Sun are being resolved piecemeal in the literature)  
**Next action:** Research problem with identifiable avenue: ternary quadratic polynomial universality via theta series / ternary form genus theory (several of Sun's universal-triple conjectures from arXiv:1502.03056 have been settled this way). Needs a literature sweep for a post-2020 proof of this specific triple.

## `conjecture` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/OEIS/303656.lean:61`  
**Statement:** Sun's $3500 conjecture: every integer n > 1 can be written a^2 + b^2 + 3^c + 5^d with a, b, c, d nonnegative integers.  
**Source:** https://oeis.org/A303656  
**Statement matches intent:** yes  
**Known status:** Open; one of Sun's largest cash-prize conjectures. Extensively verified numerically per OEIS.  
**Difficulty:** math 9/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Formalization faithful: n > 1 hypothesis matches (n=2 = 0+0+1+1 minimal). No internal or known external resolution as of Jan 2026 cutoff.  
**Next action:** Leave open. Sums of two squares have density x/sqrt(log x) and {3^c+5^d} is log^2-sparse; no covering or circle-method approach exists (compare Crocker's negative results for x^2+y^2+2^a+2^b).

## `conjecture` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/OEIS/306477.lean:57`  
**Statement:** Sun's 2-4-6-8 conjecture ($2468 prize): every n > 0 equals C(w,2)+C(x,4)+C(y,6)+C(z,8) with w,x,y,z >= 2.  
**Source:** https://oeis.org/A306477; https://mathoverflow.net/questions/323541  
**Statement matches intent:** yes  
**Known status:** Open; verified to 1.2*10^12 (Yaakov Baruch, 2019). No proof known.  
**Difficulty:** math 9/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Indexing audited: value-set equality holds because leading binomials below the diagonal vanish, and C(w+2,2) >= 1 gives minimum total 1, matching n > 0. Test lemma 1 = C(2,2)+0+0+0 confirms. No prior-work hits.  
**Next action:** Leave open. Exponent sum 1/2+1/4+1/6+1/8 = 25/24 barely exceeds 1; quaternary additive problems with a degree-8 sparsest variable are beyond the circle method; only avenue is further verification.

## `conjecture` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/OEIS/308734.lean:61`  
**Statement:** Sun's $2500 conjecture: every n > 1 equals (2^a*3^b)^2 + (2^c*5^d)^2 + x^2 + y^2 with all exponents and x, y nonnegative.  
**Source:** https://oeis.org/A308734; Banerjee, J. Number Theory 256 (2024) 253-289 (arXiv:2202.04057)  
**Statement matches intent:** yes  
**Known status:** Open. Banerjee (JNT 2024) proves partial results (three-squares generalizations, almost-prime restrictions via Bruedern-Fouvry) and states the full conjecture 'seems out of reach with current techniques'. Internal fork PR #14 (closed, unmerged) adds only 4-adic reduction lemmas (enough to restrict to n not divisible by 4) and explicitly does not claim the conjecture.  
**Difficulty:** math 9/10, Lean 9/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Web check confirmed Banerjee 2024 is progress-only, matching the exact statement (every n = 2,3,... as x^2+y^2+(2^a3^b)^2+(2^c5^d)^2). Formalization matches. PR #14 is explicitly non-solving.  
**Flags:** internal partial PR #14 (unmerged, non-solving)  
**Next action:** Research problem; avenue = Banerjee's ineffective Gauss-Legendre generalizations plus almost-prime relaxations. First milestone: the conjecture for n in specific residue classes. Sources: https://arxiv.org/abs/2202.04057

## `a_isBigO` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/OEIS/34693.lean:92`  
**Statement:** Conjecture: a(n) = least k with nk+1 prime satisfies a(n) = O(log n * log log n).  
**Source:** https://oeis.org/A034693 (comment)  
**Statement matches intent:** yes  
**Known status:** Open, and heuristically believed FALSE: Granville-Wagstaff heuristics predict least prime p ≡ 1 (mod n) of size phi(n) log^2 n infinitely often, i.e. a(n)/(log n loglog n) unbounded. The same file states the counter-conjecture (a_unbounded); at most one of the two can hold.  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** Faithful transcription of the OEIS growth conjecture; mutually exclusive with a_unbounded below (a bounded tail plus finitely many finite values forces a bounded range), which is intentional (conjecture / counter-conjecture pair).  
**Flags:** believed false; mutually exclusive with a_unbounded in same file; needs literature check  
**Next action:** Possible refutation avenue: known lower-bound constructions for the least prime ≡ 1 (mod n) (Pomerance-style) might already beat C log n loglog n along a subsequence - needs literature check before any formalization attempt.

## `a_unbounded` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/OEIS/34693.lean:97`  
**Statement:** Counter-conjecture: a(n) / (log n * log log n) is unbounded over n.  
**Source:** https://oeis.org/A034693 (comment)  
**Statement matches intent:** yes  
**Known status:** Open; heuristically believed TRUE (extreme values of least prime ≡ 1 mod n should reach phi(n) log^2 n scale).  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** Faithful; genuinely open. Proving unboundedness needs constructions of n for which all small k give nk+1 composite - partial results in the least-prime-in-AP literature are the only identifiable avenue.  
**Flags:** needs literature check; counter-conjecture pair with a_isBigO  
**Next action:** Avenue: adapt known omega-results / lower-bound constructions for least primes in progressions to the modulus-1 residue class; first milestone is a(n) > C log n loglog n infinitely often for every C.

## `exists_k` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/OEIS/34693.lean:57`  
**Statement:** For every n > 1 there exists k < n such that nk + 1 is prime (i.e., the least prime congruent to 1 mod n is below n^2).  
**Source:** https://oeis.org/A034693  
**Statement matches intent:** yes  
**Known status:** Open. Equivalent to least-prime-in-progression p(n,1) < n^2, which is stronger than what GRH yields and far beyond Linnik-type unconditional bounds (current Linnik exponent ~5).  
**Difficulty:** math 9/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Statement faithful (k=0 gives 1, not prime, so existence genuinely requires 1 <= k < n). Well-known open conjecture recorded in A034693 comments.  
**Next action:** Leave open; would follow from a Linnik constant <= 2 with a good implied constant, itself a major open problem.

## `exists_k_stronger` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/OEIS/34693.lean:63`  
**Statement:** Stronger conjecture: for every n > 0 there exists k < 1 + n^(3/4) with nk + 1 prime.  
**Source:** https://oeis.org/A034693 (comment)  
**Statement matches intent:** yes  
**Known status:** Open; strictly stronger than exists_k, far beyond GRH.  
**Difficulty:** math 9/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Companion solved lemma in the file (exists_k_best_possible, exponent 0.74 fails at n=19) is already proved, showing the exponent is sharp-ish; the open bound itself is untouchable with current tools.  
**Next action:** Leave open.

## `general_supercongruence` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/OEIS/357513.lean:89`  
**Statement:** For each m >= 0, the numerator u_m(p-1) of sum_{k=1}^{p-1} C(p-1,k)^2 C(p-1+k,k)^2 / k^(2m+1) is divisible by p^4 for all primes p outside a finite exceptional set depending on m.  
**Source:** https://oeis.org/A357513 (comment)  
**Statement matches intent:** yes  
**Known status:** Open for general m. The m=1 instance (a357513_supercongruence) was proved formally by AlphaProof (upstream commit 9c7f21e7d444..., referenced in the file's formal_proof attribute) with exceptional set {2,7}; the file even derives the m=1 case of this general statement from it as a test lemma. Local exact-rational check: for m=0..4 and primes p <= 43 the exceptional primes are small and finite-looking (m=0: {3,5}; m=1: {7}; m=2: {3,5}; m=3: {3,11}; m=4: {7,13}), supporting the conjecture.  
**Difficulty:** math 7/10, Lean 9/10 · **Compute:** small · **Confidence:** medium  
**Evidence:** Numerical verification performed here (exact Fractions, p <= 43, m <= 4) consistent with finitely many exceptions per m. The formally proved m=1 case provides a concrete template. No internal PR targets the general statement.  
**Flags:** m=1 special case already formally proved externally (AlphaProof)  
**Next action:** Medium-term research: generalize the AlphaProof m=1 argument (Wolstenholme/WZ-style supercongruence manipulations) to arbitrary odd exponent 2m+1; first milestone is m=0 with exceptions {2,3,5}.

## `noPowerPartitionNumber` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/OEIS/41.lean:35`  
**Statement:** Decide (answer(sorry) iff) whether no partition number p(k) is a perfect power x^m with x, m > 1 (Zhi-Wei Sun's conjecture on A000041).  
**Source:** https://oeis.org/A000041 (Zhi-Wei Sun comment, Dec 02 2013)  
**Statement matches intent:** yes  
**Known status:** Open in both directions: no proof technique for excluding perfect powers from the partition sequence (no modularity/linear-forms approach applies), and no counterexample found in extensive computation.  
**Difficulty:** math 9/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Checked IsPerfectPower definition in FormalConjecturesForMathlib/Data/Nat/PerfectPower.lean (exists k m, 1 < k, 1 < m, k^m = n), closing the p(k)=1 loophole. p defined via Fintype.card (Nat.Partition n) is the correct partition function.  
**Next action:** Leave open. Even the analogous solved problems (perfect powers among Fibonacci numbers) needed deep linear-forms-in-logs machinery unavailable for p(n).

## `comesFromPrimeQuadruple_of_a` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/OEIS/56777.lean:108`  
**Statement:** Every composite n with phi(n+12) = phi(n)+12 and sigma(n+12) = sigma(n)+12 equals p(p+8) for a prime quadruple (p, p+2, p+6, p+8).  
**Source:** https://oeis.org/A056777  
**Statement matches intent:** yes  
**Known status:** Open (converse direction; the easy direction is proved sorry-free in the same file). Verified computationally here: for all composite n <= 10^6 satisfying both conditions, n is a quadruple product (65, 209, ...), no exceptions.  
**Difficulty:** math 9/10, Lean 9/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** Definition of membership (composite via not-prime and 1 < n, both function equations) matches the module docstring; sieve check to 10^6 found only quadruple products. No prior internal work.  
**Flags:** OEIS comment wording not independently fetched - numerics strongly support the transcription  
**Next action:** Research problem of Lehmer/Schinzel totient-rigidity type (compare the classical open conjecture that phi(n+2)=phi(n)+2 forces twin-prime products). Avenue: combine sigma and phi conditions to pin the factorization shape of n and n+12; first milestone is n = product of exactly two primes.

## `mod_216_of_a` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/OEIS/63880.lean:83`  
**Statement:** Every n with sigma(n) = 2*usigma(n) (sum of divisors twice the sum of unitary divisors) satisfies n ≡ 108 (mod 216).  
**Source:** https://oeis.org/A063880  
**Statement matches intent:** yes  
**Known status:** Open. Verified computationally here: all 10^6-range terms (108, 540, 756, 1188, ...) are ≡ 108 mod 216. Follows from unique_primitive_108 plus the (stated-solved) primitive-times-squarefree structure theorem in the same file, so its difficulty is inherited from the primitive-term classification.  
**Difficulty:** math 8/10, Lean 8/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** Sieve computation (sigma + usigma via SPF factorization) to 10^6 confirms the congruence and the definition transcription (unitary divisors d with gcd(d, n/d)=1). Membership requires 0 < n, avoiding n=0 junk.  
**Next action:** Attack via the structure route: prove exists_primitive_of_a and a_of_primitive_mul_squarefree (both currently sorry, marked solved/textbook), then reduce this to unique_primitive_108.

## `unique_primitive_108` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/OEIS/63880.lean:93`  
**Statement:** 108 is the only primitive term (no proper divisor in the sequence) of the sequence sigma(n) = 2*usigma(n).  
**Source:** https://oeis.org/A063880  
**Statement matches intent:** yes  
**Known status:** Open. Verified computationally here: 108 is the only primitive term up to 10^6. Classifying all (necessarily powerful, per the companion conjecture) solutions of sigma = 2*usigma resembles multiperfect/unitary-perfect classification problems - no complete method known.  
**Difficulty:** math 9/10, Lean 9/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** Sieve check to 10^6: primitive terms = [108] only. isPrimitiveTerm_108 test already proved in file. No internal PR targets this.  
**Flags:** OEIS comment wording not independently fetched - numerics strongly support the transcription  
**Next action:** Research: first milestone is proving every primitive term is powerful and divisible by 4 and 27; a full uniqueness proof likely needs new ideas about sigma/usigma ratios on powerful numbers.

## `prime_add_one_of_a` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/OEIS/67720.lean:73`  
**Statement:** If phi(k^2+1) = k*phi(k+1) and k is not 8, then k+1 is prime.  
**Source:** https://oeis.org/A067720  
**Statement matches intent:** yes  
**Known status:** Open. Verified computationally here for all k <= 20000: every member except k=8 has k+1 prime. Note the pleasant rigidity: when k+1 is prime, membership is equivalent to k^2+1 prime (phi(k^2+1) = k^2 iff k^2+1 prime), so the conjecture says members = {8} plus {k : k+1 and k^2+1 both prime}.  
**Difficulty:** math 9/10, Lean 9/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** Full factorization check of k^2+1 for k <= 20000 found no counterexample. Definition and exception k=8 (phi(65)=48=8*phi(9)) verified. No prior internal work.  
**Flags:** OEIS comment wording not independently fetched - numerics strongly support the transcription  
**Next action:** Lehmer-type totient rigidity; avenue: for composite k+1, phi(k+1) <= k - sqrt(k+1)-ish forces phi(k^2+1)/(k^2+1) unusually small, constraining the factorization of k^2+1 - quantitative exclusion of sporadic coincidences is the obstruction.

## `conjectureA81091` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/OEIS/81091.lean:40`  
**Statement:** Decide (answer(sorry) iff) whether there are infinitely many primes with exactly three 1-bits in binary, i.e. primes of the form 2^n + 2^i + 1 with 0 < i < n (Wagstaff 2001).  
**Source:** https://oeis.org/A081091; Wagstaff, Exp. Math. 10 (2001)  
**Statement matches intent:** yes  
**Known status:** Open. Infinitude of primes in any exponentially sparse explicit set (Fermat/Mersenne-adjacent) is a recognized hard open problem; even 'infinitely many primes of the form 2^n + 3' is open.  
**Difficulty:** math 9/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Checked the bit-count/form equivalence (7 = 111_2 included, correctly, as 2^2+2^1+1). answer(sorry) encoding asks for the genuine truth value; neither direction is accessible.  
**Next action:** Leave open; no strategy known.
