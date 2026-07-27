# Audit detail — Wikipedia

168 research-open declarations. Fields per problem: plain statement, source, category, match, status, action, difficulties, compute, confidence, evidence, flags.

## `abc` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Wikipedia/ABC.lean:59`  
**Statement:** For every eps > 0 there are only finitely many coprime triples of positive integers a + b = c with rad(abc)^(1+eps) < c.  
**Source:** https://en.wikipedia.org/wiki/Abc_conjecture (Masser-Oesterle, 1985)  
**Statement matches intent:** yes  
**Known status:** Famous open problem. Mochizuki's IUT proof (PRIMS 2021) is not accepted by the wider community (Scholze-Stix obstruction); Kirti Joshi's 2024 series is likewise disputed. No formal proof exists anywhere. No PR in pr_register.json and no campaign in campaign_register.json touches ABC.lean.  
**Difficulty:** math 10/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** radical n = n.primeFactors.prod id is correct; radical 0 = 1 but a,b,c > 0 is imposed. Set.Pairwise on ({a,b,c} : Set ℕ) is the standard coprimality condition; the only degenerate collapse is a = b = 1, c = 2, which does not affect finiteness. Real exponentiation rad^(1+eps) with rad ≥ 1 is well behaved.  
**Flags:** Set.Pairwise on the *set* {a,b,c} drops the gcd(a,b)=1 requirement when a = b, but the only such triple is (1,1,2) — harmless  
**Next action:** Leave open. Only realistic Lean work is formalising known partial results (e.g. Stewart-Yu exponential bounds, or abc for Fermat-type families), not the theorem itself.

## `abc.variants.lt_constant_mul` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Wikipedia/ABC.lean:68`  
**Statement:** For every eps > 0 there is a constant K_eps with c < K_eps * rad(abc)^(1+eps) for all coprime a + b = c.  
**Source:** https://en.wikipedia.org/wiki/Abc_conjecture  
**Statement matches intent:** yes  
**Known status:** Standard 'effective constant' reformulation of abc; equivalent to `abc` above. Open, same status as ABC.  
**Difficulty:** math 10/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** K : ℝ is existentially quantified with no positivity constraint, which is harmless (any working K is positive). Quantifier order (K chosen before a,b,c) is the intended uniform one.  
**Next action:** Leave open; if `abc` is ever proved, derive this by splitting off the finitely many exceptional triples and taking K = max.

## `abc.variants.quality` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Wikipedia/ABC.lean:77`  
**Statement:** For every eps > 0 only finitely many coprime triples a + b = c have quality q(a,b,c) = log c / log rad(abc) > 1 + eps.  
**Source:** https://en.wikipedia.org/wiki/Abc_conjecture  
**Statement matches intent:** yes  
**Known status:** Quality reformulation of abc; open. Highest known quality is ~1.6299 (Reyssat, 2 + 3^10*109 = 23^5).  
**Difficulty:** math 10/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** quality divides by Real.log (radical (a*b*c)); division-by-zero junk would only arise if rad(abc) = 1, i.e. a = b = c = 1, which is incompatible with a + b = c. So no junk-value loophole.  
**Next action:** Leave open.

## `agoh_giuga` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Wikipedia/AgohGiuga.lean:60`  
**Statement:** An integer p >= 2 is prime if and only if p*B_{p-1} = -1 (mod p), where B is the Bernoulli number.  
**Source:** https://en.wikipedia.org/wiki/Agoh-Giuga_conjecture ; G. Giuga (1950), T. Agoh (1995)  
**Statement matches intent:** yes  
**Known status:** Open. Verified for all n below 10^13800 (Borwein-Borwein-Borwein-Girgensohn and successors). The forward direction (prime => congruence) is a von Staudt-Clausen consequence; the converse is the conjecture.  
**Difficulty:** math 9/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** The rational-arithmetic encoding `p * B.num + B.den = k * p^2` is a correct rendering of p*B_{p-1} ≡ -1 (mod p): it forces p | den, which by von Staudt-Clausen means den is squarefree with p | den, so den/p is coprime to p and the congruence num ≡ -(den/p) mod p is exactly num/(den/p) ≡ -1. Checked numerically: p=2 (1/2 -> 2+2=4), p=3 (1/6 -> 3+6=9), p=5 (-1/30 -> -5+30=25), p=7 (1/42 -> 7+42=49) all give k*p^2. Composites n=9,15,25 fail as required.  
**Next action:** Leave open. A tractable sub-goal is to formalise the easy direction (prime => p*num + den ≡ 0 mod p^2) via von Staudt-Clausen, which Mathlib does not yet have.

## `agoh_giuga.variants.giuga` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Wikipedia/AgohGiuga.lean:65`  
**Statement:** An integer p >= 2 is prime if and only if p divides 1 + sum_{i=1}^{p-1} i^{p-1}.  
**Source:** https://en.wikipedia.org/wiki/Agoh-Giuga_conjecture ; G. Giuga, 'Su una presumibile proprieta caratteristica dei numeri primi'  
**Statement matches intent:** yes  
**Known status:** Open (Giuga's conjecture). Equivalent to: a counterexample must be a Carmichael number that is also a weak Giuga number; none exists below 10^13800.  
**Difficulty:** math 9/10, Lean 9/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Finset.Ioo 0 p = {1,...,p-1} is exactly the intended summation range; exponent (p-1 : ℕ) is safe since p ≥ 2 so no truncated subtraction. Divisibility of 1 + sum by p is the right rendering of ≡ -1. Note the easy (=>) half is provable, so the theorem is not fully open, but the iff as a whole is.  
**Flags:** only the (<=) direction is genuinely open; the (=>) direction is elementary  
**Next action:** Leave open. The forward direction is a short Fermat-little-theorem argument (sum_{i=1}^{p-1} i^{p-1} ≡ p-1 ≡ -1 mod p) and could be split out as a lemma.

## `agrawal_conjecture` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Wikipedia/Agrawal.lean:48`  
**Secondary category:** 8 (Deep but approachable research problem)  
**Statement:** Decide whether: for coprime n > 1 and r > 0, (X-1)^n = X^n - 1 in (Z/n)[X]/(X^r-1) implies n is prime or n^2 = 1 mod r.  
**Source:** https://en.wikipedia.org/wiki/Agrawal%27s_conjecture ; https://aimath.org/WWN/primesinp/articles/html/50a/  
**Statement matches intent:** yes  
**Known status:** Open. Lenstra and Pomerance gave a heuristic argument that the conjecture is FALSE with infinitely many counterexamples of positive density in a suitable family, but no counterexample has ever been exhibited; the Primaboinca BOINC project searched 2010-2020 without finding one. Verified for r < 100, n < 10^10.  
**Difficulty:** math 9/10, Lean 9/10 · **Compute:** large · **Confidence:** high  
**Evidence:** Polynomial congruence is faithfully rendered as equality in Polynomial (ZMod n) modulo the ideal span {X^r - 1}, which is exactly 'mod n and mod X^r-1'. The r = 1 edge case is harmless: ZMod 1 is trivial so (n^2 : ZMod 1) = 1 always. answer(sorry) ↔ (full statement) is a faithful 'decide the truth value' encoding of equal difficulty in both directions.  
**Next action:** Leave open; the answer(sorry) slot cannot be filled without either a proof or an explicit counterexample. A large-scale search following the Lenstra-Pomerance heuristic recipe is the only computational avenue, and its output would be a `decide`-checkable witness.

## `agrawal_conjecture.variants.popovych` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Wikipedia/Agrawal.lean:66`  
**Statement:** If both (X-1)^n = X^n-1 and (X+2)^n = X^n+2 hold in (Z/n)[X]/(X^r-1) with gcd(n,r)=1, then n is prime or n^2 = 1 mod r.  
**Source:** https://en.wikipedia.org/wiki/Agrawal%27s_conjecture ; R. Popovych, 'A note on Agrawal conjecture', eprint.iacr.org/2009/008  
**Statement matches intent:** yes  
**Known status:** Open. Proposed precisely because Agrawal's conjecture is heuristically false; the extra congruence is expected to rule out the heuristic counterexamples. No counterexample known.  
**Difficulty:** math 9/10, Lean 9/10 · **Compute:** large · **Confidence:** high  
**Evidence:** Same encoding as agrawal_conjecture with the extra hypothesis; adding a hypothesis makes this logically weaker than Agrawal's conjecture (the docstring's phrase 'a stronger version' is Wikipedia's loose wording, not a formalisation error).  
**Flags:** docstring calls it 'a stronger version'; formally it is a weaker statement (implied by Agrawal's conjecture)  
**Next action:** Leave open.

## `exists_almost_perfect_not_power_of_two` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Wikipedia/AlmostPerfectNumbers.lean:44`  
**Statement:** Decide whether there is an almost perfect number (sigma(n) = 2n - 1) that is not a power of 2.  
**Source:** https://en.wikipedia.org/wiki/Almost_perfect_number ; https://mathworld.wolfram.com/AlmostPerfectNumber.html  
**Statement matches intent:** yes  
**Known status:** Open; expected answer False. Known partial results: any non-power-of-2 almost perfect number must be an odd perfect square exceeding 10^35 with at least 6 distinct prime factors (Kishore, Jaycob-... ).  
**Difficulty:** math 9/10, Lean 9/10 · **Compute:** none · **Confidence:** high  
**Evidence:** The definition `1 + σ 1 n = 2 * n` correctly encodes σ(n) = 2n - 1 while avoiding ℕ-subtraction truncation. n = 0 is excluded automatically (1 + 0 ≠ 0); n = 1 satisfies it but is 2^0, so no degenerate witness. answer(sorry) ↔ ∃ ... is a faithful decide-the-truth-value encoding.  
**Next action:** Leave open. A worthwhile intermediate formalisation is 'every even almost perfect number is a power of 2' or 'odd almost perfect => square'.

## `infinitely_many_amicable` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Wikipedia/AmicableNumbers.lean:77`  
**Statement:** Decide whether the set of amicable pairs is infinite.  
**Source:** https://en.wikipedia.org/wiki/Amicable_numbers ; https://www.erdosproblems.com/830  
**Statement matches intent:** suspect — Two issues. (a) This is a verbatim `type_of%` duplicate of FormalConjectures/ErdosProblems/830.lean:erdos_830.parts.i — the same open problem is stated twice in the repo. (b) The underlying set {(a,b) | IsAmicable a b} is not the set of *amicable pairs*: IsAmicable a a is just σ(a) = 2a, i.e. a is perfect. So the formal statement is implied by 'there are infinitely many perfect numbers', a different (also open) problem.  
**Known status:** Open (erdosproblems.com/830 part i is listed as open). Roughly 10^9 amicable pairs are known but infinitude is unproven.  
**Difficulty:** math 9/10, Lean 9/10 · **Compute:** none · **Confidence:** high  
**Evidence:** IsAmicable has no a ≠ b field; (a,a) with σ(a)=2a satisfies it, and (0,0) satisfies it. Contrast BetrothedNumbers.infinitely_many_betrothed which does impose p.1 < p.2.  
**Flags:** duplicate statement of ErdosProblems/830.lean:erdos_830.parts.i; degenerate diagonal (a,a) = perfect numbers admitted into the 'amicable pair' set  
**Next action:** Either delete in favour of Erdos830.erdos_830.parts.i, or strengthen IsAmicable-based set to `{(a,b) | a < b ∧ IsAmicable a b}` (as BetrothedNumbers.lean correctly does) so that perfect numbers do not leak in.

## `opposite_parity_amicable` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Wikipedia/AmicableNumbers.lean:90`  
**Secondary category:** 6 (Computationally solvable with certificate)  
**Statement:** Decide whether there is an amicable pair with one member even and the other odd.  
**Source:** https://en.wikipedia.org/wiki/Amicable_numbers  
**Statement matches intent:** yes  
**Known status:** Open; expected answer False. All known amicable pairs have both members of the same parity. A mixed-parity pair would force a + b odd, hence σ(a) and σ(b) odd, so both members are squares or twice squares — a strong but not contradictory constraint.  
**Difficulty:** math 9/10, Lean 9/10 · **Compute:** medium · **Confidence:** high  
**Evidence:** `Even a ↔ Odd b` is (perhaps accidentally) exactly right: it holds iff exactly one of a, b is even (True↔True and False↔False both encode mixed parity, same-parity cases give True↔False). It also automatically excludes the degenerate a = b diagonal, since Even a ↔ Odd a is always False. So the missing `a ≠ b` does no harm here.  
**Next action:** Leave open. A targeted search over squares/twice-squares up to ~10^14 could in principle produce a decidable witness; nonexistence is out of reach.

## `relatively_prime_amicable` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Wikipedia/AmicableNumbers.lean:62`  
**Statement:** Decide whether there exist distinct coprime amicable numbers a, b (sigma(a) = sigma(b) = a + b).  
**Source:** https://en.wikipedia.org/wiki/Amicable_numbers  
**Statement matches intent:** yes  
**Known status:** Open; expected answer False. Known: a coprime amicable pair, if it exists, has product exceeding 10^67 and at least 22 distinct prime factors. No PR/campaign in this fork touches it.  
**Difficulty:** math 9/10, Lean 9/10 · **Compute:** none · **Confidence:** high  
**Evidence:** IsAmicable (FormalConjecturesForMathlib/NumberTheory/Amicable.lean) is σ a = a + b ∧ σ b = a + b, with no positivity or distinctness built in — but the explicit `a ≠ b` here rules out the degenerate perfect-number solutions, and (0,0) is the only zero solution and is excluded by a ≠ b. Statement is faithful.  
**Next action:** Leave open. Formalising the known lower bound would need substantial sigma-multiplicativity machinery.

## `andrica_conjecture` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Wikipedia/Andrica.lean:33`  
**Statement:** sqrt(p_{n+1}) - sqrt(p_n) < 1 for all n, where p_n is the n-th prime.  
**Source:** https://en.wikipedia.org/wiki/Andrica%27s_conjecture ; L. A. Ferreira, arXiv:2307.08725  
**Statement matches intent:** yes  
**Known status:** Open. Verified past 4*10^18. It would follow from prime gaps g_n = O(sqrt(p_n)), far beyond the best unconditional bound O(p^0.525) and not implied by RH. The file also records Ferreira's 'true for sufficiently large n' claim as research solved (also sorry).  
**Difficulty:** math 9/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Dot notation `(n+1).nth Nat.Prime` resolves to Nat.nth Nat.Prime (n+1) (the ℕ argument slots into the index, not the predicate), so n ranging over all of ℕ covers every consecutive prime pair starting at (2,3). Indexing convention is correct.  
**Next action:** Leave open. The realistic Lean target in this file is `andrica_conjecture.ferreira_large_n`, not the universally quantified statement.

## `artin_primitive_roots.parts.i` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Wikipedia/ArtinPrimitiveRootsConjecture.lean:92`  
**Statement:** For any integer a that is neither a perfect square nor -1, the set of primes having a as a primitive root has positive relative density among the primes.  
**Source:** https://en.wikipedia.org/wiki/Artin%27s_conjecture_on_primitive_roots ; Hooley (1967) proved it under GRH  
**Statement matches intent:** yes  
**Known status:** Open unconditionally; proved by Hooley under GRH (the conditional version is stated separately in the same file). Heath-Brown (1986) showed at most two exceptional primes a, but no single a is known to satisfy the conjecture. The file already carries the GRH-conditional companion theorem.  
**Difficulty:** math 10/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** S a = {p prime | orderOf (a : ZMod p) = p - 1}: p ≥ 2 so the ℕ-subtraction is exact, and p | a gives orderOf 0 = 0 ≠ p-1, so bad primes are excluded correctly. Hypotheses ¬IsSquare a (which also excludes a = 0, 1) and a ≠ -1 match the source. Set.HasDensity x {p | p.Prime} is the correct relative density.  
**Next action:** Leave open. The only realistic Lean path is via the GRH-conditional statement, itself a large analytic-number-theory project.

## `artin_primitive_roots.parts.ii` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Wikipedia/ArtinPrimitiveRootsConjecture.lean:113`  
**Statement:** If a = a_0 b^2 with a_0 squarefree, a is not a perfect power, and a_0 is not 1 mod 4, then the density of primes with a as primitive root equals Artin's constant.  
**Source:** https://en.wikipedia.org/wiki/Artin%27s_conjecture_on_primitive_roots ; OEIS A085397  
**Statement matches intent:** yes  
**Known status:** Open unconditionally; proved under GRH (Hooley; Lenstra-Moree-Stevenhagen for the correction factors). The GRH-conditional twin is stated in the same file.  
**Difficulty:** math 10/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** `ha' : ∀ n m, m ≠ 1 → a ≠ n ^ m` elaborates with n : ℤ, m : ℕ (ℤ has no zpow), so it says 'a is not a perfect power'; the m = 0 instance only adds a ≠ 1, so the hypothesis is non-contradictory (e.g. a = 2 satisfies it) and correctly excludes squares and a = -1. ArtinConstant's tprod is absolutely convergent (terms 1 - 1/(p^2-p)), so no junk-value issue there.  
**Next action:** Leave open.

## `artin_primitive_roots.variants.part_ii_power_squarefreePart_modeq_one` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Wikipedia/ArtinPrimitiveRootsConjecture.lean:182`  
**Statement:** Same as above but with squarefree part of b congruent to 1 mod 4, where an extra entanglement correction factor multiplies Artin's constant.  
**Source:** https://en.wikipedia.org/wiki/Artin%27s_conjecture_on_primitive_roots ; Lenstra-Moree-Stevenhagen, arXiv:1112.4816 eq. (1.4)  
**Statement matches intent:** suspect — The module docstring and the theorem docstring describe this case as 'a = b^m, m a maximal power' with no parity restriction, but the Lean statement adds `hm₂ : Odd m`. That narrowing is arguably necessary (even m makes a a square, forcing density 0), but it means the formalised statement is strictly narrower than the prose above it.  
**Known status:** Open unconditionally; known under GRH (LMS14). GRH-conditional twin present in the file.  
**Difficulty:** math 10/10, Lean 10/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** entanglementFactor has no division-by-zero: b_0 ≡ 1 mod 4 is odd and m is odd, so 2 ∤ gcd(b_0,m) and every factor 1/(2-p) has p ≥ 3; and 1 + p - p^2 ≠ 0 for all primes p. Both products are finite Finset products, so no tprod convergence issue.  
**Flags:** prose (no parity condition) vs formal statement (Odd m) mismatch; entanglement formula transcribed from LMS14 eq. (1.4) — needs literature check  
**Next action:** Leave open; separately reconcile the docstring with the `Odd m` hypothesis, or split the even-m case out explicitly.

## `artin_primitive_roots.variants.part_ii_power_squarefreePart_not_modeq_one` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Wikipedia/ArtinPrimitiveRootsConjecture.lean:154`  
**Statement:** If a = b^m with b not a perfect power, m > 1 odd, and the squarefree part of b not 1 mod 4, the density of primes with a as primitive root is Artin's constant times prod_{p|m} p(p-2)/(p^2-p-1).  
**Source:** https://en.wikipedia.org/wiki/Artin%27s_conjecture_on_primitive_roots ; Lenstra-Moree-Stevenhagen, arXiv:1112.4816 eq. (1.2)  
**Statement matches intent:** yes  
**Known status:** Open unconditionally; known under GRH (LMS14). GRH-conditional twin present in the file.  
**Difficulty:** math 10/10, Lean 10/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** hb (b not a perfect power) forces b ≥ 2 (b = 0 = 0^2 and b = 1 = 1^2 both violate it), so no degenerate a. m odd means every p | m is ≥ 3, so p - 2 ≥ 1 and p^2 - p - 1 ≠ 0 in powCorrectionFactor: no division-by-zero junk. Nat.squarefreePart is defined in FormalConjecturesForMathlib/Data/Nat/Squarefree.lean and matches b_0.  
**Flags:** correction-factor formula transcribed from LMS14 eq. (1.2); not independently re-derived — needs literature check  
**Next action:** Leave open.

## `balanced_primes` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Wikipedia/BalancedPrimes.lean:33`  
**Statement:** Decide whether there are infinitely many n for which (p_n + p_{n+2})/2 is prime, i.e. infinitely many balanced primes.  
**Source:** https://en.wikipedia.org/wiki/Balanced_prime ; OEIS A006562  
**Statement matches intent:** yes  
**Known status:** Open; expected answer True. Equivalent to infinitude of 3-term arithmetic progressions of *consecutive* primes (CPAP-3), which is open — Green-Tao gives APs of primes but not consecutive ones.  
**Difficulty:** math 9/10, Lean 9/10 · **Compute:** none · **Confidence:** high  
**Evidence:** The condition 'the average of p_n and p_{n+2} is prime' is equivalent to 'p_{n+1} is that average', because any prime strictly between p_n and p_{n+2} must be p_{n+1}. ℕ-division truncation only bites when p_n + p_{n+2} is odd, i.e. n = 0 (2+5)/2 = 3, which happens to be prime and is a single element — irrelevant to infinitude. Nat.nth Prime indexing is 0-based and consistent.  
**Flags:** ℕ-division truncation at n = 0 spuriously includes n = 0 in the set (harmless for an infinitude question)  
**Next action:** Leave open. Out of reach of current sieve technology.

## `balanced_primes_order` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Wikipedia/BalancedPrimes.lean:43`  
**Statement:** Decide whether for every k > 0 there are infinitely many n with 2k*p_n = sum_{i=1}^{k} (p_{n-i} + p_{n+i}), i.e. infinitely many balanced primes of every order.  
**Source:** https://en.wikipedia.org/wiki/Balanced_prime ; OEIS A006562  
**Statement matches intent:** suspect — The source poses the question per order k ('are there infinitely many balanced primes of order k?'). The formalisation bundles all k into a single ∀ under one answer(sorry) truth value, so the decided answer is 'true for every k' rather than a per-k answer; if the phenomenon held for k = 1 but failed for some large k the encoding would return False, losing information.  
**Known status:** Open for every k ≥ 1 (k = 1 is already the open balanced-prime / CPAP-3 question).  
**Difficulty:** math 9/10, Lean 9/10 · **Compute:** none · **Confidence:** high  
**Evidence:** The guard `k ≤ n` together with i ∈ Finset.Ioc 0 k ensures n - i is an exact (untruncated) ℕ-subtraction, and the equation is stated in cleared-denominator form 2*k*p_n = Σ(...), avoiding ℕ-division. Indexing is 0-based and internally consistent with balanced_primes.  
**Flags:** single answer(sorry) collapses a family of questions indexed by k  
**Next action:** Leave open; consider reformulating as `∀ k > 0, answer(sorry) k ↔ ...` or as a per-k family.

## `bateman_horn_conjecture` — False / refutable as stated (cat 3)

**File:** `FormalConjectures/Wikipedia/BatemanHornConjecture.lean:73`  
**Secondary category:** 9 (Major open problem / currently infeasible)  
**Statement:** For distinct irreducible polynomials with positive leading coefficients satisfying the Schinzel condition, the count of n <= x at which all are simultaneously prime is asymptotic to C * x / (log x)^k with C the Bateman-Horn constant.  
**Source:** https://en.wikipedia.org/wiki/Bateman%E2%80%93Horn_conjecture ; Bateman-Horn (1962)  
**Statement matches intent:** no — `BatemanHornConstant` is defined with Mathlib's `∏'` (tprod), which is an *unconditional* (Finset-filter) limit and therefore requires `Multipliable`. The Bateman-Horn Euler product is in general only conditionally convergent: the p-th factor is (1-1/p)^{-k}(1-ω_p/p) = 1 + (k-ω_p)/p + O(1/p^2), and Σ_p |k - ω_p|/p diverges whenever ω_p genuinely fluctuates. For polys = {X^2+1} (k=1) one has ω_p = 0 for p ≡ 3 mod 4 and ω_p = 2 for p ≡ 1 mod 4, so |log(term)| ≍ 1/p and the sum over p ≡ 3 mod 4 diverges: the family is NOT multipliable, `∏'` falls back to its junk value 1, and BatemanHornConstant {X^2+1} collapses to 1/D = 1/2. The theorem then asserts #{n ≤ x : n^2+1 prime} ~ (1/2) x / log x, whereas the true (Hardy-Littlewood/Landau) constant is ≈ 0.6864. So the formal statement is not the Bateman-Horn conjecture and is believed false.  
**Known status:** The intended conjecture is a major open problem (it implies twin primes, Bunyakovsky, Landau's n^2+1 problem). The *formal* statement is a different, almost certainly false, assertion for any family whose ω_p is not eventually constant. No PR or campaign in this fork touches it. The file header notes it was one-shot generated by an LLM with minimal cleaning.  
**Difficulty:** math 10/10, Lean 10/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** Mathlib's `tprod f = if h : Multipliable f then h.choose else 1`; for positive reals Multipliable ⟺ Σ|log f p| < ∞ (unconditional = absolute in ℝ). The X^2+1 computation above shows divergence. Secondary minor issues: CountSimultaneousPrimes ranges over Finset.range (⌊x⌋₊ + 1) so it includes n = 0 (harmless asymptotically) and uses natAbs so negative prime values would count (harmless given positive leading coefficient and degree ≥ 1).  
**Flags:** MAJOR: tprod junk value — Bateman-Horn Euler product is only conditionally convergent, so BatemanHornConstant degenerates to 1/D for e.g. {X^2+1}; off-by-one: n = 0 counted; natAbs allows negative polynomial values to count as prime  
**Next action:** Fix the definition before any proof attempt: replace the unconditional `∏'` by an ordered limit over primes below x (e.g. `Tendsto (fun N => ∏ p ∈ primesBelow N, ...) atTop (𝓝 C)`), or bundle the constant as an existential 'C is the limit of the truncated products'. Then re-classify as cat 9.

## `beal_conjecture` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Wikipedia/BealConjecture.lean:35`  
**Statement:** If A^x + B^y = C^z with A, B, C positive and x, y, z > 2, then A, B, C share a common prime factor.  
**Source:** https://en.wikipedia.org/wiki/Beal_conjecture  
**Statement matches intent:** yes  
**Known status:** Open, with a US$1,000,000 prize. Verified for all variables up to 1000 and many exponent triples; the Darmon-Granville finiteness theorem handles fixed exponent triples with 1/x+1/y+1/z < 1 but not the full statement. The file already proves FLT follows from it (flt_of_beal_conjecture).  
**Difficulty:** math 10/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** A,B,C ≠ 0 and 2 < x,y,z are the correct hypotheses; `1 < Finset.gcd {A,B,C} id` correctly expresses a common factor even when two of A,B,C coincide (Finset dedup does not change the gcd). No degenerate solution: A=B=C=1 fails 1+1=1.  
**Next action:** Leave open. Progress would mean formalising known cases (e.g. specific exponent triples via modularity), each of which is a research project.

## `beck_fiala_conjecture` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Wikipedia/BeckFialaConjecture.lean:81`  
**Statement:** There is a universal constant C such that every set system in which each element lies in at most t sets admits a +-1 colouring with all set sums bounded by C*sqrt(t).  
**Source:** https://en.wikipedia.org/wiki/Beck%E2%80%93Fiala_theorem ; Beck-Fiala (1981)  
**Statement matches intent:** yes  
**Known status:** Open. Best known bounds: 2t - 1 (Beck-Fiala), 2t - log*t (Bukh 2016), and O(sqrt(t log n)) (Banaszczyk 1998); the n-free O(sqrt t) bound remains out of reach. It is implied by the (also open) Komlos conjecture.  
**Difficulty:** math 9/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** C is quantified before n, m, t, so the constant is uniform as required. The t = 0 case is not vacuous but is genuinely true (degree 0 forces every S i empty, so all sums are 0 ≤ C*sqrt 0 = 0), so unlike beck_fiala_theorem no `1 ≤ t` guard is needed. Fin n / Fin m indexing and χ : Fin n → ℝ with values ±1 are faithful.  
**Next action:** Leave open. A realistic Lean target in this file is `beck_fiala_theorem` (the 2t-1 bound), whose floating-colour/linear-algebra proof is a medium-size but genuinely feasible formalisation.

## `infinitely_many_betrothed` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Wikipedia/BetrothedNumbers.lean:70`  
**Statement:** Decide whether there are infinitely many betrothed (quasi-amicable) pairs m < n with sigma(m) = sigma(n) = m + n + 1.  
**Source:** https://en.wikipedia.org/wiki/Betrothed_numbers ; OEIS A005276  
**Statement matches intent:** yes  
**Known status:** Open; expected answer True. Millions of pairs are known (starting 48, 75) but infinitude is as far out of reach as for amicable pairs.  
**Difficulty:** math 9/10, Lean 9/10 · **Compute:** none · **Confidence:** high  
**Evidence:** The `p.1 < p.2` guard both enforces distinctness (excluding the quasiperfect diagonal) and counts each unordered pair once, so the set is exactly the set of betrothed pairs. Contrast same_parity_betrothed in the same file, which omits it.  
**Next action:** Leave open.

## `same_parity_betrothed` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Wikipedia/BetrothedNumbers.lean:60`  
**Secondary category:** 6 (Computationally solvable with certificate)  
**Statement:** Decide whether there is a betrothed (quasi-amicable) pair sigma(m) = sigma(n) = m + n + 1 in which m and n have the same parity.  
**Source:** https://en.wikipedia.org/wiki/Betrothed_numbers ; OEIS A005276  
**Statement matches intent:** no — `m ≠ n` is missing. Taking m = n, IsBetrothed m m says σ(m) = 2m + 1, i.e. m is a QUASIPERFECT number, and Even m ↔ Even m is trivially true. So the formal statement is the disjunction 'there is a same-parity betrothed pair OR a quasiperfect number exists' — it merges two distinct open problems and is strictly weaker than the intended question. (Quasiperfect numbers are themselves a famous open existence problem: none below 10^35, any one must be an odd square with ≥ 7 distinct prime factors.)  
**Known status:** Both disjuncts open. All known quasi-amicable pairs have opposite parity; a same-parity pair must exceed 10^10.  
**Difficulty:** math 9/10, Lean 9/10 · **Compute:** medium · **Confidence:** high  
**Evidence:** IsBetrothed is a bare structure with fields σ 1 m = m+n+1 and σ 1 n = m+n+1 — no distinctness or positivity. The sibling theorem `infinitely_many_betrothed` in the same file explicitly imposes p.1 < p.2, showing the omission here is an oversight rather than a convention.  
**Flags:** MISSING m ≠ n: admits quasiperfect numbers as degenerate witnesses, turning the question into a disjunction of two different open problems  
**Next action:** Add `m ≠ n` (or `m < n`, as `infinitely_many_betrothed` in the same file does) to the statement, then re-classify as cat 9.

## `bing_borsuk_conjecture` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Wikipedia/BingBorsuk.lean:47`  
**Statement:** Every n-dimensional homogeneous absolute neighbourhood retract is a topological n-manifold.  
**Source:** https://en.wikipedia.org/wiki/Bing%E2%80%93Borsuk_conjecture ; Halverson-Repovs, Math. Communications 13 (2008), arXiv:0811.0886  
**Statement matches intent:** yes  
**Known status:** Open for n ≥ 3; known for n = 1, 2. The n = 3 case implies the Poincare conjecture (now a theorem, so that implication gives no leverage). Closely tied to the Busemann conjecture and to decomposition-space / cell-like-map theory (Bing's dogbone space etc.).  
**Difficulty:** math 10/10, Lean 10/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** Definitions check out: HomogeneousSpace (transitive homeomorphism group), IsAbsoluteNeighborhoodRetract (closed embedding into a normal space admits a neighbourhood retraction), HasLebesgueCoveringDimensionEq X n (LE n and ¬LE m for m < n). `Nonempty (ChartedSpace (Fin n → ℝ) X)` is an adequate 'topological n-manifold' conclusion since PartialHomeomorph sources/targets are open and compatible with the given topology; MetrizableSpace supplies T2 as the docstring notes.  
**Flags:** universe restricted to `X : Type` (Type 0) rather than Type*; harmless in practice; second countability / sigma-compactness is not asserted in the conclusion (Mathlib's ChartedSpace does not include it)  
**Next action:** Leave open. Even the n = 1 and n = 2 cases would require ANR theory, covering-dimension theory and topological-manifold recognition machinery that Mathlib does not have.

## `blochConstant_exact_value` — False / refutable as stated (cat 3)

**File:** `FormalConjectures/Wikipedia/Bloch.lean:134`  
**Secondary category:** 4 (Vacuously true / accidentally weakened)  
**Statement:** Ahlfors-Grunsky conjecture: the Bloch constant B (largest r such that every holomorphic f on the unit disk with f'(0)=1 contains a schlicht disk of radius r in its image) equals Gamma(1/3)Gamma(11/12)/(Gamma(1/4)sqrt(1+sqrt3)) ~ 0.4719.  
**Source:** Ahlfors & Grunsky, Uber die Blochsche Konstante, Math. Z. 42 (1937) 671-673; https://en.wikipedia.org/wiki/Bloch%27s_theorem_(complex_analysis)  
**Statement matches intent:** no — `blochConstant` (line 114) quantifies the schlicht set as an ARBITRARY set `∃ S ⊆ ball 0 1, ball x B ⊆ f '' S ∧ InjOn f S`, with no openness/connectedness/domain requirement on S. By the axiom of choice, whenever ball x B ⊆ f '' (ball 0 1) one can choose a set-theoretic section S (one preimage per point of the ball); then f '' S = ball x B and InjOn f S holds automatically. Hence the defining set of `blochConstant` is literally the same as that of `landauConstant` (line 170), i.e. blochConstant = landauConstant as defined, not the Bloch constant.  
**Known status:** Ahlfors-Grunsky conjecture is still open mathematically (best known: sqrt3/4+2e-4 <= B <= 0.4719). But the FORMAL statement is false: since the Lean `blochConstant` collapses to the Landau constant, and Landau's classical theorem gives L >= 1/2 (the file itself asserts landauConstant >= 0.5 + 10^-335 in `landauConstant_lower_bound`), we get blochConstant >= 0.5 > 0.4719 = RHS. The file is internally inconsistent: `blochConstant_upper_bound`, `blochConstant_exact_value` and `landauConstant_lower_bound` cannot all hold.  
**Difficulty:** math 9/10, Lean 8/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Choice-section argument shows `∃ S ⊆ ball 0 1, ball x B ⊆ f '' S ∧ InjOn f S ↔ ball x B ⊆ f '' (ball 0 1)`; the InjOn side condition is vacuous for arbitrary S. Numerically Gamma(1/3)Gamma(11/12)/(Gamma(1/4)sqrt(1+sqrt3)) = 0.4719 < 0.5 <= Landau constant. Note `univalentBlochConstant` is unaffected (f is globally injective there), and `blochRadius`/`blochRadius_id_eq_one` are also degenerate for the same reason.  
**Flags:** major semantic mismatch: InjOn-on-arbitrary-set loophole makes Bloch constant = Landau constant; formal statement false as written; intended Ahlfors-Grunsky conjecture remains open; same loophole affects blochRadius (line 45) and the research-solved theorems blochConstant_lower_bound / blochConstant_upper_bound (the latter also becomes false)  
**Next action:** Fix the definition: require S to be open (or a domain) and f injective *and* conformal on S, e.g. `∃ S ⊆ ball 0 1, IsOpen S ∧ ...`, or define blochRadius via `∃ S, IsOpen S ∧ InjOn f S ∧ ball x B = f '' S`. Then re-tag as open. Refuting the current statement in Lean would need Landau's theorem L >= 1/2 (not in Mathlib), so the practical action is a definition repair, not a proof.

## `landauConstant_exact_value` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Wikipedia/Bloch.lean:188`  
**Statement:** Rademacher's conjecture: the Landau constant L (largest r such that the image of every holomorphic f on the unit disk with f'(0)=1 contains some disk of radius r) equals Gamma(1/3)Gamma(5/6)/Gamma(1/6) ~ 0.5433.  
**Source:** H. Rademacher, On the Bloch-Landau constant, Amer. J. Math. 65 (1943) 387-390; https://mathworld.wolfram.com/BlochConstant.html  
**Statement matches intent:** yes  
**Known status:** Open. Known: 0.5 + 10^-335 <= L (Yanagihara 1995) <= 0.5433 (Rademacher). No exact evaluation known; extremal-function existence is not established.  
**Difficulty:** math 9/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** `landauConstant` is defined faithfully (sup of B such that every normalized holomorphic f contains a disk of radius B in its image; deriv f 0 is honest since ball 0 1 is open). The set is nonempty (all B <= 0 belong) and bounded above by 1 (identity map), so the sSup is meaningful.  
**Next action:** Leave open. Any progress would first need Mathlib support for the Koebe/Landau-Schottky machinery; even the classical bound L >= 1/2 is a substantial standalone formalization target.

## `bounded_burnside_problem` — Already solved externally (cat 1)

**File:** `FormalConjectures/Wikipedia/BoundedBurnsideProblem.lean:31`  
**Secondary category:** 5 (Solved mathematically, not yet formalized)  
**Statement:** Bounded Burnside problem: must a finitely generated group of finite exponent n be finite?  
**Source:** Novikov & Adian (1968), Infinite periodic groups I-III, Izv. Akad. Nauk SSSR; Ol'shanskii (1982); https://en.wikipedia.org/wiki/Burnside_problem#Bounded_Burnside_problem  
**Statement matches intent:** yes  
**Known status:** SOLVED EXTERNALLY, negatively: Novikov-Adian (1968) proved the free Burnside group B(m,n) is infinite for m >= 2 and odd n >= 4381 (later n >= 665, and Ivanov/Lysenok for even n >= 8000/8000+). Hence the answer is `False`. Not formalized in any proof assistant to my knowledge.  
**Difficulty:** math 9/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** The inner proposition `∀ G [Group G], Group.FG G → ∀ n > 0, (∀ g, g^n = 1) → Finite G` is refuted by B(2,665); so answer(sorry) = False and the theorem becomes `False ↔ False`. No degenerate hypotheses: n > 0 is required, G : Type is only a universe restriction and Novikov-Adian groups live in Type 0.  
**Flags:** mis-tagged: category should be `research solved`, not `research open`; closing the Lean statement is research-scale despite the mathematics being settled  
**Next action:** Re-tag as `research solved` with answer(False), and record that closing it in Lean requires formalizing an infinite finitely generated group of finite exponent (Novikov-Adian or Ol'shanskii's geometric proof) — research-scale.

## `brennan_universalSpectrum` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Wikipedia/Brennanconjecture.lean:70`  
**Statement:** Brennan's conjecture in integral-means form: the universal integral means spectrum of the class S of normalized univalent functions satisfies B(-2) = 1.  
**Source:** https://en.wikipedia.org/wiki/Brennan_conjecture ; Pommerenke, Boundary Behaviour of Conformal Maps, ch. 8  
**Statement matches intent:** yes  
**Known status:** Open. B(-2) >= 1 is classical; the upper bound B(-2) <= 1 is exactly Brennan's conjecture. Best known upper bounds are ~1.21 (Hedenmalm-Shimorin, Kayumov). arXiv:2512.09330 (Jin, Dec 2025 / rev. Mar 2026) only proves Brennan's conjecture for univalent *rational* functions and continuity of IMS functionals on Teichmuller space — not the general case.  
**Difficulty:** math 9/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Definitions check out: limsup over 𝓝[Iio 1] 1 of log ∫_{-π}^{π} |f'(re^{iθ})|^τ dθ / |log(1-r)| is the standard beta_f(tau); univalence gives f' non-vanishing so the τ=-2 integrand is continuous on each circle of radius r<1 and no Bochner junk value arises. AnalyticOn on the open unitDisk gives an honest `deriv`.  
**Flags:** sSup junk-value risk if the spectrum set were unbounded above (it is not, for τ=-2, but this is unproved in-file)  
**Next action:** Leave open. A Lean attack would first require Mathlib theory for integral means of univalent functions (Koebe distortion, area theorem); milestone: prove `universalSpectrum (-2) >= 1` via the Koebe function.

## `brennan_universalSpectrumBounded` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Wikipedia/Brennanconjecture.lean:76`  
**Statement:** Brennan's conjecture restricted to bounded univalent functions: the universal integral means spectrum over normalized univalent f with bounded image satisfies B_b(-2) = 1.  
**Source:** https://en.wikipedia.org/wiki/Brennan_conjecture ; arXiv:2409.15074  
**Statement matches intent:** yes  
**Known status:** Open, equivalent in difficulty to the unbounded version (the two spectra at tau=-2 are conjecturally equal; `brennan_spectra_eq` in the file is derived from both). No proof in the literature; the Dec-2025 arXiv paper cited in the header only settles the rational-function subclass.  
**Difficulty:** math 9/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Same faithful definitions as the unbounded case, with the extra `Bornology.IsBounded (f '' unitDisk)` restriction, matching the bounded-univalent formulation of Brennan's conjecture.  
**Next action:** Leave open; same prerequisite Mathlib theory as `brennan_universalSpectrum`.

## `brocard_conjecture` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Wikipedia/BrocardConjecture.lean:36`  
**Statement:** Brocard's conjecture: for n >= 2 there are at least four primes strictly between p_n^2 and p_{n+1}^2.  
**Source:** https://en.wikipedia.org/wiki/Brocard%27s_conjecture  
**Statement matches intent:** yes  
**Known status:** Open. Stronger than Legendre's conjecture-type statements about primes between consecutive squares; no unconditional proof. The cited Ferreira preprint (arXiv:2307.08725) claims the large-n case and is recorded separately in the file as `research solved`.  
**Difficulty:** math 9/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Statement is `4 <= ((Ioo (prev^2) (next^2)).filter Nat.Prime).card` with prev/next consecutive primes — faithful; Ioo is the strict interval, matching 'between the squares'.  
**Next action:** Leave open. A conditional route (e.g. from Cramer/Riemann-type gap bounds plus a finite check) is not currently formalizable; verifying small n by computation does not resolve the universal statement.

## `buchi_problem` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Wikipedia/Buchi.lean:38`  
**Statement:** Buchi's problem: is there M such that whenever (x+n)^2 + a is a perfect square for n = 0..M-1, necessarily a = 0?  
**Source:** https://en.wikipedia.org/wiki/B%C3%BCchi%27s_problem ; Vojta, Diagonal quadratic forms and Hilbert's tenth problem (1999)  
**Statement matches intent:** yes  
**Known status:** Open unconditionally. Vojta (1999) proved a positive answer (with M = 8) assuming the Bombieri-Lang conjecture for surfaces of general type; unconditionally nothing is known beyond the M<=4 counterexamples. The expected answer is `True`.  
**Difficulty:** math 9/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** `IsBuchi` is monotone in M (larger M weakens the hypothesis), and the file correctly certifies ¬IsBuchi M for M <= 4 with explicit witnesses, so the `∃ M, 1 <= M ∧ IsBuchi M` encoding is non-degenerate.  
**Next action:** Leave open. Only a conditional variant (assume Bombieri-Lang, conclude M=8) is currently statable; that would be a worthwhile added `research solved`-style conditional theorem.

## `buchi_problem_M5` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/Wikipedia/Buchi.lean:51`  
**Statement:** First open case of Buchi's problem: if (x+n)^2 + a is a perfect square for n = 0,1,2,3,4, then a = 0.  
**Source:** https://en.wikipedia.org/wiki/B%C3%BCchi%27s_problem ; Hensley (1983) length-4 example; Vojta (1999)  
**Statement matches intent:** yes  
**Known status:** Open, and not known to be true — M=5 could conceivably fail (nontrivial length-4 sequences exist, e.g. (6,23,32,39)). Vojta's conditional result only gives M=8. Searches have found no length-5 nontrivial sequence, which is evidence but not proof.  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** medium · **Confidence:** medium  
**Evidence:** The M=5 instance corresponds to rational points on a surface cut out by three quadric relations; unlike M>=8 (curves of general type / conditional Vojta), no unconditional method covers it. The statement could be FALSE, so proving it is not the only possible outcome.  
**Flags:** statement may be false: no proof that nontrivial length-5 sequences do not exist; needs literature check for post-2024 progress on M=5  
**Next action:** Two concrete avenues: (a) run a large search for length-5 nontrivial sequences (elliptic/K3 surface point search) — a hit would refute it outright and is a genuinely reachable outcome; (b) study the associated surface x_n^2 = (x+n)^2+a for n=0..4 (an intersection of quadrics / K3) and look for an unconditional determination of its rational points.

## `bunyakovsky_conjecture` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Wikipedia/Bunyakovsky.lean:32`  
**Statement:** Bunyakovsky's conjecture: an irreducible integer polynomial of degree >= 1 with positive leading coefficient and no fixed prime divisor takes prime values infinitely often.  
**Source:** https://en.wikipedia.org/wiki/Bunyakovsky_conjecture  
**Statement matches intent:** yes  
**Known status:** Open in the strongest sense: not a single case of degree >= 2 is known (n^2+1 is the famous instance). The degree-1 case is Dirichlet's theorem, but the statement is universally quantified over all degrees, so it is not weakened.  
**Difficulty:** math 10/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Definitions read from FormalConjecturesForMathlib/Algebra/Polynomial/Basic.lean lines 36-45; hypotheses are non-vacuous (X^2+1 satisfies both) and the conclusion is the intended infinitude.  
**Next action:** Leave open. The only tractable sub-result is the degree-1 specialization via Mathlib's Dirichlet theorem (`Nat.setOf_prime_and_eq_mod_infinite` / `forall_exists_prime_gt_and_eq_mod`), worth adding as a `research solved` corollary.

## `BB_6` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Wikipedia/BusyBeaver.lean:97`  
**Statement:** Determine BB(6), the maximum number of steps a halting 6-state 2-symbol Turing machine can make on a blank tape.  
**Source:** https://wiki.bbchallenge.org/wiki/Main_Page ; https://en.wikipedia.org/wiki/Busy_beaver  
**Statement matches intent:** no — The state/symbol roles are SWAPPED. In `FormalConjecturesForMathlib/Computability/TuringMachine/BusyBeavers.lean`, `Machine Γ Λ := Λ → Γ → Option (Option Λ × Stmt Γ)` with Γ = tape symbols and Λ = states. But `Candidate n` (line 36) sets `Γ_card = n` and `Λ_card = 2`, i.e. n SYMBOLS and 2 STATES, and `sanity_check` uses `Machine (Fin n) (Fin 2)` accordingly. So `BB n` as defined is the 2-state n-symbol busy beaver, not the n-state 2-symbol one. Cross-check: the file's own `BB_1 = 1` and `BB_3 = 21` are the n-state 2-symbol values (2-state 1-symbol gives 2, and BB(2 states,3 symbols) = 38), so the definition contradicts the stated small values.  
**Known status:** BB(6) (n-state, 2-symbol) is open and widely believed to be beyond reach: bbchallenge showed BB(6) > 2 ↑↑ 5 (2024) and later far larger towers; 'Antihydra' is a known Collatz-like obstruction. BB(5) = 47,176,870 was settled and Coq-verified in 2024. The swapped reading BB(2 states, 6 symbols) is also unknown (huge lower bounds known).  
**Difficulty:** math 10/10, Lean 10/10 · **Compute:** large · **Confidence:** high  
**Evidence:** Read the Machine definition (BusyBeavers.lean lines 49-77) confirming Γ = symbols, Λ = labels/states; Candidate n fixes Γ_card = n, Λ_card = 2. Under either reading the value is unknown, so the mismatch does not make the statement provable — but it does mean the file's BB_1..BB_5 values are inconsistent with its own definition.  
**Flags:** definition defect: states and symbols swapped in `Candidate` and `sanity_check`; the research-solved theorems BB_1..BB_5 in the same file are FALSE under the definition as written; answer(sorry) here demands an explicit numeral for a value believed independent of strong theories  
**Next action:** Fix `Candidate` to `Γ_card = 2`, `Λ_card = n` (and `sanity_check` to `Machine (Fin 2) (Fin n)`), then leave BB_6 open. Do not attempt to supply an answer.

## `charmichaelTotient` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Wikipedia/CarmichaelTotient.lean:55`  
**Statement:** Carmichael's totient conjecture: for every n >= 1 there is some m ≠ n with phi(m) = phi(n).  
**Source:** https://en.wikipedia.org/wiki/Carmichael%27s_totient_function_conjecture ; K. Ford, The distribution of totients (arXiv:1104.3264)  
**Statement matches intent:** yes  
**Known status:** Open. Ford proved any counterexample exceeds 10^(10^10) (recorded in the same file as `carchimaelTotient_bound`); the odd case is elementary (phi(2n)=phi(n)) and already proved in-file, so only n even with a unique totient preimage is at stake.  
**Difficulty:** math 9/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** `CarmichaelTotientFor n = ∃ m ≠ n, phi m = phi n` with `0 < n`; no degeneracy (m = 0 is unusable since phi 0 = 0 < phi n for n > 0). Faithful to the standard statement.  
**Next action:** Leave open. Realistic partial targets: extend the in-file elementary reductions (e.g. handle n ≡ 2 mod 4, n divisible by small primes) rather than attempt Ford's analytic machinery.

## `lebesgue_nagell` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/Wikipedia/Catalan.lean:64`  
**Statement:** Lebesgue-Nagell equation: for every odd prime p the only integer solutions of x^2 - 2 = y^p are (x,y) = (±1,-1).  
**Source:** E. Katz and K. Pratt, On the Lebesgue-Nagell equation x^2-2=y^p, arXiv:2507.12397 (2025)  
**Statement matches intent:** yes  
**Known status:** Open only in a finite explicit exponent window. Katz-Pratt (arXiv:2507.12397, verified by web lookup) prove the conjecture unconditionally for p <= 13 and for p > 911, and show any nontrivial solution has y > 10^1000. So only the primes 17 <= p <= 911 remain.  
**Difficulty:** math 8/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Statement is an iff quantified over odd primes p and integers x,y; the reverse direction is trivially true (p odd), the forward direction is the conjecture. Matches the folklore conjecture as stated in the cited paper.  
**Next action:** Medium-to-large: the residual range is a finite list of ~150 primes attacked by the modular method (Frey curves, level lowering) plus linear forms in logarithms — none of which exists in Mathlib. Realistic first milestone: formalize the p = 3 case (Mordell curve X^2 = Y^3 + 2 has only integral points (±1,-1)) and the reverse implication of the iff (immediate: `simp [hodd.neg_one_pow]`).

## `pillais_conjecture` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Wikipedia/Catalan.lean:42`  
**Statement:** Pillai's conjecture: for fixed positive a, b, c the equation a x^n - b y^m = c has only finitely many solutions with x, y > 1, m, n > 1, (m,n) ≠ (2,2).  
**Source:** https://en.wikipedia.org/wiki/Catalan%27s_conjecture#Pillai's_conjecture  
**Statement matches intent:** yes  
**Known status:** Open. Pillai's conjecture follows from the abc conjecture (Tijdeman/Langevin); unconditionally only special families (Catalan-type, fixed exponents via Baker's method) are known.  
**Difficulty:** math 9/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Set-builder over ℕ^4 with 1 < x, 1 < y, 1 < m, 1 < n, (m,n) ≠ (2,2) and `.Finite`; the exclusion of (2,2) correctly removes the Pell families that give infinitely many solutions.  
**Next action:** Leave open. A worthwhile in-repo variant: state the abc-conditional implication, or the known fixed-exponent case via linear forms in logarithms.

## `cerny_conjecture` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Wikipedia/CernyConjecture.lean:56`  
**Statement:** Cerny's conjecture: every synchronizing DFA with n states has a synchronizing (reset) word of length at most (n-1)^2.  
**Source:** J. Cerny (1964); Y. Shitov, J. Autom. Lang. Comb. 24 (2019) 367-373; https://en.wikipedia.org/wiki/Synchronizing_word  
**Statement matches intent:** yes  
**Known status:** Open since 1964; best known upper bound ~0.1654 n^3 (Shitov 2019, recorded in-file). Verified for n <= 12-ish by computer search and for structured classes (Eulerian, aperiodic). Expected answer is `True`.  
**Difficulty:** math 9/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Uses Mathlib `DFA α σ` with repo-local `IsSynchronizing`/`IsSynchronizingWord`; alphabet α is unrestricted (correct — the conjecture is uniform in the alphabet) and σ is a Fintype.  
**Next action:** Leave open. A tractable adjacent contribution: formalize the cubic Frankl-Pin bound (n^3-n)/6, which is a clean linear-algebra/extremal argument, as a stepping stone.

## `class_number_problem` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Wikipedia/ClassNumberProblem.lean:36`  
**Statement:** Gauss's class number one problem for real quadratic fields: there are infinitely many squarefree d > 1 with h(Q(sqrt d)) = 1.  
**Source:** https://en.wikipedia.org/wiki/Class_number_problem  
**Statement matches intent:** yes  
**Known status:** Wide open (Gauss). Cohen-Lenstra heuristics predict ~75.4% of real quadratic fields have class number 1, but not a single infinite family is proved; the imaginary counterpart (Stark-Heegner) is in the same file as solved.  
**Difficulty:** math 10/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** `IsClassNumberOne d` bundles the irreducibility of X^2 - d over Q as a proof-carrying existential and takes `NumberField.classNumber (AdjoinRoot (X^2 - C d)) = 1`; combined with `Squarefree d ∧ d > 1` this correctly picks out real quadratic fields of class number one, and `.Infinite` is the intended conclusion.  
**Next action:** Leave open. No feasible Lean path; even the heuristic side is unformalizable. Could add the (proved) Stark-Heegner statement as the tractable neighbour.

## `collatz_conjecture` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Wikipedia/CollatzConjecture.lean:49`  
**Statement:** Collatz (3x+1) conjecture: iterating n -> n/2 (n even), 3n+1 (n odd) from any positive integer eventually reaches 1.  
**Source:** https://en.wikipedia.org/wiki/Collatz_conjecture ; Lagarias, The 3x+1 problem: an overview (2010); erdosproblems.com/1135  
**Statement matches intent:** yes  
**Known status:** Famous open problem. Tao (2019) proved almost all orbits attain almost bounded values; verified below 2^68. No proof.  
**Difficulty:** math 10/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** `collatzStep` and the iterate formulation `∃ m, collatzStep^[m] n = 1` with `n > 0` is faithful (n = 0 is correctly excluded since it is a fixed point).  
**Next action:** Leave open. Do not spend effort.

## `Tunnell_even_converse` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Wikipedia/CongruentNumber.lean:108`  
**Statement:** Converse of Tunnell's theorem for even squarefree n: if 2|C_n| = |D_n| (counts for 8x^2+2y^2+64z^2 and 8x^2+2y^2+16z^2) then n is a congruent number.  
**Source:** https://en.wikipedia.org/wiki/Tunnell%27s_theorem ; Tunnell, Invent. Math. 72 (1983)  
**Statement matches intent:** yes  
**Known status:** Open unconditionally; equivalent in status to the odd case and follows from BSD.  
**Difficulty:** math 10/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Identical structure to `Tunnell_odd_converse` with the even-n forms; finiteness of the representation sets keeps `ncard` meaningful.  
**Flags:** unconditional statement of a BSD-conditional theorem  
**Next action:** Leave open or restate conditionally on BSD.

## `Tunnell_odd_converse` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Wikipedia/CongruentNumber.lean:102`  
**Statement:** Converse of Tunnell's theorem for odd squarefree n: if 2|A_n| = |B_n| (counts of representations by 2x^2+y^2+32z^2 and 2x^2+y^2+8z^2) then n is a congruent number.  
**Source:** https://en.wikipedia.org/wiki/Tunnell%27s_theorem ; Tunnell, Invent. Math. 72 (1983); Keith Conrad's notes  
**Statement matches intent:** yes  
**Known status:** Open unconditionally; it is a known consequence of the Birch-Swinnerton-Dyer conjecture (weak BSD for the congruent number curves y^2 = x^3 - n^2). The forward direction (in the same file) is Tunnell's theorem, proved.  
**Difficulty:** math 10/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Requires BSD-strength input: the criterion detects L(E_n,1) = 0, and deducing positive rank from vanishing central value is exactly the open half of BSD.  
**Flags:** the statement is unconditional but the mathematics is only known under BSD; consider adding a BSD hypothesis to make the intent explicit  
**Next action:** Leave open, or restate conditionally on BSD, which would turn it into a (still very large) formalization of Tunnell + Waldspurger + Coates-Wiles machinery.

## `conway99Graph` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Wikipedia/Conway99Graph.lean:63`  
**Statement:** Conway's 99-graph problem: is there a graph on 99 vertices in which every two adjacent vertices have exactly one common neighbour and every two non-adjacent vertices have exactly two?  
**Source:** https://en.wikipedia.org/wiki/Conway%27s_99-graph_problem (Conway's $1000 problem)  
**Statement matches intent:** yes  
**Known status:** Open; one of Conway's five $1000 problems. Non-existence is not known and no construction is known; standard srg feasibility conditions do not rule it out.  
**Difficulty:** math 9/10, Lean 10/10 · **Compute:** large · **Confidence:** high  
**Evidence:** The file validates the encoding on the two known small analogues (K_3 with 3 vertices, K_3 □ K_3 with 9), which are exactly the classical Conway-type examples — good evidence the predicate is right.  
**Next action:** Leave open. Exhaustive search over 99-vertex graphs is hopeless; progress would come from algebraic/spectral non-existence arguments for srg(99,14,1,2).

## `Dedekind_10` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Wikipedia/DedekindNumber.lean:275`  
**Secondary category:** 4 (Vacuously true / accidentally weakened)  
**Statement:** Determine the 10th Dedekind number M(10), the number of antichains of subsets of a 10-element set.  
**Source:** https://en.wikipedia.org/wiki/Dedekind_number ; OEIS A000372 (D(9) computed 2023 by Jakel and by Van Hirtum et al.)  
**Statement matches intent:** suspect — Same answer-encoding weakness as `M_eq`: `M 10 = answer(M' 10)` or `answer(kisielewiczFormula 10)` are formally legal answers that convey nothing. The intended reading (a decimal numeral) is clear but not enforced.  
**Known status:** M(10) is unknown. D(9) (42 digits) required ~5.3x10^18 operations on an FPGA supercomputer (2023); D(10) is estimated far beyond current hardware, and even given the number, certifying it in the Lean kernel is not feasible.  
**Difficulty:** math 8/10, Lean 10/10 · **Compute:** large · **Confidence:** medium  
**Evidence:** The file itself notes `native_decide` already crashes at n = 4 for the Kisielewicz formula; M is defined as `Fintype.card` over (Fin 10 → Bool) → Bool, i.e. a 2^1024-element function space — no kernel-checkable route exists.  
**Flags:** answer(sorry) loophole (non-numeral answers admissible); needs literature check that D(10) was not computed after Jan 2026 (believed not)  
**Next action:** Leave open; do not attempt. If kept, tighten the statement to `M 10 = (<numeral> : ℕ)` shape so the answer slot cannot be filled by an equal-by-construction expression.

## `M_eq` — Vacuously true / accidentally weakened (cat 4)

**File:** `FormalConjectures/Wikipedia/DedekindNumber.lean:268`  
**Secondary category:** 10 (Cannot classify without correction/clarification)  
**Statement:** Intended: find a (efficiently computable) closed form for the Dedekind numbers M(n). As formalized: exhibit some function equal to M.  
**Source:** https://en.wikipedia.org/wiki/Dedekind_number ; OEIS A000372; Kisielewicz (1988) arithmetic formula  
**Statement matches intent:** no — `M = answer(sorry)` places no constraint on the answer term: `answer(M')` closes it via the already-proved `M_eq_M'`, and `answer(kisielewiczFormula)` closes it modulo the in-file `M_eq_kisielewiczFormula`. The docstring's real content ('no closed form allowing efficient computation is known') is a complexity-theoretic/informal claim that this encoding cannot express.  
**Known status:** Not a well-posed formal problem. Trivially answerable as written; the informal question (efficient closed form for Dedekind numbers) is open/ill-defined and not captured.  
**Difficulty:** math 1/10, Lean 2/10 · **Compute:** none · **Confidence:** high  
**Evidence:** `M_eq_M' : M = M'` is proved sorry-free in the same file (line 230) via `equivMonotoneSperner`, so the goal `M = M'` is already available.  
**Flags:** answer(sorry) trivialization: any provably-equal function is a legal answer; prose/formal mismatch: 'no efficient closed form' is not expressed by the statement  
**Next action:** Either delete/downgrade this statement, or replace it with a precise complexity claim (e.g. counting antichains is #P-complete — Provan-Ball style) that can actually be formalized. As it stands `answer(M')` + `exact M_eq_M'` closes it in one line.

## `determinantal_conjecture` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Wikipedia/DeterminantalConjecture.lean:42`  
**Statement:** Marcus-de Oliveira conjecture: for normal complex n x n matrices A, B, det(A+B) lies in the convex hull of the n! products prod_i (lambda_i(A) + lambda_{sigma(i)}(B)).  
**Source:** https://en.wikipedia.org/wiki/Determinantal_conjecture ; Marcus (1973), de Oliveira (1982)  
**Statement matches intent:** yes  
**Known status:** Open since 1973/1982. Known for n <= 3, for Hermitian A,B (where it reduces to a classical result), and in various special positions; no general proof.  
**Difficulty:** math 9/10, Lean 9/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** Statement quantifies over all d1 d2 : n → ℂ and unitaries U1 U2 with n an arbitrary Fintype; the empty-index and n=1 cases are degenerate but true, so no vacuity issue.  
**Flags:** needs literature check for post-2024 progress on the Marcus-de Oliveira conjecture  
**Next action:** Leave open. A reachable sub-target: the Hermitian case, or n <= 3 by explicit computation.

## `babai_seress_conjecture` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Wikipedia/DiameterSimpleFiniteGroups.lean:164`  
**Statement:** Babai's conjecture (Babai-Seress 1.7): there is an absolute C such that every finite non-abelian simple group G has diam(G) <= (log|G|)^C.  
**Source:** L. Babai and A. Seress, On the diameter of permutation groups, Eur. J. Combin. 13 (1992), Conjecture 1.7  
**Statement matches intent:** yes  
**Known status:** Open, and strictly harder than Conjecture 1.5 (which it implies). Known for groups of Lie type of bounded rank (Helfgott, Pyber-Szabo, Breuillard-Green-Tao); the alternating/symmetric case is only quasipolynomial (Helfgott-Seress).  
**Difficulty:** math 10/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** The bounded-rank Lie type case is proved but the statement quantifies over all non-abelian finite simple groups, including A_n, so the open case is included and the statement is not accidentally weakened.  
**Next action:** Leave open; a genuine research problem requiring growth-in-groups machinery entirely absent from Mathlib.

## `babai_seress_conjecture_alternating` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Wikipedia/DiameterSimpleFiniteGroups.lean:152`  
**Statement:** Babai-Seress Conjecture 1.5: there is an absolute constant C with diam(A_n) <= n^C for every n, where diam is the max over generating sets of the Cayley graph diameter.  
**Source:** L. Babai and A. Seress, On the diameter of permutation groups, Eur. J. Combin. 13 (1992), Conjecture 1.5  
**Statement matches intent:** yes  
**Known status:** Open. Helfgott-Seress (2014) proved diam(A_n) <= exp(O((log n)^4)), quasipolynomial — the strongest known, still short of polynomial. No polynomial bound is known even for A_n with two generators.  
**Difficulty:** math 9/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** `cayleyGraph` via `SimpleGraph.fromRel` symmetrizes and enforces irreflexivity, matching the undirected Cayley graph on S ∪ S^{-1}; the file sanity-checks groupDiam on A_0, A_3, S_2.  
**Next action:** Leave open. Nothing in Mathlib supports expander/growth arguments; a first milestone would be the classical diam(A_n) bound for specific generating sets (e.g. the n^2-type bound for a transposition + n-cycle), which is a self-contained combinatorial exercise.

## `dickson_conjecture` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Wikipedia/Dickson.lean:38`  
**Statement:** For any finite set of degree-1 integer polynomials that are irreducible with positive leading coefficient and have no fixed prime divisor (Schinzel condition), there are infinitely many n making all of them simultaneously prime.  
**Source:** Dickson's conjecture, https://en.wikipedia.org/wiki/Dickson%27s_conjecture ; module docstring cites arXiv:0906.3850  
**Statement matches intent:** yes  
**Known status:** Open. Contains the twin-prime conjecture as the case fs = {X, X+2}. Repo already contains the strictly stronger Schinzel hypothesis H with an identical conclusion (FormalConjectures/Wikipedia/Schinzel.lean:schinzel_conjecture, also sorry) and a hypothesis-form copy in FormalConjectures/ErdosProblems/252.lean:88. No PR in pr_register.json and no campaign in campaign_register.json touches Dickson/Schinzel.  
**Difficulty:** math 10/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Degree-1 case of Schinzel's hypothesis H; implies twin primes, Sophie Germain, Polignac. Wide-open.  
**Flags:** duplicate: strictly implied by Schinzel.lean:schinzel_conjecture (same conclusion, weaker hypotheses) — the two sorries are redundant  
**Next action:** Leave open. Cheap repo-level improvement: derive dickson_conjecture from schinzel_conjecture (a one-line `exact schinzel_conjecture fs (fun f hf => (hfs f hf).2) hfs'`) so only one sorry carries the mathematical content.

## `infinite_cousin_primes` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Wikipedia/Dickson.lean:67`  
**Statement:** There are infinitely many primes p such that p+4 is also prime.  
**Source:** https://en.wikipedia.org/wiki/Cousin_prime ; special case of Dickson's conjecture  
**Statement matches intent:** yes  
**Known status:** Open; equivalent in difficulty to twin primes (Polignac with k = 2). Brun-type upper bounds only.  
**Difficulty:** math 10/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Instance of polignac_conjecture with k = 2, itself open.  
**Next action:** Leave open.

## `infinite_safe_primes` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Wikipedia/Dickson.lean:58`  
**Statement:** There are infinitely many primes p such that 2p+1 is also prime (Sophie Germain primes).  
**Source:** https://en.wikipedia.org/wiki/Safe_and_Sophie_Germain_primes ; special case of Dickson's conjecture  
**Statement matches intent:** yes  
**Known status:** Open. Largest known Sophie Germain primes are records, but infinitude is unknown; only sieve upper bounds and Chen-type results exist.  
**Difficulty:** math 10/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Case fs = {X, 2X+1} of Dickson.  
**Flags:** name/statement mismatch: 'safe_primes' vs Sophie Germain primes  
**Next action:** Leave open; rename to infinite_sophie_germain_primes (or state as {q | q.Prime ∧ ∃ p, q = 2p+1 ∧ p.Prime}) to match the name.

## `infinite_sexy_primes` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Wikipedia/Dickson.lean:76`  
**Statement:** There are infinitely many primes p such that p+6 is also prime.  
**Source:** https://en.wikipedia.org/wiki/Sexy_prime ; special case of Dickson's conjecture  
**Statement matches intent:** yes  
**Known status:** Open (Polignac with k = 3).  
**Difficulty:** math 10/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Instance of polignac_conjecture with k = 3, itself open.  
**Next action:** Leave open.

## `polignac_conjecture` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Wikipedia/Dickson.lean:49`  
**Statement:** For every k there are infinitely many primes p with p+2k also prime.  
**Source:** de Polignac's conjecture, https://en.wikipedia.org/wiki/Polignac%27s_conjecture  
**Statement matches intent:** yes  
**Known status:** Open. k = 1 is the twin prime conjecture (also stated in FormalConjectures/Wikipedia/TwinPrimes.lean:twin_primes as an answer(sorry) ↔ form). Zhang/Maynard/Polymath give bounded gaps (some even 2k ≤ 246 works) but no single k is known.  
**Difficulty:** math 10/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Special case of Dickson; no admissible pair is known to occur infinitely often.  
**Flags:** k = 0 instance is trivially true (infinitude of primes) — no positivity hypothesis; near-duplicate of TwinPrimes.lean:twin_primes at k = 1  
**Next action:** Leave open; possibly restrict to 0 < k and note that Maynard–Tao gives 'for some k'. Alternatively record the k = 0 case as a solved instance.

## `finite_twentyone_lt_finrank` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Wikipedia/EllipticCurveRank.lean:131`  
**Statement:** Only finitely many elliptic curves over ℚ (up to isomorphism) have rank greater than 21.  
**Source:** [PPVW2016] Section 8.2(a)  
**Statement matches intent:** yes  
**Known status:** Open. This is a heuristic prediction, not a theorem; it contradicts the classical unboundedness expectation stated two declarations earlier.  
**Difficulty:** math 10/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** PPVW random-matrix/lattice-point heuristic; no unconditional rank upper bound of any kind is known.  
**Flags:** contradicts unbounded_rank_conjecture in the same file  
**Next action:** Leave open.

## `half_rank_zero_and_half_rank_one` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Wikipedia/EllipticCurveRank.lean:92`  
**Statement:** When elliptic curves over ℚ are ordered by naive height, the proportion of rank-0 curves and the proportion of rank-1 curves each tend to 1/2.  
**Source:** Goldfeld / Katz–Sarnak minimalist conjecture; Bhargava's survey p.28, https://people.maths.bris.ac.uk/~matyd/BSD2011/bsd2011-Bhargava.pdf  
**Statement matches intent:** yes  
**Known status:** Open. Bhargava–Shankar prove average rank < 0.885 and density ≥ 20.62% of rank 0 (both stated as 'research solved' elsewhere in the same file), far from 50/50; the conjecture needs (at least) BSD-type input plus the parity conjecture.  
**Difficulty:** math 10/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Minimalist conjecture; even average rank = 1/2 is unknown.  
**Next action:** Leave open. Realistic Lean work would first need Mordell–Weil and Selmer machinery that Mathlib does not have.

## `rank_elkies28` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Wikipedia/EllipticCurveRank.lean:222`  
**Secondary category:** 5 (Solved mathematically, not yet formalized)  
**Statement:** Elkies' 2006 curve has Mordell–Weil rank exactly 28.  
**Source:** https://en.wikipedia.org/wiki/Rank_of_an_elliptic_curve#Largest_known_ranks ; https://mathoverflow.net/a/478050  
**Statement matches intent:** yes  
**Known status:** Rank = 28 known only under GRH (Klagsbrun–Sherman–Weigandt computed the rank exactly assuming GRH); unconditionally rank ≥ 28.  
**Difficulty:** math 9/10, Lean 10/10 · **Compute:** large · **Confidence:** high  
**Evidence:** Same as above; Mathlib lacks all required elliptic-curve arithmetic.  
**Flags:** unconditional exact rank is not known — statement should probably carry a GRH hypothesis  
**Next action:** Leave open; add GRH hypothesis, or first target the unconditional lower bound.

## `rank_elkiesKlagsbrun29` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Wikipedia/EllipticCurveRank.lean:191`  
**Secondary category:** 5 (Solved mathematically, not yet formalized)  
**Statement:** The Elkies–Klagsbrun (2024) curve has Mordell–Weil rank exactly 29.  
**Source:** https://en.wikipedia.org/wiki/Rank_of_an_elliptic_curve#Largest_known_ranks ; https://mathoverflow.net/a/478050  
**Statement matches intent:** yes  
**Known status:** Rank = 29 is known only conditionally on GRH (Mestre-style analytic upper bound / conditional BSD), as the file's own docstring for the curve says. Unconditionally only ≥ 29 is proved. No formal proof anywhere; Mathlib has no Mordell–Weil, no Selmer groups, no L-function machinery for elliptic curves.  
**Difficulty:** math 9/10, Lean 10/10 · **Compute:** large · **Confidence:** high  
**Evidence:** Exact rank of record curves is GRH-conditional; the Lean statement is unconditional.  
**Flags:** unconditional exact rank is not known — statement should probably carry a GRH hypothesis  
**Next action:** Leave open as stated. Realistic intermediate goal: formalize the ≥ 29 lower bound (explicit points + height-pairing regulator nonvanishing) — already large; the exact value needs GRH added as a hypothesis.

## `rank_height_count_asymptotic` — False / refutable as stated (cat 3)

**File:** `FormalConjectures/Wikipedia/EllipticCurveRank.lean:141`  
**Secondary category:** 8 (Deep but approachable research problem)  
**Statement:** For 1 ≤ r ≤ 20, the number of elliptic curves over ℚ of naive height ≤ H and rank ≥ r is H^((21-r)/24 + o(1)).  
**Source:** [PPVW2016] Section 8.2(b), cf. Theorem 7.3.3  
**Statement matches intent:** no — Two defects. (1) FALSE AS STATED: the o(1) is encoded as a single f with `∀ H : ℕ, 1 < H → ncard = (H:ℝ)^((21-r)/24 + f H)`, an exact equality required at *every* H > 1. But heightLE 2 and heightLE 3 are empty (naiveHeight E = max (4|A|³) (27B²) ≤ 3 forces A = B = 0, excluded by Δ_ne_zero), so the left side is 0 while (H:ℝ)^x is a positive rpow for H ≥ 2. Even for H = 4..~10 the set {E | r ≤ E.rank} is empty for r ≥ 1 (the only curves of height ≤ 4 are y² = x³ ± x, rank 0). Hence no f can exist and the theorem is unprovable/refutable. (2) The docstring says 'curves with rank r' but the statement counts `r ≤ E.rank`; these agree only to within the o(1), so it is a benign but real prose/formal mismatch.  
**Known status:** The intended conjecture is open (PPVW heuristic 8.2(b)). The Lean statement as written is false.  
**Difficulty:** math 10/10, Lean 3/10 · **Compute:** none · **Confidence:** high  
**Evidence:** heightLE 2 = ∅ since 4|A|³ ≤ 2 ⟹ A = 0 and 27B² ≤ 2 ⟹ B = 0, contradicting 4A³+27B² ≠ 0; so ncard = 0, but (2:ℝ)^y > 0 for all real y. Refuting the current statement is a short Lean argument (specialize the ∃f to H = 2).  
**Flags:** FALSE AS STATED: small-H emptiness vs strictly positive rpow; docstring/statement mismatch: 'rank = r' vs 'r ≤ rank'; the sibling twentyone_le_rank_height_count_asymptotic avoids the bug only because it uses ≤  
**Next action:** Fix the quantifier: replace `∀ H, 1 < H → ...` by an eventually-form, e.g. `∀ᶠ H in atTop, ...`, or state it as two-sided bounds H^(c-ε) ≤ N(H) ≤ H^(c+ε) for large H. Then re-classify as open (cat 8/9).

## `twentyone_le_rank_height_count_asymptotic` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Wikipedia/EllipticCurveRank.lean:149`  
**Statement:** The number of elliptic curves over ℚ of naive height ≤ H with rank ≥ 21 is at most H^o(1).  
**Source:** [PPVW2016] Section 8.2(c)  
**Statement matches intent:** yes  
**Known status:** Open; a heuristic prediction. No unconditional bound on the number of high-rank curves of bounded height is known (not even that finitely many exist, cf. finite_twentyone_lt_finrank).  
**Difficulty:** math 10/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Same heuristic source as 8.2(b); no known technique gives subpolynomial counts for high rank.  
**Next action:** Leave open.

## `unbounded_rank_conjecture` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Wikipedia/EllipticCurveRank.lean:122`  
**Statement:** For every n there is an elliptic curve over ℚ of rank at least n (ranks are unbounded).  
**Source:** [PPVW2016] Park–Poonen–Voight–Wood, Section 3.1, https://ems.press/journals/jems/articles/16228  
**Statement matches intent:** yes  
**Known status:** Open, and now widely doubted: the PPVW heuristic predicts boundedness (rank ≤ 21 for all but finitely many curves), which directly contradicts this statement — the same file states both as 'research open'. Records: Elkies–Klagsbrun rank ≥ 29 (2024), so the statement is provable for n ≤ 29 given explicit generators.  
**Difficulty:** math 10/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Classical open problem; PPVW heuristics suggest it is false.  
**Flags:** mutually contradictory with finite_twentyone_lt_finrank in the same file (at most one can be provable) — intentional per docstring, but both carry 'research open'  
**Next action:** Leave open. A partial win: prove the n ≤ 29 instances from the explicit points on elkiesKlagsbrun29 — but that itself needs a Mordell–Weil independence argument Mathlib lacks.

## `euclid_numbers_are_square_free` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Wikipedia/Euclid.lean:42`  
**Secondary category:** 6 (Computationally solvable with certificate)  
**Statement:** Is every Euclid number p_1···p_n + 1 squarefree?  
**Source:** https://en.wikipedia.org/wiki/Euclid_number  
**Statement matches intent:** yes  
**Known status:** Open. No Euclid number below the computed range has a square factor, and no proof is known; it is a folklore-hard question (a counterexample would need a Wieferich-like coincidence).  
**Difficulty:** math 9/10, Lean 10/10 · **Compute:** medium · **Confidence:** high  
**Evidence:** Answer(sorry) demands deciding a ∀-statement over all n; a 'False' answer would need an explicit non-squarefree Euclid number, none known.  
**Next action:** Leave open. Only realistic short-term contribution: extend the computational verification for small n (does not decide the ∀).

## `infinite_prime_euclid_numbers` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Wikipedia/Euclid.lean:35`  
**Statement:** Are there infinitely many prime Euclid numbers p_1·p_2···p_n + 1?  
**Source:** https://en.wikipedia.org/wiki/Euclid_number ; OEIS A006862 / A014545  
**Statement matches intent:** yes  
**Known status:** Open. Only 22-odd primorial primes p# + 1 are known; it is not even known whether infinitely many Euclid numbers are composite.  
**Difficulty:** math 9/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Classical open problem (primorial primes); no repo PR or campaign touches it.  
**Next action:** Leave open.

## `cuboidThree` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/Wikipedia/EulerBrick.lean:140`  
**Statement:** Sharipov's third cuboid conjecture: for all positive pairwise-distinct coprime integers a,b,c with bc ≠ a² and ac ≠ b², the associated degree-12 cuboid polynomial is irreducible over ℤ.  
**Source:** [Sh12] R. Sharipov, 'Perfect cuboids and irreducible polynomials', arXiv:1108.5348  
**Statement matches intent:** suspect — The Lean coprimality hypothesis is `gcd a (gcd b c) = 1`, i.e. SETWISE coprimality, whereas the docstring says 'pairwise different coprime integers'. If Sharipov's hypothesis is pairwise coprimality, the Lean statement is strictly stronger than the published conjecture and could be false for e.g. (a,b,c) = (2,3,4). I tested exactly this regime — all 1488 triples a,b,c ≤ 15 that are setwise-but-not-pairwise coprime and satisfy the side conditions — and the polynomial was irreducible in every case, so the over-strengthening is not obviously falsifying.  
**Known status:** Open. No counterexample found (a,b,c ≤ 7 general scan and a,b,c ≤ 15 non-pairwise-coprime scan, both fully irreducible).  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** small · **Confidence:** medium  
**Evidence:** Scripts /tmp/.../scratchpad/cub2.py and cub3.py: 0 reducible instances found.  
**Flags:** possible over-strengthening: setwise gcd = 1 instead of pairwise coprimality; needs literature check against arXiv:1108.5348 for the exact hypothesis set  
**Next action:** Check Sharipov's exact hypothesis and, if it is pairwise coprimality, weaken `gcd a (gcd b c) = 1` to pairwise Coprime; then attack via the same elliptic-curve/irreducibility-criterion route as cuboidOne/cuboidTwo.

## `cuboidTwo` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/Wikipedia/EulerBrick.lean:118`  
**Statement:** Sharipov's second cuboid conjecture: for all coprime distinct positive integers a,b, the associated degree-10 cuboid polynomial in X is irreducible over ℤ.  
**Source:** [Sh12] R. Sharipov, 'Perfect cuboids and irreducible polynomials', arXiv:1108.5348  
**Statement matches intent:** yes  
**Known status:** Open. I factored the stated polynomial over ℤ for all coprime a ≠ b with a,b ≤ 14 (sympy): irreducible in every case, so no small counterexample and no obvious transcription error. Note the sibling first cuboid conjecture is marked solved in this file, with an informal proof by Asiryan (arXiv:2510.11768) via a rank-zero elliptic curve and a formal DeepMind proof link; a similar elliptic-curve route is the natural attack here.  
**Difficulty:** math 8/10, Lean 8/10 · **Compute:** small · **Confidence:** medium  
**Evidence:** No counterexample for a,b ≤ 14 (script /tmp/.../scratchpad/cub2.py); conjecture stands as stated by Sharipov; a proof of the analogous first conjecture now exists in the literature.  
**Flags:** needs literature check: whether cuboid conjectures 2/3 have been settled after Asiryan's 2025 paper  
**Next action:** Attempt the Asiryan-style reduction (specialize X, reduce irreducibility to a rank-0 elliptic curve / genus argument) for the degree-10 family; first milestone = an irreducibility criterion mod small primes covering an infinite family of (a,b). Verify the existing cuboidOne proof builds before reusing its infrastructure.

## `four_dim_euler_brick_existence` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/Wikipedia/EulerBrick.lean:58`  
**Secondary category:** 6 (Computationally solvable with certificate)  
**Statement:** Are there four positive integers such that the sum of the squares of any two of them is a perfect square (a 4-dimensional Euler brick / 'Euler tesseract')?  
**Source:** https://en.wikipedia.org/wiki/Euler_brick ; https://math.stackexchange.com/questions/2264401 ; O. Knill, 'The Babylonian Graph', arXiv:2205.13285  
**Statement matches intent:** yes  
**Known status:** Open. Knill's Babylonian-graph paper states explicitly that triangles in the graph a~b ⟺ a²+b² is a square are Euler bricks and that whether the graph contains a K₄ ('Euler tesseract') is an open question. I ran an exhaustive search: all Pythagorean-leg pairs with both legs ≤ 10^6 (677,205 vertices / 2,269,788 edges) contain 17,873 triangles (Euler bricks) but NO K₄. So any example has an edge > 10^6.  
**Difficulty:** math 9/10, Lean 2/10 · **Compute:** large · **Confidence:** medium  
**Evidence:** Own exhaustive K₄ search to 10^6 found none; Knill (arXiv:2205.13285) lists the K₄ question as open.  
**Flags:** if a witness is ever found the Lean side is trivial (explicit 4-tuple + norm_num); the difficulty is entirely computational/number-theoretic  
**Next action:** Two-track: (a) push the K₄ search to 10^8–10^9 with a leg-indexed sieve on a cluster — a hit gives a 4-line `decide`/`norm_num` Lean proof of the True branch; (b) otherwise leave open. Script: /tmp/claude-0/-home-user-formal-conjectures/bc21ed42-743c-5cee-96d2-6b29240119cb/scratchpad/k4b.py

## `n_dim_euler_brick_existence` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Wikipedia/EulerBrick.lean:66`  
**Statement:** For every n > 3, does there exist an n-dimensional Euler brick (n positive integers whose pairwise sums of squares are all perfect squares)?  
**Source:** https://en.wikipedia.org/wiki/Euler_brick ; https://math.stackexchange.com/questions/2264401  
**Statement matches intent:** yes  
**Known status:** Open; strictly implies four_dim_euler_brick_existence. No K_n (n ≥ 4) in the Babylonian graph is known and no nonexistence proof is known.  
**Difficulty:** math 10/10, Lean 10/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** Strictly stronger than the (open) 4-dimensional case; a 'False' answer needs an unconditional nonexistence theorem that nobody has.  
**Flags:** logically subsumes four_dim_euler_brick_existence — the two answer(sorry) slots are not independent  
**Next action:** Leave open; resolve the n = 4 case first.

## `perfect_euler_brick_existence` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Wikipedia/EulerBrick.lean:50`  
**Statement:** Does a perfect cuboid exist: positive integers a,b,c with a²+b², a²+c², b²+c² and a²+b²+c² all perfect squares?  
**Source:** https://en.wikipedia.org/wiki/Euler_brick ; Sharipov, arXiv:1108.5348  
**Statement matches intent:** yes  
**Known status:** Open since the 18th century. Searches rule out a perfect cuboid with smallest edge < 5·10^11 and odd edge < 2.5·10^13. Several 2026 arXiv preprints claim partial/complete nonexistence results (e.g. arXiv:2604.09328, arXiv:2604.28072); these are past my knowledge cutoff and unverified — I do not treat the problem as solved.  
**Difficulty:** math 10/10, Lean 10/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** Long-standing open problem; the file itself gives a conditional route (cuboid_perfect_euler_brick from the three cuboid conjectures).  
**Flags:** needs literature check: post-cutoff arXiv preprints 2604.09328 / 2604.28072 claim perfect-cuboid obstruction results  
**Next action:** Leave open. If any of the 2026 preprints is genuine and accepted, re-classify to cat 5.

## `eulers_sum_of_powers_conjecture` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Wikipedia/EulerSumOfPowers.lean:35`  
**Statement:** For k ≥ 6, if a sum of n ≥ 2 positive k-th powers is itself a k-th power, then n ≥ k.  
**Source:** https://en.wikipedia.org/wiki/Euler%27s_sum_of_powers_conjecture  
**Statement matches intent:** yes  
**Known status:** Open for k ≥ 6; no counterexample known for any k ≥ 6, and no proof for any k ≥ 6 except the n = 2 sub-case (Fermat's Last Theorem, Wiles — not yet in Mathlib either).  
**Difficulty:** math 10/10, Lean 10/10 · **Compute:** large · **Confidence:** high  
**Evidence:** Wikipedia and Lander–Parkin–Selfridge searches: counterexamples only for k = 4, 5; k ≥ 6 untouched.  
**Next action:** Leave open. Only realistic contributions: (i) the n = 2 sub-case once FLT lands in Mathlib; (ii) extend computer searches for k = 6, n ≤ 5 (large compute, no known hit).

## `four_exponentials_conjecture` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Wikipedia/Exponentials.lean:34`  
**Statement:** If x0,x1 are ℚ-linearly independent complex numbers and y0,y1 are ℚ-linearly independent, then at least one of the four numbers e^{x_i y_j} is transcendental.  
**Source:** https://en.wikipedia.org/wiki/Four_exponentials_conjecture  
**Statement matches intent:** yes  
**Known status:** Open since Alaoglu–Erdős / Schneider (1940s). The six exponentials theorem (2×3 case) is the best known unconditional result; the 2×2 case is a famous open problem (strong four exponentials, Schanuel-adjacent).  
**Difficulty:** math 10/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Well-known open transcendence conjecture, implied by Schanuel's conjecture.  
**Next action:** Leave open. Mathlib does not even have the six exponentials theorem; formalizing that would be the sensible prerequisite milestone.

## `two_pow_three_pow_transcendental` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Wikipedia/Exponentials.lean:44`  
**Statement:** For every irrational real t, at least one of 2^t and 3^t is transcendental.  
**Source:** https://en.wikipedia.org/wiki/Four_exponentials_conjecture (standard corollary)  
**Statement matches intent:** yes  
**Known status:** Open. Gelfond–Schneider settles algebraic irrational t; the six exponentials theorem gives only that one of 2^t, 3^t, 5^t is transcendental. The two-prime version is exactly the open four-exponentials corollary.  
**Difficulty:** math 10/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Textbook example of what four exponentials would give beyond six exponentials.  
**Next action:** Leave open; if the file's four_exponentials_conjecture is ever available, derive this from it (a genuine but nontrivial Lean derivation requiring log-independence of 2 and 3 over ℚ).

## `feit_thompson_primes` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Wikipedia/FeitThompsonPrimeConjecture.lean:30`  
**Statement:** For distinct primes p < q, (q^p − 1)/(q − 1) never divides (p^q − 1)/(p − 1).  
**Source:** https://en.wikipedia.org/wiki/Feit%E2%80%93Thompson_conjecture  
**Statement matches intent:** yes  
**Known status:** Open. Stephens (1971) disproved the stronger 'gcd = 1' version with p = 17, q = 3313, but the divisibility conjecture itself is untouched; it is known that a counterexample would give a huge Wieferich-type condition.  
**Difficulty:** math 9/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Classical open conjecture from the odd-order theorem literature; no partial results give the full statement.  
**Flags:** docstring says 'distinct primes p and q' while the statement fixes p < q — acceptable (the other order is elementary) but worth a comment  
**Next action:** Leave open. A worthwhile companion statement would be the known Stephens counterexample to the gcd version, to prevent anyone from formalizing the wrong strengthening.

## `all_fermat_squarefree` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Wikipedia/Fermat.lean:51`  
**Statement:** Is every Fermat number squarefree (equivalently, does no square of a prime divide any F_n)?  
**Source:** https://en.wikipedia.org/wiki/Fermat_number (Open questions: 'Does a Fermat number exist that is not square-free?')  
**Statement matches intent:** yes  
**Known status:** Open. If p^2 | F_n then p is a Wieferich prime; the two known Wieferich primes (1093, 3511) do not divide any Fermat number, so no non-squarefree example is known.  
**Difficulty:** math 9/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** `∀ n, Squarefree n.fermatNumber` is the negation of Wikipedia's phrasing, faithful. F_n ≥ 3 > 0 so Squarefree carries no degenerate-zero junk.  
**Next action:** Leave open; the Wieferich reduction would be a good @[category research solved] companion lemma.

## `fermat_number_are_composite` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Wikipedia/Fermat.lean:30`  
**Statement:** Is every Fermat number F_n = 2^(2^n)+1 composite for n > 4?  
**Source:** https://en.wikipedia.org/wiki/Fermat_number (Open questions)  
**Statement matches intent:** yes  
**Known status:** Open. F_5..F_32 known composite (and many further n), no Fermat prime found beyond F_4=65537; no method known to decide the general case.  
**Difficulty:** math 10/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Nat.fermatNumber n = 2^(2^n)+1; statement '∀ n > 4, ¬Prime n.fermatNumber' matches Wikipedia's first open question verbatim. Prime on ℕ is defeq-equivalent to Nat.Prime, no encoding defect. Note logical entanglement with infinite_fermat_primes in the same file (this statement implies exactly 5 Fermat primes).  
**Next action:** Leave open; the answer(sorry) slot cannot be filled honestly. Could add supporting @[category research solved] lemmas (e.g. 641 | F_5) as scaffolding.

## `infinite_fermat_composite` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Wikipedia/Fermat.lean:44`  
**Statement:** Are there infinitely many composite Fermat numbers?  
**Source:** https://en.wikipedia.org/wiki/Fermat_number (Open questions)  
**Statement matches intent:** yes  
**Known status:** Open per Wikipedia's open-questions list. Only finitely many F_n are individually known composite; no infinitude proof exists (each prime divides at most one Fermat number, which blocks easy arguments).  
**Difficulty:** math 9/10, Lean 10/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** Statement is the exact set-theoretic dual of infinite_fermat_primes; formalization faithful. Confidence medium only on the literature status (no search spent): treating Wikipedia's list as authoritative.  
**Flags:** needs literature check (is infinitude of composite Fermat numbers really unproved?)  
**Next action:** Leave open. Cheap partial credit: note that this and infinite_fermat_primes cannot both be false (ℕ = union of the two index sets), which could be added as a @[category test] lemma.

## `infinite_fermat_primes` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Wikipedia/Fermat.lean:37`  
**Statement:** Are there infinitely many Fermat primes (primes of the form 2^(2^n)+1)?  
**Source:** https://en.wikipedia.org/wiki/Fermat_number (Open questions; Eisenstein 1844)  
**Statement matches intent:** yes  
**Known status:** Open. Only 5 Fermat primes known (n=0..4); heuristics say finitely many, but nothing is proved.  
**Difficulty:** math 10/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** `Infinite {n : ℕ | Prime n.fermatNumber}` uses the Infinite class on a set-coercion; that is the intended 'infinitely many indices' reading and is fine. Directly contradicts fermat_number_are_composite, so the two answer() slots are linked.  
**Next action:** Leave open.

## `fermat_catalan` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Wikipedia/FermatCatalanConjecture.lean:55`  
**Statement:** There are only finitely many triples (a^m, b^n, c^k) with a,b,c pairwise coprime positive integers, m,n,k ≥ 1, 1/m+1/n+1/k < 1 and a^m + b^n = c^k.  
**Source:** https://en.wikipedia.org/wiki/Fermat%E2%80%93Catalan_conjecture  
**Statement matches intent:** yes  
**Known status:** Open. Only 10 solutions are known; the conjecture follows from the abc conjecture, and Darmon–Granville (stated as 'research solved' in the same file) gives finiteness for each fixed (m,n,k).  
**Difficulty:** math 10/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Known consequence of abc; unconditional proof would be a major result.  
**Next action:** Leave open. A reasonable formal milestone is Darmon–Granville or the Beal/abc implication rather than the conjecture itself.

## `fib_primes_infinite` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Wikipedia/FibonacciPrimes.lean:33`  
**Statement:** There are infinitely many prime Fibonacci numbers.  
**Source:** https://en.wikipedia.org/wiki/Fibonacci_prime  
**Statement matches intent:** yes  
**Known status:** Open; a classical unsolved problem (only ~50 Fibonacci primes/probable primes known).  
**Difficulty:** math 10/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Set {n | (∃ m, m.fib = n) ∧ n.Prime} infinite. Nat.fib conventions (fib 0 = 0, fib 1 = fib 2 = 1) cause no problem since 0 and 1 are not prime. Stated in the true direction (believed true).  
**Next action:** Leave open. Note the file already proves the equivalence with the index formulation (indices_infinite_iff_fib_primes_infinite), so only one of the two needs work.

## `fib_primes_infinite.variant` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Wikipedia/FibonacciPrimes.lean:40`  
**Statement:** There are infinitely many indices i such that the i-th Fibonacci number is prime.  
**Source:** https://en.wikipedia.org/wiki/Fibonacci_prime  
**Statement matches intent:** yes  
**Known status:** Open, same problem as fib_primes_infinite; the in-file test theorem proves the two are equivalent.  
**Difficulty:** math 10/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** {n | n.fib.Prime}.Infinite. Faithful; equivalence to the value formulation is already discharged in the file (lines 47-63), so no duplication defect.  
**Next action:** Leave open.

## `firoozbakht_conjecture` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Wikipedia/Firoozbakht.lean:41`  
**Statement:** The sequence p_n^(1/n) is strictly decreasing, where p_n is the n-th prime.  
**Source:** https://en.wikipedia.org/wiki/Firoozbakht%27s_conjecture ; https://www.primepuzzles.net/conjectures/conj_030.htm  
**Statement matches intent:** yes  
**Known status:** Open; verified for all primes below 4·10^18. It implies prime gaps p_{n+1}-p_n < (log p_n)^2 - log p_n, far beyond anything provable today; several authors regard it as possibly false on Cramér/Granville-type heuristics.  
**Difficulty:** math 10/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** firoozbakhtSeq n = (Nat.nth Prime n : ℝ) ^ (1/(n+1) : ℝ). Nat.nth is 0-indexed, so firoozbakhtSeq n = p_{n+1}^{1/(n+1)} in 1-indexed notation and the claim seq(n+1) < seq(n) is exactly p_{n+2}^{1/(n+2)} < p_{n+1}^{1/(n+1)} — indexing is consistent. The exponent is real division under a type ascription (no ℕ-division truncation) and the base is cast to ℝ (rpow), so no junk values.  
**Flags:** stated in the 'true' direction although heuristics suggest possible failure — a disproof would leave this theorem unprovable  
**Next action:** Leave open. Guard against the risk that it is false by keeping the consequence theorem conditional (already done via `type_of%`).

## `cookson_hills_series_converges` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Wikipedia/FlintCooksonHills.lean:45`  
**Statement:** Does the Cookson Hills series sum_{n≥1} 1/(n^3 cos^2 n) converge?  
**Source:** https://mathworld.wolfram.com/CooksonHillsSeries.html  
**Statement matches intent:** yes  
**Known status:** Open, for the same reason as the Flint Hills series: convergence is tied to how well π/2 is approximated by rationals (irrationality-measure bounds for π).  
**Difficulty:** math 10/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** `Summable fun n : ℕ => 1/(((n+1):ℝ)^3 * Real.cos (n+1)^2)`; cos(n+1) ≠ 0 for integers, no junk values, indexing consistent with the docstring.  
**Next action:** Leave open.

## `flint_hills_series_converges` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Wikipedia/FlintCooksonHills.lean:35`  
**Statement:** Does the Flint Hills series sum_{n≥1} 1/(n^3 sin^2 n) converge?  
**Source:** https://mathworld.wolfram.com/FlintHillsSeries.html ; Alekseyev, arXiv:1104.5100  
**Statement matches intent:** yes  
**Known status:** Open. Alekseyev proved that convergence implies the irrationality measure of π is ≤ 2.5; the best known unconditional bound is ≈7.10 (Zeilberger–Zudilin), so convergence is currently out of reach, and divergence is equally unknown.  
**Difficulty:** math 10/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** `Summable fun n : ℕ => 1/(((n+1):ℝ)^3 * Real.sin (n+1)^2)`: 0-indexing shift documented and correct, `Real.sin (n+1)^2` parses as (sin(n+1))^2, and sin(n+1) ≠ 0 for integer arguments so no division-by-zero junk value arises.  
**Next action:** Leave open; the honest answer slot is 'unknown'. A worthwhile companion would be formalizing Alekseyev's implication (convergence → μ(π) ≤ 2.5).

## `FugledeConjecture.variants.dim_1` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Wikipedia/Fuglede.lean:41`  
**Statement:** In dimension 1, is a bounded positive-measure set spectral if and only if it tiles ℝ by translation?  
**Source:** https://en.wikipedia.org/wiki/Fuglede%27s_conjecture  
**Statement matches intent:** yes  
**Known status:** Open. Disproved for n ≥ 3 (Tao 2004 and successors, recorded in the same file); still open for n = 1 and n = 2. In dim 1 it is closely tied to the Coven–Meyerowitz conjecture for finite sets; convex-body and union-of-intervals special cases are known.  
**Difficulty:** math 9/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** FugledeConjectureFor 1 quantifies over bounded measurable Ω ⊆ (Fin 1 → ℝ) with 0 < volume Ω, using isSpectral (∃ Λ with orthogonal exponentials whose span is dense in L²(Ω), FormalConjecturesForMathlib/Analysis/Fourier/SpectralSets.lean:75-86) and tilesByTranslation (countable T, a.e. cover, a.e. pairwise disjoint). Definitions are the standard ones; 'bounded' rather than 'finite measure' matches the usual statement.  
**Next action:** Leave open. Realistic intermediate targets: formalize the finite-abelian-group reductions or the union-of-intervals case (cf. FormalConjectures/Paper/WeakTiling.lean).

## `FugledeConjecture.variants.dim_2` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Wikipedia/Fuglede.lean:49`  
**Statement:** In dimension 2, is a bounded positive-measure set spectral if and only if it tiles ℝ² by translation?  
**Source:** https://en.wikipedia.org/wiki/Fuglede%27s_conjecture  
**Statement matches intent:** yes  
**Known status:** Open. Known for convex bodies in all dimensions (Lev–Matolcsi 2022) and for various discrete models; the general planar case is unresolved.  
**Difficulty:** math 9/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Same definitional apparatus as dim_1 with n = 2; faithful. Note the file's dim_3_or_higher theorem correctly records the disproof and the caveat that lower-dimensional counterexamples would propagate upward.  
**Next action:** Leave open.

## `gap_conjecture` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Wikipedia/GapConjecture.lean:37`  
**Secondary category:** 8 (Deep but approachable research problem)  
**Statement:** Grigorchuk's Gap Conjecture: a finitely generated group whose growth is superpolynomial must have growth at least exp(sqrt(n)).  
**Source:** https://en.wikipedia.org/wiki/Gromov%27s_theorem_on_groups_of_polynomial_growth#The_gap_conjecture ; Grigorchuk, arXiv:1202.6044  
**Statement matches intent:** yes  
**Known status:** Open. Grigorchuk proved it for residually solvable / residually finite-p groups and for groups with 'nice' self-similar structure; the general case is open and Gromov's polynomial-growth theorem (also only stated with sorry in this repo) is a prerequisite.  
**Difficulty:** math 9/10, Lean 10/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** HasSuperPolynomialGrowth (FormalConjecturesForMathlib/Algebra/Group/GrowthFunction.lean:149) = ∃ finite generating S, ∀ d ∃ C>0, eventually n^d ≤ γ_S(Cn); the conclusion asks for exp(√n) ≤ γ_S(Cn) eventually, i.e. e^{√n} ≼ γ in Grigorchuk's preorder. Since e^{√n} dominates every polynomial, the conclusion does not follow from the hypothesis — no vacuity/weakening loophole. Restriction to `G : Type` (universe 0) is harmless.  
**Flags:** depends on repo-local growth-function API; hypothesis gives one generating set while the conclusion quantifies over all, so a (true but unformalized) independence lemma is needed  
**Next action:** Leave open. First formal milestone would be generating-set independence of the growth preorder (γ_S ≼ γ_T for any two finite generating sets), which the statement implicitly needs since the hypothesis supplies one generating set and the conclusion quantifies over all.

## `error_isBigO` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Wikipedia/GaussCircleProblem.lean:88`  
**Statement:** Gauss circle problem: the error term E(r) = #{(m,n) ∈ ℤ² : m²+n² ≤ r²} − πr² is O(r^{1/2+o(1)}).  
**Source:** https://en.wikipedia.org/wiki/Gauss_circle_problem ; Hardy, Ramanujan lectures, p.67; https://arxiv.org/abs/2305.03549  
**Statement matches intent:** yes  
**Known status:** Open. Best known exponent is ≈0.6289 (Bourgain–Watt / Li–Yang); the conjectured exponent 1/2 is a famous unsolved problem (Hardy–Landau lower bound rules out anything below).  
**Difficulty:** math 10/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** `∃ o, Tendsto o atTop (𝓝 0) ∧ E =O[atTop] fun r => r ^ (1/2 + o r)` (rpow; 1/2 elaborates in ℝ, not ℕ-division). This ∃-o form is equivalent to the standard 'for every ε>0, E = O(r^{1/2+ε})': one direction is immediate, the other by a blockwise-slowly-decaying o. Because o must tend to 0, no cheap witness trivializes it.  
**Next action:** Leave open. Formalizable intermediate steps: the trivial O(r) bound, Gauss's 2√2πr bound (the `error_le` sorry in the same file), or exact_form_floor.

## `gilbreath_conjecture` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Wikipedia/Gilbreath.lean:41`  
**Secondary category:** 8 (Deep but approachable research problem)  
**Statement:** Iterating 'absolute value of successive differences' on the sequence of primes, the leading entry of every row after the first equals 1.  
**Source:** https://en.wikipedia.org/wiki/Gilbreath%27s_conjecture  
**Statement matches intent:** yes  
**Known status:** Open. Verified by Odlyzko for k up to ~3.4·10^11 rows; Odlyzko's heuristic shows it would follow from mild statements about the density/irregularity of primes, but no proof exists.  
**Difficulty:** math 9/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** d 0 n = Nat.nth Nat.Prime n (0-indexed primes: 2,3,5,...), d (k+1) n = Int.natAbs (d k (n+1) - d k n). Crucially the subtraction sits under Int.natAbs, so `binop%` elaborates it in ℤ and inserts casts on both operands — there is NO ℕ-truncation defect here. Statement over k : ℕ+ correctly excludes row 0 (where d 0 0 = 2 ≠ 1).  
**Next action:** Leave open. A tractable sub-target is the finite verification pattern (d^k 0 = 1 for k ≤ N) once Nat.nth Prime is made computable/decidable enough for `decide`/`native_decide`-free evaluation.

## `goldbach` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Wikipedia/GoldbachConjecture.lean:32`  
**Statement:** Is every even integer greater than 2 a sum of two primes?  
**Source:** https://en.wikipedia.org/wiki/Goldbach%27s_conjecture  
**Statement matches intent:** yes  
**Known status:** Open (verified past 4·10^18). Ternary Goldbach is solved (Helfgott) and is recorded separately in the same file as @[category research solved].  
**Difficulty:** math 10/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** `∀ n, 2 < n → Even n → ∃ p q, Prime p ∧ Prime q ∧ n = p + q`; p, q are elaborated at ℕ from `n = p + q` and `Prime` on ℕ agrees with Nat.Prime, so no defect. The bound 2 < n is right (n = 2 has no representation; n = 4 = 2+2 works).  
**Next action:** Leave open.

## `graceful_tree_conjecture` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Wikipedia/GracefulLabeling.lean:73`  
**Secondary category:** 8 (Deep but approachable research problem)  
**Statement:** Ringel–Kotzig: every finite tree with m edges has an injective vertex labeling by {0,...,m} whose induced edge differences are exactly 1,...,m.  
**Source:** https://en.wikipedia.org/wiki/Graceful_labeling (Ringel 1963, Kotzig; Rosa 1967)  
**Statement matches intent:** yes  
**Known status:** Open since 1963. Verified by computer for all trees up to ~35 vertices; proved for caterpillars, trees of diameter ≤ 5, symmetrical trees, etc.  
**Difficulty:** math 9/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** For a tree, |V| = m+1, so `Function.Injective f ∧ ∀ v, f v ≤ m` forces f to be a bijection onto {0,...,m}, and `edgeFinset.image diff = Finset.Icc 1 m` with |edgeFinset| = m = |Icc 1 m| forces the differences to be pairwise distinct — hence the Finset (set-level) image is equivalent to the intended multiset condition. Differences use Int.natAbs of casts, so no ℕ-subtraction truncation. IsTree implies V nonempty, excluding the degenerate empty graph.  
**Next action:** Leave open. A realistic formal milestone is the caterpillar case (explicit zig-zag labeling), or the finite verification for trees with ≤ 6 vertices via `decide`.

## `grimm_conjecture` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Wikipedia/Grimm.lean:34`  
**Statement:** If n, n+1, ..., n+k−1 are all composite then one can pick k distinct primes p_i with p_i | n+i.  
**Source:** https://en.wikipedia.org/wiki/Grimm%27s_conjecture (Grimm 1969)  
**Statement matches intent:** yes  
**Known status:** Open, and known to be very strong: Erdős–Selfridge showed Grimm's conjecture implies prime-gap bounds (a prime between consecutive squares-type results) far beyond current technology. Ramachandra–Shorey–Tijdeman proved it only for k ≪ (log n / log log n)^3.  
**Difficulty:** math 10/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Hypotheses `1 ≤ n`, `1 ≤ k`, `∀ i : Fin k, (n+i).Composite` (Nat.Composite := 1 < n ∧ ¬n.Prime, FormalConjecturesForMathlib/Data/Nat/Prime/Composite.lean:22). Distinctness of the primes is enforced by `Fin k ↪ ℕ` — correct and stronger than a bare ∃ family. Coercion of i : Fin k into ℕ is the intended 0-based offset.  
**Next action:** Leave open. Formalizable partial credit: the k = 1, 2 cases and small-n verification.

## `grimm_conjecture_weak` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Wikipedia/Grimm.lean:45`  
**Secondary category:** 8 (Deep but approachable research problem)  
**Statement:** If n, ..., n+k−1 are all composite then the product (n)(n+1)...(n+k−1) has at least k distinct prime divisors.  
**Source:** https://en.wikipedia.org/wiki/Grimm%27s_conjecture (weak form)  
**Statement matches intent:** yes  
**Known status:** Open (Wikipedia explicitly calls the weaker version 'still unproven'). Implied by full Grimm; partial results in the same RST range.  
**Difficulty:** math 9/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** `∃ ps : Fin k ↪ ℕ, ∀ i, (ps i).Prime ∧ ∃ j : Fin k, ps i ∣ (n+j)` — k distinct primes each dividing some term, which is exactly 'the product has ≥ k distinct prime factors'. The embedding gives distinctness; the inner ∃ j correctly relaxes the matching requirement of the strong form. Faithful, and genuinely weaker than grimm_conjecture as intended.  
**Next action:** Leave open; try the same small-k cases as the strong form.

## `HadamardConjecture` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Wikipedia/Hadamard.lean:86`  
**Statement:** For every k there exists a Hadamard matrix of order 4k (a ±1 matrix meeting Hadamard's determinant bound).  
**Source:** https://en.wikipedia.org/wiki/Hadamard_matrix#Hadamard_conjecture ; Hadamard 1893  
**Statement matches intent:** yes  
**Known status:** Open since 1893; the smallest undecided order is 668 = 4·167. Many infinite families are known (Paley, Sylvester, Williamson).  
**Difficulty:** math 9/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** IsHadamard M := entries ∈ ({1,-1} : Finset ℝ) ∧ |det M| = n ^ ((n:ℝ)/2) (rpow). This is the equality case of Hadamard's inequality, so it does characterize Hadamard matrices; k = 0 (n = 0) is degenerate but true and is discharged separately (exists_hadamard_zero). Faithful.  
**Flags:** the practical characterization MᵀM = n·1 is only half-proved in this file (sorry at line 75), so any explicit construction must fight the rpow determinant formulation  
**Next action:** Leave open. Highest-value cleanup: finish the ← direction of isHadamard_equiv_isHadamard' (sorry at line 75) so that concrete matrices can be certified via MᵀM = nI instead of an rpow determinant identity; then formalize the Sylvester family (orders 2^k) as partial credit.

## `HadamardConjecture.variants.«167»` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/Wikipedia/Hadamard.lean:129`  
**Secondary category:** 6 (Computationally solvable with certificate)  
**Statement:** There exists a Hadamard matrix of order 668 = 4·167 — the smallest order for which none is known.  
**Source:** https://en.wikipedia.org/wiki/Hadamard_matrix#Hadamard_conjecture (order 428 settled by Kharaghani–Tayfeh-Rezaie 2004, leaving 668)  
**Statement matches intent:** yes  
**Known status:** Open as of my knowledge cutoff: 668 has been the smallest open order since 2004 and extensive computer searches (Williamson-type, Turyn, Baumert–Hall arrays) have not settled it. Not verified against any post-Jan-2026 announcement.  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** large · **Confidence:** medium  
**Evidence:** A single explicit matrix would settle it mathematically, but the Lean statement demands |det M| = 668^334 as a real rpow; naive kernel evaluation of a 668×668 determinant is hopeless, and the equivalent MᵀM = nI criterion (668³ ≈ 3·10^8 ring operations) is itself out of reach without structured lemmas.  
**Flags:** needs literature check for any post-2026-01 construction of order 668; certificate-verification path in Lean is blocked by the sorry'd IsHadamard/IsHadamard' equivalence  
**Next action:** Do not attempt a search in Lean. Monitor the combinatorial-design literature for a construction; if one appears, the Lean import needs a kernel-friendly route (prove MᵀM = 668·I by block/orthogonality lemmas, not by evaluating a 668×668 determinant), which first requires closing the isHadamard_equiv_isHadamard' sorry.

## `hall_conjecture` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Wikipedia/Hall.lean:43`  
**Statement:** There is C > 0 with |y² − x³| > C·|x|^{1/2} for all integers x, y with y² ≠ x³ (Hall's original 1971 conjecture).  
**Source:** https://en.wikipedia.org/wiki/Hall%27s_conjecture ; Danilov, Math. Notes 32 (1982) 617-618  
**Statement matches intent:** yes  
**Known status:** Formally open but NOT believed true: Wikipedia states 'the original, strong, form of the conjecture with exponent 1/2 has never been disproved, although it is no longer believed to be true', and 'Hall's conjecture' now standardly means the ε-version. Danilov produced infinitely many solutions with 0 < |x³−y²| < 0.97√x; Elkies' example forces C < 0.0215 (already formalized in this file).  
**Difficulty:** math 9/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** HallIneq C e := ∀ x y : ℤ, y² ≠ x³ → |y²−x³| > C*|x|^e. Extending to x ≤ 0 is harmless (for x < 0, |y²−x³| ≥ |x|³; for x = 0, LHS ≥ 1 > 0), so the ℤ-quantification does not change the problem. Casts/rpow are correct.  
**Flags:** asserted in a direction that the literature considers likely false — a 'theorem' that may be unprovable because it is false  
**Next action:** Consider restating with an answer(sorry) encoding (as the repo does elsewhere for undecided-direction questions), since the expected resolution is a refutation. Otherwise leave open.

## `weak_hall_conjecture` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Wikipedia/Hall.lean:79`  
**Statement:** For every ε > 0 there is C(ε) > 0 with |y² − x³| > C·|x|^{1/2−ε} whenever y² ≠ x³ (the modern form of Hall's conjecture).  
**Source:** https://en.wikipedia.org/wiki/Hall%27s_conjecture  
**Statement matches intent:** yes  
**Known status:** Open; it is a known consequence of the (effective) abc conjecture, and is the version now generally called Hall's conjecture. Danilov's theorem shows the exponent cannot exceed 1/2.  
**Difficulty:** math 9/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Quantifier order is correct: ε is a theorem parameter and C is existentially bound inside HallConjectureExp, so C may depend on ε. For ε > 1/2 the exponent is negative and (0:ℝ)^negative = 0 under rpow, so the x = 0 case degenerates harmlessly rather than producing a false instance.  
**Next action:** Leave open; the realistic formal path is 'abc ⟹ weak Hall', which could be stated conditionally in the repo as partial credit.

## `first_hardy_littlewood_conjecture` — Vacuously true / accidentally weakened (cat 4)

**File:** `FormalConjectures/Wikipedia/HardyLittlewood.lean:81`  
**Secondary category:** 3 (False / refutable as stated)  
**Statement:** First Hardy–Littlewood (prime k-tuples) conjecture: the count of admissible prime constellations (p, p+m_1, ..., p+m_k) with p ≤ n is asymptotic to C_P ∫_2^n dt/(log t)^{k+1}.  
**Source:** https://en.wikipedia.org/wiki/First_Hardy%E2%80%93Littlewood_conjecture  
**Statement matches intent:** no — Two independent defects. (1) The docstring (and the actual conjecture) assert an ASYMPTOTIC EQUIVALENCE π_P(n) ~ C_P ∫_2^n dt/log^{k+1}t, but the formal statement only asserts `π_P =O[atTop] (fun n => C * ∫ ...)`. Big-O absorbs the constant C entirely, so the formal claim is merely an upper bound of the correct order of magnitude — which is a classical theorem (Selberg/Brun sieve, Halberstam–Richert), not an open conjecture. All the content of the conjecture (the lower bound, i.e. infinitude of prime tuples, and the exact constant) has been dropped. (2) `m` is not required to be injective.  
**Known status:** The intended conjecture is wide open (it contains the twin prime conjecture). The formalized O-version, restricted to injective m, is a known sieve theorem. For non-injective m the formalized version is expected to be FALSE: e.g. k = 2, m = (0,3,3) makes IsAdmissiblePrimeConstellation m p ⟺ p and p+6 are both prime, whose counting function is conjecturally ≍ n/log²n, while the asserted bound is C·n/log³n. (That refutation is not unconditional — it needs a lower bound for sexy-prime counts — but it means the statement is almost certainly false as written.)  
**Difficulty:** math 10/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Lines 60-65: `π_P =O[atTop] fun n => C * ∫ t in (2)..n, 1/t.log ^ k.succ` while the docstring at lines 76-79 states `π_P(n) ~ C_P ∫_2^n dt/log^{k+1} t`. Positive finding on the constant: numResidues counts residues of m (not 2m) but the Euler product runs over q ≥ 3 where doubling is a bijection mod q, so w(q) is right. Inadmissible tuples give a zero factor, hence C = 0 and count ≡ 0, consistently.  
**Flags:** major semantic mismatch: O(·) instead of ~ turns an open conjecture into a known sieve upper bound; missing injectivity hypothesis on the shift tuple m makes the statement conjecturally false for repeated shifts; the file's Richards incompatibility theorem depends on this weakened definition and is likely unprovable as stated  
**Next action:** Rewrite: require `Function.Injective m` (or m strictly monotone), and replace `=O[atTop]` by an asymptotic-equivalence statement (`Filter.Tendsto (π_P n / (C * ∫ ...)) atTop (𝓝 1)` or `IsEquivalent`). Also re-examine `not_first_and_secondHardyLittlewoodConjecture` in the same file, whose proof of Richards' incompatibility needs the lower-bound half that the current definition lacks.

## `second_hardy_littlewood_conjecture` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Wikipedia/HardyLittlewood.lean:99`  
**Statement:** For all x, y ≥ 2, π(x+y) ≤ π(x) + π(y).  
**Source:** https://en.wikipedia.org/wiki/Second_Hardy%E2%80%93Littlewood_conjecture ; Richards, Bull. AMS 80 (1974) 419-438  
**Statement matches intent:** yes  
**Known status:** Formally open, but widely believed FALSE: Hensley–Richards (1973/74) showed it is incompatible with the prime k-tuples conjecture, and the k-tuples conjecture is far more strongly believed. No explicit counterexample is known (candidate admissible tuples would need ~10^174 digits).  
**Difficulty:** math 10/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** `π` is Mathlib's Nat.primeCounting (primes ≤ n), matching the docstring. Hypotheses 2 ≤ x, 2 ≤ y are necessary (x = y = 1 gives π(2) = 1 > 0 = π(1)+π(1)) and present. Small cases check out (x=y=2: 2 ≤ 2).  
**Flags:** stated as a theorem although the mathematical community expects it to be false; if a counterexample is ever exhibited, this declaration becomes unprovable  
**Next action:** Prefer an answer(sorry) encoding, as the expected resolution is a disproof. As a proof strategy, only the conditional route (assume k-tuples ⟹ ∃ counterexample) is realistic; that is what the file's not_first_and_secondHardyLittlewoodConjecture is meant to record.

## `idoneal_numbers_completeness` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Wikipedia/IdonealCompleteness.lean:99`  
**Secondary category:** 8 (Deep but approachable research problem)  
**Statement:** Euler's list of 65 idoneal numbers (OEIS A000926, largest 1848) is complete: every positive integer that cannot be written as ab+bc+ca with 0<a<b<c lies in that list.  
**Source:** https://en.wikipedia.org/wiki/Idoneal_number ; OEIS A000926 ; Weinberger, 'Exponents of the class groups of complex quadratic fields', Acta Arith. 22 (1973)  
**Statement matches intent:** yes  
**Known status:** Unconditionally open. Weinberger (1973) proved at most one further idoneal number can exist, that it would exceed 10^8, and that the list is complete under GRH (and complete for D not a Siegel-zero discriminant). No PR in this fork touches it (grep of pr_register.json for 'idoneal' returned nothing); no campaign in campaign_register.json. No duplicate elsewhere in FormalConjectures/.  
**Difficulty:** math 9/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Definition IsIdoneal n := 0 < n /\ not-exists 0<a<b<c with n = a*b+b*c+a*c is exactly the Wikipedia criterion; the 65-element Finset matches A000926 term-for-term (spot-checked 11,14,17,19,20,23,26,27,29,32 correctly excluded and 33 correctly included by hand). answer(sorry) elaborates to True by default (google.answer := alwaysTrue in FormalConjectures/Util/Answer.lean), so the statement asserts the conjecture rather than trivialising it. Resolving it unconditionally is a Siegel-zero/effective-class-number problem.  
**Flags:** supporting test theorem knownIdonealNumbers_are_idoneal relies on native_decide (compiler in trusted base); equivalence between Euler's x^2+Dy^2 definition and the ab+bc+ca criterion is asserted only in a docstring  
**Next action:** Leave open. Realistic intermediate targets: formalise 'IsIdoneal n -> n <= 1848 or n is one further exceptional value' is out of reach; a tractable API step is proving the decidable-search bridge already present (exists_triple_iff_bounded) is used without native_decide, i.e. replace the native_decide in knownIdonealNumbers_are_idoneal by decide/Finset.decide to remove the compiler from the trusted base.

## `inscribed_rectangle_problem` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Wikipedia/InscribedSquare.lean:63`  
**Secondary category:** 8 (Deep but approachable research problem)  
**Statement:** Does every Jordan curve in the plane inscribe a rectangle of every prescribed aspect ratio r > 0?  
**Source:** https://en.wikipedia.org/wiki/Inscribed_square_problem ; Greene-Lobb, 'The rectangular peg problem', arXiv:2005.09193 (smooth case)  
**Statement matches intent:** yes  
**Known status:** Open for merely continuous Jordan curves; solved by Greene-Lobb (Annals 2021) for smooth curves (stated in the same file as exists_inscribed_rectangle_of_smooth, also sorry). Strictly implies the square peg problem (r = 1), so at least as hard. No PR/campaign coverage in this fork.  
**Difficulty:** math 9/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Same IsRectangle predicate as above, nondegeneracy verified; ratio r ranges over all positive reals with hr : r > 0 so the r = 1 instance recovers inscribed_square_problem. No quantifier-order loophole: gamma and r are both universally quantified before the existential witnesses t1..t4.  
**Next action:** Leave open. Milestone with real value: formalise the elementary solved companion exists_inscribed_rectangle (every Jordan curve inscribes SOME rectangle) via the Vaughan/Mobius-band argument -- still large in Lean.

## `inscribed_square_problem` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Wikipedia/InscribedSquare.lean:53`  
**Secondary category:** 8 (Deep but approachable research problem)  
**Statement:** Toeplitz's square peg problem: does every Jordan curve in the plane contain four points forming a square?  
**Source:** https://en.wikipedia.org/wiki/Inscribed_square_problem ; Matschke, 'A survey on the square peg problem', Notices AMS 61 (2014) ; Greene-Lobb, arXiv:2005.09193  
**Statement matches intent:** yes  
**Known status:** Open for general continuous Jordan curves. Known for C^2 curves (Schnirelmann/Guggenheimer) and, by Greene-Lobb (2020), every smooth Jordan curve inscribes rectangles of every aspect ratio. No PR or campaign in this fork mentions it; no duplicate in FormalConjectures/.  
**Difficulty:** math 9/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** IsRectangle a b c d ratio = (a+c = b+d, dist a c = dist b d, a != b, b != c, dist a b / dist b c = ratio). I checked degeneracy: a+c=b+d and |a-c|=|b-d| force all four points onto a circle about the common midpoint with a,c and b,d antipodal; a=c would force a=b (excluded) and a=d would force b=c (excluded), so the four points are genuinely a nondegenerate rectangle and, at ratio 1, a square. dist b c != 0 by b_ne_c so the division carries no junk value. gamma : Circle -> R^2 with IsEmbedding is exactly a Jordan curve (Circle is compact, R^2 Hausdorff). answer(sorry) defaults to True, so the statement asserts the conjecture.  
**Next action:** Leave open. Any Lean progress would first need the solved companions in the same file (exists_inscribed_rectangle, exists_inscribed_square_of_C2), which are themselves sorry and require Jordan-curve/degree theory not present in Mathlib.

## `Invariant_subspace_problem` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Wikipedia/InvariantSubspaceProblem.lean:44`  
**Statement:** Does every bounded linear operator on a separable complex Hilbert space of dimension at least 2 have a nontrivial closed invariant subspace?  
**Source:** https://en.wikipedia.org/wiki/Invariant_subspace_problem ; Chalendar-Partington survey arXiv:2507.21834  
**Statement matches intent:** yes  
**Known status:** The central open problem of operator theory. Enflo (1987) and Read (1985) gave Banach-space counterexamples (recorded in the same file as Invariant_subspace_problem_l1), but the Hilbert-space case is open. Enflo's 2023 arXiv claim of a positive solution has not been accepted. No PR/campaign in this fork.  
**Difficulty:** math 10/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** ClosedInvariantSubspace T bundles toSubspace != bot, != top, IsClosed, and map T <= itself -- exactly a nontrivial closed invariant subspace. Hypotheses [InnerProductSpace C H] [SeparableSpace H] [CompleteSpace H] and 2 <= Module.rank C H give a separable complex Hilbert space; complex scalars matter (the real 2-dim rotation counterexample is excluded). Including finite dimensions is harmless since those cases are true. No vacuity: separable complete inner-product spaces of rank >= 2 exist.  
**Next action:** Leave open. The only nearby formalisable items in the file are the finite-dimensional case (needs Jordan normal form / at least existence of an eigenvector, feasible in Mathlib via Module.End.exists_hasEigenvalue over an algebraically closed field) and the normal-operator case (needs the spectral theorem).

## `inverse_galois_problem` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Wikipedia/InverseGalois.lean:47`  
**Statement:** Is every finite group the Galois group of some Galois extension of the rationals?  
**Source:** https://en.wikipedia.org/wiki/Inverse_Galois_problem  
**Statement matches intent:** yes  
**Known status:** Open since Hilbert. Known for solvable groups (Shafarevich), symmetric/alternating groups, most sporadic groups (except possibly M23). No PR or campaign in this fork; no duplicate elsewhere in FormalConjectures/.  
**Difficulty:** math 10/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** GaloisRealization K G bundles a field L, a K-algebra structure, IsGalois K L, and a MulEquiv G ~= (L ~=a[K] L). Checked the potential loophole that Mathlib's IsGalois does not require FiniteDimensional: if Aut(L/Q) is finite and L/Q is normal+separable then Q is the fixed field, so Artin's lemma forces [L:Q] = |G| finite -- no weakening. The field L : Type* introduces an auto-bound universe, so the theorem is quantified over all universes for L; this is a (mild) strengthening handled by ULift, not a loophole.  
**Flags:** GaloisRealization.L carries an auto-bound universe parameter; a proof must produce a realization in an arbitrary universe (ULift boilerplate)  
**Next action:** Leave open. The realistic Lean milestone is inverse_galois_problem.variants.cyclic (Kronecker-Weber / cyclotomic subfields), for which Mathlib has IsCyclotomicExtension and the Galois group of Q(zeta_n).

## `algebraicIndependent_e_pi` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Wikipedia/Irrational.lean:35`  
**Statement:** Are e and pi algebraically independent over the rationals?  
**Source:** https://en.wikipedia.org/wiki/Irrational_number#Open_questions ; special case of Schanuel's conjecture  
**Statement matches intent:** yes  
**Known status:** Open. Follows from Schanuel's conjecture (formalised as open in FormalConjectures/Wikipedia/SchanuelsConjecture.lean); not known unconditionally. Even the weaker statement that e+pi is irrational is open. No PR/campaign coverage.  
**Difficulty:** math 10/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** AlgebraicIndependent Q ![exp 1, pi] with ![.] : Fin 2 -> R is the correct Mathlib encoding of algebraic independence over Q inside R. answer(sorry) elaborates to True by default, so the statement asserts the (expected) affirmative answer.  
**Next action:** Leave open; no unconditional approach known. Could optionally be linked to the repo's Schanuel statement as a derived consequence (that derivation is itself nontrivial: it needs Lindemann-Weierstrass plus the Schanuel instance for {1, i*pi}).

## `irrational_catalanConstant` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Wikipedia/Irrational.lean:99`  
**Statement:** Is Catalan's constant G = sum (-1)^n/(2n+1)^2 irrational?  
**Source:** https://en.wikipedia.org/wiki/Catalan%27s_constant ; Zudilin, 'Arithmetic of Catalan's constant and its relatives', arXiv:1804.09922  
**Statement matches intent:** yes  
**Known status:** Open as of 2026 (web-checked this batch). Known partial results: infinitely many beta(2n) are irrational, and at least one of beta(2),...,beta(12) is irrational (Rivoal-Zudilin); Calegari-Garoufalidis-Zagier settled the analogous L(2,chi_-3) but not G itself. The repo already records the weaker solved disjunction Transcendental.transcendental_catalanConstant_or_gompertzConstant. No PR/campaign coverage.  
**Difficulty:** math 9/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Irrational catalanConstant, the constant coming from FormalConjecturesForMathlib/Data/Real/Constants.lean; faithful. Web search (2026) confirms the irrationality of G is still unproved.  
**Next action:** Leave open; do not attempt. Note the several arXiv/ResearchGate 'proofs that Catalan's constant is irrational' surfacing in search results are unrefereed and not accepted -- do not cite them.

## `irrational_e_plus_pi` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Wikipedia/Irrational.lean:43`  
**Statement:** Is e + pi irrational?  
**Source:** https://en.wikipedia.org/wiki/Irrational_number#Open_questions  
**Statement matches intent:** yes  
**Known status:** Open. Only the disjunction is known: at least one of e+pi, e*pi is transcendental (recorded in this repo as Transcendental.exp_add_pi_or_exp_add_mul_transcendental, category textbook), because both cannot be algebraic (else e and pi would be roots of x^2-(e+pi)x+e*pi). No PR/campaign coverage.  
**Difficulty:** math 10/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Irrational is Mathlib's x not-in range of the rational cast; the statement is exactly 'e + pi is irrational'. answer(sorry) defaults to True. Near-duplicate but strictly stronger transcendence statement exists at FormalConjectures/Wikipedia/Transcendental.lean:exp_add_pi_transcendental (also open) -- not a defect.  
**Next action:** Leave open. A legitimate repo improvement would be proving the textbook disjunction in Transcendental.lean, which is genuinely provable from Lindemann-Weierstrass once Mathlib's transcendence of e and pi is combined with a quadratic-field argument.

## `irrational_e_times_pi` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Wikipedia/Irrational.lean:51`  
**Statement:** Is e*pi irrational?  
**Source:** https://en.wikipedia.org/wiki/Irrational_number#Open_questions  
**Statement matches intent:** yes  
**Known status:** Open, same status as e+pi: only the disjunction 'at least one of e+pi, e*pi is transcendental' is known. No PR/campaign coverage.  
**Difficulty:** math 10/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Statement is Irrational (exp 1 * pi); faithful. Companion transcendence version at Transcendental.lean:exp_mul_pi_transcendental, also open.  
**Next action:** Leave open.

## `irrational_e_to_e` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Wikipedia/Irrational.lean:59`  
**Statement:** Is e^e irrational?  
**Source:** https://en.wikipedia.org/wiki/Irrational_number#Open_questions  
**Statement matches intent:** yes  
**Known status:** Open. Transcendence would follow from Schanuel's conjecture. No PR/campaign coverage. Referenced (as an example open problem) from FormalConjectures/Subsets/FC100OpenSet1.lean line 154, which is a curated index, not a proof.  
**Difficulty:** math 9/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** e^e elaborates via Real.rpow (both base and exponent are real); base exp 1 > 0 so no junk-value/branch-cut issue. answer(sorry) defaults to True.  
**Next action:** Leave open.

## `irrational_eulerMascheroniConstant` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Wikipedia/Irrational.lean:91`  
**Statement:** Is the Euler-Mascheroni constant gamma irrational?  
**Source:** https://en.wikipedia.org/wiki/Euler%27s_constant ; https://en.wikipedia.org/wiki/Irrational_number#Open_questions  
**Statement matches intent:** yes  
**Known status:** Famous open problem. Best known results are conditional/partial (e.g. gamma is not a rational with denominator below ~10^244663 (Brent-McMillan style continued-fraction computations); Sondow-type criteria). No PR/campaign coverage; the constant itself is defined in FormalConjecturesForMathlib/Data/Real/Constants.lean.  
**Difficulty:** math 10/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Irrational Real.eulerMascheroniConstant with the constant taken from Mathlib/the repo's Constants file; faithful, no encoding freedom.  
**Next action:** Leave open. A finite computation cannot settle it (only excludes small denominators).

## `irrational_ln_pi` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Wikipedia/Irrational.lean:83`  
**Statement:** Is log(pi) irrational?  
**Source:** https://en.wikipedia.org/wiki/Irrational_number#Open_questions  
**Statement matches intent:** yes  
**Known status:** Open. (Transcendence of log pi would follow from Schanuel; note irrationality of log pi is not known even though pi is transcendental.) Companion transcendence statement at Transcendental.lean:rlog_pi_transcendental, also open. No PR/campaign coverage.  
**Difficulty:** math 9/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Real.log pi with pi > 0, so Mathlib's log is on its genuine branch (no junk value from log of a nonpositive argument). Faithful.  
**Next action:** Leave open.

## `irrational_pi_to_e` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Wikipedia/Irrational.lean:67`  
**Statement:** Is pi^e irrational?  
**Source:** https://en.wikipedia.org/wiki/Irrational_number#Open_questions  
**Statement matches intent:** yes  
**Known status:** Open (in contrast to e^pi = Gelfond's constant, which is transcendental by Gelfond-Schneider). No PR/campaign coverage.  
**Difficulty:** math 9/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** pi^e via Real.rpow with pi > 0; faithful. Note the asymmetry with e^pi is real mathematics, not a formalisation slip.  
**Next action:** Leave open.

## `irrational_pi_to_pi` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Wikipedia/Irrational.lean:75`  
**Statement:** Is pi^pi irrational?  
**Source:** https://en.wikipedia.org/wiki/Irrational_number#Open_questions  
**Statement matches intent:** yes  
**Known status:** Open. Even whether pi^pi^pi^pi is an integer is open (stated separately in Transcendental.lean). No PR/campaign coverage.  
**Difficulty:** math 9/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** pi^pi via Real.rpow, pi > 0; faithful.  
**Next action:** Leave open.

## `jacobian_conjecture` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Wikipedia/JacobianConjecture.lean:71`  
**Statement:** Jacobian conjecture: a polynomial map k^n -> k^n over a characteristic-zero field whose Jacobian determinant is a nonzero constant has a polynomial inverse.  
**Source:** https://en.wikipedia.org/wiki/Jacobian_conjecture ; van den Essen, 'Polynomial Automorphisms and the Jacobian Conjecture'  
**Statement matches intent:** yes  
**Known status:** Open since Keller (1939); many published proofs have been withdrawn. Known for n = 1, and reducible to degree-3 (Bass-Connell-Wright / Yagzhev). No PR or campaign in this fork.  
**Difficulty:** math 10/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** RegularFunction k sigma tau := tau -> MvPolynomial sigma k; Jacobian i j = pderiv i (F j), the transpose of the usual Jacobian (determinant unchanged). comp F G := bind1 F o G, i.e. 'F then G' -- confirmed by the file's own comp_aeval lemma. The conclusion demands both G.comp F = id and F.comp G = id, i.e. a genuine two-sided polynomial inverse, so there is no one-sided weakening. IsUnit (det J) over a field is exactly 'det J is a nonzero constant'. CharZero is required and present (the conjecture is false in positive characteristic, e.g. x - x^p).  
**Flags:** in-file sanity_check_condition_1 that pins down the 'invertible Jacobian' encoding is itself sorry, so the encoding is unverified inside the repo (it is nonetheless mathematically correct); sigma is only [Fintype sigma], so the empty index type is admitted; that instance is vacuously true and harmless  
**Next action:** Leave open. A worthwhile, genuinely reachable repo task is closing sanity_check_condition_1 (IsUnit (det J) iff det J = C c with c != 0), which is true over a field because units of MvPolynomial over a domain are the units of the coefficient ring -- Mathlib has MvPolynomial.isUnit_iff_eq_C-type lemmas via isUnit_C / Polynomial.isUnit_iff for domains.

## `juggler_conjecture` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Wikipedia/JugglerConjecture.lean:41`  
**Secondary category:** 8 (Deep but approachable research problem)  
**Statement:** Juggler conjecture: iterating n -> floor(sqrt n) for even n and n -> floor(n^(3/2)) for odd n always reaches 1 from any positive start.  
**Source:** https://en.wikipedia.org/wiki/Juggler_sequence ; Clifford Pickover, 'Computers and the Imagination' (1992)  
**Statement matches intent:** yes  
**Known status:** Open, in the same 'no known technique' family as Collatz. Verified computationally to very large starting values (Harry J. Smith's searches); a heuristic argument shows the sequence decreases in expectation, but no proof exists. No PR/campaign coverage; no duplicate in FormalConjectures/.  
**Difficulty:** math 9/10, Lean 9/10 · **Compute:** none · **Confidence:** high  
**Evidence:** jugglerStep n = floor_nat (n^(1/2)) if Even n else floor_nat (n^(3/2)), evaluated in real rpow (exact, no floating point). Matches the standard definition. The hypothesis n > 0 correctly excludes the fixed point jugglerStep 0 = 0; from any n >= 1 the orbit stays >= 1 (even n >= 2 gives floor(sqrt n) >= 1), so there is no truncation loophole. m = 0 legitimately witnesses n = 1.  
**Next action:** Leave open. Only cheap improvements are available: mark jugglerStep as computable-friendly (Nat.sqrt for the even branch) and add more test theorems; a bounded 'all n <= N reach 1' variant would be a computable certificate but not a resolution.

## `kakeya_set_conjecture` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Wikipedia/Kakeya.lean:58`  
**Secondary category:** 8 (Deep but approachable research problem)  
**Statement:** Kakeya set conjecture: every subset of R^n containing a unit segment in every direction has Hausdorff dimension n.  
**Source:** https://en.wikipedia.org/wiki/Kakeya_set ; Davies (1971) for n=2 ; Wang-Zahl, arXiv:2502.17655 for n=3  
**Statement matches intent:** yes  
**Known status:** Open for n >= 4. Solved for n = 1 (trivial), n = 2 (Davies 1971) and n = 3 (Wang-Zahl 2025, recorded in the same file as kakeya_3d, still sorry). The statement quantifies over all n > 0, so it is not resolved by the known cases. No PR/campaign coverage in this fork; no duplicate elsewhere.  
**Difficulty:** math 10/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** IsKakeya S := for every unit vector v there is a with affineSegment R a (a+v) subset S; KakeyaSetConjectureDim n := for all S, IsKakeya S -> dimH S = n. Since S subset R^n always has dimH <= n, the equality is equivalent to the usual '>= n' formulation, so no strengthening slip. Compactness is deliberately omitted with a cited equivalence (arXiv:2203.15731). n is coerced N -> ENNReal in dimH S = n; correct.  
**Flags:** equivalence of the compact and non-compact formulations is cited in a docstring but not formalised  
**Next action:** Leave open. The tractable milestone in this file is the n = 1 instance of KakeyaSetConjectureDim (a Kakeya set in R^1 contains a unit segment, so dimH = 1 via Mathlib's dimH of a set containing an interval); n = 2 (Davies) is a serious but not hopeless formalisation project.

## `idempotent_conjecture` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Wikipedia/Kaplansky.lean:45`  
**Statement:** Kaplansky's idempotent conjecture: for a field K and a torsion-free group G, the only idempotents of K[G] are 0 and 1.  
**Source:** https://en.wikipedia.org/wiki/Kaplansky%27s_conjectures  
**Statement matches intent:** yes  
**Known status:** Open in general; implied by the zero-divisor conjecture stated immediately above it in the same file, and known for groups satisfying the Baum-Connes conjecture with coefficients (Higson-Kasparov) when K = C. No PR/campaign in this fork.  
**Difficulty:** math 10/10, Lean 8/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Statement: for a : MonoidAlgebra K G with IsIdempotentElem a, a = 0 or a = 1. Faithful ('no nontrivial idempotents'). Torsion-freeness hypothesis present via include hG; not vacuous.  
**Flags:** strictly weaker than the neighbouring zero_divisor_conjecture; the one-line derivation between the two file-mates is currently missing  
**Next action:** Leave open, but add the free reduction inside the repo: from zero_divisor_conjecture K G hG, an idempotent a satisfies a*(a-1) = 0, hence a = 0 or a = 1 -- a three-line proof that makes the logical dependency explicit (it does not remove any sorry, since zero_divisor_conjecture is itself open).

## `zero_divisor_conjecture` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Wikipedia/Kaplansky.lean:36`  
**Statement:** Kaplansky's zero-divisor conjecture: for a field K and a torsion-free group G, the group algebra K[G] has no nonzero zero divisors.  
**Source:** https://en.wikipedia.org/wiki/Kaplansky%27s_conjectures  
**Statement matches intent:** yes  
**Known status:** Open. Known for large classes (orderable groups, groups satisfying the Atiyah/Baum-Connes-type conditions, unique-product groups). Unaffected by Gardam's 2021 refutation of the *unit* conjecture (that counterexample, recorded later in this file, does not produce zero divisors). No PR/campaign in this fork.  
**Difficulty:** math 10/10, Lean 9/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Statement is NoZeroDivisors (MonoidAlgebra K G) under [Field K] [Group G] and the included hypothesis hG : IsMulTorsionFree G. For a group, IsMulTorsionFree is exactly torsion-freeness. Hypothesis is genuinely used as a premise (include hG), so the statement is not accidentally the false unrestricted claim, and it is not vacuous (Z is torsion-free).  
**Next action:** Leave open. A realistic Lean sub-target: prove it for left-orderable G (Malcev-Neumann / leading-term argument), which is a self-contained argument but needs group-ordering API.

## `KotheConjecture` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Wikipedia/Koethe.lean:49`  
**Statement:** Koethe's conjecture: in any ring, the sum of two nil left ideals is nil.  
**Source:** https://en.wikipedia.org/wiki/K%C3%B6the_conjecture ; Koethe (1930)  
**Statement matches intent:** yes  
**Known status:** Open since 1930. Known for rings satisfying a polynomial identity, for Noetherian rings, and for algebras over uncountable fields (Amitsur-type results). Smoktunowicz's counterexample to the Amitsur conjecture (recorded at the end of the same file) does not settle Koethe. No PR/campaign in this fork; no duplicate elsewhere in FormalConjectures/.  
**Difficulty:** math 9/10, Lean 9/10 · **Compute:** none · **Confidence:** high  
**Evidence:** IsNil I := every element of I is nilpotent. In Mathlib Ideal R = Submodule R R, which for a noncommutative Ring is a LEFT ideal -- exactly the right notion for the conjecture (the two-sided version is a theorem, not a conjecture). I + J is the sup of submodules, i.e. the set of sums. Faithful.  
**Next action:** Leave open. Useful adjacent API the file itself flags as TODO: basic lemmas about nil ideals (nil ideals are contained in the Jacobson radical; a nil two-sided ideal plus a nil two-sided ideal is nil).

## `KotherConjecture.variants.general_matrix` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Wikipedia/Koethe.lean:61`  
**Statement:** Equivalent form of Koethe's conjecture: for every nil two-sided ideal I of a ring R and every finite index type n, the matrix ideal M_n(I) is nil in M_n(R).  
**Source:** https://en.wikipedia.org/wiki/K%C3%B6the_conjecture (list of equivalent formulations)  
**Statement matches intent:** yes  
**Known status:** Open; equivalent to KotheConjecture. No PR/campaign in this fork.  
**Difficulty:** math 9/10, Lean 9/10 · **Compute:** none · **Confidence:** high  
**Evidence:** TwoSidedIdeal.matrix n I is the ideal of matrices with entries in I; IsNil of it says every such matrix is nilpotent. Matches the standard equivalent formulation. The empty index type is admitted (M_0(R) is the trivial ring, vacuously true) but the statement quantifies over all finite n, so the nontrivial content is retained.  
**Flags:** no [DecidableEq n] hypothesis; the file relies on the scoped Classical.propDecidable instance from `open Classical` for the Matrix ring structure -- fragile but not a semantic defect  
**Next action:** Leave open.

## `KotherConjecture.variants.le_KotherRadical` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Wikipedia/Koethe.lean:54`  
**Statement:** Equivalent form of Koethe's conjecture: every nil left ideal of a ring is contained in the upper nilradical (the sum of all nil two-sided ideals).  
**Source:** https://en.wikipedia.org/wiki/K%C3%B6the_conjecture (list of equivalent formulations)  
**Statement matches intent:** yes  
**Known status:** Open; equivalent to KotheConjecture in the same file. No PR/campaign in this fork.  
**Difficulty:** math 9/10, Lean 9/10 · **Compute:** none · **Confidence:** high  
**Evidence:** KotheRadical R := sSup {I : TwoSidedIdeal R | IsNil I}, the standard upper nilradical Nil*(R); the conclusion (I : Set R) subset KotheRadical R with I a nil left ideal is exactly the Wikipedia equivalent formulation. No degenerate reading: I is universally quantified and the containment is on underlying sets.  
**Next action:** Leave open. If any one of the five Koethe variants in this file is ever proved, formalising the classical equivalences between them would be a valuable follow-up (currently none of the equivalences is stated in the repo).

## `KotherConjecture.variants.matrixOver_KotherRadical` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Wikipedia/Koethe.lean:74`  
**Statement:** Equivalent form of Koethe's conjecture: for every ring R and every finite n, Nil*(M_n(R)) = M_n(Nil*(R)).  
**Source:** https://en.wikipedia.org/wiki/K%C3%B6the_conjecture (list of equivalent formulations)  
**Statement matches intent:** suspect — The binder {I : TwoSidedIdeal R} (hI : IsNil I) is entirely unused: I does not occur in the conclusion matrix n (Nil* R) = Nil* (Matrix n n R). Because bot is always a nil ideal, the hypothesis is satisfiable for every R and the statement is therefore logically EQUIVALENT to the intended hypothesis-free claim -- so it is neither weakened nor strengthened, but it is a spec defect that should be deleted. Separately, the docstring says 'the matrix ideal M_2(Nil*(R))' while the statement is for general finite n; the docstring is wrong, the statement is right.  
**Known status:** Open; equivalent to KotheConjecture. No PR/campaign in this fork.  
**Difficulty:** math 9/10, Lean 9/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** Statement: matrix n (Nil* R) = Nil* (Matrix n n R) with (n : Type*) [Fintype n], under an unused nil-ideal hypothesis. I checked the unused hypothesis cannot vacuously trivialise anything: IsNil (bot : TwoSidedIdeal R) holds for every R (0 is nilpotent), so the premise is always inhabited and the theorem is equivalent to the unhypothesised version. Confidence is medium only on the exact Mathlib spelling of TwoSidedIdeal.matrix, which I could not check (no Mathlib source in this container, and lake cannot be run).  
**Flags:** dead hypothesis {I : TwoSidedIdeal R} (hI : IsNil I) unused in the conclusion; docstring/statement mismatch: docstring says M_2, statement is M_n; needs build check: TwoSidedIdeal.matrix spelling unverified (no Mathlib source available offline)  
**Next action:** Cosmetic fix worth making now: drop the unused {I} (hI) binders and correct the docstring from M_2 to M_n. Mathematically leave open.

## `KotherConjecture.variants.two_by_two_matrix` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Wikipedia/Koethe.lean:68`  
**Statement:** Equivalent form of Koethe's conjecture: for every nil two-sided ideal I of a ring R, the 2x2 matrix ideal M_2(I) is nil in M_2(R).  
**Source:** https://en.wikipedia.org/wiki/K%C3%B6the_conjecture (list of equivalent formulations)  
**Statement matches intent:** yes  
**Known status:** Open; the n = 2 case is already equivalent to the full Koethe conjecture (a classical reduction). No PR/campaign in this fork.  
**Difficulty:** math 9/10, Lean 9/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Identical shape to general_matrix with n := Fin 2. Faithful to the Wikipedia formulation.  
**Flags:** logically a special case of KotherConjecture.variants.general_matrix in the same file (the classical equivalence of the two is not formalised)  
**Next action:** Leave open. Note this is a literal instance of general_matrix at n = Fin 2, so it should be derivable from it in one line once general_matrix exists.

## `komlos_conjecture` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/Wikipedia/KomlosConjecture.lean:51`  
**Secondary category:** 9 (Major open problem / currently infeasible)  
**Statement:** There is a universal constant K such that any finite list of vectors in R^m with Euclidean norm at most 1 can be signed +/-1 so that the resulting signed sum has sup-norm at most K.  
**Source:** Komlos conjecture, https://en.wikipedia.org/wiki/Discrepancy_theory#Major_open_problems ; Banaszczyk, Random Structures & Algorithms 12 (1998) 351-360  
**Statement matches intent:** yes  
**Known status:** Open. Best known bound is Banaszczyk's O(sqrt(log n)) (1998), stated in the same file as komlos_conjecture.variants.banaszczyk. Beck-Fiala theorem is a scaled special case (see FormalConjectures/Wikipedia/BeckFialaConjecture.lean). No PR in pr_register.json or campaign in campaign_register.json touches this.  
**Difficulty:** math 9/10, Lean 9/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Statement matches the standard formulation exactly; K universal (independent of n and m). Partial progress exists (Banaszczyk O(sqrt log n)), so avenues are identifiable, but the conjecture itself has resisted since the 1980s.  
**Next action:** Leave open. A realistic intermediate target is formalising Beck-Fiala (discrepancy <= 2t-1) or the Spencer 'six standard deviations' bound; the Komlos statement itself needs Banaszczyk-style convex-geometry machinery (Gaussian measure of convex bodies) absent from Mathlib.

## `kummer_vandiver` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Wikipedia/KummerVandiver.lean:35`  
**Statement:** For every prime p, p does not divide the class number of the maximal real subfield Q(zeta_p)^+ of the p-th cyclotomic field.  
**Source:** Kummer-Vandiver conjecture, https://en.wikipedia.org/wiki/Kummer%E2%80%93Vandiver_conjecture  
**Statement matches intent:** yes  
**Known status:** Open. Verified computationally for all p < 2^31 (Buhler-Harvey, and earlier Buhler-Crandall-Ernvall-Metsankyla). Widely regarded as very hard; Washington has argued heuristics suggest it may be false for some enormous p. No internal PR/campaign hit for 'kummer'/'vandiver' in pr_register.json or campaign_register.json.  
**Difficulty:** math 9/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Textbook statement of Kummer-Vandiver, faithfully rendered. Resolution would be a major result in algebraic number theory.  
**Next action:** Leave open. Mathlib currently lacks Iwasawa theory / Herbrand-Ribet-level machinery; even formalising the computational verification for a single small p would require class-number computation infrastructure that does not exist.

## `lander_parkin_selfridge` — False / refutable as stated (cat 3)

**File:** `FormalConjectures/Wikipedia/LanderParkinAndSelfridgeConjecture.lean:36`  
**Secondary category:** 9 (Major open problem / currently infeasible)  
**Statement:** If a sum of n positive k-th powers equals a sum of m positive k-th powers with every left value different from every right value, then n + m >= k.  
**Source:** Lander, Parkin and Selfridge conjecture, https://en.wikipedia.org/wiki/Lander,_Parkin,_and_Selfridge_conjecture  
**Statement matches intent:** no — The docstring says 'for positive integers k, n, m', but the Lean statement quantifies over ALL k n m : N with no positivity on n or m. Taking n = m = 0 makes every hypothesis vacuous and both sums equal to 0, forcing the conclusion k <= 0 for every k. The formal statement is therefore false.  
**Known status:** The FORMAL statement is refutable. Explicit counterexample: k := 5, n := 0, m := 0, x := Fin.elim0, y := Fin.elim0. Hypotheses (forall i, 0 < x i), (forall j, 0 < y j), (forall i j, x i <> y j) hold vacuously over Fin 0; sum over Fin 0 of x i ^ 5 = 0 = sum over Fin 0 of y j ^ 5 (closed by `simp`/`rfl`); conclusion demands 5 <= 0 + 0. The INTENDED conjecture (with n, m >= 1) remains wide open.  
**Difficulty:** math 9/10, Lean 1/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Fin 0 -> N is inhabited by Fin.elim0, all three side conditions are vacuous quantifications over Fin 0, and Finset.sum over Fin 0 is 0. Note that n=0,m>=1 is not a counterexample (0 = sum of positive k-th powers is impossible for k>=1, and for k=0 the sums are n and m), so n=m=0 is the unique degenerate hole.  
**Flags:** missing positivity hypothesis on n and m; empty-index degenerate object admitted; prose docstring (positive n, m) does not match the formal quantification  
**Next action:** Fix the statement by adding hypotheses `0 < n` and `0 < m` (or requiring the common sum to be positive), then re-classify as cat 8/9. Do not attempt to prove the current form. Cannot verify by build here (no lake cache); the refutation is a one-liner once stated as a negation.

## `lander_parkin_selfridge.variants.five_three` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/Wikipedia/LanderParkinAndSelfridgeConjecture.lean:52`  
**Statement:** No three positive fifth powers sum to a fifth power: x1^5 + x2^5 + x3^5 = y^5 has no solution in positive integers.  
**Source:** Lander, Parkin and Selfridge conjecture, case k=5, n=3, m=1; https://en.wikipedia.org/wiki/Lander,_Parkin,_and_Selfridge_conjecture  
**Statement matches intent:** yes  
**Known status:** Open. Note the contrast with the famous Lander-Parkin-Selfridge counterexample to Euler 27^5 + 84^5 + 110^5 + 133^5 = 144^5, which has n+m = 5 = k and is consistent with the conjecture. Extensive searches (Scher-Seidl, Ekl) have found no 3-term solution within very large bounds. No repo duplicate; no PR in pr_register.json.  
**Difficulty:** math 9/10, Lean 9/10 · **Compute:** large · **Confidence:** high  
**Evidence:** A genuine open Diophantine case of LPS; no known technique (Fermat-style descent, modularity) applies to sums of three fifth powers.  
**Next action:** Leave open. Realistic partial targets: formalise mod-p obstructions ruling out solutions in residue classes, or a bounded exhaustive-search certificate (x_i, y below a fixed bound) as a cat-6 style sub-result.

## `legendre_conjecture` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Wikipedia/LegendreConjecture.lean:33`  
**Statement:** Is there always a prime strictly between n^2 and (n+1)^2 for every n >= 1?  
**Source:** Legendre's conjecture, https://en.wikipedia.org/wiki/Legendre%27s_conjecture (one of Landau's four problems)  
**Statement matches intent:** yes  
**Known status:** Open; one of Landau's problems. The best unconditional prime-gap results (Baker-Harman-Pintz, gaps << x^0.525) fall short of the required x^0.5. The same file records the AlphaProof-supplied conditional result bounded_gap_legendre and Ferreira's 'true for large n' claim (both still sorry). Oppermann.lean has oppermann_implies_legendre, a strictly stronger conjecture, so no duplicate resolution.  
**Difficulty:** math 10/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Famous Landau problem; even RH does not imply it.  
**Next action:** Leave open. Cannot be closed without a breakthrough in prime gaps; the only tractable adjacent work is formalising the reduction from a prime-gap hypothesis (bounded_gap_legendre) already stated in the file.

## `lehmer_mahler_measure_problem` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Wikipedia/LehmerMahlerMeasureProblem.lean:43`  
**Statement:** There is a constant mu > 1 such that every integer polynomial with Mahler measure greater than 1 has Mahler measure at least mu (no integer polynomials have Mahler measure arbitrarily close to 1 from above).  
**Source:** Lehmer's conjecture / Lehmer's Mahler measure problem, https://en.wikipedia.org/wiki/Lehmer%27s_conjecture  
**Statement matches intent:** yes  
**Known status:** Open since 1933. Best known lower bounds are of the shape M(f) >= 1 + c/(log deg f)^3 (Dobrowolski), which is not a uniform constant. Lehmer's number 1.17628... (root of the degree-10 Lehmer polynomial) is the conjectural minimum. No PR/campaign hit for 'lehmer' or 'mahler'.  
**Difficulty:** math 9/10, Lean 9/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Standard formulation of Lehmer's problem; a major open problem in number theory with connections to heights, hyperbolic geometry and growth of groups.  
**Next action:** Leave open. Feasible adjacent formalisation targets in the same file are the solved variants (Smyth's non-reciprocal bound M(f) >= M(x^3-x-1), and the odd-coefficients bound), both of which are currently sorry.

## `lehmer_mahler_measure_problem.variants.best` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Wikipedia/LehmerMahlerMeasureProblem.lean:54`  
**Statement:** The strong form of Lehmer's conjecture: every integer polynomial with Mahler measure greater than 1 has Mahler measure at least that of Lehmer's polynomial x^10+x^9-x^7-x^6-x^5-x^4-x^3+x+1 (about 1.17628).  
**Source:** Lehmer's conjecture (sharp form), https://en.wikipedia.org/wiki/Lehmer%27s_conjecture  
**Statement matches intent:** yes  
**Known status:** Open, and strictly stronger than lehmer_mahler_measure_problem. Verified: no integer polynomial of degree <= 44 (Mossinghoff-Rhin-Wu) has Mahler measure in (1, 1.17628). No internal PR/campaign.  
**Difficulty:** math 9/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Sharp form of a famous open problem; verified only up to bounded degree.  
**Next action:** Leave open. Note the file does not even have a lemma computing mahlerMeasureZ lehmerPolynomial numerically; establishing that value (a real-algebraic computation) would be a useful, self-contained cat-6/7 milestone.

## `lehmer_totient` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Wikipedia/LehmerTotient.lean:31`  
**Statement:** Does there exist a composite number n > 1 with phi(n) dividing n - 1?  
**Source:** Lehmer's totient problem, https://en.wikipedia.org/wiki/Lehmer%27s_totient_problem  
**Statement matches intent:** yes  
**Known status:** Open since 1932. Any counterexample must be squarefree, odd, with at least 15 prime factors and exceed 10^30 (Cohen-Hagis and later refinements: >= 15 prime factors, n > 10^22). No repo duplicate; no PR/campaign hit.  
**Difficulty:** math 9/10, Lean 9/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Faithful rendering of Lehmer's totient problem, a well-known long-standing open problem; believed answer is 'no such n exists' (i.e. answer := False).  
**Next action:** Leave open. A tractable sub-result would be formalising the classical constraints on a hypothetical Lehmer number (squarefree, odd, composite with many prime factors), which is elementary but multi-lemma.

## `infinitely_many_leinster_groups` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/Wikipedia/LeinsterGroup.lean:58`  
**Secondary category:** 9 (Major open problem / currently infeasible)  
**Statement:** Are there infinitely many finite groups in which the orders of all normal subgroups sum to twice the group order (Leinster groups)?  
**Source:** Leinster group, https://en.wikipedia.org/wiki/Leinster_group ; T. Leinster, 'Perfect numbers and groups', arXiv:math/0104012  
**Statement matches intent:** yes  
**Known status:** Open (Wikipedia's Leinster group article lists it as unresolved). Infinitely many cyclic Leinster groups would follow from infinitely many perfect numbers (itself open, equivalent to infinitely many Mersenne primes - see Mersenne.lean:infinitely_many_mersenne_primes and PerfectNumbers.lean:infinitely_many_even_perfect in this repo). Non-abelian examples are known sporadically (S3 x C5 of order 30, A5 x C15128). No PR/campaign hit for 'leinster'.  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** small · **Confidence:** medium  
**Evidence:** Definition and infinitude encoding both check out. The obstruction is that all currently known constructions either reduce to perfect numbers (Mersenne-hard) or are sporadic.  
**Flags:** Group/Fintype instances are bound as anonymous non-instance binders (`forall (_ : Group G) (_ : Fintype G)`); if instance resolution does not pick them up this would not elaborate - worth a build check, but the same idiom is used elsewhere in the file  
**Next action:** Leave open. Identifiable avenue: find/verify an infinite family of non-abelian Leinster groups, which would settle it without touching perfect numbers. First formal milestone: prove the already-stated cyclic_of_perfect_is_leinster (currently sorry) and exists_nonabelian_leinster_group by explicit computation on S3 x C5.

## `lemoine_conjecture` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Wikipedia/Lemoine.lean:35`  
**Statement:** Every odd integer n >= 7 can be written as p + 2q with p and q prime.  
**Source:** Lemoine's (Levy's) conjecture, https://en.wikipedia.org/wiki/%C3%89mile_Lemoine#Lemoine's_conjecture_and_extensions  
**Statement matches intent:** yes  
**Known status:** Open. Verified computationally for all odd n up to about 10^9 (Corbit). It implies the (proved) weak Goldbach conjecture and is generally regarded as of Goldbach-type difficulty. No PR/campaign hit for 'lemoine'.  
**Difficulty:** math 9/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Faithful transcription of a Goldbach-strength additive prime conjecture with no known approach for all n.  
**Next action:** Leave open. No feasible formal route; circle-method machinery for the ternary Goldbach theorem is not in Mathlib, and Lemoine's conjecture is not implied by it.

## `lemoine_conjecture_extension` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Wikipedia/Lemoine.lean:44`  
**Statement:** For every odd n >= 9 there are odd primes p, q, r, s and naturals a, b with p + 2q = n, 2 + pq = 2^a + r, and 2p + q = 2^b + s.  
**Source:** Kiltinen and Young (1985), 'Goldbach, Lemoine, and a Know/Don't Know Problem', Math. Magazine; via https://en.wikipedia.org/wiki/%C3%89mile_Lemoine  
**Statement matches intent:** yes  
**Known status:** Open, and strictly stronger than lemoine_conjecture. I verified computationally here that the statement holds for every odd n from 9 to 3999 (witnesses found for all), so there is no small counterexample and the formalisation is not obviously broken. No PR/campaign hit.  
**Difficulty:** math 9/10, Lean 10/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** Brute-force check over odd n in [9, 4000) found a valid (p,q,r,s,a,b) for every n, so no cheap refutation exists; the statement implies Lemoine's conjecture and is therefore at least as hard.  
**Flags:** needs literature check: exact form of the Kiltinen-Young extension not independently confirmed  
**Next action:** Leave open. Before any proof effort, cross-check the statement against the Kiltinen-Young paper (the Wikipedia summary is terse) and record the exact citation in the docstring.

## `littlewood_conjecture` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Wikipedia/LittlewoodConjecture.lean:42`  
**Statement:** For all real alpha, beta, the liminf over n of n times the distance from n*alpha to the nearest integer times the distance from n*beta to the nearest integer is 0.  
**Source:** Littlewood conjecture, https://en.wikipedia.org/wiki/Littlewood_conjecture  
**Statement matches intent:** yes  
**Known status:** Open. Einsiedler-Katok-Lindenstrauss (2006) proved the set of exceptional pairs has Hausdorff dimension 0, but the full conjecture is open. No PR/campaign hit for 'littlewood' beyond the unrelated HardyLittlewood.lean file.  
**Difficulty:** math 10/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Faithful standard formulation of a famous open Diophantine approximation problem.  
**Next action:** Leave open. Mathlib has no homogeneous-dynamics/measure-rigidity infrastructure; even the EKL partial result is far out of reach.

## `padic_littlewood_conjecture` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Wikipedia/LittlewoodConjecture.lean:55`  
**Statement:** For every real alpha and every prime p, the liminf over n of n * |n|_p * ||n*alpha|| is 0, where |.|_p is the p-adic norm and ||.|| the distance to the nearest integer.  
**Source:** de Mathan-Teulie p-adic Littlewood conjecture (2004), 'Problemes diophantiens simultanes'; https://en.wikipedia.org/wiki/Littlewood_conjecture  
**Statement matches intent:** yes  
**Known status:** Open in the original real setting (confirmed by literature search: recent work concerns only the function-field analogues). The t-adic analogue over F_3 was DISPROVED by Adiceam-Nesharim-Lunnon (arXiv:1806.04478), and further counterexamples to the P(t)-adic version over small finite fields appear in arXiv:2405.14454 and arXiv:2307.00955 - but none of these affect the p-adic conjecture over R stated here. Einsiedler-Kleinbock proved the exceptional set has Hausdorff dimension 0.  
**Difficulty:** math 10/10, Lean 10/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** Literature search confirms the p-adic (over R) conjecture is still open as of 2026; the disproofs are all in positive characteristic.  
**Flags:** function-field analogue is known FALSE (Adiceam-Nesharim-Lunnon); the real p-adic case may plausibly also fail, so a counterexample direction should not be dismissed  
**Next action:** Leave open. Flag in the docstring that the function-field analogue is now known to be false, which is decision-relevant context for anyone tempted to prove this one.

## `lonely_runner_conjecture` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/Wikipedia/LonelyRunnerConjecture.lean:35`  
**Secondary category:** 9 (Major open problem / currently infeasible)  
**Statement:** With n runners of pairwise distinct constant speeds starting together on a unit circular track, every runner is at some nonnegative time at distance at least 1/n from all the others.  
**Source:** Lonely runner conjecture, https://en.wikipedia.org/wiki/Lonely_runner_conjecture  
**Statement matches intent:** yes  
**Known status:** Open for n >= 8 runners; proved for n <= 7 (Barajas-Serra 2008 and earlier work). Tao (arXiv:1701.02048, stated as variants.tao_2017 in the same file) reduced the conjecture for each fixed n to a finite check over bounded integer velocities, and improved the gap of loneliness bound. No PR/campaign hit for 'lonely'/'runner' (the pr_register 'runner' hits are GitHub Actions runner infrastructure PRs, not this problem).  
**Difficulty:** math 9/10, Lean 9/10 · **Compute:** medium · **Confidence:** high  
**Evidence:** Faithful transcription. Identifiable avenues exist (Tao's finite reduction per n, view-obstruction reformulation), but the general case has resisted since 1967.  
**Next action:** Leave open. Concrete milestone: formalise a single small case (n = 3, i.e. two nonzero speeds) via the standard reduction to zero observer speed and a three-distance argument; that would establish the reduction lemmas needed for any future general attack.

## `isLychrel10_196` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Wikipedia/LychrelNumbers.lean:77`  
**Statement:** Is 196 a base-10 Lychrel number, i.e. does 196 never reach a palindrome under n |-> n + reverse(n)?  
**Source:** Lychrel number, https://en.wikipedia.org/wiki/Lychrel_number ; MathWorld 'Lychrel Number'; OEIS A023108  
**Statement matches intent:** yes  
**Known status:** Open. 196 has been iterated to over a billion digits (Doucette, VanLandingham and others) with no palindrome; believed Lychrel but unproved. Note the asymmetry: answer := False could in principle be settled by a finite computation if 196 ever palindromed (it does not), while answer := True needs a genuine proof.  
**Difficulty:** math 9/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** The canonical open instance of the Lychrel problem; no invariant or carry-propagation argument is known.  
**Next action:** Leave open. No known proof technique; a partial formal result could be 'lychrelStep^[k] 196 is not a palindrome for all k <= K' for modest K via decide, but that is a test, not a resolution.

## `no_lychrel_numbers_base10` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Wikipedia/LychrelNumbers.lean:69`  
**Statement:** Is it true that no positive integer is a base-10 Lychrel number, i.e. that every positive integer eventually reaches a palindrome under n |-> n + reverse(n)?  
**Source:** Lychrel number, https://en.wikipedia.org/wiki/Lychrel_number ; OEIS A023108  
**Statement matches intent:** yes  
**Known status:** Open. No base-10 Lychrel number has ever been proved, although 196 has been iterated for billions of digits without producing a palindrome; Lychrel numbers are proved to exist in base 2 and other bases. The believed answer is False (Lychrel numbers do exist), which would require proving 196 (or another seed) never palindromes. No PR/campaign hit for 'lychrel'.  
**Difficulty:** math 9/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Definitions are correct and sanity-checked by the file's own native_decide tests. Deciding the answer requires resolving the 196 problem.  
**Next action:** Leave open. There is no known invariant proof technique for base 10; the only formalisable content is the equivalence lemma already proved in the file (eventually_palindrome_base10).

## `exists_magic_square_squares` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/Wikipedia/MagicSquares.lean:39`  
**Statement:** Does a 3x3 magic square exist whose nine entries are distinct positive perfect squares (rows, columns and both diagonals summing to the same value)?  
**Source:** Magic square of squares, https://en.wikipedia.org/wiki/Magic_square_of_squares ; http://www.multimagie.com/English/SquaresOfSquaresSearch.htm  
**Statement matches intent:** yes  
**Known status:** Open, with a 1000 euro prize offered by Christian Boyer (multimagie.com) and famously popularised by Martin Gardner ($100). Exhaustive searches have ruled out all squares with entries below very large bounds; Bremner and others have connected the problem to elliptic curves. No PR/campaign hit for 'magic'.  
**Difficulty:** math 9/10, Lean 9/10 · **Compute:** large · **Confidence:** high  
**Evidence:** Faithful statement of the prize problem; both existence and non-existence directions are open, so the answer(sorry) encoding does not trivialise anything.  
**Next action:** Leave open. Identifiable avenue: reduce to rational points on a specific elliptic surface (Bremner) - a research-scale formalisation. A cheaper deliverable is a verified exhaustive search certificate over a bounded range, giving a cat-6 partial result rather than a resolution.

## `exists_semi_magic_square_cubes` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/Wikipedia/MagicSquares.lean:61`  
**Statement:** Does a 3x3 semi-magic square exist whose nine entries are distinct positive perfect cubes (all rows and all columns summing to the same value, diagonals unconstrained)?  
**Source:** https://unsolvedproblems.org/index_files/SquareofCubes.htm ; http://www.multimagie.com/English/Morgenstern21.htm  
**Statement matches intent:** yes  
**Known status:** Open, with a 1000 euro prize (multimagie.com). Confirmed by literature search: no 3x3 semi-magic square of distinct positive cubes is known; Lee Morgenstern developed two search methods (May 2010, corrected April 2015) and verified that none exists with all entries below (10^6)^3. The smallest known semi-magic squares of cubes are 4x4 (Morgenstern, 2006). No PR/campaign hit.  
**Difficulty:** math 8/10, Lean 8/10 · **Compute:** large · **Confidence:** high  
**Evidence:** Web search of multimagie.com and unsolvedproblems.org confirms the 3x3 case is unsolved (prize outstanding) - crucially NOT resolved by Morgenstern's 4x4 construction, which is a different order.  
**Next action:** Leave open. The most realistic formal contribution is a kernel-checked exhaustive-search certificate extending the known bound, or an explicit witness if the search succeeds; a nonexistence proof appears to be research-scale.

## `mahler_conjecture` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Wikipedia/Mahler32.lean:43`  
**Statement:** Mahler's 3/2 problem: there is no nonzero real x whose fractional parts of x*(3/2)^n are all less than 1/2 (no nonzero Z-numbers).  
**Source:** Mahler's 3/2 problem, https://en.wikipedia.org/wiki/Mahler%27s_3/2_problem  
**Statement matches intent:** suspect — Two deviations, one harmless and one a strengthening. (a) IsZNumber quantifies over n > 0 rather than n >= 0; this is exactly equivalent to Mahler's definition after the substitution y = (3/2)x, so it is harmless. (b) The theorem hypothesis is x <> 0, not 0 < x; Mahler's Z-numbers are positive reals, so the Lean statement additionally rules out negative Z-numbers and is therefore STRICTLY STRONGER than the conjecture. If a negative 'Z-number' existed the Lean statement would be false while Mahler's conjecture stayed open. No such example is known (e.g. x = -2^k fails at n = k+1, where the fractional part is exactly 1/2), but the strengthening should be flagged.  
**Known status:** Open. Mahler (1968) proved the set of Z-numbers below x has counting function O(x^0.7); Flatto-Lagarias-Pollington gave Omega(p/q) > 1/p (stated as a solved variant in the same file). No PR/campaign hit for 'mahler' targeting this file.  
**Difficulty:** math 9/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Definition of IsZNumber is otherwise correct; the n > 0 vs n >= 0 shift is provably equivalent, and the x <> 0 vs 0 < x change makes the formal statement strictly stronger, not weaker (so no vacuity risk, only a mild falsity risk).  
**Flags:** hypothesis x <> 0 is stronger than Mahler's 0 < x (negative reals also ruled out)  
**Next action:** Either restrict the hypothesis to 0 < x to match Mahler exactly, or add a remark that the negative case is a deliberate strengthening. Then leave open - resolution requires new ideas in the 3x+1-adjacent distribution-mod-1 area.

## `MLC` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Wikipedia/Mandelbrot.lean:107`  
**Statement:** The Mandelbrot set (as a topological subspace of the complex plane) is locally connected.  
**Source:** MLC conjecture (Douady–Hubbard); https://en.wikipedia.org/wiki/Mandelbrot_set#Local_connectivity  
**Statement matches intent:** yes  
**Known status:** Famous open problem in complex dynamics. Known: Yoccoz proved local connectivity at all non-infinitely-renormalizable parameters; MLC in general is open. MLC implies density of hyperbolicity and zero area of the boundary.  
**Difficulty:** math 10/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** multibrotSet is defined via non-escape of the critical orbit 0 under z ↦ z^n+c, and multibrotSet_eq (proved in-file) confirms the definition agrees with the classical r = 2^{1/(n-1)} escape criterion, so mandelbrotSet is the genuine Mandelbrot set. LocallyConnectedSpace on the subtype is the intended statement.  
**Next action:** Leave open. Any Lean work should target the supporting API (multibrotSet_eq is already proved) rather than the conjecture.

## `MLC_general_exponent` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Wikipedia/Mandelbrot.lean:114`  
**Statement:** For every exponent n, the Multibrot set of z ↦ z^n + c is locally connected.  
**Source:** Generalisation of MLC to Multibrot sets; https://en.wikipedia.org/wiki/Multibrot_set  
**Statement matches intent:** yes  
**Known status:** Strictly stronger than MLC (n = 2 instance is exactly MLC). Open.  
**Difficulty:** math 10/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** The degenerate exponents are genuinely harmless as the docstring claims: for n = 0 the map is the constant 1+c so no orbit escapes and multibrotSet 0 = univ; for n = 1 the orbit is k·c so multibrotSet 1 = {0}. Both are locally connected, so no vacuity/junk-value trivialisation, and the n ≥ 2 instances carry the full open content.  
**Next action:** Leave open.

## `density_of_hyperbolicity` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Wikipedia/Mandelbrot.lean:143`  
**Statement:** Parameters c for which z ↦ z^2 + c has an attracting cycle are dense in the Mandelbrot set (Fatou's conjecture for the quadratic family).  
**Source:** Density of hyperbolicity / Fatou conjecture; https://en.wikipedia.org/wiki/Mandelbrot_set, arXiv:math/9902155  
**Statement matches intent:** yes  
**Known status:** Major open problem; implied by MLC (Douady–Hubbard). Proved in the real quadratic family (Graczyk–Świątek, Lyubich) but open over ℂ.  
**Difficulty:** math 10/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** IsAttractingCycle requires 0 < n, periodicity, differentiability and |(f^[n])'(z)| < 1, which is the standard definition (super-attracting cycles included, as intended). Hyperbolic parameters lie in M, so 'M ⊆ closure H' is exactly density of hyperbolicity in M. The in-file test lemmas (attracting 2-cycle of z^2-1, non-attracting fixed point of z^2-2, no period-0 cycles) rule out a degenerate reading.  
**Next action:** Leave open.

## `density_of_hyperbolicity_general_exponent` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Wikipedia/Mandelbrot.lean:151`  
**Statement:** For every n ≥ 2, parameters with an attracting cycle are dense in the Multibrot set of z ↦ z^n + c.  
**Source:** Density of hyperbolicity for unicritical families; https://en.wikipedia.org/wiki/Multibrot_set  
**Statement matches intent:** yes  
**Known status:** Open; contains the quadratic case as an instance.  
**Difficulty:** math 10/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** The hypothesis 2 ≤ n is genuinely needed and correctly imposed: for n = 1 the multibrot set is {0} while z ↦ z + c has an attracting cycle only for no c (deriv = 1), so the closure would be empty and the statement false; the file excludes exactly that case.  
**Next action:** Leave open.

## `volume_frontier_mandelbrotSet_eq_zero` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Wikipedia/Mandelbrot.lean:162`  
**Statement:** The boundary of the Mandelbrot set has zero two-dimensional Lebesgue measure.  
**Source:** https://en.wikipedia.org/wiki/Mandelbrot_set; mathoverflow.net/questions/37229  
**Statement matches intent:** yes  
**Known status:** Open. Shishikura (1998) proved Hausdorff dimension of ∂M equals 2, which leaves the area question open; MLC implies zero area, and Ω-non-hyperbolic constructions (Buff–Chéritat for Julia sets) show positive-area analogues can occur, so this is not considered routine.  
**Difficulty:** math 10/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** measurability is discharged in-file (frontier is closed); volume on ℂ is the standard Lebesgue measure, so the statement is faithful.  
**Next action:** Leave open.

## `volume_frontier_multibrotSet_eq_zero` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Wikipedia/Mandelbrot.lean:169`  
**Statement:** For every n, the boundary of the Multibrot set of z ↦ z^n + c has zero area.  
**Source:** https://en.wikipedia.org/wiki/Multibrot_set  
**Statement matches intent:** yes  
**Known status:** Open; contains the Mandelbrot case n = 2.  
**Difficulty:** math 10/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Degenerate exponents are fine as the docstring claims: multibrotSet 0 = univ (frontier ∅) and multibrotSet 1 = {0} (frontier a single point), both null, so quantifying over all n does not make the statement false, and the n ≥ 2 content is the open one.  
**Next action:** Leave open.

## `mean_value_problem` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/Wikipedia/MeanValueProblem.lean:46`  
**Statement:** Smale's mean value conjecture: for every complex polynomial p of degree at least 2 and every point z, some critical point c satisfies |p(z)-p(c)|/|z-c| <= |p'(z)| (i.e. K = 1 works).  
**Source:** Mean value problem, https://en.wikipedia.org/wiki/Mean_value_problem ; S. Smale, 'The fundamental theorem of algebra and complexity theory', Bull. AMS 4 (1981)  
**Statement matches intent:** suspect — Two spec defects, both minor. (1) The parameter `K : R` is declared but never used anywhere in the statement - dead binder inherited from the K=4 / K=(d-1)/d variants in the same file. (2) Division by zero: if z happens to be a critical point of p then p'(z) = 0 and one can take c := z, making the goal 0/0 = 0 <= 0, so that case is satisfied degenerately. Smale's conjecture is normally stated for z with p'(z) <> 0, so this is a degenerate-case loophole rather than a semantic change; whenever p'(z) <> 0 the constraint p'(c) = 0 forces c <> z and the statement is the genuine one.  
**Known status:** Open for K = 1. Smale proved K = 4; the current record is K = 4 - o(1) (Beardon-Minda-Ng, Crane, Dubinin-Sugawa); Tischler proved K = (d-1)/d for polynomials with all real roots or all roots of equal modulus (both stated as solved variants in the same file). The extremal example p(z) = z^d - dz shows K >= (d-1)/d. No PR/campaign hit for 'mean value'.  
**Difficulty:** math 8/10, Lean 8/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** Every polynomial of degree >= 2 has a critical point (p' has degree >= 1), so no vacuity. The div-by-zero junk value only bites on the measure-zero set of critical z, where the conjecture is not normally asserted anyway.  
**Flags:** unused hypothesis K : R (statement noise); division by ||z - c|| can be 0/0 when z is itself a critical point, admitting the degenerate witness c = z  
**Next action:** Remove the unused `K : R` binder and add a hypothesis p.derivative.eval z <> 0 (or state the bound multiplicatively as |p(z)-p(c)| <= |p'(z)| * |z-c| to avoid the division). Then leave open; a good first formal milestone is the K = 4 variant, or Tischler's real-root case.

## `catalans_mersenne_conjecture` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Wikipedia/Mersenne.lean:140`  
**Statement:** Are all Catalan-Mersenne numbers c_n (c_0 = 2, c_{n+1} = 2^{c_n} - 1) with n >= 5 prime?  
**Source:** Catalan's Mersenne conjecture, https://en.wikipedia.org/wiki/Catalan%27s_Mersenne_conjecture ; https://mathworld.wolfram.com/Catalan-MersenneNumber.html  
**Statement matches intent:** yes  
**Known status:** Open and effectively untestable: c_5 = 2^(2^127 - 1) - 1 has about 5.1 * 10^37 digits, far beyond any conceivable primality test. Most number theorists expect the answer is False (some c_n is composite), but no proof either way exists. No PR/campaign hit for 'catalan' targeting this (the one pr_register 'catalan' hit is 'Audit Geode5 arithmetic and cast bridges', unrelated).  
**Difficulty:** math 10/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** The first unknown term is astronomically large; primality of c_5 cannot be decided by any known method, so neither answer can be established.  
**Next action:** Leave open. There is no computational or theoretical handle; do not attempt.

## `infinitely_many_mersenne_primes` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Wikipedia/Mersenne.lean:130`  
**Statement:** Are there infinitely many Mersenne primes, i.e. is the set of p with 2^p - 1 prime infinite?  
**Source:** https://en.wikipedia.org/wiki/Mersenne_conjectures ; classical Lenstra-Pomerance-Wagstaff heuristic predicts yes  
**Statement matches intent:** yes  
**Known status:** Open. Note the near-duplicate in this repo: FormalConjectures/Wikipedia/PerfectNumbers.lean:infinitely_many_even_perfect states the equivalent question via even perfect numbers (Euclid-Euler), and infinitely_many_perfect is the weaker version. Neither is proved; no PR/campaign hit.  
**Difficulty:** math 10/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Classic open problem; no infinitude result for any interesting family of primes of this shape is known.  
**Flags:** near-duplicate of PerfectNumbers.lean:infinitely_many_even_perfect (equivalent by Euclid-Euler, but not formally linked)  
**Next action:** Leave open. A worthwhile (non-resolving) formal contribution would be the Euclid-Euler bridge lemma linking this statement to PerfectNumbers.lean:infinitely_many_even_perfect, so the two open statements are formally tied together.

## `new_mersenne_conjecture` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Wikipedia/Mersenne.lean:76`  
**Statement:** New Mersenne (Bateman-Selfridge-Wagstaff) conjecture: for any odd natural p, if any two of (2^p-1 prime), ((2^p+1)/3 prime), (p = 2^k +/- 1 or 4^k +/- 3) hold, then all three do.  
**Source:** New Mersenne conjecture, https://en.wikipedia.org/wiki/Mersenne_conjectures  
**Statement matches intent:** yes  
**Known status:** Open; verified for all p up to roughly 30 million (Lifchitz and others). The known triple-satisfying exponents are p = 3, 5, 7, 13, 17, 19, 31, 61, 127, and I cross-checked the known Mersenne / Wagstaff / special-form exponent lists: the pairwise intersections coincide with that set, so there is no small counterexample. The same file already contains a fully proved reduction (new_mersenne_conjecture_of_prime) showing it suffices to check primes.  
**Difficulty:** math 9/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Cross-checked against known Mersenne prime exponents, Wagstaff prime exponents and the special-form set; the conjecture is consistent with all known data and requires understanding primality of 2^p-1, which is out of reach.  
**Flags:** natural subtraction in IsSpecialForm (2^k - 1, 4^k - 3) truncates at k = 0; harmless only because Odd p excludes 0 - worth a comment  
**Next action:** Leave open. Given the proved reduction, this statement is derivable in one line from new_mersenne_conjecture.variants.prime, so effort should target the prime case (which is itself hopeless without a theory of Mersenne primality).

## `new_mersenne_conjecture.variants.prime` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Wikipedia/Mersenne.lean:122`  
**Statement:** The New Mersenne conjecture restricted to odd primes p.  
**Source:** New Mersenne conjecture, https://en.wikipedia.org/wiki/Mersenne_conjectures  
**Statement matches intent:** yes  
**Known status:** Open, equivalent to new_mersenne_conjecture via the file's own proved reduction lemma. Same computational verification range applies.  
**Difficulty:** math 9/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Same evidence as new_mersenne_conjecture; resolving it requires deciding primality of 2^p-1 and (2^p+1)/3 for infinitely many p.  
**Flags:** duplicate-in-file: logically equivalent to new_mersenne_conjecture given the proved new_mersenne_conjecture_of_prime  
**Next action:** Leave open; this is the right canonical target of the two (the general form follows from it in one line via new_mersenne_conjecture_of_prime).

## `convex_mosers_worm_problem` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Wikipedia/MoserWorm.lean:94`  
**Statement:** What is the greatest lower bound of the areas of convex planar sets that contain a congruent copy of every curve of length at most 1?  
**Source:** Convex Moser's worm problem; https://en.wikipedia.org/wiki/Moser%27s_worm_problem; Wang, Acta Math. Sinica 49 (2006) 835–846; Khandhawit–Pagonakis–Sriswasdi, IJCGA 23 (2013) 197–212, arXiv:1101.5638  
**Statement matches intent:** yes  
**Known status:** Open. Best known bounds: 0.232239 ≤ area ≤ 0.270911861 (both recorded as `research solved` companion theorems in this file). No exact value is known, so answer(sorry) cannot be filled.  
**Difficulty:** math 9/10, Lean 9/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Convexity plus the covering requirement forces nonempty interior (a null convex cover could not contain a triangular worm), so unlike the non-convex version the missing closedness condition costs nothing: passing to the closure of a convex set changes neither area nor covering. The GLB formulation matches the literature, and convex_mosers_worm_problem_bound_attained (Blaschke) says the GLB is attained.  
**Flags:** answer() has no known value — the exact convex minimum is unknown  
**Next action:** Leave open; the tractable adjacent targets are the two companion bound theorems (still sorry). Do not fill answer().

## `mosers_worm_problem` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Wikipedia/MoserWorm.lean:72`  
**Secondary category:** 4 (Vacuously true / accidentally weakened)  
**Statement:** What is the greatest lower bound of the areas of (measurable) planar sets that contain a congruent copy of every curve of length at most 1?  
**Source:** Moser's worm problem (Leo Moser, 1966); https://en.wikipedia.org/wiki/Moser%27s_worm_problem; Norwood–Poole, Discrete Comput. Geom. 29 (2003) 409–417  
**Statement matches intent:** suspect — WormCovers requires only `MeasurableSet X` — no closedness, boundedness or connectedness. The classical problem asks for a 'shape' (in practice a closed/compact region); for arbitrary measurable sets the infimum may well be 0. Compare D. J. Ward, 'A set of plane measure zero containing all finite polygonal arcs', Canad. J. Math. 22 (1970): a null set containing a congruent copy of every finite polygonal arc exists. If a Ward-type set can be adapted to all rectifiable unit arcs (e.g. by a compactness argument on a closed null cover), the answer here collapses to 0 and the formalisation captures a different, degenerate problem.  
**Known status:** Open with no known lower bound. Wikipedia explicitly notes that in the non-convex case, because a cover may contain large holes, it is not clear what a lower bound on the area might be; best known upper bound 0.260437 (Norwood–Poole 2003). No conjectured exact value exists, so answer(sorry) currently cannot be filled honestly.  
**Difficulty:** math 9/10, Lean 9/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** Worms = ranges of 1-Lipschitz maps Icc 0 1 → ℝ², which is exactly the class of curves of length ≤ 1 — faithful. The restriction to orientation-preserving isometries (det = 1) is harmless because the worm family is closed under reflection (if g reverses orientation and g(w̄) ⊆ X then g∘ref is orientation-preserving and maps w into X). The real defect is the missing closedness condition on covers.  
**Flags:** missing closedness/boundedness condition on covers; answer() has no known or conjectured value; possible collapse to GLB = 0 via Ward-type measure-zero covers; needs literature check  
**Next action:** Do not attempt to fill answer(). First tighten the specification: require `IsClosed X` (or `IsCompact X`) in `WormCovers`, and check the literature on Ward-type null covers to determine whether the current measurable-only version has GLB 0. Add a repo issue documenting the gap.

## `sofaConstant_eq_volume_iff_eq_gerversSofa` — False / refutable as stated (cat 3)

**File:** `FormalConjectures/Wikipedia/MovingSofa.lean:219`  
**Secondary category:** 4 (Vacuously true / accidentally weakened)  
**Statement:** Stated: for EVERY subset s of the plane, s has area equal to the sofa constant if and only if s equals Gerver's sofa. Intended: Gerver's sofa is the unique area-maximising moving sofa (up to rigid motion).  
**Source:** Gerver, Geom. Dedicata 42 (1992) 267–283; Romik, Exp. Math. 27 (2018) 316–330; Baek, 'Optimality of Gerver's Sofa', arXiv:2411.19826 (2024); https://en.wikipedia.org/wiki/Moving_sofa_problem  
**Statement matches intent:** no — The universally quantified `∀ s : Set ℝ²` has no restriction to moving sofas and no quotient by rigid motions. Any set with the same measure as Gerver's sofa — e.g. a translate, or Gerver's sofa with one point added or deleted — would have to be literally equal to gerversSofa. Uniqueness in the literature is uniqueness among maximal-area sofas up to congruence.  
**Known status:** FALSE AS STATED and refutable in Lean without any dynamics. The intended uniqueness claim is part of Baek's 2024 optimality proof and is at worst a hard but externally (claimed) resolved statement; the file marks the companion `sofaConstant_eq_volume_gerversSofa` as `research solved` citing [Ba24].  
**Difficulty:** math 9/10, Lean 3/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Refutation sketch, ~20 lines: assume h : ∀ s, sofaConstant = volume s ↔ s = gerversSofa. Then (h gerversSofa).mpr rfl gives sofaConstant = volume gerversSofa. Set G := gerversSofa and let s := if (0 : ℝ²) ∈ G then G \ {0} else G ∪ {0}. Since singletons are null in ℝ², measure_mono and measure_union_le give volume s = volume G in both branches (no measurability of G is needed). Hence sofaConstant = volume s, so (h s).mp gives s = G, contradicting 0 ∈ s ↔ 0 ∉ G. Note this argument needs neither the value of sofaConstant nor nonemptiness of gerversSofa; the empty-set branch is also covered because then volume G = 0 would contradict the in-file `one_le_sofaConstant`.  
**Flags:** FALSE AS STATED; quantifier scope: ∀ s ranges over all subsets, not over moving sofas; uniqueness stated up to equality rather than up to rigid motion; null-set perturbation counterexample  
**Next action:** Refute or, better, fix the statement: restrict to `∀ s, (∃ m, IsMovingSofa s m) → (volume s = sofaConstant ↔ ∃ g : ℝ² ≃ᵃⁱ[ℝ] ℝ², s = g '' gerversSofa)`. Then port the intended content from [Ba24] (research-scale). Verify the refutation builds (cannot run lake here).

## `pi_normal_base_ten` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Wikipedia/NormalityOfPi.lean:39`  
**Statement:** Every decimal digit occurs in the decimal expansion of π with asymptotic frequency 1/10.  
**Source:** https://en.wikipedia.org/wiki/Normal_number, https://en.wikipedia.org/wiki/Pi  
**Statement matches intent:** suspect — `IsNormalInBase` in FormalConjecturesForMathlib/NumberTheory/NormalNumber.lean (line 62) only requires each single digit d < b to have limiting frequency 1/b — that is SIMPLE normality in base 10, strictly weaker than normality in base 10 (which requires every block of length k to have frequency 10^{-k}). The docstring/module text says 'normal in base 10'.  
**Known status:** Open — indeed it is not even known that every digit occurs infinitely often in π. So the weakened (simple normality) reading is equally open; no trivialisation results.  
**Difficulty:** math 10/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** digitSeq b x n = ⌊b^(n+1)·fract x⌋₊ % b is a correct digit extractor (b^(n+1)⌊x⌋ ≡ 0 mod b, so using fract is harmless, and fract x ≥ 0 makes Nat.floor safe). The only defect is single-digit vs block frequencies.  
**Flags:** definition captures simple normality, not full normality — prose/formal mismatch (both versions open)  
**Next action:** Leave open, but rename/strengthen the Mathlib-shim definition (e.g. `IsSimplyNormalInBase` plus a block-based `IsNormalInBase`) so the statement matches its docstring.

## `oppermann_conjecture` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Wikipedia/Oppermann.lean:53`  
**Statement:** Both halves of Oppermann's conjecture: for every x ≥ 2 there are primes in (x²−x, x²) and in (x², x²+x).  
**Source:** Oppermann's conjecture (1882); https://en.wikipedia.org/wiki/Oppermann%27s_conjecture  
**Statement matches intent:** yes  
**Known status:** Open. This declaration is literally the conjunction of parts.i and parts.ii in the same file (an intentional in-file aggregation used by `type_of%` in oppermann_implies_brocard / oppermann_implies_legendre), so it is a duplicate rather than an independent target.  
**Difficulty:** math 10/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Identical bounds to parts.i/ii; consumed via type_of% by the two textbook implication theorems, both of which are fully proved in-file.  
**Flags:** in-file duplicate of parts.i ∧ parts.ii  
**Next action:** Leave open; optionally restate it as `⟨parts.i x hx, parts.ii x hx⟩` so only two statements carry sorries.

## `oppermann_conjecture.parts.i` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Wikipedia/Oppermann.lean:34`  
**Statement:** For every integer x ≥ 2 there is a prime strictly between x(x−1) = x²−x and x².  
**Source:** Oppermann's conjecture (1882); https://en.wikipedia.org/wiki/Oppermann%27s_conjecture  
**Statement matches intent:** yes  
**Known status:** Open; strictly stronger than Legendre's conjecture (the file proves oppermann_implies_legendre), which is itself far beyond current technology — even the best zero-density results only give primes in [x, x + x^0.525].  
**Difficulty:** math 10/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** ℕ-subtraction x - 1 is safe under hx : 2 ≤ x, and x*(x-1) = x²−x there. Finset.Ioo gives strict bounds; since x² is composite for x ≥ 2 this matches π(x²−x) < π(x²) exactly.  
**Next action:** Leave open.

## `oppermann_conjecture.parts.ii` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Wikipedia/Oppermann.lean:42`  
**Statement:** For every integer x ≥ 2 there is a prime strictly between x² and x(x+1) = x²+x.  
**Source:** Oppermann's conjecture (1882); https://en.wikipedia.org/wiki/Oppermann%27s_conjecture  
**Statement matches intent:** yes  
**Known status:** Open; also implies Legendre's conjecture.  
**Difficulty:** math 10/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** No ℕ-subtraction here; strict Ioo bounds match π(x²) < π(x²+x). Ferreira's `∀ᶠ x in atTop` companion (research solved, still sorry) is the realistic Lean target in this file.  
**Next action:** Leave open.

## `pebbling_number_conjecture` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Wikipedia/PebblingNumberConjecture.lean:127`  
**Statement:** Graham's pebbling conjecture: the pebbling number of a Cartesian product of two graphs is at most the product of their pebbling numbers.  
**Source:** Graham's conjecture (Chung 1989); https://en.wikipedia.org/wiki/Graph_pebbling  
**Statement matches intent:** suspect — Both factors are forced onto the SAME vertex type V (G H : SimpleGraph V), whereas Graham's conjecture concerns G on V and H on W for arbitrary vertex sets. This is a genuine weakening: one cannot recover the general case by padding with isolated vertices, because a disconnected graph has an empty defining set and PebblingNumber falls back to the sInf-of-∅ junk value 0.  
**Known status:** Open since 1989. Known for trees × trees (Moews), cycles × cycles, and various families; no general approach. The formal restriction to G, H on one common vertex type still contains hard instances (e.g. G = H = a tree), so nothing is trivialised.  
**Difficulty:** math 9/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** PebblingNumber is sInf {n | ∀ D, NumberOfPebbles D = n → ∀ v, ∃ D', IsReachable G D D' ∧ 1 ≤ D' v}, the standard definition (upward closure of the defining set holds by monotonicity of pebbling, though that lemma is not in the file). For a disconnected G the defining set is empty and sInf = 0; then G □ H is also disconnected so both sides are 0 and the inequality holds vacuously — no falsity, but a spec smell. IsPebblingMove uses A v - 2 with hypothesis A v ≥ 2, so the ℕ-truncation is harmless.  
**Flags:** both factors restricted to a single vertex type — weaker than Graham's conjecture; sInf junk value 0 for disconnected graphs  
**Next action:** Restate with `{V W : Type} (G : SimpleGraph V) (H : SimpleGraph W)` and add a hypothesis of connectedness (or a lemma that PebblingNumber is 0 exactly for disconnected graphs) to remove the junk value; then leave the mathematics open.

## `infinite_pellNumber_primes` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Wikipedia/Pell.lean:140`  
**Statement:** There are infinitely many indices n for which the Pell number P_n is prime (equivalently, infinitely many prime Pell numbers).  
**Source:** https://en.wikipedia.org/wiki/Pell_number#Primes_and_squares; OEIS A086383 / A000129  
**Statement matches intent:** yes  
**Known status:** Open, in the same class as 'infinitely many Fibonacci primes' or 'infinitely many Mersenne primes': no technique is known for producing infinitely many primes in an exponentially growing linear-recurrence sequence.  
**Difficulty:** math 10/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** pellNumber matches P_0 = 0, P_1 = 1, P_{n+2} = 2P_{n+1}+P_n (tests pin P_2 = 2, P_5 = 29). Indexing by n rather than by the value is equivalent since P is strictly increasing from n = 1 onward, so infinitely many indices ⟺ infinitely many prime values. `Prime` on ℕ agrees with Nat.Prime; P_0 = 0 and P_1 = 1 are non-prime so no degenerate members.  
**Next action:** Leave open. The tractable adjacent work (Binet-type formula, P_{2n+1} identity) is already proved in this file.

## `infinitely_many_even_perfect` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Wikipedia/PerfectNumbers.lean:67`  
**Statement:** Are there infinitely many even perfect numbers?  
**Source:** https://en.wikipedia.org/wiki/Perfect_number  
**Statement matches intent:** yes  
**Known status:** Open; equivalent by Euclid–Euler (in Mathlib as Nat.eq_two_pow_mul_prime_mersenne_of_even_perfect / Theorem.perfect_two_pow_mul_mersenne_of_prime) to the infinitude of Mersenne primes.  
**Difficulty:** math 10/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Set {n | Perfect n ∧ Even n}.Infinite is faithful. Equivalent statement already present elsewhere in the repo (Mersenne.lean), so this is a semantic duplicate — but not a solved one.  
**Flags:** semantic duplicate of Mersenne.lean:infinitely_many_mersenne_primes via Euclid–Euler  
**Next action:** Leave open. Worth linking to FormalConjectures/Wikipedia/Mersenne.lean:infinitely_many_mersenne_primes (line 131), which is the same question in different clothing, and proving the Euclid–Euler bridge as a textbook lemma.

## `infinitely_many_perfect` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Wikipedia/PerfectNumbers.lean:51`  
**Statement:** Are there infinitely many perfect numbers?  
**Source:** https://en.wikipedia.org/wiki/Perfect_number  
**Statement matches intent:** yes  
**Known status:** Open. Would follow from infinitude of Mersenne primes (Euclid–Euler) or from existence of infinitely many odd perfect numbers; neither is known.  
**Difficulty:** math 10/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Mathlib's Nat.Perfect n bundles 0 < n with σ-condition, so n = 0 is excluded and the set is the genuine set of perfect numbers. The answer(sorry) ↔ P shape is a faithful yes/no encoding.  
**Flags:** answer() truth value unknown — statement is unanswerable as posed, which is the intended 'open' encoding  
**Next action:** Leave open; answer() cannot be filled.

## `odd_perfect_number_conjecture` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Wikipedia/PerfectNumbers.lean:79`  
**Statement:** Every perfect number is even, i.e. no odd perfect number exists.  
**Source:** https://en.wikipedia.org/wiki/Perfect_number#Odd_perfect_numbers  
**Statement matches intent:** yes  
**Known status:** Open (oldest open problem in mathematics). Known constraints only: any odd perfect number exceeds 10^1500 (Ochem–Rao 2012) and has ≥ 101 prime factors with multiplicity, and has Euler form p^α m² with p ≡ α ≡ 1 (mod 4) — the latter two are the companion `research solved` statements in this file, one of which already has an external AlphaProof formalisation linked.  
**Difficulty:** math 10/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Statement `(hn : Perfect n) : Even n` is exactly the conjecture; Nat.Perfect excludes 0, so there is no degenerate witness (0 is even anyway).  
**Next action:** Leave open. The realistic Lean target in this file is odd_perfect_number.euler_form, for which a formal proof already exists at the linked mzhorvath1/formal-conjectures commit — port and verify it.

## `pierce_birkhoff_conjecture` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Wikipedia/PierceBirkhoff.lean:86`  
**Secondary category:** 4 (Vacuously true / accidentally weakened)  
**Statement:** Every piecewise-polynomial function on ℝⁿ can be written as a finite max of finite mins of polynomials.  
**Source:** Pierce–Birkhoff conjecture (Birkhoff–Pierce 1956, Henriksen–Isbell formulation); https://en.wikipedia.org/wiki/Pierce%E2%80%93Birkhoff_conjecture  
**Statement matches intent:** suspect — `IsSemiAlgebraic` is defined as a finite UNION of zero sets {p = 0} together with a finite union of open sets {q > 0} — there are no intersections and no complements, so this is not the class of semi-algebraic sets. It does capture sets of the form {p ≥ 0} = {p = 0} ∪ {p > 0} and finite unions of these, but not intersections such as the closed first quadrant {x ≥ 0} ∩ {y ≥ 0}. Since the defective notion appears in the HYPOTHESIS (IsPiecewiseMvPolynomial), the formal statement is weaker than the conjecture: it applies to fewer functions f.  
**Known status:** Open for n ≥ 3; proved by Mahé for n = 1 and n = 2 (both recorded as companion `research solved` statements in this file, still sorry). Whether the weakened hypothesis class already suffices to make the statement provable in all dimensions is not something I could confirm.  
**Difficulty:** math 9/10, Lean 10/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** IsSemiAlgebraic₁/IsSemiAlgebraic admit only S = (⋃ᵢ {p₀ᵢ = 0}) ∪ (⋃ⱼ {p₁ⱼ > 0}). Meanwhile the conclusion (∃ finite ι κ and g with f x = ⨆ᵢ ⨅ⱼ eval x (g i j)) is faithful except that ι, κ are not required nonempty — harmless, since an empty ⨆/⨅ in ℝ evaluates to 0 and only helps in the case f ≡ 0.  
**Flags:** non-standard definition of semi-algebraic set (unions only, no intersections/complements); hypothesis class narrower than intended ⇒ statement weaker than the conjecture; ι, κ not required nonempty; needs literature check on whether the restricted covering class already suffices  
**Next action:** Fix `IsSemiAlgebraic` to allow finite unions of finite intersections of {p = 0}, {q > 0} (and complements), then leave the mathematics open. Lower-hanging fruit: pierce_birkhoff_conjecture_dim_one.

## `pollock_tetrahedral` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Wikipedia/PollocksConjecture.lean:55`  
**Statement:** Every natural number is a sum of at most 5 tetrahedral numbers n(n+1)(n+2)/6.  
**Source:** Pollock (1850); https://en.wikipedia.org/wiki/Pollock%27s_conjectures; OEIS A000797; Dickson, History of the Theory of Numbers II, pp. 22–23  
**Statement matches intent:** yes  
**Known status:** Open; verified computationally to about 10^9. Only much weaker unconditional results exist (every sufficiently large integer is a sum of a bounded but larger number of tetrahedral numbers); no proof of the constant 5 is known.  
**Difficulty:** math 9/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** ℕ-division in `tetrahedral` is exact because 6 ∣ n(n+1)(n+2), so no junk value. tetrahedral 0 = 0 makes 'exactly 5 summands' equivalent to 'at most 5', and N = 0 is covered — the statement is the intended one, including N = 0 trivially.  
**Next action:** Leave open. A useful supporting contribution would be `tetrahedral n = n*(n+1)*(n+2)/6` divisibility API plus a verified bounded search for a fixed range.

## `pollock_tetrahedral.salzer_levine` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Wikipedia/PollocksConjecture.lean:64`  
**Secondary category:** 6 (Computationally solvable with certificate)  
**Statement:** 343867 is the largest natural number that is not a sum of four tetrahedral numbers.  
**Source:** Salzer–Levine, Math. Comp. 12 (1958) 141–144; OEIS A000797; https://en.wikipedia.org/wiki/Pollock%27s_conjectures  
**Statement matches intent:** yes  
**Known status:** Conjectural, not a theorem: the 241 exceptional values (largest 343867) have been verified by computation only up to a finite bound. Proving that every N > 343867 is a sum of four tetrahedral numbers is an open additive-number-theory problem of Waring type.  
**Difficulty:** math 9/10, Lean 8/10 · **Compute:** small · **Confidence:** high  
**Evidence:** NotSumOfFourTetrahedral = {N | ∀ f : Fin 4 → ℕ, N ≠ ∑ tetrahedral (f i)} correctly encodes 'not a sum of at most four tetrahedral numbers' because tetrahedral 0 = 0. IsGreatest packages membership plus the (open) upper-bound half; the two halves have wildly different difficulty, which is why compute is 'small' only for the membership part.  
**Flags:** IsGreatest bundles a finitely-checkable half with a genuinely open half; conjectural, not the proved Salzer–Levine computation range  
**Next action:** Split the statement: the membership half (343867 ∉ sums of four tetrahedral numbers) is a finite check and is the realistic Lean milestone — bound the summands by tetrahedral k ≤ 343867 ⇒ k ≤ 127 and run a `decide`/interval search over Fin 4 → Fin 128 (~1.1×10^7 tuples after sorting, laptop-minutes with a reflective certificate). The upper-bound half stays open.

## `infinite_prime_sq_add_one` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Wikipedia/PrimesAndPerfectSquares.lean:31`  
**Statement:** Are there infinitely many primes of the form n² + 1?  
**Source:** Landau's fourth problem; https://en.wikipedia.org/wiki/Landau%27s_problems#Near-square_primes  
**Statement matches intent:** yes  
**Known status:** Open (one of Landau's four 1912 problems). Best known: Iwaniec — infinitely many n with n²+1 having at most two prime factors; Friedlander–Iwaniec handles x²+y⁴ but not x²+1.  
**Difficulty:** math 10/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** {n : ℕ | Prime (n^2 + 1)}.Infinite is equivalent to infinitude of such primes since n ↦ n²+1 is injective on ℕ. `Prime` is the general Prime on ℕ, equivalent to Nat.Prime. Related but distinct statement at ErdosProblems/913.lean (8p²+1 variant); no duplicate.  
**Next action:** Leave open; answer() cannot be filled.

## `exists_quasiperfect` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Wikipedia/QuasiperfectNumbers.lean:42`  
**Statement:** Does there exist n with σ(n) = 2n + 1 (a quasiperfect number)?  
**Source:** https://en.wikipedia.org/wiki/Quasiperfect_number  
**Statement matches intent:** yes  
**Known status:** Open; none are known and it is conjectured none exist. Known constraints: any quasiperfect number is an odd perfect square exceeding 10^35 with at least seven distinct prime factors (Hagis–Cohen, Cattaneo).  
**Difficulty:** math 9/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Quasiperfect n := σ 1 n = 2n+1 with Mathlib's ArithmeticFunction sigma; σ 1 0 = 0 ≠ 1, so n = 0 is not an accidental witness, and there is no missing positivity condition. The answer(sorry) ↔ ∃ n shape is a faithful yes/no encoding.  
**Next action:** Leave open; answer() cannot be filled. A worthwhile addition would be the known constraint theorems (odd square, > 10^35) as `research solved` companions.

## `lehmer_ramanujan_tau` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Wikipedia/RamanujanTau.lean:65`  
**Statement:** Lehmer's conjecture: the Ramanujan tau function never vanishes at a positive integer.  
**Source:** Lehmer (1947); https://en.wikipedia.org/wiki/Ramanujan_tau_function#Conjectures_on_the_tau_function  
**Statement matches intent:** suspect — Δ is defined with an infinite product ∏' (n : ℕ+), (1 - X^n)^24 whose convergence is the in-file lemma `multipliable`, which is still sorry. If that lemma were false the tprod would silently take the junk value 1, making Δ = X, τ n = [n = 1] and Lehmer's conjecture FALSE as formalised. The lemma is in fact true (coefficientwise stabilisation in the WithPiTopology product topology), so this is a latent rather than actual defect — but the open statement currently rests on an unproved definitional lemma.  
**Known status:** Open. Verified for n < 10^30-ish ranges by computation (Derickx–van Hoeij–Zeng etc.); no proof known. Note τ_two = -24 is also still sorry in this file, i.e. the basic API is not yet in place.  
**Difficulty:** math 10/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** ∀ n > 0, τ n ≠ 0 is the correct statement and correctly excludes n = 0 (τ 0 = 0, proved in-file). The definitional dependency on the sorried Multipliable instance is the only faithfulness risk.  
**Flags:** statement's meaning depends on the unproved `multipliable` lemma; tprod junk value would falsify it; supporting API (τ_two) still sorry  
**Next action:** First discharge `multipliable` and `τ_two` (small/medium Lean work) so the definition is certified non-junk; then leave Lehmer open.
