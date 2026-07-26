# Audit detail — Books

14 research-open declarations. Fields per problem: plain statement, source, category, match, status, action, difficulties, compute, confidence, evidence, flags.

## `problem_10_1` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Books/BugeaudDistributionModuloOne/IntDistanceDistribution.lean:48`  
**Statement:** Decide (answer(sorry) iff) whether there exist a transcendental alpha with |alpha|>1 and a positive real xi such that the distance from xi*alpha^n to the nearest integer tends to 0.  
**Source:** Bugeaud, Distribution modulo one and Diophantine approximation (2012), Problem 10.1; Hardy 1919  
**Statement matches intent:** yes  
**Known status:** Century-old open problem from Pisot theory: Hardy showed algebraic alpha>1 with ||xi*alpha^n||->0 must be Pisot; whether a transcendental alpha can work is open.  
**Difficulty:** math 9/10, Lean 9/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Recognized longstanding open problem (Bugeaud Ch. 10). distToNearestInt = |x - round x| is the correct nearest-integer distance. Quantifier structure matches the book.  
**Next action:** Leave open; no known avenue. No repo PR targets it (pr_register has no Bugeaud entries).

## `problem_10_2` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Books/BugeaudDistributionModuloOne/IntDistanceDistribution.lean:58`  
**Statement:** Prove that ||e^n|| (distance from e^n to the nearest integer) does not tend to 0 as n -> infinity.  
**Source:** Bugeaud (2012), Problem 10.2  
**Statement matches intent:** yes  
**Known status:** Notoriously open; nothing is known about the distribution of e^n mod 1 beyond weak transcendence-measure bounds.  
**Difficulty:** math 9/10, Lean 9/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Faithful direct transcription; no truncation or junk-value issues (Real.exp, distToNearestInt on reals).  
**Next action:** Leave open.

## `problem_10_3` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Books/BugeaudDistributionModuloOne/IntDistanceDistribution.lean:67`  
**Statement:** Mahler's problem: prove there is c>0 with ||e^n|| > e^{-cn} for all n >= 1.  
**Source:** Bugeaud (2012), Problem 10.3; Mahler 1953  
**Statement matches intent:** yes  
**Known status:** Open. Known transcendence measures give only much weaker bounds like ||e^n|| > n^{-c n log n}.  
**Difficulty:** math 9/10, Lean 9/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Faithful; exponential lower bound with universal c, correct quantifier order (exists c, forall n).  
**Next action:** Leave open. Note the in-file test lemma correctly derives it from the Waldschmidt statement.

## `waldschmidt` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Books/BugeaudDistributionModuloOne/IntDistanceDistribution.lean:80`  
**Statement:** Waldschmidt's strengthening of Mahler: there is c>0 with ||e^n|| > n^{-c} for all n >= 2.  
**Source:** Bugeaud (2012), Ch. 10 (unnumbered); Waldschmidt, Cetraro lectures 2003  
**Statement matches intent:** yes  
**Known status:** Open; strictly stronger than Mahler's problem 10.3 (implication proved in-file as a test lemma).  
**Difficulty:** math 9/10, Lean 9/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Careful formalization: starting index adjusted from the naive n>=1 to n>=2 for exactly the right reason.  
**Next action:** Leave open.

## `spectrum_xi_alpha_pow_countable` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/Books/BugeaudDistributionModuloOne/Problem10_4.lean:43`  
**Statement:** Mendes France's conjecture: for xi != 0 and alpha > 1, the spectrum of (xi*alpha^n) — the set of irrational theta in (0,1) with (xi*alpha^n - n*theta) not u.d. mod 1 — is at most countable.  
**Source:** Bugeaud (2012), Problem 10.4; Mendes France, Sem. Delange-Pisot-Poitou 1973  
**Statement matches intent:** yes  
**Known status:** Open conjecture; partial results exist for special classes of alpha (e.g. Pisot-related cases).  
**Difficulty:** math 8/10, Lean 8/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** Statement matches the standard spectrum notion from Mendes France; no degenerate loophole found (countability unaffected by the (0,1)/irrationality trims).  
**Flags:** spectrum definition taken on trust from docstring; needs literature check against Bug12 Ch. 10 for exact wording  
**Next action:** Leave open; verify the book's exact spectrum definition against [Bug12] Ch. 10 if the file is ever revised.

## `problem_10_5` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/Books/BugeaudDistributionModuloOne/Problem10_5.lean:42`  
**Statement:** Dubickas's conjecture: for every real number field K and eps>0 there is a lacunary sequence of positive elements of K such that limsup {xi t_n} >= 1-eps for every real xi not in K.  
**Source:** Bugeaud (2012), Problem 10.5; Dubickas, Israel J. Math. 170 (2009), Conjecture 2  
**Statement matches intent:** yes  
**Known status:** Open; Dubickas proved partial approximation properties of lacunary sequences in the same paper.  
**Difficulty:** math 8/10, Lean 8/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** IsLacunaryReal (exists c>1 eventually c*a(k) < a(k+1)) is the standard lacunarity; Int.fract is the right fractional part; limsup formulation matches.  
**Next action:** Leave open.

## `problem_10_5_moreover` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/Books/BugeaudDistributionModuloOne/Problem10_5.lean:58`  
**Statement:** Strengthening of Problem 10.5: the sequence can be chosen so that every length-eps subinterval of [0,1] contains a limit point of ({xi t_n}) for every xi not in K.  
**Source:** Bugeaud (2012), Problem 10.5 (moreover clause); Dubickas 2009, Conjecture 2  
**Statement matches intent:** yes  
**Known status:** Open.  
**Difficulty:** math 8/10, Lean 8/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** Cluster-point formulation via MapClusterPt is the right notion of limit point of a sequence; internal implication lemma type-checks the relationship claimed in the docstring.  
**Flags:** vacuous-for-eps>1 subinterval clause (benign: original is trivial there too)  
**Next action:** Leave open.

## `problem_10_6_variant_1` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/Books/BugeaudDistributionModuloOne/Problem10_6.lean:135`  
**Statement:** Find a strictly increasing 'genuinely sublacunary' integer sequence (ratio eventually >= 1 + c/log n, i.e. growth ~ exp(cn/log n)) such that ({xi m_n}) is dense mod 1 for every irrational xi.  
**Source:** Bugeaud (2012), Problem 10.6; Furstenberg 1967; Boshernitzan 1994  
**Statement matches intent:** yes  
**Known status:** Open: no sequence growing faster than Furstenberg's exp(c*sqrt(n)) example is known to be dense mod 1 for all irrationals; lacunary is impossible (Pollington-de Mathan).  
**Difficulty:** math 9/10, Lean 9/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Division junk c/log n at n=0,1 (log=0 gives c/0=0) is harmless inside an eventually-filter. The growth condition is well-calibrated to keep the problem open.  
**Next action:** Leave open; avenues are measure rigidity (Furstenberg/Einsiedler-Katok-Lindenstrauss school).

## `problem_10_6_variant_2` — Vacuously true / accidentally weakened (cat 4)

**File:** `FormalConjectures/Books/BugeaudDistributionModuloOne/Problem10_6.lean:145`  
**Secondary category:** 5 (Solved mathematically, not yet formalized)  
**Statement:** Find a strictly increasing integer sequence with intermediate growth (m_n >= exp(n^alpha) eventually, for some 0<alpha<1) that is dense mod 1 for every irrational xi.  
**Source:** Bugeaud (2012), Problem 10.6 (contributor's 'intermediate-growth variant')  
**Statement matches intent:** no — The exists-alpha quantifier admits alpha < 1/2, and the increasing enumeration of {2^a*3^b : a,b>=1} has m_n = exp((sqrt(2*log2*log3)+o(1))*sqrt(n)), so it satisfies HasIntermediateGrowth for any alpha < 1/2; density for every irrational xi is exactly Furstenberg's x2,x3 theorem (1967), stated as furstenberg_two_three in the same file. So the formal statement is a known theorem, not an open problem — the intended 'very rapidly increasing' problem needs growth beyond exp(c*sqrt(n)).  
**Known status:** Mathematically settled affirmatively by Furstenberg 1967 (Math. Systems Theory 1, 1-49) applied to 6*xi; no Lean formalization of Furstenberg's theorem exists in Mathlib.  
**Difficulty:** math 3/10, Lean 9/10 · **Compute:** none · **Confidence:** high  
**Evidence:** #{(a,b): a,b>=1, 2^a*3^b <= x} ~ (log x)^2/(2 log2 log3), so the n-th element is exp(Theta(sqrt(n))) >= exp(n^{1/3}) eventually; Furstenberg's theorem gives density of {2^a 3^b xi mod 1} for irrational xi (apply to 6*xi for a,b>=1). StrictMono holds for the increasing enumeration.  
**Flags:** accidentally-weakened: exists-alpha allows alpha<1/2, admitting the known Furstenberg example; formal statement is not open; fix: require alpha > 1/2  
**Next action:** Either restrict to alpha > 1/2 (which restores openness) or reclassify as a corollary of Furstenberg. Closing the current formal statement requires formalizing Furstenberg's x2-x3 theorem plus the counting asymptotics of {2^a*3^b} — research-scale Lean effort (large).

## `problem_10_7` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/Books/BugeaudDistributionModuloOne/Problem10_7.lean:37`  
**Statement:** Decide whether for every eps>0 there are arbitrarily large non-Pisot reals alpha such that all fractional parts {alpha^n}, n>=1, lie in an interval of length eps/alpha.  
**Source:** Bugeaud (2012), Problem 10.7; Bugeaud-Moshchevitin, Math. Z. 271 (2012)  
**Statement matches intent:** yes  
**Known status:** Open; Bugeaud-Moshchevitin constructed alpha close to 1 with confined fractional parts, and showed the non-dense set has full Hausdorff dimension — the arbitrarily-large non-Pisot version is the open part.  
**Difficulty:** math 8/10, Lean 8/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** IsPisot (algebraic integer >1 with conjugates <1 in modulus) is correct; interval of length eps/alpha with free left endpoint c matches the book.  
**Flags:** answer() folds 'for a given eps' into 'for all eps' (minor); Icc interval excludes wrap-around arcs (minor)  
**Next action:** Leave open; optionally document the fixed-eps vs all-eps reading in the file.

## `problem_10_8` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Books/BugeaudDistributionModuloOne/Problem10_8.lean:45`  
**Statement:** p-adic Littlewood conjecture (de Mathan-Teulie): for every real xi and prime p, inf over q>=1 of q * |q|_p * ||q xi|| is 0.  
**Source:** Bugeaud (2012), Problem 10.8; de Mathan-Teulie, Monatsh. Math. 143 (2004)  
**Statement matches intent:** yes  
**Known status:** Major open problem. Quadratic case solved (de Mathan-Teulie 2004), exceptional set has Hausdorff dimension 0 (Einsiedler-Kleinbock 2007) — both recorded as solved variants in the file. The function-field analogue was disproved (Adiceam-Lunnon-Nesharim, char 3), but the number-field case remains open as of knowledge cutoff.  
**Difficulty:** math 9/10, Lean 9/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Set is nonempty and bounded below so sInf is well-behaved; padicNorm p q coerced from Q to R is the correct |q|_p.  
**Flags:** duplicate-of-open-statement in Wikipedia/LittlewoodConjecture.lean (documented, not a defect)  
**Next action:** Leave open. Note duplicate liminf formulation padic_littlewood_conjecture in FormalConjectures/Wikipedia/LittlewoodConjecture.lean:56 (both open; the file docstring cross-references it).

## `isAccumulationPoint_three_halves_pow` — Vacuously true / accidentally weakened (cat 4)

**File:** `FormalConjectures/Books/UniformDistributionOfSequences/Equidistribution.lean:80`  
**Secondary category:** 7 (Plausibly solvable with moderate formal work)  
**Statement:** Find (as an answer() term) an accumulation point of the sequence of fractional parts of (3/2)^n.  
**Source:** Kuipers-Niederreiter (1974); folklore open question on the distribution of (3/2)^n mod 1  
**Statement matches intent:** suspect — The intended problem — exhibit an EXPLICIT accumulation point, which is genuinely open — is not enforced by the answer() encoding: the degenerate closed-form witness answer := limsup_n fract((3/2)^n) (or sSup of the accumulation-point set) provably IS an accumulation point, because for n>=1 the values fract((3/2)^n) = (3^n mod 2^n)/2^n are in lowest terms with denominator exactly 2^n (numerator odd), hence pairwise distinct; a bounded sequence with pairwise distinct values has its limsup as a cluster point approached by infinitely many distinct values, giving membership in closure(range \ {x}).  
**Known status:** No explicit accumulation point of (3/2)^n mod 1 is known (only existence, and infinitude by Vijayaraghavan; Flatto-Lagarias-Pollington show limit points span an interval of length >= 1/3). The formal statement, however, is closable by the non-informative limsup witness with moderate Lean work.  
**Difficulty:** math 9/10, Lean 5/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** IsAccumulationPoint x s := x in closure(range s \ {x}); distinctness of values (odd/2^n in lowest terms) means every neighbourhood of the limsup contains sequence values different from it. All ingredients (boundedness in [0,1), limsup cluster-point lemmas, fract of rational) are available in Mathlib.  
**Flags:** answer()-encoding admits degenerate non-informative witness (limsup/sSup of the accumulation set), much weaker than the intended 'find an explicit point'  
**Next action:** Close the formal statement via answer := Filter.limsup (fun n => Int.fract ((3/2)^n)) atTop: prove fract((3/2)^n) = (3^n % 2^n)/2^n, oddness of 3^n % 2^n, pairwise distinctness, then limsup-is-cluster-point via Filter.frequently_lt_of_lt_limsup / eventually_lt_of_limsup_lt; alternatively flag upstream that the answer() encoding trivializes 'find'.

## `isEquidistributedModuloOne_three_halves_pow` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Books/UniformDistributionOfSequences/Equidistribution.lean:56`  
**Statement:** The sequence (3/2)^n is equidistributed modulo 1.  
**Source:** Kuipers-Niederreiter, Uniform Distribution of Sequences (1974), Ch. 1 notes after Cor. 4.2  
**Statement matches intent:** yes  
**Known status:** Famous open problem; even density of {(3/2)^n} mod 1 is unknown. Related to Mahler's Z-number problem (see FormalConjectures/Wikipedia/Mahler32.lean) and Waring's problem g(k).  
**Difficulty:** math 9/10, Lean 9/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Direct faithful transcription; n starts at 0 (fract=0), which never affects equidistribution.  
**Next action:** Leave open.

## `isEquidistributedModuloOne_transcendental_three_halves_pow` — False / refutable as stated (cat 3)

**File:** `FormalConjectures/Books/UniformDistributionOfSequences/Equidistribution.lean:63`  
**Statement:** Claims that for EVERY transcendental x, the sequence x*(3/2)^n is equidistributed modulo 1.  
**Source:** Kuipers-Niederreiter (1974) — but the book only states the almost-all metric result and the open specific cases; no such transcendence claim appears there  
**Statement matches intent:** no — The universally-quantified statement over transcendental x does not correspond to any conjecture in the cited book and is false by known results.  
**Known status:** FALSE as stated (modulo formalizing known literature): (3/2)^n is a lacunary real sequence, and by the Peres-Schlag method (Peres-Schlag, Bull. LMS 2010; exposition for lacunary/sublacunary real sequences in Moshchevitin's 'Density modulo 1 of lacunary and sublacunary sequences: application of Peres-Schlag's construction', J. Math. Sci. 2012; see also Katznelson 2001 and Akhunzhanov-Moshchevitin on badly approximable numbers) the set of xi with inf_n ||xi (3/2)^n|| > 0 has positive Hausdorff dimension, hence is uncountable, hence contains transcendental x (algebraics are countable). For such x the fractional parts avoid a neighbourhood of 0, so the sequence is not even dense, let alone equidistributed. The genuinely intended statements — Koksma's almost-all result or the specific open case (3/2)^n — are respectively proved and open.  
**Difficulty:** math 4/10, Lean 9/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** Counterexample existence: badly-approximable-for-(3/2)^n numbers form an uncountable (positive-dimension) set; uncountable minus countable algebraics is nonempty. The statement's own source (module docstring) only says almost-all x^n equidistribution and open specific cases, confirming the formalization invented a stronger claim.  
**Flags:** false-as-stated: universal quantifier over transcendental x contradicts Peres-Schlag/Katznelson-type constructions; no matching conjecture in cited source; needs literature check only for the precise citation of the (3/2)^n badly-approximable construction (Akhunzhanov-Moshchevitin)  
**Next action:** Flag for correction upstream: weaken to 'for almost every x' (Koksma/Weyl metric theorem, provable but nontrivial) or delete. Formally refuting the current statement in Lean would require a Peres-Schlag-type Cantor construction — large effort, so the practical action is to fix the statement, not to prove its negation.
