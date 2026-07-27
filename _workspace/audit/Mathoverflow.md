# Audit detail — Mathoverflow

14 research-open declarations. Fields per problem: plain statement, source, category, match, status, action, difficulties, compute, confidence, evidence, flags.

## `mathoverflow_10799.variants.kahn_kalai_conjecture_7` — Already solved externally (cat 1)

**File:** `FormalConjectures/Mathoverflow/10799.lean:171`  
**Secondary category:** 5 (Solved mathematically, not yet formalized)  
**Statement:** Kahn-Kalai Conjecture 7: for every monotone increasing family F on [n] and every interval [s,t] with t/s > 1000 log n and mu_t(F) = 1/2, there is p in [s,t] for which F is 'optimal' (the discrete isoperimetric inequality is sharp for F at p up to a factor 1000 log(1/p)).  
**Source:** MathOverflow 10799 (Gil Kalai); Kahn-Kalai, 'An isoperimetric inequality for the Hamming cube...', arXiv:math/0603218, Conjecture 7; Kalai's 2026 AI-Polymath project page 'Optimal Monotone Families for the Discrete Isoperimetric Inequality' (gilkalai.wordpress.com/projects/...)  
**Statement matches intent:** yes  
**Known status:** Kalai's AI-Polymath project page reports that on 26 June 2026 Conjecture 7 was REFUTED by a construction of Sahar Diskin and Uri Kreitner (assisted by ChatGPT 5.5 pro), named 'The Scale-Dense Dual-Tribes Counterexample'; secondary reports say the authors also verified the argument in Lean. The unconditioned version in the same file is already marked research solved with answer(False) via a Perles counterexample (April 2026). Primary source page returned HTTP 403 to WebFetch; evidence is from web search snippets of that page. No PR in this fork's pr_register.json and no campaign in campaign_register.json touches Mathoverflow/10799.  
**Difficulty:** math 8/10, Lean 7/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** Web search of Kalai's project page: 'A Polymath Project involving AI agents concluded on June 26, 2026 that Conjecture 7 from the Kahn-Kalai paper has been refuted, with a counterexample construction by Sahar Diskin and Uri Kreitner... The disproof is called The Scale-Dense Dual-Tribes Counterexample' and 'Sahar and Uri also verified the proof using lean'. The file itself already encodes the Perles counterexample for the version without mu_t(F)=1/2 and explicitly labels the mu_t(F)=1/2 version as 'Conjecture 7 from Kahn-Kalai 2006'.  
**Flags:** solved-after-knowledge-cutoff: primary source (gilkalai.wordpress.com) returns 403; classification rests on search snippets - needs literature check to confirm which exact variant was refuted; constant-sensitivity: the formalization hard-codes 1000 in both t/s > 1000*log n and IsOptimal; a counterexample tuned to a different constant would not immediately close this statement; IsOptimal uses Real.logb p m / p with Lean's junk value log 0 = 0, so degenerate families with mu_p(F) in {0,1} give RHS 0; harmless here since mu_t(F)=1/2 forbids them at t, but worth noting  
**Next action:** Track down the Diskin-Kreitner 'Scale-Dense Dual-Tribes' write-up (and their Lean file, if public), check that the construction defeats the concrete constant 1000 used in `IsOptimal` and in `t/s > 1000 * log n`, then set answer(False) and port the counterexample (structurally very similar to the already-referenced upstream proof of mathoverflow_10799 at commit 408f53d). Verify build afterwards; lake cannot be run in this container.

## `mathoverflow_17560` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Mathoverflow/17560.lean:31`  
**Statement:** If both 2^x and 3^x are natural numbers (x a real), must x be a natural number?  
**Source:** MathOverflow 17560 (Alon Amit); classical consequence of the Four Exponentials Conjecture; the 2,3,5 version follows from the Six Exponentials Theorem (Siegel/Lang/Ramachandra).  
**Statement matches intent:** yes  
**Known status:** Genuinely open. Four Exponentials Conjecture implies it: if x is irrational then {1,x} and {log 2, log 3} are each Q-linearly independent, so one of 2, 3, 2^x, 3^x is transcendental, forcing 2^x or 3^x to be non-integral. The rational case is elementary (2^{p/q} in N forces q | p). The file's own variants (with 5, and 'for all n') are correctly marked textbook since they follow from the Six Exponentials Theorem. No PR/campaign in this fork addresses it.  
**Difficulty:** math 9/10, Lean 9/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Statement uses Real.rpow ((2:R)^x with x : R). Conclusion 'exists m : N, x = m' is not a weakening: 2^x = m with m : N forces 2^x > 0 hence m >= 1 hence x >= 0, so the N-valued conclusion is equivalent to x being an integer. Hypotheses are honest existentials, no vacuity. Mathlib has no six/four exponentials machinery.  
**Next action:** Leave open. A legitimate partial step would be to formalize the rational-x case as a lemma and to record the Four-Exponentials implication; a full proof requires transcendence theory absent from Mathlib.

## `mathoverflow_1973` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Mathoverflow/1973.lean:37`  
**Statement:** Does the 6-sphere admit a complex-manifold structure (a holomorphic atlas modelled on C^3)?  
**Source:** MathOverflow 1973; classical problem going back to Hopf/Ehresmann/Borel-Serre; Atiyah's 2016 claimed proof (arXiv:1610.09366) is not accepted.  
**Statement matches intent:** yes  
**Known status:** One of the most famous open problems in complex geometry. S^6 admits an almost complex structure (from octonion multiplication); whether it admits an integrable one is open. Atiyah's 2016 preprint claiming non-existence is not regarded as correct. No PR/campaign in this fork; the declaration is merely re-exported in FormalConjectures/Subsets/FC100OpenSet1.lean.  
**Difficulty:** math 10/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Formalization is faithful: `exists atlas : ChartedSpace (EuclideanSpace C (Fin 3)) (unitSphere 6), IsManifold (modelWithCorners C ...) 1 (unitSphere 6)`. The bound `atlas` is a class-typed local hypothesis so it is used as the local instance for IsManifold. ChartedSpace's mem_chart_source axiom forbids degenerate/empty atlases, charts are PartialHomeomorphs into C^3 hence open embeddings of the subspace topology, and C^1 over the field C is equivalent to holomorphic in finite dimension, so `IsManifold 1` is genuinely the holomorphic-atlas condition. answer(sorry) asks for the decided truth value, which is exactly the MO question.  
**Next action:** Leave open (cat 9). Nothing actionable in Lean short of a research breakthrough.

## `mathoverflow_21003` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Mathoverflow/21003.lean:38`  
**Statement:** Is there a polynomial f in Q[x,y] whose induced map Q x Q -> Q is a bijection?  
**Source:** MathOverflow 21003 (Z.H.); Poonen, 'Multivariable polynomial injections on rational numbers' (2010) shows injections exist conditional on Bombieri-Lang; the bijection question is attributed to Zagier and is open.  
**Statement matches intent:** yes  
**Known status:** Well-known open problem. Even the existence of a polynomial injection Q^2 -> Q is only known conditionally (Poonen, under Bombieri-Lang); a bijection is open in both directions. No PR/campaign in this fork.  
**Difficulty:** math 9/10, Lean 9/10 · **Compute:** none · **Confidence:** high  
**Evidence:** `exists f : MvPolynomial (Fin 2) Q, Function.Bijective fun x => f.eval x` elaborates via dot notation to `MvPolynomial.eval x f` with x : Fin 2 -> Q, i.e. bijectivity of the induced map Q^2 -> Q. Fin 2 -> Q vs Q x Q is an immaterial encoding choice. No hidden weakening; answer(sorry) is the truth value of the existence statement, exactly the MO question.  
**Next action:** Leave open (cat 9). Mathlib lacks the arithmetic-geometry input; no cheap partial result is available.

## `mathoverflow_235893` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/Mathoverflow/235893.lean:203`  
**Statement:** For n > 1, if a bijection f : R^n -> R^n maps every connected set to a connected set, must its inverse do the same?  
**Source:** MathOverflow 235893 (Willie Wong); companion MO 260589 (Gro-Tsen) gives a connected bijection R -> R^2 whose inverse is not connected.  
**Statement matches intent:** yes  
**Known status:** Open as far as I can determine. The n = 1 case is true and is proved in this very file (isConnectedMap_symm_of_R / isConnectedMap_symm_of_E1, complete proofs, no sorry). The cross-dimensional analogue fails (MO 260589, stated in the file as research solved). No PR/campaign in this fork touches it.  
**Difficulty:** math 8/10, Lean 8/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** IsConnectedMap is defined with Mathlib's IsConnected (nonempty + preconnected), so no degenerate empty-set loophole; f is an Equiv on R^n so images of nonempty sets are nonempty. The statement `answer(sorry) <-> forall n > 1, forall f : R^n =~ R^n, IsConnectedMap f -> IsConnectedMap f.symm` is a faithful rendering of the MO question. No hypothesis vacuity: the n = 1 lemma in the same file shows the analogous statement is non-vacuous and provable there.  
**Flags:** needs literature check: could not confirm via MathOverflow (site unfetchable from this container) that no answer has appeared since 2016  
**Next action:** Leave open. Identifiable avenues: (a) try to transfer the 1-dimensional order/IVT argument using local separation properties of R^n (invariance of domain, unicoherence); (b) look for a counterexample built from a wild bijection whose inverse destroys connectedness of an arc, in the spirit of the Gro-Tsen R -> R^2 example. First milestone: decide n = 2.

## `mathoverflow_31809` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Mathoverflow/31809.lean:32`  
**Statement:** Is every pretriangulated category (TR1-TR3) automatically triangulated, i.e. does the octahedral axiom follow from the other axioms? Equivalently, is there a pretriangulated category that is not triangulated?  
**Source:** MathOverflow 31809 'Pre-triangulated category that isn't triangulated'; cf. Neeman, 'Some new axioms for triangulated categories' (1991) and Neeman's book, where the independence of TR4 is discussed.  
**Statement matches intent:** yes  
**Known status:** To the best of my knowledge the independence of the octahedral axiom from TR1-TR3 is a long-standing open question with no published example; I could not verify this against the MO thread (mathoverflow.net is unfetchable here) and did not spend a search on it. No PR/campaign in this fork.  
**Difficulty:** math 9/10, Lean 9/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** Uses Mathlib's `Pretriangulated C` (TR1-TR3: contractible/rotate/complete-morphism axioms) and `IsTriangulated C` (the octahedron axiom), with all the required instance hypotheses (Preadditive, HasZeroObject, HasShift C Z, additivity of shift functors), so the formal statement is the intended one. The universe parameters are auto-bound at theorem level, which is standard and harmless.  
**Flags:** docstring/statement polarity mismatch (existence question vs universally quantified statement) - cosmetic but should be noted; needs literature check: status of TR4 independence not verified against a primary source  
**Next action:** Leave open (cat 9). Either direction is a research problem; even if a counterexample is found on paper, constructing an explicit pretriangulated-but-not-triangulated category in Mathlib's CategoryTheory.Pretriangulated hierarchy would be a very large formalization.

## `mathoverflow_339137` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/Mathoverflow/339137.lean:48`  
**Statement:** If two monic real polynomials with non-negative coefficients multiply to a polynomial all of whose coefficients are 0 or 1, must each factor also have only 0/1 coefficients?  
**Source:** MathOverflow 339137 (Sil); Ben Green, '100 open problems' (2024), Problem 28 (probabilistic form); MSE 3325163.  
**Statement matches intent:** yes  
**Known status:** Open. Listed as Problem 28 in Ben Green's 2024 open-problems list; the equivalent probabilistic form (X + Y uniform on its range with X, Y independent integer-valued => X, Y uniform) is stated in FormalConjectures/GreensOpenProblems/28.lean:green_28 (also research open, answer(sorry)), and this file contains a textbook-category equivalence theorem linking the two type_of% statements. No PR/campaign in this fork proves either.  
**Difficulty:** math 8/10, Lean 8/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** IsZeroOne P := P.coeffs subset {1}; Polynomial.coeffs is the image of the support under coeff, i.e. exactly the set of NONZERO coefficients, so IsZeroOne correctly means 'every coefficient is 0 or 1'. Monic forces P, Q nonzero and hence R = P*Q monic and nonzero, so no degenerate/vacuous instances. The non-negativity hypotheses quantify over coeffs (nonzero coefficients) only, but zero coefficients are trivially non-negative, so nothing is lost. Duplicate-of-record: GreensOpenProblems/28.lean:green_28 states the probabilistic form (both still open, so no cat 0).  
**Flags:** duplicate statement of the same problem: FormalConjectures/GreensOpenProblems/28.lean:green_28 (probabilistic form); resolving either should resolve the other via the file's own equivalence theorem  
**Next action:** Leave open. Concrete progress: verify the statement for small degrees by computation (bounded-degree cases reduce to real algebraic systems / Groebner bases), or formalize the known partial results on decompositions of the uniform distribution. First milestone would be the degree <= 6 case.

## `rectangles_cover_unit_square` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/Mathoverflow/34145.lean:141`  
**Statement:** Can the unit square be covered by the countable family of rectangles of dimensions 1/k by 1/(k+1), k = 1, 2, 3, ..., placed with arbitrary rotations and translations (overlaps and overhang allowed)?  
**Source:** MathOverflow 34145 (Kaveh); Meir-Moser (1968) packing problem; partial results: packing into a square of side 133/132 (Discrete Math. 1994) and 501/500 (2008), both stated in this file.  
**Statement matches intent:** yes  
**Known status:** Open (Meir-Moser problem). The total area of the rectangles is exactly 1 (proved in this file as tsum_area_eq_one), so a cover forces a measure-theoretically perfect packing; only near-perfect packings into slightly larger squares are known. No PR/campaign in this fork.  
**Difficulty:** math 9/10, Lean 9/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** Configuration pins width (rect n) = 1/(n+1) and height = 1/(n+2), matching the k >= 1 indexing after the documented shift. Rectangle.toSet is the image of the unit square under scale then rigidMotion with an arbitrary Real.Angle, so arbitrary rotations are permitted as the MO question requires. The cover statement deliberately does not confine rectangles to the square; since sum of areas = 1 = area of the square, any cover has null overlap and null overhang, so it is equivalent (up to measure zero) to the packing statement, which is how the file presents the two variants.  
**Flags:** needs literature check: could not confirm no post-2024 resolution of the Meir-Moser problem  
**Next action:** Leave open. Realistic Lean-side progress is limited to the infrastructure already present (measure of rotated rectangles) plus, at best, formalizing a published near-packing; deciding the answer is a research problem.

## `rectangles_pack_unit_square` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/Mathoverflow/34145.lean:148`  
**Statement:** Can rectangles of dimensions 1/k by 1/(k+1), k = 1, 2, 3, ..., be packed (interiors pairwise disjoint) inside the unit square?  
**Source:** MathOverflow 34145 (Kaveh); Meir-Moser (1968); Januszewski et al. partial results (133/132 and 501/500 squares).  
**Statement matches intent:** yes  
**Known status:** Open (Meir-Moser). Known: the family packs into a square of side 501/500 (stated in this file as research solved, still sorry). No PR/campaign in this fork.  
**Difficulty:** math 9/10, Lean 9/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** IsPacking = Pairwise (m != n) disjointness of interiors, which is the standard packing notion and does not degenerate (all widths/heights are strictly positive). Containment in unitSquare is required for every n. Faithful to the MO question; answer(sorry) asks for the decided truth value.  
**Flags:** needs literature check: same as the cover variant  
**Next action:** Leave open. A worthwhile intermediate Lean target is rectangles_pack_square_133_div_132 (a published constructive packing), which is finite-description and could be formalized with the measure/rigid-motion infrastructure already in the file.

## `mathoverflow_347178` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/Mathoverflow/347178.lean:33`  
**Statement:** For n >= 2 and every C^1 function f : R^n -> R, is sup f equal to sup over x of f(x + grad f(x)) (as extended reals, including the unbounded case)?  
**Source:** MathOverflow 347178 (Biagio Ricceri).  
**Statement matches intent:** yes  
**Known status:** Open as far as I can determine (a Ricceri-style question posted in 2019; I could not reach MathOverflow from this container and my one search on it returned nothing relevant). No PR/campaign in this fork.  
**Difficulty:** math 7/10, Lean 8/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** R^n is EuclideanSpace R (Fin n), an inner product space, so Mathlib's `gradient` is the right notion; ContDiff R 1 f is exactly C^1. The EReal-valued iSup correctly handles the unbounded case (iSup = top iff not BddAbove, since the index type is nonempty), which is the point of using EReal. The first conjunct (BddAbove iff BddAbove) is logically implied by the second, so it is redundant but not a weakening.  
**Flags:** redundant conjunct: the BddAbove iff follows from the EReal supremum equality; needs literature check: MO answer status unverified  
**Next action:** Leave open. Key structural facts to exploit: the inequality sup f(x + grad f(x)) <= sup f is trivial (the map x |-> x + grad f(x) has range inside R^n); and if sup f is ATTAINED at x0 then grad f(x0) = 0, so x0 is a fixed point of the map and equality holds. Hence the whole problem lives in the non-attained-supremum case. First milestone: formalize those two reductions as lemmas, then attack (or refute) the non-attained case by a maximizing-sequence argument.

## `mathoverflow_347178.variants.bounded_iff` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/Mathoverflow/347178.lean:44`  
**Statement:** For n >= 2 and every C^1 function f : R^n -> R, is f bounded above if and only if x |-> f(x + grad f(x)) is bounded above?  
**Source:** MathOverflow 347178 (Biagio Ricceri), boundedness half of the question.  
**Statement matches intent:** yes  
**Known status:** Open; a strictly weaker consequence of the main question. No PR/campaign in this fork.  
**Difficulty:** math 7/10, Lean 8/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** Same setup as the main statement; the iff is genuinely a weakening of the main equality but is presented as a separate variant, which is legitimate. No vacuity: the class of C^1 functions on R^n with n >= 2 is rich.  
**Flags:** needs literature check: MO answer status unverified  
**Next action:** Leave open. Only the direction 'f(x + grad f) bounded above => f bounded above' has content (the converse is immediate because range (f o g) is contained in range f). That trivial direction should be extracted as a Lean lemma; the hard direction is the research content.

## `mathoverflow_347178.variants.bounded_only` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/Mathoverflow/347178.lean:55`  
**Statement:** For n >= 2 and every C^1 function f : R^n -> R with both f and x |-> f(x + grad f(x)) bounded above, is sup f = sup f(x + grad f(x))?  
**Source:** MathOverflow 347178 (Biagio Ricceri), bounded case.  
**Statement matches intent:** yes  
**Known status:** Open; the bounded-supremum case of the main question. No PR/campaign in this fork.  
**Difficulty:** math 7/10, Lean 8/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** Both suprema are real-valued iSups guarded by BddAbove hypotheses, so no Lean junk-value (iSup of an unbounded family = 0) issue arises. Hypothesis h' (boundedness of the composed function) is implied by h, hence redundant but harmless; it does not weaken the statement because the conclusion is the same.  
**Flags:** redundant hypothesis h' (implied by h); needs literature check: MO answer status unverified  
**Next action:** Leave open. Same reduction as the main statement: prove sup f(x+grad f(x)) <= sup f as an easy lemma, prove equality when the sup is attained (grad vanishes at the maximizer), then attack the non-attained bounded case.

## `exists_isFractionRing_self_ideal_ne_top_invertible` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/Mathoverflow/507128.lean:31`  
**Secondary category:** 10 (Cannot classify without correction/clarification)  
**Statement:** Does there exist a commutative ring R that equals its own total ring of fractions (every non-zero-divisor is a unit) and has a proper ideal I (I not equal to R) that is an invertible R-module?  
**Source:** MathOverflow 507128, 'Embeddability order on Picard groups', asked by Junyan Xu (2026).  
**Statement matches intent:** suspect — The declaration ASSERTS the existence, with no answer(...) wrapper, even though it is filed as research open and the underlying MO question is (as far as I can tell) open in both directions. If the true answer is 'no such R exists' the theorem is false as stated and would have to be replaced by its negation. Every other open MO problem in this batch uses the answer(sorry) <-> ... encoding; this one should too.  
**Known status:** Question posted in 2026, after my knowledge cutoff; my one search for it returned nothing and mathoverflow.net is not fetchable from this container, so I could not determine whether an example or an impossibility proof has been given. Known context that constrains the answer: for an ideal I of R, I is an invertible FRACTIONAL ideal iff it is projective of rank 1 and contains a non-zero-divisor - and if R is its own total ring of fractions any non-zero-divisor is a unit, forcing I = R. So any example must be an ideal that is invertible as a MODULE without containing a regular element. Also, Pic vanishes for zero-dimensional rings, so von Neumann regular examples are excluded, consistent with the docstring's remark that R cannot be Noetherian. No PR/campaign in this fork.  
**Difficulty:** math 7/10, Lean 8/10 · **Compute:** none · **Confidence:** low  
**Evidence:** `IsFractionRing R R` unfolds to `IsLocalization (nonZeroDivisors R) R` with the identity algebra map, whose only non-trivial condition is that every non-zero-divisor is a unit - so it does correctly say 'R is its own total ring of fractions'. `Module.Invertible R I` (Mathlib.RingTheory.PicardGroup) is module-invertibility, strictly weaker than fractional-ideal invertibility, which is what makes the question non-trivial. Restriction of R to universe `Type` is harmless. The defect is directional: an existence claim stated as a theorem for a question whose answer is not established.  
**Flags:** encoding defect: research-open existence statement asserted directly instead of via answer(sorry) <-> ...; if the MO answer is negative the declaration is FALSE as written; needs literature check: MO 507128 (2026) is past my knowledge cutoff and unreachable from this container  
**Next action:** First fix the encoding: restate as `answer(sorry) <-> exists R ...` (or confirm from the MO thread that an example is actually known and cite it). Then either import a literature example of a total quotient ring with a proper module-invertible ideal, or prove the impossibility. Needs a literature check on MO 507128 and on Picard groups of total quotient rings.

## `complexity_two_pow` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/Mathoverflow/75792.lean:206`  
**Secondary category:** 6 (Computationally solvable with certificate)  
**Statement:** Is the integer complexity (minimum number of 1s using + and * ) of 2^n exactly 2n for every n > 0?  
**Source:** MathOverflow 75792 (Harry Altman); Iraids-Balodis-Cernenoks-Opmanis-Opmanis-Podnieks, arXiv:1203.6462; Altman-Zelinsky, arXiv:1207.4841; OEIS A005245.  
**Statement matches intent:** yes  
**Known status:** Open. The upper bound complexity(2^n) <= 2n is immediate (Reachable.pow in this file); the lower bound is the hard direction. Verified computationally for all n up to roughly 39 (Iraids et al.). The analogous statement for 3 is a theorem of Selfridge (stated in the file as research solved) and for 5 it is FALSE, with the file's own decidable counterexample 5^6 = 1 + 2^3*3^2*(1 + 2^3*3^3) giving complexity(5^6) <= 29 < 30. So it is not obvious in which direction the 2-case resolves. No PR/campaign in this fork.  
**Difficulty:** math 9/10, Lean 9/10 · **Compute:** medium · **Confidence:** high  
**Evidence:** The Reachable inductive (one; add; mul, each charging a+b ones) plus Reachable.le (upward closure in the number of ones, via multiplying by 1) makes `complexity n = Nat.find` the genuine Mahler-Popken complexity for n > 0; complexity 0 = 0 is a junk value excluded by the hypothesis 0 < n. So the formalization is faithful. The parallel declarations complexity_three_pow (answer(True)) and complexity_five_pow (answer(False), fully proved by decide) confirm the intended reading of the encoding.  
**Next action:** Leave the general statement open. Useful and cheap: use the file's `Reachable.decide` instance to `decide` complexity(2^n) = 2n for small n (n <= 8 or so before kernel reduction blows up) as test lemmas, which would also be the natural certificate route if a counterexample exists at moderate n. Deciding the full statement needs the Altman-Zelinsky 'defect' theory, which is a large formalization.
