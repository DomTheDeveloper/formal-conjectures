# Audit detail — Millenium

10 research-open declarations. Fields per problem: plain statement, source, category, match, status, action, difficulties, compute, confidence, evidence, flags.

## `navier_stokes_breakdown_R3` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Millenium/NavierStokes.lean:279`  
**Statement:** Clay problem (C): there exist an admissible initial velocity and forcing term on R^3 for which no globally smooth finite-energy solution exists.  
**Source:** Clay Millennium Problem, Fefferman (statement (C))  
**Statement matches intent:** yes  
**Known status:** Open. Widely regarded as the more likely alternative for R^3 but no proof; Tao's 2016 averaged-equation blowup is not a proof for the true equation.  
**Difficulty:** math 10/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** No cheap loophole: the force must satisfy the full rapid-decay condition (condition 5), so energy input is finite and breakdown cannot be manufactured trivially.  
**Next action:** Leave open.

## `navier_stokes_breakdown_periodic` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Millenium/NavierStokes.lean:287`  
**Statement:** Clay problem (D): there exist an admissible periodic initial velocity and forcing term for which no globally smooth periodic solution exists.  
**Source:** Clay Millennium Problem, Fefferman (statement (D))  
**Statement matches intent:** yes  
**Known status:** Open. Nothing internal or external.  
**Difficulty:** math 10/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Faithful rendering; no degenerate witness available since the force conditions are the source's.  
**Next action:** Leave open.

## `navier_stokes_existence_and_smoothness_R3` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Millenium/NavierStokes.lean:265`  
**Statement:** Clay problem (A): for every viscosity nu>0 and every smooth, divergence-free, rapidly decaying initial velocity on R^3, a globally smooth finite-energy solution of Navier-Stokes with zero force exists.  
**Source:** Clay Millennium Problem, Fefferman, 'Existence and smoothness of the Navier-Stokes equation' (statement (A), conditions 1-4, 6, 7)  
**Statement matches intent:** yes  
**Known status:** Open Millennium Prize problem. No formal proof anywhere; nothing in pr_register.json / campaign_register.json for Navier-Stokes; no duplicate in repo.  
**Difficulty:** math 10/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Statement matches Fefferman's (A) including the f identically 0 specialization; the junk-value note on `divergence` is harmless because velocity smoothness is assumed wherever divergence is constrained.  
**Next action:** Leave open. Any realistic Lean work here is API (divergence_add/divergence_smul are the file's own open API lemmas) rather than the conjecture.

## `navier_stokes_existence_and_smoothness_periodic` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Millenium/NavierStokes.lean:272`  
**Statement:** Clay problem (B): the same global existence and smoothness statement on the torus R^3/Z^3 with zero force.  
**Source:** Clay Millennium Problem, Fefferman (statement (B), conditions 8, 10, 11 + errata on pressure periodicity)  
**Statement matches intent:** yes  
**Known status:** Open Millennium Prize problem. Nothing internal or external.  
**Difficulty:** math 10/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** IsOnePeriodic f defined by invariance under EuclideanSpace.single i 1 in each coordinate - correct encoding of R^3/Z^3.  
**Next action:** Leave open.

## `poincare_conjecture.variants.smooth_dimension_four` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Millenium/Poincare.lean:100`  
**Statement:** Smooth Poincare conjecture in dimension 4: every smooth 4-manifold homotopy equivalent to S^4 is diffeomorphic to S^4.  
**Source:** SPC4; Wang-Xu, 'The triviality of the 61-stem', Annals 186 (2017), Section 1; Milnor, 'Fifty years ago: topology of manifolds'  
**Statement matches intent:** suspect — SmoothConjectureFor omits [T2Space M], unlike ConjectureFor which has it. Non-Hausdorff smooth 4-manifolds (e.g. R^4 with a doubled origin, a legitimate ChartedSpace + IsManifold in Mathlib) are weakly homotopy equivalent to S^4 and are certainly not diffeomorphic to S^4; if such an example is a genuine ContinuousMap.HomotopyEquiv (not merely a weak equivalence) the statement is outright false, and the file's own smooth_known_cases would be false too.  
**Known status:** SPC4 is a famous open problem (the last open case of the Poincare conjecture family; opinion is divided on its truth). No formal proof. Nothing in pr_register.json / campaign_register.json for Poincare; no duplicate in repo.  
**Difficulty:** math 10/10, Lean 10/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** Line 41 (ConjectureFor) has [T2Space M]; line 73 (SmoothConjectureFor) does not - an asymmetry that reads as an oversight. R^n with doubled origin is the homotopy pushout of pt <- S^{n-1} -> pt realized as an actual pushout, hence weakly equivalent to S^n.  
**Flags:** missing [T2Space M] in SmoothConjectureFor (possible major semantic defect affecting three theorems in this file); needs literature check: is the line/plane/R^4 with doubled origin genuinely homotopy equivalent (not just weakly) to S^n?  
**Next action:** Add [T2Space M] to SmoothConjectureFor (matching ConjectureFor) before any further work; then leave open.

## `poincare_conjecture.variants.smooth_other_cases` — False / refutable as stated (cat 3)

**File:** `FormalConjectures/Millenium/Poincare.lean:106`  
**Secondary category:** 1 (Already solved externally)  
**Statement:** For every n > 4 outside {1,2,3,5,6,12,56,61}, the smooth Poincare conjecture fails in dimension n (i.e. exotic n-spheres exist).  
**Source:** Conjecture 1.17 in Wang-Xu, 'The triviality of the 61-stem in the stable homotopy groups of spheres', Annals 186 (2017)  
**Statement matches intent:** no — n = 126 is a counterexample after Lin-Wang-Xu (2024/25): the file's SmoothTrueValues set is out of date, and the conjecture it encodes was disproved rather than proved.  
**Known status:** Wang-Xu (2017) reduced the classification of dimensions with a unique smooth structure on S^n to the single open case n = 126, whose answer is governed by the existence of the Kervaire invariant one element theta_6 in dimension 126. Lin-Wang-Xu, 'On the last Kervaire invariant problem' (arXiv:2412.10879, Dec 2024; reported peer-reviewed by 2026) proved theta_6 EXISTS, so Theta_126 = ker(Kervaire map) = 0 and S^126 has a unique smooth structure. Hence SmoothConjectureFor 126 holds and the stated negation fails at n = 126.  
**Difficulty:** math 10/10, Lean 10/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** Confirmed by web search that Lin-Wang-Xu proved existence of Kervaire invariant one manifolds in dimension 126, completing the list 2,6,14,30,62,126. Kervaire-Milnor exact sequence 0 -> bP_{n+1} -> Theta_n -> coker J_n -> Z/2 with bP_127 = 0 gives Theta_126 = ker(Kervaire), which vanishes exactly when theta_6 exists (this is the equivalence Wang-Xu isolated as the last open case).  
**Flags:** status changed externally after the file was written (2025 result); the same missing-[T2Space] defect as smooth_dimension_four would instead make this statement degenerately TRUE for every n - two competing defects, both requiring repair; needs literature check on the exact Theta_126 = 0 <=> theta_6 exists equivalence in Wang-Xu  
**Next action:** Update SmoothTrueValues to {1,2,3,5,6,12,56,61,126}, restate as a research-solved theorem citing Hill-Hopkins-Ravenel + Wang-Xu + Lin-Wang-Xu, and demote/retire the 'conjectured' framing. Formalizing either direction is research-scale.

## `NP_ne_coNP` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Millenium/PvsNP.lean:97`  
**Statement:** NP differs from coNP (the class of languages whose complements are in NP).  
**Source:** Standard complexity conjecture; Arora-Barak Chapter 2; Wikipedia  
**Statement matches intent:** yes  
**Known status:** Open; strictly stronger than P != NP (NP != coNP implies P != NP). No formal proof.  
**Difficulty:** math 10/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** No loophole: complement is the genuine pointwise negation, so the statement is the standard conjecture.  
**Next action:** Leave open.

## `P_ne_NP` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Millenium/PvsNP.lean:89`  
**Statement:** The class P of polynomial-time decidable languages differs from the class NP of polynomially verifiable languages.  
**Source:** Clay Millennium Problem; Arora-Barak, Computational Complexity, Def. 2.1  
**Statement matches intent:** yes  
**Known status:** Open Millennium Prize problem. No formal proof; nothing in pr_register.json / campaign_register.json.  
**Difficulty:** math 10/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Definitions are the standard ones and non-degenerate; equality of the two ComplexityClass sets is the intended assertion.  
**Next action:** Leave open. The tractable work in this file is the textbook lemmas coP_eq_P and P_subset_NP (both still sorry).

## `generalized_riemann_hypothesis` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Millenium/RiemannHypothesis.lean:79`  
**Statement:** Every non-trivial zero of the Dirichlet L-function of a primitive Dirichlet character has real part 1/2.  
**Source:** Generalized Riemann Hypothesis; Wikipedia; standard trivial-zero classification (Davenport, Multiplicative Number Theory, Ch. 9)  
**Statement matches intent:** yes  
**Known status:** Open. The file's own test lemma implies_riemannHypothesis checks the q = 1 specialization reduces to RiemannHypothesis, which is good evidence of faithfulness.  
**Difficulty:** math 10/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Checked branch-by-branch against the classical trivial-zero sets; the q = 1 pole at s = 1 is handled by Mathlib's riemannZeta_one_ne_zero, as exploited in the test lemma.  
**Next action:** Leave open.

## `riemannHypothesis` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Millenium/RiemannHypothesis.lean:57`  
**Statement:** Every non-trivial zero of the Riemann zeta function has real part 1/2.  
**Source:** Clay Millennium Problem; Mathlib's `RiemannHypothesis` definition  
**Statement matches intent:** yes  
**Known status:** Open Millennium Prize problem. No formal proof; nothing internal.  
**Difficulty:** math 10/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Mathlib's riemannZeta is the true meromorphic continuation, so no junk-value loophole (contrast the file's own well-reasoned note on why ERH for dedekindZeta is deliberately omitted).  
**Next action:** Leave open.
