# Audit detail — LittProblems

2 research-open declarations. Fields per problem: plain statement, source, category, match, status, action, difficulties, compute, confidence, evidence, flags.

## `lam_litt.variants.integrality_implies_algebraicity` — False / refutable as stated (cat 3)

**File:** `FormalConjectures/LittProblems/1.lean:154`  
**Secondary category:** 9 (Major open problem / currently infeasible)  
**Statement:** If a power series solution of an algebraic ODE has all coefficients in Z[1/N] for some N, then it is algebraic over Q(z).  
**Source:** Lam-Litt conjecture (2) => (1) (the form on Litt's problem page); Lam & Litt, arXiv:2501.13175  
**Statement matches intent:** no — The cleared-denominator encoding of the ODE has no q(pt) != 0 side condition, so degenerate 'solutions' are admitted and the statement is false; the intended conjecture is untouched and remains open.  
**Known status:** FALSE AS STATED. Counterexample: n := 2, f := the Euler series sum_{j} j! z^j, g := 0, p := 0, q := X0^2*X2 + X0*X1 - X1 + 1, N := 1. Then q != 0 as a polynomial, g = 0 = algebraMap 0 / algebraMap q, IsDefined 0 holds (witness (0,1)), and aeval pt q = z^2 f' + z f - f + 1 = 0 (verified: z^2 f' + z f = f - 1), so f'' * aeval pt q = 0 = aeval pt p and hODE holds. All coefficients j! lie in Z = ZAdjoinInvNat 1, so hN holds. But sum j! z^j has zero radius of convergence, hence is transcendental over Q(z) - contradicting the conclusion. Intended conjecture (which excludes this f because the genuine ODE f' = ((1-z)f - 1)/z^2 is undefined at z = 0) remains open and implies Grothendieck p-curvature.  
**Difficulty:** math 9/10, Lean 8/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Euler-series identity checked by hand and symbolically: z^2 f' = sum_{k>=2}(k-1)(k-1)! z^k, z f = sum_{k>=1}(k-1)! z^k, sum = z + sum_{k>=2} k! z^k = f - 1. IsDefined only constrains the abstract g (here 0), not the (p,q) used in the equation.  
**Flags:** false as stated: degenerate object admitted (q(pt) = 0); same defect present in the sibling omega-integrality statement and in the definition IsSolutionOfAlgebraicODE used by both  
**Next action:** Repair IsSolutionOfAlgebraicODE by adding `MvPolynomial.aeval pt q != 0` (or state the ODE as f^(n) = aeval pt p / aeval pt q in the fraction field). Repair is strongly preferable to formalizing the refutation, since proving sum j! z^j transcendental in Lean needs growth/convergence theory Mathlib lacks for this purpose.

## `lam_litt.variants.omega_integrality_implies_algebraicity` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/LittProblems/1.lean:143`  
**Secondary category:** 4 (Vacuously true / accidentally weakened)  
**Statement:** If a power series solution of an algebraic ODE has p-integral coefficients up to index omega(p) with omega(p)/p -> infinity, then its coefficients lie in Z[1/N] for a single N.  
**Source:** Lam-Litt conjecture (3) => (2); Lam & Litt, arXiv:2501.13175; https://www.problemsilike.com/1  
**Statement matches intent:** suspect — IsSolutionOfAlgebraicODE clears denominators as f^(n) * q(pt) = p(pt) without requiring q(pt) != 0, so ANY differentially algebraic f qualifies (take g := 0, p := 0, q := a nonzero polynomial relation among z, f, ..., f^(n-1)). The hypothesis class is therefore strictly larger than 'solutions of f^(n) = g(...) with g defined at 0', making the formal statement stronger than the conjecture.  
**Known status:** Open; the Lam-Litt conjecture implies Grothendieck's p-curvature conjecture (noted in the file's own TODO), so it is at least that hard. I could not produce a counterexample to the widened statement: a counterexample would need a D-algebraic series with unbounded denominators whose denominators appear only at indices >> p, and every classical D-finite family has ratio omega(p)/p bounded. No PR/campaign targets LittProblems/1.lean (campaign_register.json explicitly notes the 'litt-most-unfair-bet' campaign is a DIFFERENT Litt problem).  
**Difficulty:** math 9/10, Lean 10/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** Definition audit of IsSolutionOfAlgebraicODE (lines 60-66) plus IsDefined (FormalConjecturesForMathlib/FieldTheory/MvRatFunc/Defs.lean:31): with p = 0 the requirement IsDefined 0 x0 holds via (0, 1), so the only real constraint left is q(pt) = 0, i.e. f differentially algebraic.  
**Flags:** degenerate-solution loophole: q(pt) = 0 admitted (same defect as the sibling theorem, where it is fatal); name/statement mismatch: '..._implies_algebraicity' but conclusion is bounded denominators  
**Next action:** Add the side condition MvPolynomial.aeval pt q != 0 to IsSolutionOfAlgebraicODE, then leave the (repaired) statement open. Also rename: the conclusion is (2) bounded denominators, not algebraicity.
