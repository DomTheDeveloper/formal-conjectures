# Audit detail — OptimizationConstants

3 research-open declarations. Fields per problem: plain statement, source, category, match, status, action, difficulties, compute, confidence, evidence, flags.

## `c1a_eq` — Vacuously true / accidentally weakened (cat 4)

**File:** `FormalConjectures/OptimizationConstants/1a.lean:61`  
**Secondary category:** 2 (Trivially or easily solvable)  
**Statement:** Determine the exact value of Tao's autocorrelation constant 1a.  
**Source:** Tao's optimization constant 1a; Matolcsi-Vinuesa arXiv:0907.1379; Yuksekgonul et al. arXiv:2601.16175  
**Statement matches intent:** no — With the broken t-range the constant collapses to 0, so 'the exact value' is answerable as answer := 0 with a short measure-theoretic argument - nothing to do with the real constant, whose value is a hard open problem.  
**Known status:** Formal statement is provable (C1a = 0). The intended question (exact value of the autoconvolution constant, known only to lie in [1.2748, 1.5029]) is wide open.  
**Difficulty:** math 8/10, Lean 5/10 · **Compute:** none · **Confidence:** high  
**Evidence:** C1a = sSup {C | C <= 0} = 0 as computed above; the set is nonempty and bounded above, so no sSup junk value is involved.  
**Flags:** answer-encoding trivialized by the definitional defect; resolving it would falsely mark a research-open problem as solved  
**Next action:** Fix the definition first. If one wants the degenerate fact recorded, C1a = 0 is provable in maybe 100 lines: upper bound via the indicator test function, lower bound via nonnegativity of the sup-set.

## `mem_Ico_c1a` — Vacuously true / accidentally weakened (cat 4)

**File:** `FormalConjectures/OptimizationConstants/1a.lean:51`  
**Secondary category:** 2 (Trivially or easily solvable)  
**Statement:** Exhibit a number in [C1a, 1.5029), i.e. improve the known upper bound for Tao's autocorrelation constant 1a.  
**Source:** Tao's optimization constant 1a (https://teorth.github.io/optimizationproblems/constants/1a.html); Matolcsi-Vinuesa, arXiv:0907.1379  
**Statement matches intent:** no — The definition of C1a is broken: the mass is integrated over [-1/4,1/4] but the autoconvolution supremum is taken over t in [1/2,1], which is disjoint from the support of f*f for f supported in [-1/4,1/4]. Consequently C1a = 0 and the interval is [0, 1.5029), so any answer such as 1.2748 works.  
**Known status:** The genuine constant (min over nonnegative f supported in [-1/4,1/4] with integral 1 of sup_t (f*f)(t)) satisfies 1.2748 <= C <= 1.5029 and improving the upper bound is open. As formalized the problem is trivial. No PR/campaign touches OptimizationConstants.  
**Difficulty:** math 8/10, Lean 5/10 · **Compute:** medium · **Confidence:** high  
**Evidence:** Take f = indicator of [-1/4,1/4]: integral over [-1/4,1/4] is 1/2, while for every t in [1/2,1] the supports of x -> f(x) and x -> f(t-x) meet in a null set, so every element of the sup-set is 0 and the sSup is 0. Hence every admissible C satisfies C*(1/4) <= 0, i.e. C <= 0; and every C <= 0 is admissible, so C1a = sSup {C | C <= 0} = 0.  
**Flags:** wrong t-range in the definition of C1a (major semantic mismatch); the companion theorem c1a_lower_bound (1.2748 <= C1a, tagged research solved) is FALSE under the current definition  
**Next action:** Fix the definition: take the supremum over t in Icc (-1/2) (1/2) (or over all t) and, preferably, restrict f to functions supported in [-1/4,1/4]. Then re-triage (expected cat 8).

## `mem_Ioc_c1a` — False / refutable as stated (cat 3)

**File:** `FormalConjectures/OptimizationConstants/1a.lean:56`  
**Secondary category:** 4 (Vacuously true / accidentally weakened)  
**Statement:** Exhibit a number in (1.2748, C1a], i.e. improve the known lower bound for Tao's autocorrelation constant 1a.  
**Source:** Tao's optimization constant 1a; Matolcsi-Vinuesa lower bound 1.2748, arXiv:0907.1379  
**Statement matches intent:** no — Because the broken definition forces C1a = 0, the target set Set.Ioc 1.2748 C1a = Ioc 1.2748 0 is EMPTY, so no value of answer(sorry) can make the statement true.  
**Known status:** Unprovable as stated (false for every candidate answer). The intended problem - improving the 1.2748 lower bound of Matolcsi-Vinuesa - is genuinely open.  
**Difficulty:** math 8/10, Lean 5/10 · **Compute:** medium · **Confidence:** high  
**Evidence:** Same computation as for mem_Ico_c1a: C1a = 0 < 1.2748, so Set.Ioc 1.2748 C1a = empty.  
**Flags:** statement is unsatisfiable as written (empty interval); root cause is the shared broken definition of C1a  
**Next action:** Fix C1a (supremum over t in Icc (-1/2) (1/2), f supported in [-1/4,1/4]) and restate; do not attempt to prove the current statement.
