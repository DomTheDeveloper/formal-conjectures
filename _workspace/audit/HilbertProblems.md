# Audit detail — HilbertProblems

2 research-open declarations. Fields per problem: plain statement, source, category, match, status, action, difficulties, compute, confidence, evidence, flags.

## `hilbert_smith_conjecture` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/HilbertProblems/5.lean:68`  
**Statement:** Every locally compact topological group acting continuously and faithfully on a connected finite-dimensional topological manifold is a Lie group.  
**Source:** Hilbert-Smith conjecture; Pardon, 'The Hilbert-Smith conjecture for three-manifolds', arXiv:1112.2324; Tao's blog 2011-08-13  
**Statement matches intent:** yes  
**Known status:** Open in general since 1940s. Known: dim <= 3 (Pardon 2013), isometric actions (Myers-Steenrod), Lipschitz/quasiconformal actions. No formal proof anywhere. No PR in pr_register.json touches HilbertProblems/5.lean; no duplicate in repo.  
**Difficulty:** math 9/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Classic open problem; the reduction to the p-adic form (next entry) is the standard attack and is itself open. AdmitsLieGroupStructure is not degenerate: ChartedSpace over R^k forces local Euclidean topology, so it is not satisfiable by an arbitrary group.  
**Flags:** minor: X is not required to be second countable/metrizable, so exotic (long-line-type) manifolds are admitted; the classical statement usually assumes second countability; minor: LieGroup (R k) TOP G uses TOP = omega (analytic) smoothness, a slightly stronger conclusion than C^infty (harmless, every Lie group is analytic)  
**Next action:** Leave open. If any work is done, target the API lemmas (admitsLieGroupStructure_of_lieGroup already proved) or the dimension-3 variant, which is a full research-scale formalization of Pardon.

## `hilbert_smith_padic_formulation` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/HilbertProblems/5.lean:100`  
**Statement:** The p-adic integers Z_p admit no continuous faithful action on any connected finite-dimensional topological manifold.  
**Source:** Equivalent p-adic form of the Hilbert-Smith conjecture (via Gleason-Yamabe/Newman); Wikipedia; arXiv:math/0103145  
**Statement matches intent:** yes  
**Known status:** Open; equivalent to hilbert_smith_conjecture by Gleason-Yamabe. Known for n <= 3 (Pardon 2013). No internal or external formalization; nothing in pr_register.json / campaign_register.json.  
**Difficulty:** math 9/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Standard equivalent formulation; not vacuous (PadicInt p has its usual topology, ContinuousVAdd is the genuine continuity requirement, and ConnectedSpace X implies X nonempty so FaithfulVAdd is a real constraint).  
**Flags:** minor: second countability of X not assumed (see previous entry)  
**Next action:** Leave open. A tractable sub-goal would be the n = 1 case (Newman/Montgomery-Zippin), still substantial in Lean.
