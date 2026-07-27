# Audit detail — Other

10 research-open declarations. Fields per problem: plain statement, source, category, match, status, action, difficulties, compute, confidence, evidence, flags.

## `beaver_math_olympiad_problem_1` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/Other/BeaverMathOlympiad.lean:67`  
**Statement:** Starting from (a,b) = (1,2) and iterating (a-b, 4b+2) when a >= b and (2a+1, b-a) otherwise, does some term satisfy a_i = b_i?  
**Source:** Beaver Math Olympiad #1, https://wiki.bbchallenge.org/wiki/Beaver_Math_Olympiad; equivalent to halting of the 6-state TM 1RB1RE_1LC0RA_0RD1LB_---1RC_1LF1RE_0LB0LE  
**Statement matches intent:** yes  
**Known status:** Open, no consensus on halting. I simulated 300000 steps with no i satisfying a_i = b_i; the entries reach ~65000 bits, so a halting witness (if any) is far out of reach of naive search and non-halting needs an invariant.  
**Difficulty:** math 8/10, Lean 8/10 · **Compute:** medium · **Confidence:** high  
**Evidence:** Independent Python replay confirms the docstring trajectory (1,2),(3,1),(2,6),(5,4),(1,18),(3,17),(7,14),(15,7),(8,30),(17,22) and exponential growth of both coordinates.  
**Next action:** Leave open; realistic progress is a longer search plus a search for a modular/measure invariant certifying non-halting. Not a good formalization target yet.

## `beaver_math_olympiad_problem_2_antihydra` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Other/BeaverMathOlympiad.lean:94`  
**Statement:** Antihydra: iterating n -> floor(3n/2) from 8, the running count 2*(#even values) - (#odd values) never becomes negative.  
**Source:** Beaver Math Olympiad #2 / Antihydra, https://bbchallenge.org/antihydra; equivalent to non-halting of 1RB1RA_0LC1LE_1LD1LC_1LA0LB_1LF1RE_---0RA  
**Statement matches intent:** yes  
**Known status:** Open; the flagship obstruction to determining BB(6) and considered Collatz-hard (only a probabilistic heuristic supports non-halting). I verified no negative value within 500000 iterations (b = 248257 there, a has ~292000 bits).  
**Difficulty:** math 9/10, Lean 9/10 · **Compute:** medium · **Confidence:** high  
**Evidence:** b uses Z (not N), so no truncation; the b recurrence keys on a n (not a (n+1)), matching the wiki convention.  
**Next action:** Leave open. Do not chase; any progress would be a research result on floor(3n/2) orbits.

## `beaver_math_olympiad_problem_2_antihydra.variants.set` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Other/BeaverMathOlympiad.lean:110`  
**Statement:** Antihydra, cardinality form: among the first n iterates of n -> floor(3n/2) from 8, the number of odd values is at most twice the number of even values.  
**Source:** Beaver Math Olympiad #2 (variant), https://wiki.bbchallenge.org/wiki/Antihydra  
**Statement matches intent:** yes  
**Known status:** Open; identical content to beaver_math_olympiad_problem_2_antihydra (an intentional in-file restatement, not a stray duplicate).  
**Difficulty:** math 9/10, Lean 9/10 · **Compute:** medium · **Confidence:** high  
**Evidence:** card(filter Odd) <= 2*card(filter Even) over range n is the exact unwinding of the integer counter b n = 2*#even - #odd >= 0.  
**Next action:** Leave open; if ever proved, derive one form from the other rather than duplicating work.

## `beaver_math_olympiad_problem_5` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/Other/BeaverMathOlympiad.lean:249`  
**Statement:** With f(x) = 10*2^x - 1, starting from (a,b) = (0,5) and iterating (a+1, b-f(a)) when b >= f(a) and (a, 3b+a+5) otherwise, does some term satisfy b_i = f(a_i) - 1?  
**Source:** Beaver Math Olympiad #5, https://wiki.bbchallenge.org/wiki/Beaver_Math_Olympiad; equivalent to halting of 1RB0LD_1LC0RA_1RA1LB_1LA1LE_1RF0LC_---0RE (reduction verified in Rocq, busycoq BB6)  
**Statement matches intent:** yes  
**Known status:** Open, no consensus. Simulation: 200000 steps with no hit; a reaches 80000 and b ~80000 bits, i.e. the orbit escapes any feasible search.  
**Difficulty:** math 8/10, Lean 8/10 · **Compute:** medium · **Confidence:** high  
**Evidence:** Independent replay reproduces the intended dynamics and shows monotone growth of a with doubling thresholds f(a); no near-miss of b = f(a) - 1 observed.  
**Next action:** Leave open; the plausible route is a non-halting invariant on the (a, b) pair, mirroring the Rocq reduction work at ccz181078/busycoq.

## `beaver_math_olympiad_problem_8` — Already solved internally (cat 0)

**File:** `FormalConjectures/Other/BeaverMathOlympiad.lean:277`  
**Secondary category:** 4 (Vacuously true / accidentally weakened)  
**Statement:** Starting from (a,b) = (10,12) with the two-branch recurrence keyed on a vs floor(b/2), does some term satisfy a_i = floor(b_i/2) + 1?  
**Source:** Beaver Math Olympiad #8, https://wiki.bbchallenge.org/wiki/Beaver_Math_Olympiad; equivalent to halting of 1RB0LD_0RC1RB_0RD0RA_1LE0RD_1LF---_0LA1LA  
**Statement matches intent:** no — The Lean statement is TRUE and already proved in-repo, but only because of N-subtraction truncation: at index 462 the orbit is (675, 1347) with a - b/2 = 2, so the intended value a - floor(b/2) - 3 = -1 is truncated to 0 and the Lean orbit follows a DIFFERENT trajectory from index 462 onward. The intended BMO#8 / Turing-machine halting question is untouched.  
**Known status:** SOLVED INTERNALLY for the formal statement: FormalConjectures/Other/BeaverMathOlympiad8Proof.lean (merged PR 'Add verified BMO #8 Lean certificate', merged 2026-07-23) proves the exact canonical statement with answer := True, witness index 1210682 where (a,b) = (1749056, 3498111) and 1749056 = 3498111/2 + 1. I independently reproduced this by replaying the truncated N recurrence - the witness is correct (so the PR titled 'INVALID - BMO 8 is not OEIS A263135', which claimed the witness fails the recurrence, is itself wrong about that point). The sibling PR 'BMO #8: correct the reduced recurrence...' independently identifies the same (675,1347) -> (0,2028) truncation defect.  
**Difficulty:** math 8/10, Lean 2/10 · **Compute:** small · **Confidence:** high  
**Evidence:** Python replay with truncation: first index with a = b/2 + 1 is exactly 1210682 with (1749056, 3498111); replay in Z semantics: the value a - floor(b/2) - 3 first goes negative at index 462 at (675, 1347), before any occurrence of the target condition. So the truncation is not cosmetic - it changes the orbit before the answer is decided.  
**Flags:** N-subtraction truncation changes the dynamics (different problem, not a weaker one); already-proved formal statement would mislabel an open BB(6)-related problem as solved; proof depends on native_decide  
**Next action:** Do NOT propagate the certificate upstream as a solution of BMO#8. Restate the recurrence over Z (or add the halting guard a n >= b n / 2 + 3 / stop at difference <= 2) so the model matches the machine, then re-triage as open. Also note the certificate uses native_decide (Lean.ofReduceBool), which upstream formal-conjectures generally does not accept.

## `Finite.Equation677_implies_Equation255` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Other/EquationalTheories_677_255.lean:71`  
**Statement:** Every finite magma satisfying law E677 (x = y◇(x◇((y◇x)◇y))) also satisfies law E255 (x = ((x◇x)◇x)◇x).  
**Source:** Equational Theories Project (teorth/equational_theories); ETP paper arXiv:2512.07087; https://teorth.github.io/equational_theories/implications/?677&finite  
**Statement matches intent:** yes  
**Known status:** Open, and the direction the ETP community believes is FALSE (they tentatively conjecture a finite counterexample exists). So this is the branch on which effort is most likely wasted. No PR or branch in this fork addresses it; no duplicate in the repo.  
**Difficulty:** math 9/10, Lean 9/10 · **Compute:** none · **Confidence:** high  
**Evidence:** ETP write-up states the implication could not be proved or disproved after months of collaborative effort and is tentatively conjectured false; the unrestricted-magma implication is already known false via a greedy construction, which removes the easiest possible proof routes.  
**Flags:** Exact negation of `Finite.Equation677_not_implies_Equation255` in the same file — one of the two declarations is necessarily unprovable. Any 'proof' of both would be an inconsistency signal.; Community consensus leans toward this statement being false; treat any quick claimed proof with extreme suspicion.  
**Next action:** Leave open; deprioritize relative to the counterexample direction. Only worth attacking if one first finds a syntactic/confluence-style argument that the ETP's finite-magma toolkit missed.

## `Finite.Equation677_not_implies_Equation255` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/Other/EquationalTheories_677_255.lean:63`  
**Secondary category:** 6 (Computationally solvable with certificate)  
**Statement:** There exists a FINITE magma satisfying law E677 (x = y◇(x◇((y◇x)◇y))) that fails law E255 (x = ((x◇x)◇x)◇x).  
**Source:** Equational Theories Project (teorth/equational_theories); ETP paper arXiv:2512.07087 lists 'does E677 imply E255 for finite magmas?' as the flagship unresolved implication. File cites https://teorth.github.io/equational_theories/implications/?677&finite and the Zulip thread '#narrow/channel/458659-Equational/topic/FINITE.3A.20677.20-.3E.20255'.  
**Statement matches intent:** yes  
**Known status:** Genuinely open. The unrestricted-magma version (E677 ⊬ E255) was settled by a greedy infinite construction (that is the sorry'd `Equation677_not_implies_Equation255` at line 45, category research solved). The FINITE version resisted the whole ETP effort: per the ETP write-up the participants 'were unable to obtain a proof or disproof' and tentatively conjecture this direction (no implication) is the true one, noting the refutation is 'immune' to essentially all techniques developed in the project (including large-scale finite-model / SAT search). No PR in this fork's 262-PR register touches it; no branch on the fork mentions equational theories; no duplicate elsewhere in FormalConjectures/.  
**Difficulty:** math 9/10, Lean 9/10 · **Compute:** large · **Confidence:** high  
**Evidence:** WebSearch confirmed (ETP paper / Tao blog, Dec 2025) that 'Does E677 imply E255 for finite magmas?' is the named open problem, conjecturally false, resistant to the project's automated methods. This declaration and the next are exact logical negations of each other, so exactly one of the two is true.  
**Flags:** This declaration and `Finite.Equation677_implies_Equation255` are exact negations; at most one can ever be proved — the file deliberately states both branches of an open dichotomy.; Exact term-level transcription of ETP numbering (E677 = x = y◇(x◇((y◇x)◇y)), E255 = x = ((x◇x)◇x)◇x) not independently re-verified against the ETP equation list; consistent with equation-order ranges and with the file's compiling Fin 3 witness. needs literature check (low risk).  
**Next action:** Leave open. Any serious attempt means re-running / extending ETP-scale finite magma search (their exhaustive enumeration already covers small orders), or finding a structural construction; do not spend Lean effort until a candidate magma exists — once a magma is found the Lean proof is a `decide` on a Fin n table.

## `exists_hasAddVCNDimAtMost_n_of_convex_rn_add_one` — False / refutable as stated (cat 3)

**File:** `FormalConjectures/Other/VCDimConvex.lean:62`  
**Secondary category:** 8 (Deep but approachable research problem)  
**Statement:** For every n there is a finite d such that every convex set in ℝ^(n+1) has additive VCₙ dimension at most d.  
**Source:** FormalConjectures/Other/VCDimConvex.lean 'Conjectures' section; `HasAddVCNDimAtMost` defined in FormalConjecturesForMathlib/Combinatorics/Additive/VCDim.lean:84.  
**Statement matches intent:** no — Missing `1 ≤ n` (the companion conjecture on line 69 does carry `2 ≤ n`). At n = 0 the notion degenerates: `Fin 0 → Fin (d+1)` is a singleton type, the sum ∑ k : Fin 0 is 0, and `HasAddVCNDimAtMost A 0 d` unfolds to 'no y : Set (unit-type) → G with y s ∈ A ↔ i₀ ∈ s', which holds iff A = ∅ or A = univ, independently of d. Since ℝ^(0+1) = (Fin 1 → ℝ) contains convex sets that are neither empty nor everything (e.g. C = {p | p 0 ≤ 0}), the n = 0 instance is false, hence the declaration as stated is false.  
**Known status:** FALSE AS STATED for the degenerate index n = 0; the intended statement (n ≥ 1, or n ≥ 2) is open. n = 1 reduces to ordinary VC dimension via `hasMulVCNDimAtMost_one` and is settled in the literature by the ℝ² bound d = 3 (line 38 of the same file, itself still sorry). For n ≥ 2 nothing is known here; note the verified counterexample from fork PR #88 kills only d = 1 at n = 2, leaving 'some finite d' open. No PR or branch targets this declaration.  
**Difficulty:** math 8/10, Lean 4/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Unfolding `HasAddVCNDimAtMost A n d` at n = 0: `∀ x : Fin 0 → Fin (d+1) → G, ∀ y : Set (Fin 0 → Fin (d+1)) → G, ¬ ∀ i s, y s + ∑ k : Fin 0, x k (i k) ∈ A ↔ i ∈ s`. The index type `Fin 0 → Fin (d+1)` is a singleton, so choosing y s := (a if i₀ ∈ s else b) with a ∈ A, b ∉ A satisfies the inner ∀ for every proper nonempty A — refuting the property for all d simultaneously.  
**Flags:** Missing positivity hypothesis on n makes the statement false for a purely degenerate reason (spec defect, not a mathematical refutation of the authors' intent).; Even the intended n ≥ 2 case is now under pressure: the verified PR #88 certificate shows d = 1 fails at n = 2; whether the construction scales to arbitrary grid size (which would refute the intended conjecture too) is untested.; verifier:confirmed  
**Next action:** Add the hypothesis `(hn : 1 ≤ n)` (or state it only for n ≥ 2) to the canonical statement; then leave it open. Refuting the current statement in Lean is easy if desired: take n = 0, C = {p | p 0 ≤ 0}, x = elim, y s = if i₀ ∈ s then 0 else 1, using `Subsingleton (Fin 0 → Fin (d+1))`.

## `hasAddVCNDimAtMost_n_one_of_convex_rn_add_one` — False / refutable as stated (cat 3)

**File:** `FormalConjectures/Other/VCDimConvex.lean:68`  
**Secondary category:** 0 (Already solved internally)  
**Statement:** For n ≥ 2, every convex set in ℝ^(n+1) has additive VCₙ dimension at most 1 (no convex set admits translates cutting out all 2^(2ⁿ) subsets of a 2×…×2 additive grid).  
**Source:** FormalConjectures/Other/VCDimConvex.lean 'Conjectures' section; `HasAddVCNDimAtMost` from FormalConjecturesForMathlib/Combinatorics/Additive/VCDim.lean:84.  
**Statement matches intent:** yes  
**Known status:** REFUTED at n = 2 by the same certificate as above (fork PR #88, branch `agent/solve-vc2-convex-counterexample`, file FormalConjectures/Other/VCDimConvexCounterexample.lean, terminal theorem `exists_convex_r3_not_hasAddVCNDimAtMost_two_one : ∃ C : Set (Fin 3 → ℝ), Convex ℝ C ∧ ¬ HasAddVCNDimAtMost C 2 1`). I verified the 13-halfspace / 16-translate certificate in exact integer arithmetic — all 64 incidences correct. PR closed, never merged; canonical file still asserts the false lemma.  
**Difficulty:** math 6/10, Lean 3/10 · **Compute:** small · **Confidence:** high  
**Evidence:** Instantiating n := 2 gives `∀ C : Set (Fin 3 → ℝ), Convex ℝ C → HasAddVCNDimAtMost C 2 1`, contradicted directly by the verified certificate C = ⋂ over 13 halfspaces with the explicit x (grid vectors (50000,0,0), (0,50000,0)) and 16 translates Y. Certificate re-checked from the branch source with auto-extracted constants: no mismatches.  
**Flags:** Canonical repo statement is FALSE as written — high priority defect; whether the conjecture survives for n ≥ 3 is untested (the counterexample only covers n = 2).; Refutation lives only on unmerged fork branches (PR #88 closed).; verifier:confirmed  
**Next action:** Port the branch counterexample and instantiate it at n = 2 to derive `¬ ∀ n ≥ 2, ...`; then replace this lemma with a corrected statement (e.g. ask for the true growth of VCₙ dimension of convex sets in ℝ^(n+1), or restrict to larger n if the authors believe n ≥ 3 survives) and verify the build. Report upstream.

## `hasAddVCNDimAtMost_two_one_of_convex_r3` — False / refutable as stated (cat 3)

**File:** `FormalConjectures/Other/VCDimConvex.lean:56`  
**Secondary category:** 0 (Already solved internally)  
**Statement:** Every convex set C in ℝ³ has additive VC₂ dimension at most 1, i.e. no convex C admits translates cutting out all 16 subsets of a 2×2 additive grid {x₀(a)+x₁(b) : a,b ∈ {0,1}}.  
**Source:** FormalConjectures/Other/VCDimConvex.lean module docstring ('What's not in the literature' / 'Conjectures'); definition `HasAddVCNDimAtMost` = to_additive of `HasMulVCNDimAtMost` in FormalConjecturesForMathlib/Combinatorics/Additive/VCDim.lean:84. Authors' own conjecture, no external citation given.  
**Statement matches intent:** yes  
**Known status:** REFUTED. Fork PR #88 'Disprove the convex additive-VC₂ bound in ℝ³' (state closed, merged_at null, head branch `agent/solve-vc2-convex-counterexample`, also `submit/vc2-convex-counterexample{,-gdm,-upstream}`) contains FormalConjectures/Other/VCDimConvexCounterexample.lean with an explicit convex polyhedron C ⊆ Fin 3 → ℝ (intersection of 13 rational halfspaces) plus 16 explicit translates Y and the 2×2 grid Z. I re-extracted all constants directly from the branch file and re-checked all 64 incidences (Y m + Z j ∈ C ⟺ bit j of m) in exact integer arithmetic: the certificate is VALID, and every 'not in C' case is witnessed by the recorded violated halfspace row. Convexity is trivial (finite intersection of halfspaces). Never merged to main; canonical file still asserts the false lemma.  
**Difficulty:** math 6/10, Lean 4/10 · **Compute:** small · **Confidence:** high  
**Evidence:** Independent exact-arithmetic verification of the 13-halfspace / 16-translate certificate: all 64 membership tests match the required shattering pattern. Structural sanity check also passes: 13 of the 16 translates sit in the plane z=0 (a single 2-D convex slice realizing 13 of 16 subsets, consistent with the known bound VC-dim ≤ 3 for convex sets in ℝ², which permits at most 15), while the subsets needing the 'diagonal' pattern {p₀₀,p₁₁} (m=9, m=11) are realized in the z=1 slice and ∅ (m=0) at z=50001. So the construction genuinely circumvents the planar obstruction by varying the slice — real mathematics, not a definitional loophole.  
**Flags:** Canonical repo statement is FALSE as written — high priority defect.; PR #88 was closed without merging, so the refutation exists only on fork branches; main still carries the false claim.; Type mismatch to resolve when porting: branch works in `Fin 3 → ℝ`, canonical lemma in `EuclideanSpace ℝ (Fin 3)`.; verifier:confirmed  
**Next action:** Correct the canonical file: replace this lemma by `∃ C : Set ℝ³, Convex ℝ C ∧ ¬ HasAddVCNDimAtMost C 2 1`, porting the certificate from branch `agent/solve-vc2-convex-counterexample` (file FormalConjectures/Other/VCDimConvexCounterexample.lean) and verifying the build; the only porting work is moving from `R3 := Fin 3 → ℝ` to `ℝ³ = EuclideanSpace ℝ (Fin 3)` (same additive group / module structure, transfer via the WithLp type synonym or `WithLp.equiv`). Also fix the module docstring, which advertises this bound. Consider notifying upstream google-deepmind/formal-conjectures.
