# Prioritized work queue

Ranked per the audit prioritization order. Within a bucket, sorted by confidence then Lean difficulty.
Every 'solved/solvable' claim below is static-analysis only until a `lake --wfail build` and axiom audit pass — see README verification standards.

## 0. Internal proofs to port/merge (category 0 — fastest wins)  (26)

- **`GreensOpenProblems/14.lean:W_3_20_lower`** (cat 0, conf high, L2, small) — Close the catalog statement: set answer(True) in 14.lean and prove with Iff.intro/iff_of_true using Green14.FastKernel.W_3_20_lower_fast; verify build (cannot run lake in this container).
- **`Paper/MonochromaticQuantumGraph.lean:eqSystem6_no_solution_d3_int`** (cat 0, conf high, L8, medium) — Set answer(True), wire QuantumGraphGlobal.no_eqSystem_int into the canonical decl (extend FORMAL_CONJECTURES_STATUS_PATCH.diff, which currently omits the d3 pair), re-run setup_certificates.sh + verif
- **`Paper/MonochromaticQuantumGraph.lean:eqSystem6_no_solution_d3_trinary_int`** (cat 0, conf high, L8, medium) — Wire QuantumGraphGlobal.no_eqSystem_trinary_int (verbatim statement match, immediate corollary of the Z result) into the canonical decl; extend the status patch, which omits the d3 trinary decl.
- **`Paper/MonochromaticQuantumGraph.lean:eqSystem6_no_solution_d5_int`** (cat 0, conf high, L8, medium) — Apply FORMAL_CONJECTURES_STATUS_PATCH.diff (targets exactly this decl, answer := True, formal_proof link to QuantumGraphColorRestriction.lean no_eqSystem6_d5_int) after re-running verify.sh.
- **`Paper/MonochromaticQuantumGraph.lean:eqSystem6_no_solution_d5_trinary_int`** (cat 0, conf high, L8, medium) — Apply FORMAL_CONJECTURES_STATUS_PATCH.diff (targets this decl via no_eqSystem6_d5_trinary_int).
- **`Paper/MonochromaticQuantumGraph.lean:eqSystem6_no_solution_ge3_int`** (cat 0, conf high, L8, medium) — Apply the status patch (no_eqSystem6_ge3_int gives exactly the universally quantified statement) after certificate replay.
- **`Paper/MonochromaticQuantumGraph.lean:eqSystem6_no_solution_ge3_trinary_int`** (cat 0, conf high, L8, medium) — Apply the status patch (no_eqSystem6_ge3_trinary_int matches verbatim).
- **`GreensOpenProblems/14.lean:W_3_21_lower`** (cat 0, conf medium, L4, small) — Port zeros21 into the merged FunctionCertificateBridge bitmask pattern (as done for t=20), run kernel decide, apply W_ge_succ_of_checks, set answer(True); verify build.
- **`GreensOpenProblems/14.lean:W_3_22_lower`** (cat 0, conf medium, L4, small) — Port certificate to merged kernel bridge, set answer(True), prove via W_ge_succ_of_checks; verify build.
- **`GreensOpenProblems/14.lean:W_3_23_lower`** (cat 0, conf medium, L4, small) — Port certificate to merged kernel bridge, set answer(True), prove via W_ge_succ_of_checks; verify build.
- **`GreensOpenProblems/14.lean:W_3_24_lower`** (cat 0, conf medium, L4, small) — Port certificate to merged kernel bridge, set answer(True), prove via W_ge_succ_of_checks; verify build.
- **`GreensOpenProblems/14.lean:W_3_25_lower`** (cat 0, conf medium, L4, small) — Port certificate to merged kernel bridge, set answer(True), prove via W_ge_succ_of_checks; verify build.
- **`GreensOpenProblems/14.lean:W_3_26_lower`** (cat 0, conf medium, L4, small) — Port certificate to merged kernel bridge, set answer(True), prove via W_ge_succ_of_checks; verify build.
- **`GreensOpenProblems/14.lean:W_3_27_lower`** (cat 0, conf medium, L4, small) — Port certificate to merged kernel bridge, set answer(True), prove via W_ge_succ_of_checks; verify build.
- **`GreensOpenProblems/14.lean:W_3_28_lower`** (cat 0, conf medium, L4, small) — Port certificate to merged kernel bridge, set answer(True), prove via W_ge_succ_of_checks; verify build.
- **`GreensOpenProblems/14.lean:W_3_29_lower`** (cat 0, conf medium, L4, small) — Port certificate to merged kernel bridge, set answer(True), prove via W_ge_succ_of_checks; verify build.
- **`GreensOpenProblems/14.lean:W_3_30_lower`** (cat 0, conf medium, L4, small) — Port certificate to merged kernel bridge, set answer(True), prove via W_ge_succ_of_checks; verify build.
- **`GreensOpenProblems/14.lean:W_3_31_lower`** (cat 0, conf medium, L4, medium) — Port certificate to merged kernel bridge, set answer(True), prove via W_ge_succ_of_checks (N+1 = 931 > 930); verify build.
- **`GreensOpenProblems/14.lean:W_3_32_lower`** (cat 0, conf medium, L4, medium) — Port certificate to merged kernel bridge, set answer(True); verify build.
- **`GreensOpenProblems/14.lean:W_3_33_lower`** (cat 0, conf medium, L4, medium) — Port certificate to merged kernel bridge, set answer(True); verify build.
- **`GreensOpenProblems/14.lean:W_3_34_lower`** (cat 0, conf medium, L4, medium) — Port certificate to merged kernel bridge, set answer(True); verify build.
- **`GreensOpenProblems/14.lean:W_3_35_lower`** (cat 0, conf medium, L4, medium) — Port certificate to merged kernel bridge, set answer(True); verify build.
- **`GreensOpenProblems/14.lean:W_3_36_lower`** (cat 0, conf medium, L4, medium) — Port certificate to merged kernel bridge, set answer(True); verify build.
- **`GreensOpenProblems/14.lean:W_3_37_lower`** (cat 0, conf medium, L4, medium) — Port certificate to merged kernel bridge, set answer(True); verify build.
- **`GreensOpenProblems/14.lean:W_3_38_lower`** (cat 0, conf medium, L4, medium) — Port certificate to merged kernel bridge, set answer(True); verify build.
- **`GreensOpenProblems/14.lean:W_3_39_lower`** (cat 0, conf medium, L5, medium) — Port certificate to merged kernel bridge (bitmask form), set answer(True); verify build. If kernel decide is too slow at N = 1418, fall back to native_decide subject to repo policy.

## 1. External solutions to import (category 1)  (4)

- **`Arxiv/2107.00295/IndependentDomination.lean:independentDominationEven`** (cat 1, conf high, L9, none) — Reclassify to research solved and port the Cho-Kim-Kim-Oum discharging proof plus the easy D=2 case; large effort (research-scale graph-theory formalization).
- **`GreensOpenProblems/14.lean:green_14_polynomial`** (cat 1, conf high, L10, none) — Report upstream: label should not be 'research open' as stated, and the statement likely misrenders Problem 14; either restate faithfully to Green's text or record answer(False) with the k-monotonicit
- **`ErdosProblems/42.lean:erdos_42.variants.constructive`** (cat 1, conf medium, L5, none) — Port/import the external Lean proof of erdos_42, set answer(True), and derive f from the atTop-eventually threshold via Classical.choice (f M := witness N0 for M >= 1, arbitrary for M = 0); verify the
- **`OpenQuantumProblems/23.lean:hasSICPOVM_56`** (cat 1, conf medium, L9, large) — Confirm against the primary source (Grassl's exact-solutions data / the 2025 JMP paper) which paper contains the d=56 fiducial; then answer := True. Formalizing the witness in Lean means verifying 313

## 2. Defective statements needing correction (categories 3, 4, 10)  (44)

- **`ErdosProblems/357.lean:erdos_357.parts.ii.bigO_version`** (cat 4, conf high, L1, none) — Tighten the encoding (e.g. require an explicit elementary function with a stated exponent) or accept as convention-guarded; do not count a trivial closure as progress.
- **`ErdosProblems/357.lean:erdos_357.parts.ii.bigO_version_symm`** (cat 4, conf high, L1, none) — Same as bigO_version: tighten encoding or treat as convention-guarded.
- **`ErdosProblems/357.lean:erdos_357.parts.ii.bigTheta_version`** (cat 4, conf high, L1, none) — Same as bigO_version.
- **`ErdosProblems/357.lean:erdos_357.parts.ii.littleO_version`** (cat 4, conf high, L1, none) — Same as bigO_version.
- **`ErdosProblems/357.lean:erdos_357.variants.monotone.parts.ii.bigO_version`** (cat 4, conf high, L1, none) — Tighten encoding or treat as convention-guarded.
- **`ErdosProblems/357.lean:erdos_357.variants.monotone.parts.ii.bigO_version_symm`** (cat 4, conf high, L1, none) — Tighten encoding or treat as convention-guarded.
- **`ErdosProblems/357.lean:erdos_357.variants.monotone.parts.ii.bigTheta_version`** (cat 4, conf high, L1, none) — Tighten encoding or treat as convention-guarded.
- **`ErdosProblems/357.lean:erdos_357.variants.monotone.parts.ii.littleO_version`** (cat 4, conf high, L1, none) — Tighten encoding or treat as convention-guarded.
- **`ErdosProblems/40.lean:erdos_40`** (cat 4, conf high, L1, none) — Report the trivialization upstream: the encoding needs a nontriviality constraint (e.g. require some divergent g in G, or state it for a specific g). As stated, 'exact fun g hg => absurd hg (Set.not_m
- **`ErdosProblems/409.lean:erdos_409.parts.i.isBigO`** (cat 4, conf high, L1, none) — Same as isTheta variant: accept as design-acknowledged placeholder or add a nontriviality spec.
- **`ErdosProblems/409.lean:erdos_409.parts.i.isTheta`** (cat 4, conf high, L1, none) — Acknowledge as design-accepted loophole; a real contribution would prove nontrivial bounds (e.g. c(n) << log n type results), which is research-level.
- **`ErdosProblems/409.lean:erdos_409.parts.iii`** (cat 4, conf high, L1, none) — Report upstream: answer must be stated as a function of p only (move alpha out of scope, e.g. 'HasDensity (answer p)'), and existence of the density should be part of the claim.
- **`ErdosProblems/409.lean:erdos_409.variants.sigma_isBigO`** (cat 4, conf high, L1, none) — Design-acknowledged placeholder.
- **`ErdosProblems/409.lean:erdos_409.variants.sigma_isTheta`** (cat 4, conf high, L1, none) — Design-acknowledged placeholder; treat as spec-weak.
- **`GreensOpenProblems/24.lean:green_24`** (cat 4, conf high, L1, none) — Respec as the asymptotic question (the file's variants.conjecture already does this); flag the echo loophole to maintainers.
- **`GreensOpenProblems/25.lean:green_25`** (cat 4, conf high, L1, none) — Respec as bound-improvement statements (the file's green_25.upper/.lower already do this); flag the echo loophole.
- **`GreensOpenProblems/27.lean:green_27.equivalent`** (cat 4, conf high, L1, none) — Flag echo loophole; prefer the .lower/.upper improvement forms in the same file.
- **`GreensOpenProblems/37.lean:green_37_asymptotic`** (cat 4, conf high, L1, none) — Report spec defect; replace with a genuine two-sided asymptotic statement (e.g. explicit upper/lower bound pairs, or IsTheta against a concrete elementary function).
- **`GreensOpenProblems/37.lean:green_37_theta`** (cat 4, conf high, L1, none) — Report spec defect; a meaningful version must quantify answer over a restricted grammar of functions or state concrete bounds.
- **`GreensOpenProblems/51.lean:green_51`** (cat 4, conf high, L1, none) — Restate as bracketing asymptotics (as the file's solved variants do) or add a closed-form requirement; treat any rfl-style closure as illegitimate.
- **`ErdosProblems/361.lean:erdos_361.bigO`** (cat 4, conf high, L2, none) — Fix the statement: remove the inner 'forall c' (use the outer c) and change the filter to exclude all B having a subset summing to n; then re-audit. Current statement closable by deriving False from h
- **`ErdosProblems/361.lean:erdos_361.bigTheta`** (cat 4, conf high, L2, none) — Fix statement as for bigO; current version closable by contradiction from hA 0 1 and hA 2 1.
- **`ErdosProblems/361.lean:erdos_361.smallO`** (cat 4, conf high, L2, none) — Fix statement as for bigO; current version closable by contradiction from hA 0 1 and hA 2 1.
- **`ErdosProblems/409.lean:erdos_409.parts.i`** (cat 4, conf high, L2, none) — Flag upstream that the encoding admits the sInf non-answer; a faithful version should demand a closed form or asymptotic with a nontriviality criterion (as the file's own note admits for the asymptoti
- **`ErdosProblems/409.lean:erdos_409.parts.i.isLittleO`** (cat 4, conf high, L2, none) — Same as the other asymptotic variants.
- **`ErdosProblems/409.lean:erdos_409.variants.sigma_isLittleO`** (cat 4, conf high, L2, none) — Design-acknowledged placeholder.
- **`ErdosProblems/357.lean:erdos_357.parts.ii.littleO_version_symm`** (cat 4, conf high, L3, none) — Same as bigO_version; note a non-degenerate answer o(n) would resolve parts.i.
- **`ErdosProblems/357.lean:erdos_357.variants.monotone.parts.ii.littleO_version_symm`** (cat 4, conf high, L3, none) — Tighten encoding or treat as convention-guarded.
- **`GreensOpenProblems/16.lean:green_16`** (cat 4, conf high, L3, none) — Tighten the spec (e.g. ask for asymptotics of f, or forbid self-referential answers by convention); the echo closure could be formalized quickly if one only wants to discharge the formal statement.
- **`GreensOpenProblems/31.lean:green_31.variants.sidon_01n`** (cat 4, conf high, L3, none) — Report defect upstream: use a distinct-pair Sidon/B_2 definition for F_2^n. Meanwhile the theorem closes with answer := False plus the two-element violation lemma and 1 < 2^{0.51 n}.
- **`GreensOpenProblems/4.lean:green_4`** (cat 4, conf high, L3, none) — Report spec defect upstream (answer should be an explicit family, e.g. the extremalFamily construction, with a proof of optimality). To close as-is: prove exists S, MaximalFor ProdFree ncard S by Fini
- **`GreensOpenProblems/31.lean:green_31.variants.abelian`** (cat 4, conf high, L4, none) — Report defect upstream: IsSidon needs the distinct-pair/group convention for 2-torsion groups. Meanwhile the formal theorem closes with answer := False, witness G := (Fin 14 -> ZMod 2), a two-element 
- **`GreensOpenProblems/37.lean:green_37`** (cat 4, conf high, L4, none) — Report the spec defect upstream (answer should be constrained to a closed form, or the statement replaced by two-sided explicit bounds). If closing as-is: prove nonemptiness with range((k-1)N+1) and a
- **`GreensOpenProblems/40.lean:green_40.variants.all_n`** (cat 4, conf high, L7, none) — Fix the statement to 'Tendsto f_all atTop (nhds top)'. Alternatively the current statement can be legitimately closed with answer(False) by formalizing bounded-density covering constructions (shortene
- **`Books/BugeaudDistributionModuloOne/Problem10_6.lean:problem_10_6_variant_2`** (cat 4, conf high, L9, none) — Either restrict to alpha > 1/2 (which restores openness) or reclassify as a corollary of Furstenberg. Closing the current formal statement requires formalizing Furstenberg's x2-x3 theorem plus the cou
- **`ErdosProblems/36.lean:erdos_36.variants.lower`** (cat 4, conf high, L9, none) — Either tighten the encoding to demand an explicit decimal strictly above 0.379005, or treat closure as 'formalize White 2022' (large effort).
- **`ErdosProblems/422.lean:erdos_422`** (cat 10, conf high, L10, none) — Redefine f before any proof attempt: e.g. an Option-valued/fuel-based total function or an inductively defined graph relation capturing the (possibly partial) recurrence; note PNat subtraction also tr
- **`ErdosProblems/422.lean:erdos_422.variants.eventually_const`** (cat 10, conf high, L10, none) — Same fix as erdos_422: redefine f, then re-state.
- **`ErdosProblems/422.lean:erdos_422.variants.surjective`** (cat 10, conf high, L10, none) — Same fix as erdos_422: redefine f, then re-state.
- **`GreensOpenProblems/41.lean:green_41`** (cat 4, conf high, L10, none) — Tighten the spec (e.g. require ans = o of the KrLe bound for the SAME C, or demand a fixed iterated-exp level lower). Closing the current formal statement still requires formalizing quantitative pyjam
- **`GreensOpenProblems/41.lean:green_41.variants.exists_better_bound`** (cat 4, conf high, L10, none) — Replace by a spec that quantifies the improvement (e.g. double-exponential or polynomial bound). Formal closure = answer(True) + formalizing KrLe (research-scale).
- **`Books/UniformDistributionOfSequences/Equidistribution.lean:isAccumulationPoint_three_halves_pow`** (cat 4, conf medium, L5, none) — Close the formal statement via answer := Filter.limsup (fun n => Int.fract ((3/2)^n)) atTop: prove fract((3/2)^n) = (3^n % 2^n)/2^n, oddness of 3^n % 2^n, pairwise distinctness, then limsup-is-cluster
- **`Books/UniformDistributionOfSequences/Equidistribution.lean:isEquidistributedModuloOne_transcendental_three_halves_pow`** (cat 3, conf medium, L9, none) — Flag for correction upstream: weaken to 'for almost every x' (Koksma/Weyl metric theorem, provable but nontrivial) or delete. Formally refuting the current statement in Lean would require a Peres-Schl
- **`ErdosProblems/36.lean:erdos_36`** (cat 4, conf medium, L9, none) — Tighten encoding (e.g. require a closed-form or high-precision decimal with matching Tendsto proof), or treat closure as 'formalize Haugland's limit-existence theorem' (large effort).

## 3. Easy direct Lean proofs (category 2)  (4)

- **`ErdosProblems/422.lean:erdos_422.variants.growth_rate`** (cat 2, conf high, L1, none) — Either close formally with answer g := (fun n => (f n : R)) via Asymptotics.isBigO_refl, or (better) flag upstream: fix the definition of f and use an encoding that forces a nontrivial comparison func
- **`GreensOpenProblems/37.lean:green_37_bigO`** (cat 2, conf high, L1, none) — Close via isBigO_refl if a formal resolution is wanted, but better: report spec defect (statement should demand a bound of a specific sharp shape).
- **`ErdosProblems/416.lean:erdos_416.parts.ii`** (cat 2, conf high, L2, none) — Close with answer f := V: for x >= 1, V x >= 1 (1 = phi(1) is counted), so V x / V x is eventually 1 and Tendsto follows by congruence with the constant 1. Alternatively flag upstream for a better enc
- **`GreensOpenProblems/37.lean:green_37_littleO`** (cat 2, conf high, L2, none) — Close via the f*N trick if desired; report spec defect upstream.

## 4. Small certificate-based finite problems (category 6, small compute)  (0)


## 5. Mathematically solved, moderate formalization (category 5)  (8)

- **`ErdosProblems/357.lean:erdos_357.variants.hegyvari`** (cat 5, conf high, L7, none) — Relabel to research solved and formalize Hegyvari's proof; effort medium-large (combinatorial construction for the lower bound plus a counting upper bound).
- **`ErdosProblems/44.lean:erdos_44.variants.empty_start`** (cat 5, conf high, L8, none) — Formalize (large effort): Bose-Chowla Sidon construction over F_{q^2} (discrete logs in the cyclic unit group, quadratic-uniqueness argument) plus prime-ratio-tends-to-1 from PNT (available in Lean vi
- **`ErdosProblems/1084.lean:erdos_1084.variants.triangular_optimal_d2`** (cat 5, conf high, L9, none) — Relabel as research solved citing Harborth 1974 and attempt formalization: lower bound from the explicit hexagonal-lattice configuration (medium), upper bound via Harborth's convex-position/boundary i
- **`GreensOpenProblems/16.lean:green_16_lower_bound`** (cat 5, conf medium, L7, none) — Retag research solved; formalize Ruzsa's Sidon-type construction for this invariant equation - medium effort (construction plus counting).
- **`GreensOpenProblems/16.lean:green_16_upper_bound`** (cat 5, conf medium, L9, none) — Retag research solved; formalization is research-scale (almost-periodicity machinery, Fourier analysis on Z).
- **`GreensOpenProblems/19.lean:green_19.lower`** (cat 5, conf medium, L9, none) — Retag research solved; formalize Mandache's (or directly FSSZ's) lower-bound construction plus the sInf bookkeeping - large effort (probabilistic/entropy construction).
- **`GreensOpenProblems/19.lean:green_19.upper`** (cat 5, conf medium, L9, none) — Retag research solved; formalizing Mandache's positive result needs heavy regularity/analytic machinery - research-scale.
- **`Paper/CasasAlvero.lean:casas_alvero_conjecture`** (cat 5, conf medium, L10, none) — Monitor refereeing of Ghosh's proof; formalization would be research-scale (Koszul homology machinery absent from Mathlib). Keep category open in repo until the proof is refereed, then flip to solved 

## 6. Tractable unsolved with clear strategies (category 7 + heavier 6)  (2)

- **`Paper/MonochromaticQuantumGraph.lean:eqSystem8_no_solution_d3_int`** (cat 6, conf medium, L8, large) — Extend the QuantumGraphN6D3 pipeline: reduce mod 2 (ring hom argument is N-generic), classify odd-perfect-matching diagonal supports of K8 up to S_8, emit one CNF per orbit (252 GF(2) weight variables
- **`Paper/MonochromaticQuantumGraph.lean:eqSystem8_no_solution_d3_trinary_int`** (cat 6, conf medium, L8, large) — Follows for free from any N=8 integer resolution (trinary subset of Z); or attack directly as a finite CSP - but the mod-2 SAT route is strictly easier and already suffices, so extend the N=6 pipeline

## 7. Deep research problems (category 8)  (230)

230 problems — see per-directory reports; not individually queued.

## 8. Major open problems (category 9)  (66)

66 problems — see per-directory reports; not individually queued.
