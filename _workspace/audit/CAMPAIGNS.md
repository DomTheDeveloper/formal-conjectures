# Internal solving campaigns

This fork contains substantial proof work that is **not connected to the canonical problem statements**.
This register maps each campaign to the statement it targets and records what state the proof is in.
Produced by static inspection of the working tree, `.github/workflows/`, git history, and the GitHub API.

`canonical_still_open = true` means the proof exists but the catalog theorem still says `sorry` —
these are the repository's cheapest wins, and they are why category 0 exists.

> No campaign below was rebuilt or re-audited here. Every axiom-audit claim is the campaign's
> own assertion, recorded as such. Re-run the build and `#print axioms` before trusting any of them.

## Summary

| Campaign | Proof state | Canonical still open | Next action |
|---|---|---|---|
| `wowii-143` | complete-proof-in-repo | **yes** | Port proof to the canonical conjecture143 statement (or submit upstream PR) and flip category t |
| `wowii-314` | complete-proof-in-repo | no | Nothing locally — solved in canonical file on fork main; confirm upstream PR #4496 outcome and  |
| `wowii-316` | complete-proof-in-repo | **yes** | Port proof to canonical conjecture316 / upstream PR |
| `wowii-59` | partial | **yes** | Verify build of audit/wowii59-clean-final (or agent/solve-wowii-59), then merge the disproof in |
| `wowii-145` | certificates-only | **yes** | Recover/merge agent/solve-wowii-145-current into canonical GraphConjecture145.lean (or add a Fo |
| `quantum-n6d3-color-restriction` | complete-proof-in-repo | **yes** | Apply FORMAL_CONJECTURES_STATUS_PATCH.diff (wire answers/formal_proof links into canonical file |
| `rna-quasipowers` | complete-proof-in-repo | no | Nothing — merged on fork main with audit harness; optionally submit upstream |
| `a100434` | complete-proof-in-repo | no | Nothing — already merged to fork main; optionally reconcile audit branch extras (auxiliary iden |
| `a147983-chomp-10x42` | partial | **yes** | Investigate whether a147983-generate-explicit-proof ever completed (check Actions artifacts 'co |
| `chomp-native-experiment` | workflow-only | **yes** | Nothing to port — treat as scaling experiment for the A147983 kernel campaign |
| `a226247-kagey137` | complete-proof-in-repo | **yes** | Merge branch solve-a226247-1000 (or a ready/* descendant) into main; then remove the temporary  |
| `a261865-kagey13` | complete-proof-in-repo | no | Nothing — merged on fork main; run lake build to reconfirm, restore category attribute for cata |
| `a343881-kagey16` | complete-proof-in-repo | **yes** | Merge ci/oeis-a343881-warning-free (or ready/a343881-gdm-20260723) into main and add an axiom a |
| `geode5-1000` | complete-proof-in-repo | **yes** | Verify build of audit-geode5-crt-proof (run geode5-current-proof-audit), then merge Geode5Defs  |
| `litt-most-unfair-bet` | partial | unknown | Trigger litt-final-current-audit (workflow_dispatch) against audit/litt-final-current-main; if  |
| `w320-green14` | complete-proof-in-repo | **yes** | Port: answer(True) + proof via W_3_20_lower_fast into the canonical W_3_20_lower in 14.lean |
| `worldcup7` | workflow-only | **yes** | Investigate whether a Lean proof is feasible (finite but astronomically large count) or relabel |
| `restricted-run-tableaux` | partial | **yes** | Investigate branch agent/restricted-run-tableaux-final for how far the reduction got; merge the |

## Detail

### wowii-143

**Proof state:** complete-proof-in-repo · **Canonical still open:** yes

**Canonical target(s):**
- `FormalConjectures/WrittenOnTheWallII/GraphConjecture143.lean:conjecture143`

**Evidence:**
- WOWII/GraphConjecture143{Proof,Next,Leaves,Boundary,CycleAttach,ZZFinal}.lean (conjecture143_proved, doc: 'complete modular, sorry-free proof')
- FormalConjectures/WrittenOnTheWallII/GraphConjecture143ForkProof.lean (conjecture143_fork_proof wrapper, in-file #print axioms)
- lakefile.toml WOWII lean_lib ('Fork-hosted complete Lean proofs that are linked from upstream metadata')
- branches: wowii-143-solved, wowii-143-solved-clean, merge/wowii143-full-proof, cleanup/wowii143-canonical-proof-link, proof/wowii143-canonical-path

**Kernel-verification claim (as asserted by the campaign):** In-file #print axioms on conjecture143_fork_proof; no sorry, no native_decide/bv_decide anywhere in WOWII/ on main; pure tactic proof built by lake as part of the FormalConjectures lib (via ForkProof import).

**Trust caveats:**
- Canonical theorem conjecture143 in GraphConjecture143.lean is untouched: still @[category research open] with sorry; the proof lives in a parallel *_fork_proof theorem
- Axiom printout output not captured in repo; must be re-run to confirm [propext, Classical.choice, Quot.sound]

**Next action:** Port proof to the canonical conjecture143 statement (or submit upstream PR) and flip category to research solved

### wowii-314

**Proof state:** complete-proof-in-repo · **Canonical still open:** no

**Canonical target(s):**
- `FormalConjectures/WrittenOnTheWallII/GraphConjecture314.lean:conjecture314`

**Evidence:**
- WOWII/ZZGraphConjecture314*.lean (18 modules; final theorem conjecture314_proved in ZZGraphConjecture314Final.lean)
- FormalConjectures/WrittenOnTheWallII/GraphConjecture314.lean now @[category research solved] and proved via conjecture314_proved (no sorry)
- FormalConjectures/WrittenOnTheWallII/GraphConjecture314Proof.lean ('Verification harness for the CRL proof', #print axioms conjecture314_proved)
- FormalConjectures/WrittenOnTheWallII/GraphConjecture314Core.lean (largestInducedPathSize definition)
- branches: upstream/wowii-314-solved(-clean), proof/wowii-314-numbered, proof/wowii314-upstream, fix/wowii314-final-verified, audit/wowii314-crl; upstream PR #4496 referenced in _certificates/145Certificate.md

**Kernel-verification claim (as asserted by the campaign):** #print axioms conjecture314_proved in GraphConjecture314Proof.lean plus an example re-checking the exact theorem type; no sorry, no native_decide in the WOWII proof modules.

**Trust caveats:**
- Statement was DISAMBIGUATED by the fork: earlier revisions used SimpleGraph.path (floor of average distance); the solved statement uses largestInducedPathSize. The proved theorem is therefore not literally the earlier upstream formalization
- Canonical file solved only in this fork; upstream merge status unverified

**Next action:** Nothing locally — solved in canonical file on fork main; confirm upstream PR #4496 outcome and that the disambiguated invariant is accepted upstream

### wowii-316

**Proof state:** complete-proof-in-repo · **Canonical still open:** yes

**Canonical target(s):**
- `FormalConjectures/WrittenOnTheWallII/GraphConjecture316.lean:conjecture316`

**Evidence:**
- WOWII/WotW316*.lean (8 modules; final theorem conjecture316_solved in WotW316Final.lean)
- FormalConjectures/WrittenOnTheWallII/GraphConjecture316ForkProof.lean (conjecture316_fork_proof wrapper, in-file #print axioms)
- branches: agent/solve-wotw316, agent/wotw316-verification, upstream/wowii-316-solved, merge/wowii316-full-proof

**Kernel-verification claim (as asserted by the campaign):** In-file #print axioms on conjecture316_fork_proof; sorry-free WOWII modules, no native_decide.

**Trust caveats:**
- Canonical conjecture316 still @[category research open] with sorry; proof only exposed as conjecture316_fork_proof
- Axiom output must be re-generated to confirm no extra axioms

**Next action:** Port proof to canonical conjecture316 / upstream PR

### wowii-59

**Proof state:** partial · **Canonical still open:** yes

**Canonical target(s):**
- `FormalConjectures/WrittenOnTheWallII/GraphConjecture59.lean:conjecture59`

**Evidence:**
- .github/workflows/wowii59-clean-audit.yml (builds GraphConjecture59, #print axioms WrittenOnTheWallII.GraphConjecture59.conjecture59, rejects sorryAx/ofReduceBool/trustCompiler; CI-applies bv_decide patch and pushes it back)
- .github/workflows/wowii59-source-repair.yml, one-shot-repair-wowii59.yml (rewrites theorem into explicit disproof: counterexample counterG on Fin 18, residue=10, b>=17, largestInducedForestSize<=13 < ceil(sqrt(170))), one-shot-wow59-linear-branch.yml (Scratch/WOWII59CycleBridgeTest.lean interval_cases certificate)
- commits 6f3688f, df6ebaf, ac48523, de9a4b1, 9ea6d06 ('Use verified bv_decide certificates for WOWII 59'), 1c8454f ('Restore the two WOWII 59 bit-vector certificates idempotently')
- branches (all still exist): agent/solve-wowii-59, audit/wowii59-clean-current, audit/wowii59-clean-final, audit/wowii-59-ci, trigger/wowii59-repair, submit/wowii59-current

**Kernel-verification claim (as asserted by the campaign):** Workflow gate: no sorry/admit/native_decide/axiom/unsafe/opaque in source, and axiom audit of conjecture59 must not contain sorryAx, Lean.ofReduceBool, or Lean.trustCompiler. The two finite certificates (residue of counterG = 10; every 14-subset of Fin 18 contains a listed clique/structure) are discharged with bv_decide (kernel-checked LRAT) with a plain-decide fallback in the repair workflow.

**Trust caveats:**
- The finished disproof exists only on branches; parts of it are constructed BY CI (workflows patch the .lean source during the run and push back), so the exact final source depends on branch head + workflow-applied edits
- This is a disproof: it needs the canonical statement quantified over the vertex type (repair inserts 'hP (Fin 18) counterG'), i.e. the canonical statement shape was adjusted on the branch
- No committed audit log in the repo confirming the CI run passed

**Next action:** Verify build of audit/wowii59-clean-final (or agent/solve-wowii-59), then merge the disproof into the canonical file

### wowii-145

**Proof state:** certificates-only · **Canonical still open:** yes

**Canonical target(s):**
- `FormalConjectures/WrittenOnTheWallII/GraphConjecture145.lean:conjecture145`

**Evidence:**
- _certificates/145Certificate.md (novelty/priority audit dated 2026-07-21; solution branch DomTheDeveloper:agent/solve-wowii-145-current)
- branches (all still exist): agent/solve-wowii-145-current, agent/solve-wowii-145(-clean), agent/wowii-145-proof, wowii-145-proof-20260721, solve-wowii-145-{proof,geodesic,standalone,root-audit,final-audit-webtest}
- External immutable standalone proof: DomTheDeveloper/crl commit 2ee448baa80c98f0c8b9a0c1c3d9421200f99aa5 math/wowii145/WOW145/145.lean; fork verification PRs #59/#60, crl PR #190; upstream submission commit 39297c37f51d2af2142af316f40d95f13c359e84

**Kernel-verification claim (as asserted by the campaign):** 145Certificate.md asserts: pinned Lean 4.27.0 build passed and terminal axiom audit reported exactly [propext, Classical.choice, Quot.sound]; no sorryAx, admit, native_decide, or project-specific axiom.

**Trust caveats:**
- The proof itself is not on the fork's main branch — only the certificate document is; the Lean proof lives on agent/solve-wowii-145-current (branch still exists, NOT deleted) and in the external crl repository
- Certificate is a self-produced audit; axiom claim not independently reproduced here

**Next action:** Recover/merge agent/solve-wowii-145-current into canonical GraphConjecture145.lean (or add a ForkProof wrapper like 143/316) and re-run the axiom audit

### quantum-n6d3-color-restriction

**Proof state:** complete-proof-in-repo · **Canonical still open:** yes

**Canonical target(s):**
- `FormalConjectures/Paper/MonochromaticQuantumGraph.lean:eqSystem6_no_solution_d3_int`
- `FormalConjectures/Paper/MonochromaticQuantumGraph.lean:eqSystem6_no_solution_d5_int`
- `FormalConjectures/Paper/MonochromaticQuantumGraph.lean:eqSystem6_no_solution_ge3_int`
- `FormalConjectures/Paper/MonochromaticQuantumGraph.lean:eqSystem6_no_solution_d5_trinary_int (via status patch)`
- `FormalConjectures/Paper/MonochromaticQuantumGraph.lean:eqSystem6_no_solution_ge3_trinary_int`

**Evidence:**
- QuantumGraphN6D3/ (README, 47 QuantumGraphCaseNNCertificate.lean, QuantumGraph{CompactLRAT,Semantic,OrbitData,OrbitBridge,ParityBridge,AllCases,Global,AxiomAudit}.lean, orbit_data/, setup_certificates.sh, verify.sh; final theorems QuantumGraphGlobal.no_eqSystem_{zmod2,int,trinary_int})
- QuantumGraphColorRestriction.lean (repo root; color-embedding restriction; terminal theorems no_eqSystem6_d5_int, no_eqSystem6_ge3_int, no_eqSystem6_d5_trinary_int, no_eqSystem6_ge3_trinary_int; 8 in-file #print axioms)
- QuantumGraphN6D3/COLOR_RESTRICTION_AUDIT.md; QuantumGraphN6D3/FORMAL_CONJECTURES_STATUS_PATCH.diff (unapplied patch flipping the 4 int/trinary conjectures to research solved with formal_proof links)
- .github/workflows/quantum_full_color_restriction_audit.yml (downloads+hash-checks certificate bundle, replays verify.sh, compiles color restriction with cert dir on LEAN_PATH, rejects sorryAx)
- branches: agent/quantum-n6d3-full-proof-color-restriction, agent/quantum-n6-all-colors-gdm*, audit/quantum-* (many)

**Kernel-verification claim (as asserted by the campaign):** README: axiom audit contains no sorryAx, but LRAT certificates and orbit tables are evaluated by Lean's native reflected machinery, so the audit lists Lean.ofReduceBool AND Lean.trustCompiler in addition to the standard axioms. Color-restriction layer itself is escape-free (workflow greps out sorry/admit/native_decide/unsafe/axiom/opaque in that file).

**Trust caveats:**
- Depends on Lean.ofReduceBool / Lean.trustCompiler (compiler-trusted reflected LRAT checking) — weaker than a pure-kernel proof
- 47 LRAT certificates are NOT in the repo: downloaded from a release asset on a THIRD-PARTY fork (github.com/infinityscroll/formal-conjectures, quantum-graph-n6d3-clrat-v1.tar.zst) pinned by SHA-256
- Proof modules are outside the lake build (compiled manually by verify.sh with LEAN_PATH); pinned to upstream commit 8f6e7457...
- Canonical statements in FormalConjectures/Paper/MonochromaticQuantumGraph.lean are still @[category research open] with answer(sorry) — FORMAL_CONJECTURES_STATUS_PATCH.diff was never applied
- Covers only ℤ and {-1,0,1} coefficients; the ℝ≥0/ℝ/ℂ N=6 conjectures remain open and are NOT claimed

**Next action:** Apply FORMAL_CONJECTURES_STATUS_PATCH.diff (wire answers/formal_proof links into canonical file) after re-running verify.sh + certificate download; consider a pure-kernel (non-native) replay to drop trustCompiler

### rna-quasipowers

**Proof state:** complete-proof-in-repo · **Canonical still open:** no

**Canonical target(s):**
- `FormalConjectures/Arxiv/2602.19255/RNAQuasiPowers.lean:grammar_discriminant_eq_radicand`
- `FormalConjectures/Arxiv/2602.19255/RNAQuasiPowers.lean:quasiPowers_algebraic_certificate`
- `FormalConjectures/Arxiv/2602.19255/RNAQuasiPowers.lean:printed_density_not_standardized`
- `FormalConjectures/Arxiv/2602.19255/RNAQuasiPowers.lean:gaussian_precision_correction`
- `FormalConjectures/Arxiv/2602.19255/RNAQuasiPowers.lean:three_track_certificate`

**Evidence:**
- RNAQuasiPowers/ root library (Radicand, GeneratingFunction, GoldenRoot, Covariance, DensityCorrection, GaussianPrecision, ImplicitDerivatives, AlgebraicCertificate, AxiomAudit.lean) + RNAQuasiPowers.lean root module; registered as lean_lib in lakefile.toml
- FormalConjectures/Arxiv/2602.19255/RNAQuasiPowers.lean (5 theorems, all @[category research solved], zero sorry on main) + RNAQuasiPowersAxiomAudit.lean
- .github/workflows/rna-quasipowers-kernel-audit.yml (lake --wfail build RNAQuasiPowers + FormalConjectures, runs both axiom-audit files, greps out sorryAx/trustCompiler/ofReduce)
- branches: rna-quasipowers-upstream, agent/rna-quasipowers-gdm-final, agent/rna-density-erratum, submit/rna-quasipowers-certificates*

**Kernel-verification claim (as asserted by the campaign):** Dedicated axiom-audit files (#print axioms on all 6 internal + 5 public declarations) with CI grep forbidding sorryAx, Lean.trustCompiler, Lean.ofReduce(Bool); pinned toolchain lean4:v4.27.0.

**Trust caveats:**
- Statements are the campaign's own formalization of results/errata about arXiv:2602.19255 (incl. an erratum-style 'printed density not standardized' claim), not pre-existing upstream conjecture statements
- Upstream (google-deepmind) merge status unverified

**Next action:** Nothing — merged on fork main with audit harness; optionally submit upstream

### a100434

**Proof state:** complete-proof-in-repo · **Canonical still open:** no

**Canonical target(s):**
- `FormalConjectures/OEIS/100434.lean:a100434_conjecture_false`

**Evidence:**
- FormalConjectures/OEIS/100434.lean on main: @[category research solved] theorem a100434_conjecture_false (auxiliary-sequence identity conjecture from OEIS A100434 is FALSE, counterexample n=2, norm_num proof; zero sorry)
- .github/workflows/a100434-focused-audit.yml (checks out branch audit/a100434-exact-ci, compiles the file, audits OeisA100434.a100434_auxiliary_identities, rejects sorryAx/ofReduceBool/trustCompiler)
- commits 6dd04ba..13096b2 (11 audit-iteration commits at top of main history)
- branches: audit/a100434-exact-ci, audit/a100434-proof-candidate(-current), work/a100434-primary-proof, proof/a100434-primary-final, submit/oeis-a100434*, merge/oeis-a100434, add/oeis-a100434

**Kernel-verification claim (as asserted by the campaign):** CI axiom audit with sorryAx/ofReduceBool/trustCompiler rejection (on the audit branch); main-tree proof is a short elementary norm_num disproof.

**Trust caveats:**
- The audited theorem name (a100434_auxiliary_identities) exists only on the audit branch, not on main — main carries only the disproof theorem
- Problem statement (the OEIS-comment identity conjecture) was formalized by the campaign itself; attribution note: 'produced by ProofOrchestrator, using OpenAI GPT-5.6 Thinking'

**Next action:** Nothing — already merged to fork main; optionally reconcile audit branch extras (auxiliary identities) into main

### a147983-chomp-10x42

**Proof state:** partial · **Canonical still open:** yes

**Canonical target(s):**
- `UNKNOWN — no FormalConjectures/OEIS/147983.lean exists on main (searched FormalConjectures/ for '147983' and 'chomp'); target statement lives only on branch proof/oeis-a147983-chomp-kernel as OeisA147983.chomp_10_by_42_has_three_winning_openings`

**Evidence:**
- branch proof/oeis-a147983-chomp-kernel: FormalConjectures/OEIS/A147983/{ChompRank,Game,KernelPSet,KernelCertificate,MDDCertificate,StrategyCertificate,SparseStrategyData,MoveClosureCertificate,SymbolicCertificate,ClosedResponseSet,ResponseCertificate,DirectResponseCertificate,RankedDeterminacy}.lean
- branch proof-artifacts/oeis-a147983-chomp: ProofArtifacts/OEIS/A147983/*.cpp (chomp_export_p_ranks, chomp_p_mdd_serialize, chomp_compact_carrier, chomp_compact_export, chomp_strategy_mdd; exact counts P=107,342,138 / 16.9M MDD nodes hard-coded as CI assertions)
- workflows: a147983-kernel-audit.yml (module builds + 11-theorem #print axioms audit incl. three_openings_of_symbolic_certificate), a147983-generate-explicit-proof(.yml/-macos.yml) (regenerate stream -> emit explicit Lean proof terms -> audit OeisA147983.chomp_10_by_42_has_three_winning_openings), a147983-compact-carrier/-export/-strategy-measure/-reachable-strategy/-prestrategy-mdd
- commits 8f8708e, 803c09f, ff1dcf5, 7e74163, 248ea4a, b6f808b, 3906cbd, 382e46a, 9e44ae7 ('Measure A147983 carriers beyond the premature 100k gate'), 270696a, 0e13e4e ('Raise separated Chomp strategy gate to 10m states'), f5004f1, 5fabc5b, 4ebd26f, 68b2a9e

**Kernel-verification claim (as asserted by the campaign):** Kernel-audit workflow explicitly FORBIDS sorry/admit/native_decide/axiom and rejects sorryAx/Lean.trustCompiler/Lean.ofReduce(Bool) in the axiom printout — the certificate framework is designed to be pure-kernel. The explicit-proof-generation workflows (Linux/macOS 'race') would produce and audit the final theorem chomp_10_by_42_has_three_winning_openings.

**Trust caveats:**
- The framework (conditional theorems: certificate => three openings) is complete on the branch, but the full explicit 10x42 strategy certificate is machine-generated in CI from C++ exporters and the commit history shows the size/feasibility gates were still being raised (100k -> 500k -> 10m states) — no committed artifact proves the end-to-end run finished
- Certificate data generated by untrusted C++ programs; trust reduces to the Lean-side replay, which is fine only if the generated Lean file was actually built
- No canonical A147983 problem statement exists in FormalConjectures/ on main

**Next action:** Investigate whether a147983-generate-explicit-proof ever completed (check Actions artifacts 'concrete-proof-axioms.log'); if yes, commit the generated proof and add a canonical OEIS/147983 statement file

### chomp-native-experiment

**Proof state:** workflow-only · **Canonical still open:** yes

**Canonical target(s):**
- `UNKNOWN — supports a147983-chomp-10x42; FormalConjectures/Paper/ChompThreeOpeningsNative.lean exists only at pinned commit 0e5ff5b9bbef619bebfe9e6e04e212ed6a3f7d53, not on main`

**Evidence:**
- .github/workflows/chomp-native-proof-audit.yml (checks out immutable commit 0e5ff5b9..., builds FormalConjectures.Paper.ChompThreeOpeningsNative under /usr/bin/time; triggered from ci/chomp-native-final-audit* branches)
- FormalConjectures/Paper/ChompThreeOpeningsNative.lean@0e5ff5b9: bit-packed retrograde Chomp search Engine; only checked fact is 'example : exactSearch 6 13 2 = true := by native_decide'
- branches: ci/chomp-native-final-audit .. -6, work/chomp-native-proof(-v2,-v3), proof/chomp-three-openings-{v1,clean}, audit/chomp-three-openings-reduction(-v2)

**Kernel-verification claim (as asserted by the campaign):** None — uses native_decide (Lean.ofNat/ofReduceBool compiler trust) and the checked instance is a small 6x13 smoke case, not 10x42; file has no theorem about the actual A147983 claim.

**Trust caveats:**
- native_decide; partial defs; measures runtime feasibility rather than proving the target
- Lives only at a pinned commit reachable from ci/chomp-native-final-audit* branches

**Next action:** Nothing to port — treat as scaling experiment for the A147983 kernel campaign

### a226247-kagey137

**Proof state:** complete-proof-in-repo · **Canonical still open:** yes

**Canonical target(s):**
- `UNKNOWN on main — file only on branch: FormalConjectures/OEIS/226247.lean:{blue_iff_negative, depth_is_shortest, rank_recurrence} (branch solve-a226247-1000); no 226247 reference anywhere in FormalConjectures/ on main`

**Evidence:**
- branch solve-a226247-1000: complete sorry-free file (canonical shortest-path tree for x->x+1 / x->-1/x from 0; proves blue vertices <=> negative value, canonical depth minimality, and rank recurrence a(n)=a(n-1)+a(n-3) answering Kagey Problem 137); ends with three #print axioms
- .github/workflows/a226247-pr-audit.yml (pull_request_target, head.ref == solve-a226247-1000 + label ci:full; lake env lean -DwarningAsError=true on the file — a sorry warning would fail; posts PASS/FAIL comment)
- README.md line 3: 'Temporary A226247 raw compiler log' link to an Actions job log
- branches: agent/solve-oeis-a226247-kagey137, agent/a226247-focused-*, audit/oeis-a226247-*, submit/oeis-a226247-*, ready/a226247-gdm-20260723, mirror/gdm-e751-proof-a226247, cleanup/kagey-137-two-commit

**Kernel-verification claim (as asserted by the campaign):** Proof is elementary structural induction (simp/linarith/omega/rfl — no decide, no native_decide); compiled with warnings-as-errors in CI (sorry impossible); in-file #print axioms on all three research theorems. README links a raw compiler log as evidence of a passing run.

**Trust caveats:**
- Not merged to main — main has no OEIS/226247.lean at all
- The README's 'temporary raw compiler log' is an expiring GitHub API link

**Next action:** Merge branch solve-a226247-1000 (or a ready/* descendant) into main; then remove the temporary README log link

### a261865-kagey13

**Proof state:** complete-proof-in-repo · **Canonical still open:** no

**Canonical target(s):**
- `FormalConjectures/OEIS/261865.lean:density_formula (OEIS A261865 / Kagey Problem 13 natural-density formula)`

**Evidence:**
- main tree: FormalConjectures/OEIS/261865.lean (density_formula := density_formula_solution; zero sorry), 261865Solution.lean, A261865Base.lean, 261865FinalAudit.lean (density_formula_final_audit harness)
- foundation files merged: FormalConjecturesForMathlib/NumberTheory/SquarefreeRadical.lean, FormalConjecturesForMathlib/Analysis/Equidistribution/{UnitAddTorus,TerminalBox,UnitAddCircleArc,...}.lean (zero sorry)
- .github/workflows/a261865-foundation-autofix-main.yml + a261865-repair-pass2.yml (CI patch-bots that rewrote proofs on branch a261865-research; commit msg 'Fix A261865 Lean foundation errors from AXLE')
- branches: a261865-research, ci/a261865-repair-pass{2,3}, solve-oeis-a261865, submit/oeis-a261865-solved, rewrite/oeis-a261865-two-commit

**Kernel-verification claim (as asserted by the campaign):** 261865FinalAudit.lean re-derives the theorem as density_formula_final_audit (audit-by-reproof harness). No native_decide/bv_decide observed; analytic equidistribution proof through the ForMathlib layers.

**Trust caveats:**
- Docstring attribution: 'produced by ProofOrchestrator, using OpenAI GPT-5.6 Thinking' (and CI commit references 'AXLE') — machine-generated proof, human review status unknown
- density_formula carries no @[category] attribute and uses the newer module/public syntax — diverges from repo statement conventions; upstream merge status unverified
- Proof was partially assembled by CI patch workflows performing exact string rewrites

**Next action:** Nothing — merged on fork main; run lake build to reconfirm, restore category attribute for catalog consistency

### a343881-kagey16

**Proof state:** complete-proof-in-repo · **Canonical still open:** yes

**Canonical target(s):**
- `UNKNOWN on main — file only on branches: FormalConjectures/OEIS/343881.lean:{conjecture (answer(False)), twelve_seventy_two_not_candidate} (branch ci/oeis-a343881-warning-free)`

**Evidence:**
- branch ci/oeis-a343881-warning-free: complete sorry-free DISPROOF of the OEIS A343881 eventual-value conjecture (k=12 counterexample via factorization determinant argument mod p; answer(False))
- .github/workflows/a343881-pr-audit.yml (pull_request_target gated to that branch + ci:full label; -DwarningAsError compile; PASS/FAIL PR comment)
- branches: solve/oeis-a343881, audit/oeis-a343881*, proof/oeis-a343881-current-*, submit/oeis-a343881*, ready/a343881-gdm-20260723, mirror/gdm-e751-*-a343881

**Kernel-verification claim (as asserted by the campaign):** Warnings-as-errors CI compile (sorry would fail); elementary kernel tactics only (norm_num/linear_combination/ZMod cast) — no decide/native_decide; no explicit #print axioms in-file.

**Trust caveats:**
- Not merged to main; no axiom-audit step in the workflow (compile-only)
- Statement formalized by the campaign itself (no pre-existing upstream file)

**Next action:** Merge ci/oeis-a343881-warning-free (or ready/a343881-gdm-20260723) into main and add an axiom audit

### geode5-1000

**Proof state:** complete-proof-in-repo · **Canonical still open:** yes

**Canonical target(s):**
- `FormalConjectures/Arxiv/2508.10245/Geode5.lean:geode5_1000 (hyper-Catalan 'Geode' diagonal value at n=1000, explicit ~3000-digit answer)`

**Evidence:**
- main: Geode5.lean has @[category research solved] geode5_1000 with answer(<huge integer>) but proof = sorry
- branch audit-geode5-crt-proof: Geode5.lean proves geode5_1000 := by simpa using Geode5Proof.geode5_1000_complete, zero sorry, in-file #print axioms; Geode5Proof/ has 36 modules (CRT, ModularRecurrence, RemainderTables, MomentAlgebra, HyperCatalanIntegrality, CastBridges, Complete, ...)
- workflows: geode5-current-proof-audit.yml (macOS, 6h, placeholder reject + build + axiom audit rejecting sorryAx/trustCompiler/ofReduce), geode5-arm-proof-audit.yml, geode5-windows-proof-audit.yml, geode5-proof-targeted.yml, geode5-arithmetic-targeted.yml (branch audit-geode5-arithmetic-proof), geode5-moment-algebra-audit.yml, geode5-table-maintenance.yml (CI self-patches RemainderTables.lean on the branch)
- commits 4609f18..ce18ce3 (install/fix Geode5 audits, 'Fix false-positive Geode5 placeholder gate', 'Audit the final Geode5 theorem on ARM'); branches solve-geode5-1000, agent/geode5-1000(-gdm), gdm-geode5-1000, upstream-main-geode5

**Kernel-verification claim (as asserted by the campaign):** Audit workflows build the final theorem and #print axioms geode5_1000, failing on sorryAx, Lean.trustCompiler, Lean.ofReduce(Bool) — i.e. a pure-kernel claim (CRT/recurrence certificate arithmetic, maxHeartbeats-heavy, no native_decide).

**Trust caveats:**
- Complete proof exists on branch audit-geode5-crt-proof only; main's canonical geode5_1000 is still sorry (yet already labeled research solved)
- Repeated multi-platform audit installs and a CI self-patch workflow (table-maintenance) show the branch was still being repaired; no committed log proves the final audit passed
- Extremely large kernel computation (giant literals, maxHeartbeats 1000000) — build should be re-verified

**Next action:** Verify build of audit-geode5-crt-proof (run geode5-current-proof-audit), then merge Geode5Defs + Geode5Proof + proved Geode5.lean into main

### litt-most-unfair-bet

**Proof state:** partial · **Canonical still open:** unknown

**Canonical target(s):**
- `UNKNOWN — campaign-created problem; no LittMostUnfairBet statement exists in FormalConjectures/ on main. (FormalConjectures/LittProblems/1.lean is a DIFFERENT Litt problem — Lam–Litt power-series algebraicity — and untouched by this campaign.) Branch target: FormalConjectures/Other/LittMostUnfairBet.lean:LittMostUnfairBet.most_unfair_litt_coin_word_bet and endpoint_flip_pair_attains`

**Evidence:**
- branch agent/litt-most-unfair-proof: 26 modules FormalConjectures/Other/LittMostUnfairBet*.lean (Defs, Proof, Reversal, Walsh energy/correlation/orbit/gap/two-endpoint decomposition) + LittMostUnfairBetProof.md + scripts/verify_litt_most_unfair.py
- final audit branch: audit/litt-final-current-main; also audit/litt-clean-current, audit/litt-final-20260722, agent/litt-most-unfair-final-clean, submit/litt-most-unfair-{current,solved}, trigger/litt-constant-repair
- workflows: litt-final-current-audit.yml (bf5f8b8 'Install trusted final Litt current-main audit': source-level ban on sorry/admit/native_decide/axiom/unsafe/opaque, lake build, #print axioms audit rejecting sorryAx/trustCompiler/ofReduce, exact finite replay via verify_litt_most_unfair.py --max-length 10, reports to fork PR 239), litt-most-unfair-check.yml, one-shot-litt-{h1int,h1int-direct,constant-gap,overlap-bridge,final-three,final-clean}.yml, one-shot-repair-litt.yml (7-block exact source rewrite)
- commits d43423c, 0a64733, 4c652ed, 105f66e, 5d3cca0, 5d4359b, bf5f8b8

**Kernel-verification claim (as asserted by the campaign):** Strongest audit gate in the repo: no sorry/admit/native_decide and no axiom/unsafe/opaque declarations allowed in source; terminal #print axioms must be free of sorryAx/Lean.trustCompiler/Lean.ofReduce; plus an independent exact finite replay in Python up to word length 10.

**Trust caveats:**
- At least six one-shot CI repair workflows successively rewrote the proof source on the branch — the proof went through many broken states; the 'trusted final' audit was installed at the very tip of main history and there is no committed evidence it passed
- Problem statement (Daniel Litt's most-unfair coin-word bet) was formalized by the campaign; no upstream canonical file exists to compare against
- Nothing merged to main; scripts/verify_litt_most_unfair.py exists only on the branch

**Next action:** Trigger litt-final-current-audit (workflow_dispatch) against audit/litt-final-current-main; if green, merge the module family + a canonical problem statement into main

### w320-green14

**Proof state:** complete-proof-in-repo · **Canonical still open:** yes

**Canonical target(s):**
- `FormalConjectures/GreensOpenProblems/14.lean:W_3_20_lower (line 218: answer(sorry) ↔ W 3 20 ≥ 389 := sorry)`

**Evidence:**
- main tree (merged, all zero sorry): FormalConjectures/GreensOpenProblems/Green14Core.lean, Green14FiniteExistence.lean, Green14OrderBridge.lean, Green14FunctionCertificateBridge.lean, Green14FastKernel20.lean (388-point coloring as a single Nat bitmask zeroMask20; theorem Green14.FastKernel.valid_20 by decide; theorem Green14.FastKernel.W_3_20_lower_fast : Green14.W 3 20 ≥ 389; two in-file #print axioms)
- .github/workflows/w320-pr-audit.yml (branch agent/w320-kernel-proof; builds Green14FastKernel20, audits both theorems, fails on sorryAx/Lean.ofReduceBool/Lean.trustCompiler)
- branches: agent/w320-{kernel-proof,exact-certificate,lower-kernel,lrat-kernel(-v2),proof-clean(-v2),hard-cube-split,great-grandchildren,upper-lean-bridge}, audit/green14-{bv-kernel,fast-kernel,kernel-decide,kernel-matrix-trigger}, submit/green14-w320-solved-gdm(-v2), agent/green14-certificates-20-39

**Kernel-verification claim (as asserted by the campaign):** Pure kernel decide (set_option maxHeartbeats 0) over a bitmask certificate; CI audit explicitly rejects sorryAx/ofReduceBool/trustCompiler, so the claim is kernel-only (no native_decide, and the earlier bv/LRAT kernel attempts were superseded).

**Trust caveats:**
- The proved theorem is Green14.FastKernel.W_3_20_lower_fast, a parallel statement; the canonical catalog theorem Green14.W_3_20_lower still ends in sorry with answer(sorry) unanswered on main
- Correctness also depends on the Green14OrderBridge/FunctionCertificateBridge reduction from the coloring certificate to Green's W definition — should be re-audited when porting

**Next action:** Port: answer(True) + proof via W_3_20_lower_fast into the canonical W_3_20_lower in 14.lean

### worldcup7

**Proof state:** workflow-only · **Canonical still open:** yes

**Canonical target(s):**
- `UNKNOWN on main — file only on branches: FormalConjectures/Other/WorldCup7.lean:seven_team_world_cup_polynomial (Zeilberger 2026 DIMACS challenge: degree-29 counting polynomial for 7-team score matrices)`

**Evidence:**
- branches: worldcup7-targeted-check-main, formalize-worldcup7-polynomial(-pr), worldcup7-final-lean-audit, worldcup7-lean-audit-clean, gdm-main-worldcup7-full-audit, ready/worldcup7-gdm-20260723
- .github/workflows/worldcup7-targeted.yml (branch prefix worldcup7-targeted-check; only compiles the file — no sorry gate, no axiom audit)
- ready/worldcup7-gdm-20260723 version inspected: main theorem is @[category research solved] but proof is `sorry`; two norm_num sanity tests (P(0)=1, P(1)=1854=!7) do compile; docstring links external computational verification repo DomTheDeveloper/ProofPlaygrond (recurrence, data, regression checks)

**Kernel-verification claim (as asserted by the campaign):** None for the main claim — only that the statement file compiles and the polynomial passes two point-evaluation sanity checks in Lean; the polynomial identity itself rests on external (non-Lean) enumeration/recurrence computations in ProofPlaygrond.

**Trust caveats:**
- Labeled research solved while the Lean proof is sorry — 'solved' reflects the external computational answer, not a formal proof
- Nothing on main; even the newest 'ready' branch has no proof

**Next action:** Investigate whether a Lean proof is feasible (finite but astronomically large count) or relabel; at minimum merge as an open answer(...)-style statement

### restricted-run-tableaux

**Proof state:** partial · **Canonical still open:** yes

**Canonical target(s):**
- `FormalConjectures/Arxiv/RestrictedRunTableaux.lean:conjecture_2a (Kauers–Zeilberger Conjecture 2a: G(n) ~ C1·8^n/n^4)`

**Evidence:**
- main tree: FormalConjectures/Arxiv/RestrictedRunTableaux.lean (statement, @[category research open], sorry) + FormalConjecturesForMathlib/Combinatorics/RestrictedRunTableaux.lean (definitions, zero sorry) — both merged
- workflows: restricted-run-tableaux-clean-pr-audit.yml (branch agent/restricted-run-tableaux-clean-reduction; builds ForMathlib RestrictedRunTableaux + RestrictedRunTableauxReduction + the Arxiv statement), restricted-run-tableaux-gdm-ready-audit.yml (branch agent/restricted-run-tableaux-gdm-ready)
- branches: proof/restricted-run-tableaux-reduction, agent/restricted-run-tableaux-{clean-reduction,gdm-ready,final,upstream,conjecture-2a,conjecture-2a-v2}

**Kernel-verification claim (as asserted by the campaign):** Compile-only PR audits (PASS/FAIL comment); no axiom audit. The Reduction module (ballot-word / transfer-matrix reduction layer) exists only on branches.

**Trust caveats:**
- conjecture_2a is a genuine asymptotic-with-unknown-constant statement; branch names ('reduction', 'conjecture-2a-v2') suggest partial reduction work, and there is no claim anywhere that the conjecture itself was proved

**Next action:** Investigate branch agent/restricted-run-tableaux-final for how far the reduction got; merge the reduction layer if it builds; canonical statement stays open

### OTHER-CAMPAIGNS-OBSERVED (aggregate, outside the requested list)

**Proof state:** unclear · **Canonical still open:** unknown

**Canonical target(s):**
- `merged sorry-free on main: FormalConjectures/Other/BeaverMathOlympiad8Proof.lean (bmo8; NOTE branch archive/invalid-bmo8-claim-20260723 signals an earlier retracted claim), FormalConjectures/WrittenOnTheWallII/GraphConjecture65.lean, GraphConjecture109.lean, GraphConjecture322.lean`
- `branch-only / still sorry on main: OEIS 317940, 308734, 281976, 287616, 280831, a263135 (many audit/proof branches incl. 'native' variants), a248380, a387471; WOWII 100, 146, 160 (correction), 217 (c217), WOWII 2; Paper/VoronovskajaTypeFormula (large verify-* branch family), Other/VCDimConvex (vc2 counterexample submit branches), Other/EquationalTheories_677_255, SchurTruncatedExponential, SuffixPrefixAvoidance, erdos602, erdos1150 (Parseval), erdos7, erdos-545 counterexample, checkerboard-all-n, sun-2-7-i / sun-214, bmo4, kagey-13/20`

**Evidence:**
- ~330 branches on the fork enumerated via GitHub API (agent/*, audit/*, proof/*, solve*/, submit/*, upstream/*, cleanup/*, mirror/*, work/*, ready/*)
- main-tree files listed above; emergency-stop-actions.yml + queue-drain.yml are campaign-infrastructure (mass-cancel Actions runs), not proof campaigns

**Kernel-verification claim (as asserted by the campaign):** Not individually examined; several branch names advertise 'kernel-verified' (agent/a263135-kernel-verified) or 'native' (audit/a263135-native) variants.

**Trust caveats:**
- This aggregate row exists so the register is honest about scope: these campaigns were discovered via branch listing but were not in the requested audit list and were not deep-audited
- archive/invalid-bmo8-claim-20260723 shows at least one campaign produced an invalid claim that had to be archived — recommend spot-checking merged 'solved' files

**Next action:** Separate audit pass if a complete inventory of every campaign is desired
