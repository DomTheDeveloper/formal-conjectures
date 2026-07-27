# Audit detail — OpenQuantumProblems

35 research-open declarations. Fields per problem: plain statement, source, category, match, status, action, difficulties, compute, confidence, evidence, flags.

## `mutuallyUnbiasedBases` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/OpenQuantumProblems/13.lean:560`  
**Statement:** Determine mu(d), the maximal number of mutually unbiased bases of C^d, as a function of d for all d >= 2 (answer is a function N -> N).  
**Source:** IQOQI Vienna Open Quantum Problems #13, https://oqp.iqoqi.oeaw.ac.at/mutually-unbiased-bases  
**Statement matches intent:** yes  
**Known status:** Major open problem. mu(d) = d+1 for prime powers (Ivanovic 1981, Wootters-Fields 1989); unknown for every non-prime-power d, starting with the famous d=6 case. Determining the full function is strictly harder than any single open case.  
**Difficulty:** math 10/10, Lean 10/10 · **Compute:** large · **Confidence:** high  
**Evidence:** answer(sorry) : N -> N applied to d correctly asks for the whole function; hd : 2 <= d excludes the degenerate d=0,1 cases (in d=1 every pair of bases is vacuously unbiased and no maximum exists, so the guard is needed and present).  
**Next action:** Keep open. The prime-power piece is itself a large but feasible formalization project (finite-field MUB constructions); the composite cases need a mathematical breakthrough.

## `mutuallyUnbiasedBases_dim10` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/OpenQuantumProblems/13.lean:532`  
**Statement:** Determine the exact maximal number mu(10) of mutually unbiased bases of C^10 (10 = 2*5 is not a prime power).  
**Source:** IQOQI Vienna Open Quantum Problems #13, https://oqp.iqoqi.oeaw.ac.at/mutually-unbiased-bases  
**Statement matches intent:** yes  
**Known status:** Open. Known: 3 <= mu(10) <= 11 (tensor bound min(mu(2),mu(5)) = 3; general upper bound d+1). Even less studied than d=6; exact value unknown.  
**Difficulty:** math 9/10, Lean 10/10 · **Compute:** large · **Confidence:** high  
**Evidence:** Same faithful IsMaxMUBCount encoding as the d=6 case. Value of mu(d) for any non-prime-power d is a recognized open problem; d=10 has no distinguishing structure.  
**Next action:** Keep open; no viable formal path known.

## `mutuallyUnbiasedBases_dim12` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/OpenQuantumProblems/13.lean:539`  
**Statement:** Determine the exact maximal number mu(12) of mutually unbiased bases of C^12.  
**Source:** IQOQI Vienna Open Quantum Problems #13, https://oqp.iqoqi.oeaw.ac.at/mutually-unbiased-bases  
**Statement matches intent:** yes  
**Known status:** Open. Known: 4 <= mu(12) <= 13 (tensor bound min(mu(4),mu(3)) = min(5,4) = 4). Exact value unknown.  
**Difficulty:** math 9/10, Lean 10/10 · **Compute:** large · **Confidence:** high  
**Evidence:** Faithful encoding; genuinely open non-prime-power case of OQP 13.  
**Next action:** Keep open; no viable formal path known.

## `mutuallyUnbiasedBases_dim14` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/OpenQuantumProblems/13.lean:546`  
**Statement:** Determine the exact maximal number mu(14) of mutually unbiased bases of C^14.  
**Source:** IQOQI Vienna Open Quantum Problems #13, https://oqp.iqoqi.oeaw.ac.at/mutually-unbiased-bases  
**Statement matches intent:** yes  
**Known status:** Open. Known: 3 <= mu(14) <= 15 (tensor bound min(mu(2),mu(7)) = 3). Exact value unknown.  
**Difficulty:** math 9/10, Lean 10/10 · **Compute:** large · **Confidence:** high  
**Evidence:** Faithful encoding; genuinely open non-prime-power case of OQP 13.  
**Next action:** Keep open; no viable formal path known.

## `mutuallyUnbiasedBases_dim15` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/OpenQuantumProblems/13.lean:553`  
**Statement:** Determine the exact maximal number mu(15) of mutually unbiased bases of C^15.  
**Source:** IQOQI Vienna Open Quantum Problems #13, https://oqp.iqoqi.oeaw.ac.at/mutually-unbiased-bases  
**Statement matches intent:** yes  
**Known status:** Open. Known: 4 <= mu(15) <= 16 (tensor bound min(mu(3),mu(5)) = 4). Exact value unknown.  
**Difficulty:** math 9/10, Lean 10/10 · **Compute:** large · **Confidence:** high  
**Evidence:** Faithful encoding; genuinely open non-prime-power case of OQP 13.  
**Next action:** Keep open; no viable formal path known.

## `mutuallyUnbiasedBases_dim6` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/OpenQuantumProblems/13.lean:525`  
**Statement:** Determine the exact maximal number mu(6) of pairwise mutually unbiased orthonormal bases of C^6, encoded as IsMaxMUBCount 6 (answer(sorry)).  
**Source:** IQOQI Vienna Open Quantum Problems #13, https://oqp.iqoqi.oeaw.ac.at/mutually-unbiased-bases  
**Statement matches intent:** yes  
**Known status:** Famous open problem: 3 <= mu(6) <= 7 known; conjectured mu(6)=3 with strong numerical evidence (Butterley-Hall 2007, Brierley-Weigert 2008, Raynal-Lu-Englert 2011) but no proof. In-file solved case mu(2)=3 (qubit_maximal) confirms the definitions are sane. No internal PR/campaign targets this file (quantum-n6d3 campaign is a different OQP).  
**Difficulty:** math 9/10, Lean 10/10 · **Compute:** large · **Confidence:** high  
**Evidence:** Definitions faithful: bases as unitary matrices, IsUnbiased demands |(U^dag V)_ij|^2 = 1/d for all i,j; Pairwise unbiasedness forces distinct bases for d>=2, so no degenerate counting. Max exists since mu(d)<=d+1. The statement is in principle decidable by real quantifier elimination but utterly infeasible in practice.  
**Next action:** Keep open. Any progress would come from formalizing the known bounds first; note mutuallyUnbiasedBases_dim6_bounds in the same file cites a formal proof of 3<=mu(6)<=7 in the XC0R fork (13.lean L1168) that could be ported.

## `hasSICPOVM_56` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/OpenQuantumProblems/23.lean:316`  
**Secondary category:** 5 (Solved mathematically, not yet formalized)  
**Statement:** Decide whether a SIC-POVM (d^2 = 3136 normalized vectors in C^56 with pairwise squared overlap 1/57) exists in dimension 56.  
**Source:** IQOQI Vienna Open Quantum Problems #23, https://oqp.iqoqi.oeaw.ac.at/sic-povms-and-zauners-conjecture  
**Statement matches intent:** yes  
**Known status:** Reported externally solved: per the introduction of Grassl et al., 'SIC-POVMs from Stark units: Dimensions n^2+3 = 4p, p prime', J. Math. Phys. 66, 082202 (2025), exact (symbolically verified algebraic) SIC fiducials are now known in ALL dimensions d <= 57, which includes d = 56. Two independent web lookups returned this 'all d <= 57' status; the file's claim that 56 is the smallest open case appears to be based on an outdated exact-solutions table (e.g. Flammia's page).  
**Difficulty:** math 2/10, Lean 9/10 · **Compute:** large · **Confidence:** medium  
**Evidence:** Encoding is faithful: d^2 unit vectors with pairwise |<phi_i,phi_j>|^2 = (d+1)^-1 is the standard SIC definition (such an equiangular family meeting the Gerzon bound is automatically a tight frame, hence a POVM). Duplicate vectors are excluded automatically since equal unit vectors have overlap 1, not 1/57. FC100OpenSet1.lean references hasSICPOVM_60 only as a list entry, not a proof; no internal PR/campaign targets this file.  
**Flags:** needs literature check: primary citation for exact d=56 fiducial; status claim 'exact solutions known for all d <= 57' from 2025 JMP paper obtained via web search; file docstring calls 56 the smallest open case - likely stale relative to 2025 literature; verifier:revised  
**Verifier:** Triage cat=1 ('externally solved') rests solely on a web-search summary asserting exact SIC fiducials are known for ALL d <= 57, attributed to Bengtsson-Grassl-McConnell, 'SIC-POVMs from Stark units: Dimensions n^2+3 = 4p, p prime' (arXiv:2403.02872, JMP 66, 082202 (2025)). That attribution is provably wrong: the paper's construction covers only d = n^2+3 with n^2+3 = 4p, i.e. d in {12, 28, 52, 124, 172, 292, 628, 844, ...} (verified by direct enumeration); 56 - 3 = 53 is not a perfect square, so d=56 is not in that family, nor in the sibling prime family d = n^2+3 in {7,19,67,103,199,...}, nor a dimension-tower value k(k-2). Concrete published exact-solution lists that surfaced (d = 2-28, 30, 31, 35, 37-39, 42, 43, 48, 49, 52, 53, 57, ... up to 1299) include 57 and omit 56, exactly matching the Lean file's own placement of 56 as the smallest dimension lacking an exact/rigorous fiducial. The 'all d <= 57' phrasing appears to be a search-engine interpolation (the same engine then inferred 'therefore 58 is the smallest open', contradicting the file's list of 58,59,60,64,... as open). No primary source confirming an exact d=56 fiducial was obtainable (arxiv.org, physics.usyd.edu.au, markus-grassl.de, oqp.iqoqi.oeaw.ac.at all returned 403). Internal evidence agrees with 'open': re-grep of pr_register.json and campaign_register.json finds zero hits for SIC/SICPOVM/Zauner/23.lean; the 11 'quantum' PRs are all the quantum-graph N=6 D=3 colouring campaign (a different OQP) and all closed. Formal statement re-read and faithful: 'theorem hasSICPOVM_56 : answer(sorry) <-> HasSICPOVM 56', with HasSICPOVM d = exists Phi : Fin (d^2) -> EuclideanSpace C (Fin d), all normalized and Pairwise overlapSq = (d+1)^-1 -- the standard SIC definition, no degenerate loophole (equal unit vectors have overlap 1 != 1/57). Status is therefore identical to its siblings hasSICPOVM_58/59/60/...: high-precision numerics exist (Scott, all d <= 193) so the answer is confidently True, but no rigorous existence proof. Reclassified to cat 8 (open, believed True, certified-numerics avenue) with cat2 6, matching the sibling dimensions; match stays 'yes'. (triage said cat 1)  
**Next action:** Confirm against the primary source (Grassl's exact-solutions data / the 2025 JMP paper) which paper contains the d=56 fiducial; then answer := True. Formalizing the witness in Lean means verifying 3136-vector overlap identities over a huge number field: research-scale effort, likely via a purpose-built certified-computation layer.

## `hasSICPOVM_58` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/OpenQuantumProblems/23.lean:320`  
**Secondary category:** 6 (Computationally solvable with certificate)  
**Statement:** Decide whether a SIC-POVM exists in dimension 58.  
**Source:** IQOQI Vienna Open Quantum Problems #23, https://oqp.iqoqi.oeaw.ac.at/sic-povms-and-zauners-conjecture  
**Statement matches intent:** yes  
**Known status:** Open as an exact/rigorous existence question (beyond the d <= 57 exact range reported in 2025; not in a known solved special family). High-precision numerical fiducials exist for all d <= 193 (Scott, arXiv:1703.03993 and successors), so the answer is confidently believed True.  
**Difficulty:** math 7/10, Lean 9/10 · **Compute:** large · **Confidence:** medium  
**Evidence:** answer(sorry) <-> HasSICPOVM 58 is a faithful decision encoding. Definition equivalent to standard SIC-POVM (equiangular tight frame at the Gerzon bound).  
**Flags:** needs literature check: exact solutions are being added dimension-by-dimension (Grassl et al.); any listed dimension may have been solved after Jan 2026  
**Next action:** Certification avenue: the Weyl-Heisenberg fiducial equations are a polynomial system in ~2d real unknowns; an interval-Newton/alpha-theory certificate around the published numerical fiducial would rigorously prove existence. Not yet done in the literature; kernel-checking such a certificate in Lean is research-scale. First milestone: certify a small solved dimension (d=4 or 5) end-to-end.

## `hasSICPOVM_59` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/OpenQuantumProblems/23.lean:324`  
**Secondary category:** 6 (Computationally solvable with certificate)  
**Statement:** Decide whether a SIC-POVM exists in dimension 59.  
**Source:** IQOQI Vienna Open Quantum Problems #23, https://oqp.iqoqi.oeaw.ac.at/sic-povms-and-zauners-conjecture  
**Statement matches intent:** yes  
**Known status:** Open as an exact existence question; numerical fiducials known (all d <= 193), believed True.  
**Difficulty:** math 7/10, Lean 9/10 · **Compute:** large · **Confidence:** medium  
**Evidence:** Faithful decision encoding of Zauner existence in a fixed open dimension.  
**Flags:** needs literature check: rapid ongoing exact-solution progress  
**Next action:** Same certified-numerics avenue as d=58.

## `hasSICPOVM_60` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/OpenQuantumProblems/23.lean:328`  
**Secondary category:** 6 (Computationally solvable with certificate)  
**Statement:** Decide whether a SIC-POVM exists in dimension 60.  
**Source:** IQOQI Vienna Open Quantum Problems #23, https://oqp.iqoqi.oeaw.ac.at/sic-povms-and-zauners-conjecture  
**Statement matches intent:** yes  
**Known status:** Open as an exact existence question; numerical fiducials known, believed True. Referenced (as a name only) in FormalConjectures/Subsets/FC100OpenSet1.lean, which is a curated open-problem list, not a proof.  
**Difficulty:** math 7/10, Lean 9/10 · **Compute:** large · **Confidence:** medium  
**Evidence:** Faithful decision encoding.  
**Flags:** needs literature check: rapid ongoing exact-solution progress  
**Next action:** Same certified-numerics avenue as d=58.

## `hasSICPOVM_64` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/OpenQuantumProblems/23.lean:332`  
**Secondary category:** 6 (Computationally solvable with certificate)  
**Statement:** Decide whether a SIC-POVM exists in dimension 64.  
**Source:** IQOQI Vienna Open Quantum Problems #23, https://oqp.iqoqi.oeaw.ac.at/sic-povms-and-zauners-conjecture  
**Statement matches intent:** yes  
**Known status:** Open as an exact existence question; numerical fiducials known, believed True.  
**Difficulty:** math 7/10, Lean 9/10 · **Compute:** large · **Confidence:** medium  
**Evidence:** Faithful decision encoding.  
**Flags:** needs literature check: rapid ongoing exact-solution progress  
**Next action:** Same certified-numerics avenue as d=58.

## `hasSICPOVM_68` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/OpenQuantumProblems/23.lean:336`  
**Secondary category:** 6 (Computationally solvable with certificate)  
**Statement:** Decide whether a SIC-POVM exists in dimension 68.  
**Source:** IQOQI Vienna Open Quantum Problems #23, https://oqp.iqoqi.oeaw.ac.at/sic-povms-and-zauners-conjecture  
**Statement matches intent:** yes  
**Known status:** Open as an exact existence question; numerical fiducials known, believed True.  
**Difficulty:** math 7/10, Lean 9/10 · **Compute:** large · **Confidence:** medium  
**Evidence:** Faithful decision encoding.  
**Flags:** needs literature check: rapid ongoing exact-solution progress  
**Next action:** Same certified-numerics avenue as d=58.

## `hasSICPOVM_69` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/OpenQuantumProblems/23.lean:340`  
**Secondary category:** 6 (Computationally solvable with certificate)  
**Statement:** Decide whether a SIC-POVM exists in dimension 69.  
**Source:** IQOQI Vienna Open Quantum Problems #23, https://oqp.iqoqi.oeaw.ac.at/sic-povms-and-zauners-conjecture  
**Statement matches intent:** yes  
**Known status:** Open as an exact existence question; numerical fiducials known, believed True.  
**Difficulty:** math 7/10, Lean 9/10 · **Compute:** large · **Confidence:** medium  
**Evidence:** Faithful decision encoding.  
**Flags:** needs literature check: rapid ongoing exact-solution progress  
**Next action:** Same certified-numerics avenue as d=58.

## `hasSICPOVM_70` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/OpenQuantumProblems/23.lean:344`  
**Secondary category:** 6 (Computationally solvable with certificate)  
**Statement:** Decide whether a SIC-POVM exists in dimension 70.  
**Source:** IQOQI Vienna Open Quantum Problems #23, https://oqp.iqoqi.oeaw.ac.at/sic-povms-and-zauners-conjecture  
**Statement matches intent:** yes  
**Known status:** Open as an exact existence question; numerical fiducials known, believed True.  
**Difficulty:** math 7/10, Lean 9/10 · **Compute:** large · **Confidence:** medium  
**Evidence:** Faithful decision encoding.  
**Flags:** needs literature check: rapid ongoing exact-solution progress  
**Next action:** Same certified-numerics avenue as d=58.

## `hasSICPOVM_71` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/OpenQuantumProblems/23.lean:348`  
**Secondary category:** 6 (Computationally solvable with certificate)  
**Statement:** Decide whether a SIC-POVM exists in dimension 71.  
**Source:** IQOQI Vienna Open Quantum Problems #23, https://oqp.iqoqi.oeaw.ac.at/sic-povms-and-zauners-conjecture  
**Statement matches intent:** yes  
**Known status:** Open as an exact existence question; numerical fiducials known, believed True.  
**Difficulty:** math 7/10, Lean 9/10 · **Compute:** large · **Confidence:** medium  
**Evidence:** Faithful decision encoding.  
**Flags:** needs literature check: rapid ongoing exact-solution progress  
**Next action:** Same certified-numerics avenue as d=58.

## `hasSICPOVM_72` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/OpenQuantumProblems/23.lean:352`  
**Secondary category:** 6 (Computationally solvable with certificate)  
**Statement:** Decide whether a SIC-POVM exists in dimension 72.  
**Source:** IQOQI Vienna Open Quantum Problems #23, https://oqp.iqoqi.oeaw.ac.at/sic-povms-and-zauners-conjecture  
**Statement matches intent:** yes  
**Known status:** Open as an exact existence question; numerical fiducials known, believed True.  
**Difficulty:** math 7/10, Lean 9/10 · **Compute:** large · **Confidence:** medium  
**Evidence:** Faithful decision encoding.  
**Flags:** needs literature check: rapid ongoing exact-solution progress  
**Next action:** Same certified-numerics avenue as d=58.

## `hasSICPOVM_75` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/OpenQuantumProblems/23.lean:356`  
**Secondary category:** 6 (Computationally solvable with certificate)  
**Statement:** Decide whether a SIC-POVM exists in dimension 75.  
**Source:** IQOQI Vienna Open Quantum Problems #23, https://oqp.iqoqi.oeaw.ac.at/sic-povms-and-zauners-conjecture  
**Statement matches intent:** yes  
**Known status:** Open as an exact existence question; numerical fiducials known, believed True.  
**Difficulty:** math 7/10, Lean 9/10 · **Compute:** large · **Confidence:** medium  
**Evidence:** Faithful decision encoding.  
**Flags:** needs literature check: rapid ongoing exact-solution progress  
**Next action:** Same certified-numerics avenue as d=58.

## `sicPOVMs` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/OpenQuantumProblems/23.lean:362`  
**Statement:** Decide whether SIC-POVMs exist in every dimension d >= 1 (the existence form of Zauner's conjecture / the SIC problem).  
**Source:** IQOQI Vienna Open Quantum Problems #23, https://oqp.iqoqi.oeaw.ac.at/sic-povms-and-zauners-conjecture; Zauner PhD thesis 1999; Renes-Blume-Kohout-Scott-Caves 2004  
**Statement matches intent:** yes  
**Known status:** Major open problem. Exact solutions known for all d <= 57 and assorted higher dimensions (including infinite Stark-unit families under active development); numerics for all d <= 193 and beyond; the all-d statement remains unproven despite deep connections to Hilbert's 12th problem and Stark conjectures.  
**Difficulty:** math 10/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** answer(sorry) <-> forall d >= 1, HasSICPOVM d is faithful; the d >= 1 guard is harmless (d=0 is vacuously true anyway, proved in-file as hasSICPOVM_zero). The equiangular-vectors definition is equivalent to the operational SIC-POVM definition.  
**Next action:** Keep open. Any conditional resolution (e.g. via Stark conjectures) would itself be research-scale to formalize.

## `ame_10_10_open` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/OpenQuantumProblems/35.lean:797`  
**Statement:** Decide whether an AME(10,10) state exists: 10 parties of dimension 10 with all 5-party reductions maximally mixed.  
**Source:** IQOQI Open Quantum Problems #35; arXiv:2508.04777; Huber-Wyderka AME table  
**Statement matches intent:** yes  
**Known status:** Open; d=10 family. Research open on upstream main as of 2026-07-26.  
**Difficulty:** math 8/10, Lean 10/10 · **Compute:** large · **Confidence:** high  
**Evidence:** Faithful encoding; recognized open family case.  
**Next action:** Keep open; monitor literature/upstream.

## `ame_10_6_open` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/OpenQuantumProblems/35.lean:791`  
**Statement:** Decide whether an AME(10,6) state exists: 10 parties of dimension 6 with all 5-party reductions maximally mixed.  
**Source:** IQOQI Open Quantum Problems #35; arXiv:2508.04777; Huber-Wyderka AME table  
**Statement matches intent:** yes  
**Known status:** Open; d=6 family. Research open on upstream main as of 2026-07-26.  
**Difficulty:** math 8/10, Lean 10/10 · **Compute:** large · **Confidence:** high  
**Evidence:** Faithful encoding; recognized open family case.  
**Next action:** Keep open; monitor literature/upstream.

## `ame_11_10_open` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/OpenQuantumProblems/35.lean:831`  
**Statement:** Decide whether an AME(11,10) state exists: 11 parties of dimension 10 with all 5-party reductions maximally mixed.  
**Source:** IQOQI Open Quantum Problems #35; arXiv:2508.04777; Huber-Wyderka AME table  
**Statement matches intent:** yes  
**Known status:** Open; d=10 family. Research open on upstream main as of 2026-07-26.  
**Difficulty:** math 8/10, Lean 10/10 · **Compute:** large · **Confidence:** high  
**Evidence:** Faithful encoding; recognized open family case.  
**Next action:** Keep open; monitor literature/upstream.

## `ame_11_3_open` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/OpenQuantumProblems/35.lean:803`  
**Statement:** Decide whether an AME(11,3) state exists: 11 qutrits with all 5-party reductions maximally mixed; equivalent to a pure quantum MDS code [[11,0,6]]_3.  
**Source:** IQOQI Open Quantum Problems #35; arXiv:2508.04777; Huber-Wyderka AME table  
**Statement matches intent:** yes  
**Known status:** Open per the actively maintained upstream benchmark (research open on google-deepmind main as of 2026-07-26, which reflects the 2025/2026 review); equivalent to existence of a pure [[11,0,6]]_3 code, not in known code tables and not excluded by shadow/Scott bounds.  
**Difficulty:** math 8/10, Lean 10/10 · **Compute:** large · **Confidence:** medium  
**Evidence:** Faithful encoding (file audited); case-by-case status inferred from the fresh upstream benchmark and 2025/2026 review rather than an independent per-pair literature confirmation.  
**Flags:** needs literature check (per-pair status not independently confirmed; quantum code tables evolve)  
**Next action:** Keep open; check Grassl's quantum code tables periodically for [[11,0,6]]_3; a resolution either way would likely come from coding theory.

## `ame_11_4_open` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/OpenQuantumProblems/35.lean:809`  
**Statement:** Decide whether an AME(11,4) state exists: 11 ququarts with all 5-party reductions maximally mixed; equivalent to a pure [[11,0,6]]_4 code.  
**Source:** IQOQI Open Quantum Problems #35; arXiv:2508.04777; Huber-Wyderka AME table  
**Statement matches intent:** yes  
**Known status:** Open per the fresh upstream benchmark (2026-07-26) and 2025/2026 review; no known [[11,0,6]]_4 code and no known obstruction.  
**Difficulty:** math 8/10, Lean 10/10 · **Compute:** large · **Confidence:** medium  
**Evidence:** Faithful encoding; status inferred from upstream benchmark freshness rather than direct per-pair confirmation.  
**Flags:** needs literature check (per-pair status not independently confirmed)  
**Next action:** Keep open; watch quantum code tables.

## `ame_11_6_open` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/OpenQuantumProblems/35.lean:825`  
**Statement:** Decide whether an AME(11,6) state exists: 11 parties of dimension 6 with all 5-party reductions maximally mixed.  
**Source:** IQOQI Open Quantum Problems #35; arXiv:2508.04777; Huber-Wyderka AME table  
**Statement matches intent:** yes  
**Known status:** Open; d=6 family. Research open on upstream main as of 2026-07-26.  
**Difficulty:** math 8/10, Lean 10/10 · **Compute:** large · **Confidence:** high  
**Evidence:** Faithful encoding; recognized open family case.  
**Next action:** Keep open; monitor literature/upstream.

## `ame_12_10_open` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/OpenQuantumProblems/35.lean:849`  
**Statement:** Decide whether an AME(12,10) state exists: 12 parties of dimension 10 with all 6-party reductions maximally mixed.  
**Source:** IQOQI Open Quantum Problems #35; arXiv:2508.04777; Huber-Wyderka AME table  
**Statement matches intent:** yes  
**Known status:** Open; d=10 family. Research open on upstream main as of 2026-07-26.  
**Difficulty:** math 8/10, Lean 10/10 · **Compute:** large · **Confidence:** high  
**Evidence:** Faithful encoding; recognized open family case.  
**Next action:** Keep open; monitor literature/upstream.

## `ame_12_5_open` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/OpenQuantumProblems/35.lean:837`  
**Statement:** Decide whether an AME(12,5) state exists: 12 parties of dimension 5 with all 6-party reductions maximally mixed; equivalent to a pure [[12,0,7]]_5 code.  
**Source:** IQOQI Open Quantum Problems #35; arXiv:2508.04777; Huber-Wyderka AME table  
**Statement matches intent:** yes  
**Known status:** Open per the fresh upstream benchmark (2026-07-26). Notably, the adjacent case AME(11,5) was recently resolved positively by the DeepMind prover agent with a full formal Lean construction (upstream commit 47383bf, line 2138), so d=5 is under active attack.  
**Difficulty:** math 8/10, Lean 10/10 · **Compute:** large · **Confidence:** medium  
**Evidence:** Faithful encoding; status inferred from upstream benchmark freshness; sibling case (11,5) just fell, suggesting this case may be nearer resolution than the d=6/d=10 families.  
**Flags:** needs literature check (per-pair status not independently confirmed); adjacent case AME(11,5) solved upstream in 2026 - technique may transfer  
**Next action:** Most promising target of the batch after ame_8_4: examine the upstream AME(11,5) construction (likely code/orthogonal-array based) and test whether the technique extends to (12,5); a found construction would be formalizable by the same template.

## `ame_12_6_open` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/OpenQuantumProblems/35.lean:843`  
**Statement:** Decide whether an AME(12,6) state exists: 12 parties of dimension 6 with all 6-party reductions maximally mixed.  
**Source:** IQOQI Open Quantum Problems #35; arXiv:2508.04777; Huber-Wyderka AME table  
**Statement matches intent:** yes  
**Known status:** Open; d=6 family. Research open on upstream main as of 2026-07-26.  
**Difficulty:** math 8/10, Lean 10/10 · **Compute:** large · **Confidence:** high  
**Evidence:** Faithful encoding; recognized open family case.  
**Next action:** Keep open; monitor literature/upstream.

## `ame_7_10_open` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/OpenQuantumProblems/35.lean:755`  
**Statement:** Decide whether an AME(7,10) state exists: 7 parties of local dimension 10 with all 3-party reductions maximally mixed.  
**Source:** IQOQI Open Quantum Problems #35; arXiv:2508.04777; Huber-Wyderka AME table  
**Statement matches intent:** yes  
**Known status:** Open. 10=2*5 not a prime power; AME(7,2) nonexistence blocks the tensor construction AME(7,2)x(7,5); no direct construction or obstruction known. Still research open on upstream google-deepmind main as of 2026-07-26.  
**Difficulty:** math 8/10, Lean 10/10 · **Compute:** large · **Confidence:** high  
**Evidence:** Same faithful ExistsAME encoding audited for the whole file; d=10, n>=7 sits in the same structurally blocked family as d=6, and the actively maintained upstream benchmark (which did flip AME(11,5) to solved) leaves it open.  
**Next action:** Keep open; monitor literature/upstream.

## `ame_7_6_open` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/OpenQuantumProblems/35.lean:749`  
**Statement:** Decide whether an absolutely maximally entangled pure state AME(7,6) exists, i.e. a normalized state of 7 six-level systems all of whose 3-party reductions are maximally mixed.  
**Source:** IQOQI Open Quantum Problems #35, https://oqp.iqoqi.oeaw.ac.at/existence-of-absolutely-maximally-entangled-pure-states; Rajchel-Mieldzioc et al., arXiv:2508.04777 (Rep. Prog. Phys. 2026); Huber-Wyderka AME table  
**Statement matches intent:** yes  
**Known status:** Genuinely open; explicitly named (with AME(8,4)) among the smallest unresolved cases in the 2025/2026 review. 6=2*3 is not a prime power; the tensor construction AME(7,2)x(7,3) fails because AME(7,2) does not exist (Huber-Guehne-Siewert 2017); no obstruction known below the Scott bound. Upstream google-deepmind main (fetched 2026-07-26, byte-identical to this file apart from an import) still marks it research open. No fork PR/campaign targets OQP 35.  
**Difficulty:** math 8/10, Lean 10/10 · **Compute:** large · **Confidence:** high  
**Evidence:** Full file audited: reduced-density/permutation encoding provably covers all floor(n/2)-subsets; normalization required; maximallyMixed = I/d^m; in-file Bell/GHZ sanity theorems confirm definitions. Web check confirms AME(7,6) is a flagship unresolved case; the d=6 family for n>=7 has no known construction (no AME(n,2) for n>=7 kills the tensor route, 6 not a prime power kills code routes).  
**Next action:** Keep open; monitor literature and upstream. If a construction appears, port it in the style of the upstream AME(11,5) formal proof (commit 47383bf, ~1300 extra lines) and verify build.

## `ame_8_10_open` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/OpenQuantumProblems/35.lean:773`  
**Statement:** Decide whether an AME(8,10) state exists: 8 parties of dimension 10 with all 4-party reductions maximally mixed.  
**Source:** IQOQI Open Quantum Problems #35; arXiv:2508.04777; Huber-Wyderka AME table  
**Statement matches intent:** yes  
**Known status:** Open; d=10 non-prime-power family, n>=7 blocked as for AME(7,10). Research open on upstream main as of 2026-07-26.  
**Difficulty:** math 8/10, Lean 10/10 · **Compute:** large · **Confidence:** high  
**Evidence:** Faithful encoding; recognized open family case.  
**Next action:** Keep open; monitor literature/upstream.

## `ame_8_4_open` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/OpenQuantumProblems/35.lean:761`  
**Statement:** Decide whether an AME(8,4) state exists: 8 ququarts with all 4-party reductions maximally mixed; equivalent to a pure quantum MDS code [[8,0,5]]_4.  
**Source:** IQOQI Open Quantum Problems #35; arXiv:2508.04777; Huber-Grassl, Quantum 4, 284 (2020)  
**Statement matches intent:** yes  
**Known status:** Genuinely open; named (with AME(7,6)) among the smallest unresolved cases in the 2025/2026 review ('8 ququarts'). Equivalent to existence of a pure [[8,0,5]]_4 code, unresolved despite extensive code searches. Research open on upstream main as of 2026-07-26.  
**Difficulty:** math 8/10, Lean 10/10 · **Compute:** large · **Confidence:** high  
**Evidence:** Web check confirms this exact case is highlighted as unresolved. Faithful encoding (audited). Positive resolution reduces to an explicit stabilizer state whose reductions could in principle be verified by (large) exact computation; no such code is known.  
**Next action:** Keep open. Most code-theoretic of the batch: watch quantum-code tables (Grassl) for a [[8,0,5]]_4 resolution; a found code would give a finitely-checkable state whose formalization follows the upstream AME(11,5) template.

## `ame_8_6_open` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/OpenQuantumProblems/35.lean:767`  
**Statement:** Decide whether an AME(8,6) state exists: 8 parties of dimension 6 with all 4-party reductions maximally mixed.  
**Source:** IQOQI Open Quantum Problems #35; arXiv:2508.04777; Huber-Wyderka AME table  
**Statement matches intent:** yes  
**Known status:** Open; same d=6 non-prime-power family as AME(7,6) (no tensor or code construction available for n>=7, no known obstruction). Research open on upstream main as of 2026-07-26.  
**Difficulty:** math 8/10, Lean 10/10 · **Compute:** large · **Confidence:** high  
**Evidence:** Faithful encoding (file audited in full); part of the recognized open d=6 family listed on the OQP page and in the 2025/2026 review.  
**Next action:** Keep open; monitor literature/upstream.

## `ame_9_10_open` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/OpenQuantumProblems/35.lean:785`  
**Statement:** Decide whether an AME(9,10) state exists: 9 parties of dimension 10 with all 4-party reductions maximally mixed.  
**Source:** IQOQI Open Quantum Problems #35; arXiv:2508.04777; Huber-Wyderka AME table  
**Statement matches intent:** yes  
**Known status:** Open; d=10 family. Research open on upstream main as of 2026-07-26.  
**Difficulty:** math 8/10, Lean 10/10 · **Compute:** large · **Confidence:** high  
**Evidence:** Faithful encoding; recognized open family case.  
**Next action:** Keep open; monitor literature/upstream.

## `ame_9_6_open` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/OpenQuantumProblems/35.lean:779`  
**Statement:** Decide whether an AME(9,6) state exists: 9 parties of dimension 6 with all 4-party reductions maximally mixed.  
**Source:** IQOQI Open Quantum Problems #35; arXiv:2508.04777; Huber-Wyderka AME table  
**Statement matches intent:** yes  
**Known status:** Open; d=6 family. Research open on upstream main as of 2026-07-26.  
**Difficulty:** math 8/10, Lean 10/10 · **Compute:** large · **Confidence:** high  
**Evidence:** Faithful encoding; recognized open family case (no AME(9,2), 6 not a prime power).  
**Next action:** Keep open; monitor literature/upstream.

## `oqp_35` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/OpenQuantumProblems/35.lean:857`  
**Secondary category:** 4 (Vacuously true / accidentally weakened)  
**Statement:** Give a complete classification: describe explicitly the set of all pairs (n,d) with n,d >= 2 for which an absolutely maximally entangled state AME(n,d) exists.  
**Source:** IQOQI Open Quantum Problems #35, https://oqp.iqoqi.oeaw.ac.at/existence-of-absolutely-maximally-entangled-pure-states  
**Statement matches intent:** yes  
**Known status:** The full classification is the recognized hard open problem OQP #35; it strictly contains all 16 open sub-cases above (and any others, e.g. larger n in the d=6/d=10 families), several of which have resisted attack for a decade-plus (AME(4,6) alone took ~10 years). Research open upstream as of 2026-07-26.  
**Difficulty:** math 9/10, Lean 10/10 · **Compute:** large · **Confidence:** high  
**Evidence:** Faithful encoding of the classification question over the audited ExistsAME predicate; resolving it requires settling every open AME(n,d) case, for which no general strategy is known (d=6/d=10 families lack both constructions and obstructions).  
**Flags:** answer(sorry) set-equality is trivially closable by rfl (answer := LHS set); closed-form-ness is convention-enforced only - same latent loophole as all answer() encodings in this repo, listed for the record, not a math defect  
**Next action:** Keep open. Note the spec-level weakness: the set-valued answer(sorry) equation is formally dischargeable by rfl with answer instantiated to the defining set itself; only repo convention (human review), not the type system or AnswerLinter, requires a genuinely explicit description.
