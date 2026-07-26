# Audit detail — GreensOpenProblems

96 research-open declarations. Fields per problem: plain statement, source, category, match, status, action, difficulties, compute, confidence, evidence, flags.

## `green_1` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/GreensOpenProblems/1.lean:33`  
**Statement:** Does every set of n positive integers contain a sum-free subset of size at least n/3 + w(n) for some function w(n) tending to infinity?  
**Source:** Ben Green, 100 open problems, Problem 1; Erdos 1965; Bourgain 1997 (n/3 + 2/3); Eberhard-Green-Manners, Annals of Math 181 (2014) (constant 1/3 optimal)  
**Statement matches intent:** yes  
**Known status:** Genuinely open. Erdos gave n/3, Bourgain (n+2)/3; Eberhard-Green-Manners showed density 1/3 cannot be beaten, but whether an additive w(n)->infinity gain exists remains a recognized hard open problem (Green lists it as Problem 1).  
**Difficulty:** math 9/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Formalization audited: positivity hypothesis present, Omega may be negative on small n (harmless), Finset card/real coercions correct. No internal PRs target green_1 (pr_register grep: none). Only other sum-free file is GreensOpenProblems/2.lean (product-free variant), not a duplicate.  
**Next action:** No action; keep as open. IsSumFree = Disjoint (A+A) A matches the classical definition (a+b=c forbidden, a=b allowed); quantifier structure (exists one Omega, forall n, forall A) is the correct uniform formulation.

## `green_12` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/GreensOpenProblems/12.lean:37`  
**Statement:** For any finite abelian group G of size N and A of density alpha, are there at least alpha^15 N^10 pairs of 5-tuples (x_i),(y_j) with x_i + y_j in A whenever j is in {i, i+1, i+2} mod 5? (Additive/Cayley analogue of Sidorenko's conjecture for K_{5,5} minus C_10, the smallest open Sidorenko case.)  
**Source:** Ben Green, 100 open problems (2024), Problem 12  
**Statement matches intent:** yes  
**Known status:** Open as of Green's 2024 list; no resolution known to me by Jan 2026. The graph version (Sidorenko for K_{5,5}\C_10, 15 edges) is the notorious smallest open case; the abelian-group version is what Green poses.  
**Difficulty:** math 9/10, Lean 9/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** Formal statement audited: 15 constraints (5 i's x 3 j's, indices genuinely wrap in Fin 5), count over ordered pairs of functions Fin 5 -> G gives N^10 total tuples, expected count alpha^15 N^10 -- matches the random bound. G nonempty (group), A empty gives RHS 0, no degenerate loophole. No internal PRs (register grep for green/sidorenko: none targeting this).  
**Flags:** needs literature check (post-2024 Sidorenko progress)  
**Next action:** Keep open; monitor Sidorenko-conjecture literature (entropy/Fourier-positivity methods are the identifiable avenue). Needs literature check for any 2025-2026 progress.

## `W_3_20_lower` — Already solved internally (cat 0)

**File:** `FormalConjectures/GreensOpenProblems/14.lean:217`  
**Secondary category:** 1 (Already solved externally)  
**Statement:** Decide whether W(3,20) >= 389, the AKS14 Table 2 lower bound (answer: yes).  
**Source:** Ahmed-Kullmann-Snevily 2014, Table 2 (conjectured value w(2;3,20) = 389; lower bound certified by explicit colouring)  
**Statement matches intent:** yes  
**Known status:** SOLVED INTERNALLY AND MERGED: Green14.FastKernel.W_3_20_lower_fast in FormalConjectures/GreensOpenProblems/Green14FastKernel20.lean proves Green14.W 3 20 >= 389 by kernel-clean decide on a 388-bit mask colouring, via merged bridge lemmas W_ge_succ_of_checks (FunctionCertificateBridge), mixedMonoAPGuaranteeSet_upward (OrderBridge) and Hales-Jewett nonemptiness (FiniteExistence). PR #173 'Green14: prove W(3,20) >= 389 by kernel-checked certificate' merged 2026-07-23. Exact-value (=389) upper-bound LRAT campaign (PRs #242-248) still incomplete but not needed here.  
**Difficulty:** math 2/10, Lean 2/10 · **Compute:** small · **Confidence:** high  
**Evidence:** Read Green14FastKernel20.lean: theorem W_3_20_lower_fast : Green14.W 3 20 >= 389 with #print axioms; bridge soundness audited line-by-line (hasAP enumerates all a, d with a+(k-1)d < N; step>0 forced by card=k>=2; 1-based/0-based shift handled via x.1-1). Certificate imports the exact W definition from 14.lean via Green14Core, so it targets the canonical statement.  
**Flags:** canonical file still says answer(sorry)/sorry; trivial wiring remains  
**Next action:** Close the catalog statement: set answer(True) in 14.lean and prove with Iff.intro/iff_of_true using Green14.FastKernel.W_3_20_lower_fast; verify build (cannot run lake in this container).

## `W_3_21_lower` — Already solved internally (cat 0)

**File:** `FormalConjectures/GreensOpenProblems/14.lean:221`  
**Secondary category:** 1 (Already solved externally)  
**Statement:** Decide whether W(3,21) >= 416 (AKS14 Table 2 lower bound; answer: yes).  
**Source:** Ahmed-Kullmann-Snevily 2014, Table 2  
**Statement matches intent:** yes  
**Known status:** Solved internally on a preserved branch: Green14.Certificate.valid_21 (explicit 50-element colour-0 list zeros21, native_decide check at N = 415) on branch agent/green14-certificates-20-39 (PR #23, draft closed 'proof branch preserved'); merged main-branch bridge W_ge_succ_of_checks turns the check into W 3 21 >= 416. Lower bound also published externally (AKS14).  
**Difficulty:** math 2/10, Lean 4/10 · **Compute:** small · **Confidence:** medium  
**Evidence:** git show 8f43625:...Green14Certificates.lean contains valid_21 with the explicit colouring; bound arithmetic checks out (N=415 gives W >= 416). Branch checks use native_decide and PR #23 was closed before its CI matrix finished (mergeable_state unstable), so kernel re-verification is pending.  
**Flags:** branch proof uses native_decide; kernel-clean port pending; canonical statement still sorry  
**Next action:** Port zeros21 into the merged FunctionCertificateBridge bitmask pattern (as done for t=20), run kernel decide, apply W_ge_succ_of_checks, set answer(True); verify build.

## `W_3_22_lower` — Already solved internally (cat 0)

**File:** `FormalConjectures/GreensOpenProblems/14.lean:225`  
**Secondary category:** 1 (Already solved externally)  
**Statement:** Decide whether W(3,22) >= 464 (AKS14 Table 2 lower bound; answer: yes).  
**Source:** Ahmed-Kullmann-Snevily 2014, Table 2  
**Statement matches intent:** yes  
**Known status:** Solved internally on branch agent/green14-certificates-20-39 (PR #23): valid_22 native_decide certificate at N = 463; merged bridge gives W 3 22 >= 464. Published lower bound (AKS14).  
**Difficulty:** math 2/10, Lean 4/10 · **Compute:** small · **Confidence:** medium  
**Evidence:** valid_22 in branch Green14Certificates.lean; N=463 matches >= 464.  
**Flags:** branch proof uses native_decide; kernel-clean port pending; canonical statement still sorry  
**Next action:** Port certificate to merged kernel bridge, set answer(True), prove via W_ge_succ_of_checks; verify build.

## `W_3_23_lower` — Already solved internally (cat 0)

**File:** `FormalConjectures/GreensOpenProblems/14.lean:229`  
**Secondary category:** 1 (Already solved externally)  
**Statement:** Decide whether W(3,23) >= 516 (AKS14 Table 2 lower bound; answer: yes).  
**Source:** Ahmed-Kullmann-Snevily 2014, Table 2  
**Statement matches intent:** yes  
**Known status:** Solved internally on branch agent/green14-certificates-20-39 (PR #23): valid_23 native_decide certificate at N = 515; merged bridge gives W 3 23 >= 516. Published lower bound (AKS14).  
**Difficulty:** math 2/10, Lean 4/10 · **Compute:** small · **Confidence:** medium  
**Evidence:** valid_23 in branch Green14Certificates.lean; N=515 matches >= 516.  
**Flags:** branch proof uses native_decide; kernel-clean port pending; canonical statement still sorry  
**Next action:** Port certificate to merged kernel bridge, set answer(True), prove via W_ge_succ_of_checks; verify build.

## `W_3_24_lower` — Already solved internally (cat 0)

**File:** `FormalConjectures/GreensOpenProblems/14.lean:233`  
**Secondary category:** 1 (Already solved externally)  
**Statement:** Decide whether W(3,24) >= 593 (AKS14 Table 2 lower bound; answer: yes).  
**Source:** Ahmed-Kullmann-Snevily 2014, Table 2  
**Statement matches intent:** yes  
**Known status:** Solved internally on branch agent/green14-certificates-20-39 (PR #23): valid_24 native_decide certificate at N = 592; merged bridge gives W 3 24 >= 593. Published lower bound (AKS14).  
**Difficulty:** math 2/10, Lean 4/10 · **Compute:** small · **Confidence:** medium  
**Evidence:** valid_24 in branch Green14Certificates.lean; N=592 matches >= 593.  
**Flags:** branch proof uses native_decide; kernel-clean port pending; canonical statement still sorry  
**Next action:** Port certificate to merged kernel bridge, set answer(True), prove via W_ge_succ_of_checks; verify build.

## `W_3_25_lower` — Already solved internally (cat 0)

**File:** `FormalConjectures/GreensOpenProblems/14.lean:237`  
**Secondary category:** 1 (Already solved externally)  
**Statement:** Decide whether W(3,25) >= 656 (AKS14 Table 2 lower bound; answer: yes).  
**Source:** Ahmed-Kullmann-Snevily 2014, Table 2  
**Statement matches intent:** yes  
**Known status:** Solved internally on branch agent/green14-certificates-20-39 (PR #23): valid_25 native_decide certificate at N = 655; merged bridge gives W 3 25 >= 656. Published lower bound (AKS14).  
**Difficulty:** math 2/10, Lean 4/10 · **Compute:** small · **Confidence:** medium  
**Evidence:** valid_25 in branch Green14Certificates.lean; N=655 matches >= 656.  
**Flags:** branch proof uses native_decide; kernel-clean port pending; canonical statement still sorry  
**Next action:** Port certificate to merged kernel bridge, set answer(True), prove via W_ge_succ_of_checks; verify build.

## `W_3_26_lower` — Already solved internally (cat 0)

**File:** `FormalConjectures/GreensOpenProblems/14.lean:241`  
**Secondary category:** 1 (Already solved externally)  
**Statement:** Decide whether W(3,26) >= 727 (AKS14 Table 2 lower bound; answer: yes).  
**Source:** Ahmed-Kullmann-Snevily 2014, Table 2  
**Statement matches intent:** yes  
**Known status:** Solved internally on branch agent/green14-certificates-20-39 (PR #23): valid_26 native_decide certificate at N = 726; merged bridge gives W 3 26 >= 727. Published lower bound (AKS14).  
**Difficulty:** math 2/10, Lean 4/10 · **Compute:** small · **Confidence:** medium  
**Evidence:** valid_26 in branch Green14Certificates.lean; N=726 matches >= 727.  
**Flags:** branch proof uses native_decide; kernel-clean port pending; canonical statement still sorry  
**Next action:** Port certificate to merged kernel bridge, set answer(True), prove via W_ge_succ_of_checks; verify build.

## `W_3_27_lower` — Already solved internally (cat 0)

**File:** `FormalConjectures/GreensOpenProblems/14.lean:245`  
**Secondary category:** 1 (Already solved externally)  
**Statement:** Decide whether W(3,27) >= 770 (AKS14 Table 2 lower bound; answer: yes).  
**Source:** Ahmed-Kullmann-Snevily 2014, Table 2  
**Statement matches intent:** yes  
**Known status:** Solved internally on branch agent/green14-certificates-20-39 (PR #23): valid_27 native_decide certificate at N = 769; merged bridge gives W 3 27 >= 770. Published lower bound (AKS14).  
**Difficulty:** math 2/10, Lean 4/10 · **Compute:** small · **Confidence:** medium  
**Evidence:** valid_27 in branch Green14Certificates.lean; N=769 matches >= 770.  
**Flags:** branch proof uses native_decide; kernel-clean port pending; canonical statement still sorry  
**Next action:** Port certificate to merged kernel bridge, set answer(True), prove via W_ge_succ_of_checks; verify build.

## `W_3_28_lower` — Already solved internally (cat 0)

**File:** `FormalConjectures/GreensOpenProblems/14.lean:249`  
**Secondary category:** 1 (Already solved externally)  
**Statement:** Decide whether W(3,28) >= 827 (AKS14 Table 2 lower bound; answer: yes).  
**Source:** Ahmed-Kullmann-Snevily 2014, Table 2  
**Statement matches intent:** yes  
**Known status:** Solved internally on branch agent/green14-certificates-20-39 (PR #23): valid_28 native_decide certificate at N = 826; merged bridge gives W 3 28 >= 827. Published lower bound (AKS14).  
**Difficulty:** math 2/10, Lean 4/10 · **Compute:** small · **Confidence:** medium  
**Evidence:** valid_28 in branch Green14Certificates.lean; N=826 matches >= 827.  
**Flags:** branch proof uses native_decide; kernel-clean port pending; canonical statement still sorry  
**Next action:** Port certificate to merged kernel bridge, set answer(True), prove via W_ge_succ_of_checks; verify build.

## `W_3_29_lower` — Already solved internally (cat 0)

**File:** `FormalConjectures/GreensOpenProblems/14.lean:253`  
**Secondary category:** 1 (Already solved externally)  
**Statement:** Decide whether W(3,29) >= 868 (AKS14 Table 2 lower bound; answer: yes).  
**Source:** Ahmed-Kullmann-Snevily 2014, Table 2  
**Statement matches intent:** yes  
**Known status:** Solved internally on branch agent/green14-certificates-20-39 (PR #23): valid_29 native_decide certificate at N = 867; merged bridge gives W 3 29 >= 868. Published lower bound (AKS14).  
**Difficulty:** math 2/10, Lean 4/10 · **Compute:** small · **Confidence:** medium  
**Evidence:** valid_29 in branch Green14Certificates.lean; N=867 matches >= 868.  
**Flags:** branch proof uses native_decide; kernel-clean port pending; canonical statement still sorry  
**Next action:** Port certificate to merged kernel bridge, set answer(True), prove via W_ge_succ_of_checks; verify build.

## `W_3_30_lower` — Already solved internally (cat 0)

**File:** `FormalConjectures/GreensOpenProblems/14.lean:257`  
**Secondary category:** 1 (Already solved externally)  
**Statement:** Decide whether W(3,30) >= 903 (AKS14 Table 2 lower bound; answer: yes).  
**Source:** Ahmed-Kullmann-Snevily 2014, Table 2  
**Statement matches intent:** yes  
**Known status:** Solved internally on branch agent/green14-certificates-20-39 (PR #23): valid_30 native_decide certificate at N = 902; merged bridge gives W 3 30 >= 903. Published lower bound (AKS14).  
**Difficulty:** math 2/10, Lean 4/10 · **Compute:** small · **Confidence:** medium  
**Evidence:** valid_30 in branch Green14Certificates.lean; N=902 matches >= 903.  
**Flags:** branch proof uses native_decide; kernel-clean port pending; canonical statement still sorry  
**Next action:** Port certificate to merged kernel bridge, set answer(True), prove via W_ge_succ_of_checks; verify build.

## `W_3_31_lower` — Already solved internally (cat 0)

**File:** `FormalConjectures/GreensOpenProblems/14.lean:262`  
**Secondary category:** 1 (Already solved externally)  
**Statement:** Decide whether W(3,31) > 930 (AKS14 Table 3 lower bound; answer: yes).  
**Source:** Ahmed-Kullmann-Snevily 2014, Table 3  
**Statement matches intent:** yes  
**Known status:** Solved internally on branch agent/green14-certificates-20-39 (PR #23): valid_31 native_decide certificate at N = 930 gives W >= 931 > 930 via merged bridge. Published lower bound (AKS14).  
**Difficulty:** math 2/10, Lean 4/10 · **Compute:** medium · **Confidence:** medium  
**Evidence:** valid_31 in branch Green14Certificates.lean; strict > handled since certificate at N = 930 yields W >= 931.  
**Flags:** branch proof uses native_decide; kernel-clean port pending (kernel decide cost grows ~N^2); canonical statement still sorry  
**Next action:** Port certificate to merged kernel bridge, set answer(True), prove via W_ge_succ_of_checks (N+1 = 931 > 930); verify build.

## `W_3_32_lower` — Already solved internally (cat 0)

**File:** `FormalConjectures/GreensOpenProblems/14.lean:266`  
**Secondary category:** 1 (Already solved externally)  
**Statement:** Decide whether W(3,32) > 1006 (AKS14 Table 3 lower bound; answer: yes).  
**Source:** Ahmed-Kullmann-Snevily 2014, Table 3  
**Statement matches intent:** yes  
**Known status:** Solved internally on branch agent/green14-certificates-20-39 (PR #23): valid_32 native_decide certificate at N = 1006 gives W >= 1007 > 1006 via merged bridge. Published lower bound (AKS14).  
**Difficulty:** math 2/10, Lean 4/10 · **Compute:** medium · **Confidence:** medium  
**Evidence:** valid_32 in branch Green14Certificates.lean at N = 1006.  
**Flags:** branch proof uses native_decide; kernel-clean port pending; canonical statement still sorry  
**Next action:** Port certificate to merged kernel bridge, set answer(True); verify build.

## `W_3_33_lower` — Already solved internally (cat 0)

**File:** `FormalConjectures/GreensOpenProblems/14.lean:270`  
**Secondary category:** 1 (Already solved externally)  
**Statement:** Decide whether W(3,33) > 1063 (AKS14 Table 3 lower bound; answer: yes).  
**Source:** Ahmed-Kullmann-Snevily 2014, Table 3  
**Statement matches intent:** yes  
**Known status:** Solved internally on branch agent/green14-certificates-20-39 (PR #23): valid_33 native_decide certificate at N = 1063 gives W >= 1064 > 1063 via merged bridge. Published lower bound (AKS14).  
**Difficulty:** math 2/10, Lean 4/10 · **Compute:** medium · **Confidence:** medium  
**Evidence:** valid_33 in branch Green14Certificates.lean at N = 1063.  
**Flags:** branch proof uses native_decide; kernel-clean port pending; canonical statement still sorry  
**Next action:** Port certificate to merged kernel bridge, set answer(True); verify build.

## `W_3_34_lower` — Already solved internally (cat 0)

**File:** `FormalConjectures/GreensOpenProblems/14.lean:274`  
**Secondary category:** 1 (Already solved externally)  
**Statement:** Decide whether W(3,34) > 1143 (AKS14 Table 3 lower bound; answer: yes).  
**Source:** Ahmed-Kullmann-Snevily 2014, Table 3  
**Statement matches intent:** yes  
**Known status:** Solved internally on branch agent/green14-certificates-20-39 (PR #23): valid_34 native_decide certificate at N = 1143 gives W >= 1144 > 1143 via merged bridge. Published lower bound (AKS14).  
**Difficulty:** math 2/10, Lean 4/10 · **Compute:** medium · **Confidence:** medium  
**Evidence:** valid_34 in branch Green14Certificates.lean at N = 1143.  
**Flags:** branch proof uses native_decide; kernel-clean port pending; canonical statement still sorry  
**Next action:** Port certificate to merged kernel bridge, set answer(True); verify build.

## `W_3_35_lower` — Already solved internally (cat 0)

**File:** `FormalConjectures/GreensOpenProblems/14.lean:278`  
**Secondary category:** 1 (Already solved externally)  
**Statement:** Decide whether W(3,35) > 1204 (AKS14 Table 3 lower bound; answer: yes).  
**Source:** Ahmed-Kullmann-Snevily 2014, Table 3  
**Statement matches intent:** yes  
**Known status:** Solved internally on branch agent/green14-certificates-20-39 (PR #23): valid_35 native_decide certificate at N = 1204 gives W >= 1205 > 1204 via merged bridge. Published lower bound (AKS14).  
**Difficulty:** math 2/10, Lean 4/10 · **Compute:** medium · **Confidence:** medium  
**Evidence:** valid_35 in branch Green14Certificates.lean at N = 1204.  
**Flags:** branch proof uses native_decide; kernel-clean port pending; canonical statement still sorry  
**Next action:** Port certificate to merged kernel bridge, set answer(True); verify build.

## `W_3_36_lower` — Already solved internally (cat 0)

**File:** `FormalConjectures/GreensOpenProblems/14.lean:282`  
**Secondary category:** 1 (Already solved externally)  
**Statement:** Decide whether W(3,36) > 1257 (AKS14 Table 3 lower bound; answer: yes).  
**Source:** Ahmed-Kullmann-Snevily 2014, Table 3  
**Statement matches intent:** yes  
**Known status:** Solved internally on branch agent/green14-certificates-20-39 (PR #23): valid_36 native_decide certificate at N = 1257 gives W >= 1258 > 1257 via merged bridge. Published lower bound (AKS14).  
**Difficulty:** math 2/10, Lean 4/10 · **Compute:** medium · **Confidence:** medium  
**Evidence:** valid_36 in branch Green14Certificates.lean at N = 1257.  
**Flags:** branch proof uses native_decide; kernel-clean port pending; canonical statement still sorry  
**Next action:** Port certificate to merged kernel bridge, set answer(True); verify build.

## `W_3_37_lower` — Already solved internally (cat 0)

**File:** `FormalConjectures/GreensOpenProblems/14.lean:286`  
**Secondary category:** 1 (Already solved externally)  
**Statement:** Decide whether W(3,37) > 1338 (AKS14 Table 3 lower bound; answer: yes).  
**Source:** Ahmed-Kullmann-Snevily 2014, Table 3  
**Statement matches intent:** yes  
**Known status:** Solved internally on branch agent/green14-certificates-20-39 (PR #23): valid_37 native_decide certificate at N = 1338 gives W >= 1339 > 1338 via merged bridge. Published lower bound (AKS14).  
**Difficulty:** math 2/10, Lean 4/10 · **Compute:** medium · **Confidence:** medium  
**Evidence:** valid_37 in branch Green14Certificates.lean at N = 1338.  
**Flags:** branch proof uses native_decide; kernel-clean port pending; canonical statement still sorry  
**Next action:** Port certificate to merged kernel bridge, set answer(True); verify build.

## `W_3_38_lower` — Already solved internally (cat 0)

**File:** `FormalConjectures/GreensOpenProblems/14.lean:290`  
**Secondary category:** 1 (Already solved externally)  
**Statement:** Decide whether W(3,38) > 1378 (AKS14 Table 3 lower bound; answer: yes).  
**Source:** Ahmed-Kullmann-Snevily 2014, Table 3  
**Statement matches intent:** yes  
**Known status:** Solved internally on branch agent/green14-certificates-20-39 (PR #23): valid_38 native_decide certificate at N = 1378 gives W >= 1379 > 1378 via merged bridge. Published lower bound (AKS14).  
**Difficulty:** math 2/10, Lean 4/10 · **Compute:** medium · **Confidence:** medium  
**Evidence:** valid_38 in branch Green14Certificates.lean at N = 1378.  
**Flags:** branch proof uses native_decide; kernel-clean port pending; canonical statement still sorry  
**Next action:** Port certificate to merged kernel bridge, set answer(True); verify build.

## `W_3_39_lower` — Already solved internally (cat 0)

**File:** `FormalConjectures/GreensOpenProblems/14.lean:294`  
**Secondary category:** 1 (Already solved externally)  
**Statement:** Decide whether W(3,39) > 1418 (AKS14 Table 3 lower bound; answer: yes).  
**Source:** Ahmed-Kullmann-Snevily 2014, Table 3  
**Statement matches intent:** yes  
**Known status:** Solved internally on branch agent/green14-certificates-20-39 (PR #23): valid_39 native_decide certificate at N = 1418 gives W >= 1419 > 1418 via merged bridge. Published lower bound (AKS14). Largest instance; kernel decide will be the most expensive of the family.  
**Difficulty:** math 2/10, Lean 5/10 · **Compute:** medium · **Confidence:** medium  
**Evidence:** valid_39 in branch Green14Certificates.lean at N = 1418 with 105-element colour-0 support list.  
**Flags:** branch proof uses native_decide; kernel-clean port pending; canonical statement still sorry  
**Next action:** Port certificate to merged kernel bridge (bitmask form), set answer(True); verify build. If kernel decide is too slow at N = 1418, fall back to native_decide subject to repo policy.

## `green_14_polynomial` — Already solved externally (cat 1)

**File:** `FormalConjectures/GreensOpenProblems/14.lean:66`  
**Secondary category:** 4 (Vacuously true / accidentally weakened)  
**Statement:** As formalized: for every fixed k >= 4, is the mixed 2-colour van der Waerden number W(k,r) bounded by a polynomial in r? Encoded as answer(sorry) <-> forall k >= 4, exists d, W k r = O(r^d).  
**Source:** Ben Green, 100 open problems (2024), Problem 14; Green, New lower bounds for van der Waerden numbers, Forum Math. Pi 10 (2022) [Gr21]  
**Statement matches intent:** suspect — The as-formalized question is NOT open: W(k,r) >= W(3,r) for all k >= 4 (a colouring with no red 3-AP a fortiori has no red 4-AP, so the guarantee set for (k,r) is contained in that for (3,r) and the sInf is larger), and W(3,r) is superpolynomial in r [Gr21], so the RHS is False for every k >= 4 and answer(False) is forced. The file itself records the k=3 fact (green_14_polynomial_k_eq_3, labeled solved). Green's genuine Problem 14 must concern something else (growth rate of W(3,r), explicit colourings, or possibly many-colour w(3;r)); the source PDF returned HTTP 403 so exact text unverified.  
**Known status:** Truth value of the encoded yes/no is known: NO, by [Gr21] superpolynomial lower bound W(3,r) >= exp(c (log r)^{4/3-o(1)}) plus trivial monotonicity in k. But a legitimate Lean proof requires formalizing a superpolynomial lower bound for W(3,r) (Green's or Hunter's construction) -- research-scale; no shortcut exists since no elementary superpolynomial off-diagonal bound is known.  
**Difficulty:** math 9/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Monotonicity argument is airtight (first 3 terms of a 4-AP form a 3-AP; embedding argument mirrors the already-merged mixedMonoAPGuaranteeSet_upward). [Gr21] is published (Forum of Mathematics Pi). WebSearch confirms Gr21 disproved polynomial growth of W(3,k) (gilkalai.wordpress.com 2021-02-08 post; arxiv.org/abs/2102.01543); direct fetch of Green's PDF blocked (403), so the exact Problem 14 wording is unverified.  
**Flags:** mislabeled research-open: encoded answer is determined (False); probable prose-formal mismatch with Green's actual Problem 14; needs literature check of exact source text  
**Next action:** Report upstream: label should not be 'research open' as stated, and the statement likely misrenders Problem 14; either restate faithfully to Green's text or record answer(False) with the k-monotonicity reduction to the (still-to-be-formalized) k=3 superpolynomial bound. Formal resolution effort: research-scale.

## `green_14_variant_2r2` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/GreensOpenProblems/14.lean:133`  
**Secondary category:** 6 (Computationally solvable with certificate)  
**Statement:** Exhibit an explicit r >= 3 and a 2-colouring of {1,...,2r^2-1} with no colour-0 3-term AP and no colour-1 r-term AP, i.e. write down a colouring witnessing W(3,r) >= 2r^2 for some r.  
**Source:** Ben Green, 100 open problems (2024), Problem 14 (explicit-colouring remark); Ahmed-Kullmann-Snevily, Discrete Appl. Math. 174 (2014)  
**Statement matches intent:** yes  
**Known status:** Genuinely open. Known exact values W(3,r) for r <= 19 and certified lower bounds up to r = 39 (AKS14, reproduced on fork branch agent/green14-certificates-20-39) all stay BELOW r^2 at the upper end (e.g. W(3,39) > 1418 vs 2*39^2 = 3042), so no known r qualifies; Green's superpolynomial bound only bites at astronomically large r.  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** large · **Confidence:** high  
**Evidence:** AKS14 data and the fork's own t=20-39 certificates show W(3,r)/r^2 hovering near or below 1 for all computationally reached r; a 2r^2 witness needs either massive SAT compute at larger r or new explicit constructions (exactly Green's point). Internal W(3,20) campaign (PRs #23, #149, #173, #242-248) targets fixed small bounds, not the 2r^2 threshold.  
**Next action:** In principle SAT-searchable per candidate r (certificate = the colouring, kernel-checkable via the merged FunctionCertificateBridge), but the true W(3,r) likely does not exceed 2r^2 at any SAT-feasible r; treat as open research. First milestone: push certified lower bounds past r^2 for some r.

## `green_15` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/GreensOpenProblems/15.lean:39`  
**Statement:** Decide whether there is a Lipschitz function f : N -> Z whose graph {(n, f(n))} in Z^2 contains no 3-term arithmetic progression.  
**Source:** Green, 100 open problems (2024), Problem 15; Brown-Jungic-Poelstra, Integers 14 (2014); Cassaigne-Currie-Schaeffer-Shallit, Adv. Appl. Math. 56 (2014)  
**Statement matches intent:** yes  
**Known status:** Open. Equivalent to the notorious additive-square-free word problem (Pirillo-Varricchio 1994; Halbeisen-Hungerbuhler 2000): a graph 3-AP with difference (d1,d2), d1>0, is exactly two adjacent length-d1 blocks of the bounded step sequence with equal sums. The 4-term analog (additive cubes) is solved [CCS14], matching the in-file solved variant green_15_ap4.  
**Difficulty:** math 9/10, Lean 9/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Checked Set.IsAPOfLengthFree: a length-3 AP subset must have ENat.card 3, forcing three distinct points and d != 0, so no trivial-AP loophole. Graph over N (not Z) matches Green's statement; arbitrary Lipschitz constant K quantified existentially as intended. answer() iff encoding faithful.  
**Next action:** Leave as open; no internal or external resolution. Any progress would be a breakthrough in combinatorics on words.

## `green_16` — Vacuously true / accidentally weakened (cat 4)

**File:** `FormalConjectures/GreensOpenProblems/16.lean:44`  
**Secondary category:** 8 (Deep but approachable research problem)  
**Statement:** For each N, exhibit a maximum-size subset of [N] with no solution to x+3y=2z+2w in distinct elements, with its cardinality given as an answer() term.  
**Source:** Green, 100 open problems (2024), Problem 16; Ruzsa, Acta Arith. 65 (1993); Schoen-Sisask, Forum Math. Sigma 4 (2016)  
**Statement matches intent:** suspect — The encoding admits the degenerate echo answer := Green16.f N (the sSup definition in the same file): the theorem then only asserts that a maximum-cardinality solution-free subset exists and is MaximalFor, a routine finite argument (~30 lines) that resolves nothing. Also asks for the exact value for every N, stronger than the intended asymptotic determination of f(N).  
**Known status:** Intended problem wide open: f(N) known only between c*N^(1/2) [Ruzsa] and N*exp(-c(log N)^(1/7)) [Schoen-Sisask], an enormous gap.  
**Difficulty:** math 9/10, Lean 3/10 · **Compute:** none · **Confidence:** high  
**Evidence:** f N = sSup over a finite nonempty (empty set qualifies) bounded set of cardinalities, so the sup is attained by a max-card set which satisfies Mathlib's MaximalFor; A.card = f N then holds definitionally. SolutionFree's [x,y,z,w].Nodup matches Green's 'distinct integers' convention.  
**Flags:** answer-echo loophole (answer := f N); exact-value-for-all-N reading stronger than source's asymptotic question  
**Next action:** Tighten the spec (e.g. ask for asymptotics of f, or forbid self-referential answers by convention); the echo closure could be formalized quickly if one only wants to discharge the formal statement.

## `green_16_conjectured_lower_bound` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/GreensOpenProblems/16.lean:64`  
**Statement:** Conjecture that the Schoen-Sisask upper bound is sharp: f(N) >> N*exp(-c(log N)^(1/7)) for some c > 0.  
**Source:** Green, 100 open problems (2024), Problem 16 (conjectural remark)  
**Statement matches intent:** yes  
**Known status:** Open. Best known lower bound is only N^(1/2) (Ruzsa); the conjecture asserts near-linear solution-free sets exist, an exponential gap from what is known.  
**Difficulty:** math 9/10, Lean 9/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** Statement is the big-O rendering (N exp(-c(log N)^(1/7)) = O(f N)) of the conjectured matching bound; consistent with the known bounds and not refuted by anything in the literature I know.  
**Flags:** needs literature check: whether Green states this as a conjecture or only as a possibility  
**Next action:** Leave open; progress = any lower bound N^(1/2+eps). Attribution of this exact conjectured shape to Green's text should be double-checked.

## `green_16_lower_bound` — Solved mathematically, not yet formalized (cat 5)

**File:** `FormalConjectures/GreensOpenProblems/16.lean:52`  
**Statement:** Ruzsa's lower bound: the maximum size f(N) of a subset of [N] with no distinct-element solution to x+3y=2z+2w satisfies f(N) >> N^(1/2).  
**Source:** Ruzsa, Solving a linear equation in a set of integers I, Acta Arith. 65 (1993), 259-282; Green Problem 16  
**Statement matches intent:** yes  
**Known status:** Published theorem (Ruzsa 1993, quoted in Green's Problem 16), but mis-tagged 'research open' in the repo despite the docstring citing the proof.  
**Difficulty:** math 5/10, Lean 7/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** Checked repo notation: g ≪ f is IsBigO atTop g f over ℕ → ℝ, so the statement N^(1/2) = O(f N) is the correct rendering of f(N) >> N^(1/2). No prior PR or campaign in the fork touches Green 16 (register only has Green14 work).  
**Flags:** mis-tagged research open (published result); needs literature check: confirm Ruzsa's exponent for this exact equation is 1/2  
**Next action:** Retag research solved; formalize Ruzsa's Sidon-type construction for this invariant equation - medium effort (construction plus counting).

## `green_16_upper_bound` — Solved mathematically, not yet formalized (cat 5)

**File:** `FormalConjectures/GreensOpenProblems/16.lean:58`  
**Statement:** Schoen-Sisask upper bound: f(N) << N*exp(-c(log N)^(1/7)) for sets of [N] with no distinct-element solution to x+3y=2z+2w.  
**Source:** Schoen-Sisask, Roth's theorem for four variables and additive structures in sums of sparse sets, Forum Math. Sigma 4 (2016); Green Problem 16  
**Statement matches intent:** yes  
**Known status:** Published theorem (Schoen-Sisask 2016, quoted by Green), mis-tagged 'research open'. Proof uses Croot-Sisask almost-periodicity and Bogolyubov-type arguments - none of it in Mathlib.  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** Direction correct under repo's ≪ = big-O convention: f = O(N exp(-c(log N)^(1/7))). Formal SolutionFree only forbids all-distinct solutions (weaker restriction, larger extremal family), so the upper bound is the harder direction; Green's own problem statement defines f with the distinctness convention and quotes this bound, and degenerate solutions are O(N^2), so the literature proof covers it.  
**Flags:** mis-tagged research open (published result); needs literature check: Schoen-Sisask theorem stated for x+y+z=3w; verify their method's coverage of x+3y=2z+2w as quoted by Green  
**Next action:** Retag research solved; formalization is research-scale (almost-periodicity machinery, Fourier analysis on Z).

## `zhao_question` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/GreensOpenProblems/16.lean:81`  
**Statement:** Zhao's question (via Green): can a subset of [N] of size N^(1/3-o(1)) avoid nontrivial solutions to x+2y+3z = x'+2y'+3z'? Formalized as the assertion that it cannot.  
**Source:** Green, 100 open problems (2024), Problem 16 remark (personal communication from Yufei Zhao)  
**Statement matches intent:** suspect — Two issues: (1) an open yes/no question is formalized as a committed NO (not-exists h -> 0 with g(N) >= N^(1/3-h(N)) eventually) instead of the repo's answer() iff idiom - if the answer is yes (Behrend-style constructions make yes plausible), the formal statement is false; (2) 'nontrivial solution' is rendered as all six variables distinct ([...].Nodup), strictly weaker than the usual nontriviality (x,y,z) != (x',y',z'), so the formal g(N) can exceed the intended extremal function.  
**Known status:** Open in both directions as far as known; counting gives g(N) << N^(1/3), question is whether that is attained up to N^(o(1)).  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** g := sSup of a nonempty bounded cardinality set (well-defined); h -> 0 may be negative but the existential makes that harmless. The all-distinct convention permits solutions with x = x' and 2y+3z = 2y'+3z' nontrivially, which the usual convention forbids.  
**Flags:** encodes a definite negative answer to an open question; distinctness convention broader than standard nontriviality; needs literature check  
**Next action:** Rewrite as answer(sorry) iff exists-form, and align the nontriviality convention with the source before investing proof effort.

## `green_18` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/GreensOpenProblems/18.lean:56`  
**Statement:** Decide whether every dense subset A of G x G, G an arbitrary finite group, contains >>_alpha |G|^3 naive corners (x,y),(gx,y),(x,gy) with g != 1.  
**Source:** Green, 100 open problems (2024), Problem 18; Austin, Ajtai-Szemeredi theorems over quasirandom groups (2016), Question 2  
**Statement matches intent:** yes  
**Known status:** Open (Austin's Question 2). The BMZ-corner variant (x,y),(xg,y),(x,gy) is solved by Solymosi 2013 and is correctly tagged research solved in the same file.  
**Difficulty:** math 9/10, Lean 9/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** Quantifier structure (forall alpha, exists c, exists m0, forall large G, forall alpha-dense A) is the standard finitary rendering of >>_alpha with a size threshold needed to exclude tiny groups (trivial group has zero g != 1 triples). g != 1 restriction follows [Au16] as the docstring notes and only discards <= |G|^2 triples.  
**Next action:** Leave open. Key obstruction: no nonabelian analog of the Ajtai-Szemeredi argument for the gx-side action; progress = quasirandom-group case with quantitative bounds.

## `green_19.lower` — Solved mathematically, not yet formalized (cat 5)

**File:** `FormalConjectures/GreensOpenProblems/19.lean:83`  
**Statement:** The popular-difference corners exponent C in F_2^n satisfies C >= 3.13.  
**Source:** Mandache, A variant of the corners theorem, Math. Proc. Camb. Phil. Soc. 171 (2021); superseded by Fox-Sah-Sawhney-Stoner-Zhao, Triforce and corners, MPCPS 169 (2020) (C = 4)  
**Statement matches intent:** yes  
**Known status:** Published: Mandache's construction gives C >= 3.13; FSSZ's triforce construction improves this to C >= 4, and the same file's green_19 (C = 4) is already tagged research solved. This declaration is mis-tagged research open although its own docstring cites the proof.  
**Difficulty:** math 7/10, Lean 9/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** C := sInf {c | ValidExponent c} is safe: the set is upward closed, nonempty (c slightly above 4 valid by Mandache's positive result) and bounded below (construction), so no Real.sInf junk-value shortcut exists for proving C >= 3.13 - the real construction is required. No internal PR/campaign targets Green 19.  
**Flags:** mis-tagged research open (published result)  
**Next action:** Retag research solved; formalize Mandache's (or directly FSSZ's) lower-bound construction plus the sInf bookkeeping - large effort (probabilistic/entropy construction).

## `green_19.upper` — Solved mathematically, not yet formalized (cat 5)

**File:** `FormalConjectures/GreensOpenProblems/19.lean:88`  
**Statement:** The popular-difference corners exponent C in F_2^n satisfies C <= 4.  
**Source:** Mandache, MPCPS 171 (2021) (positive result: popular difference with ~alpha^4 density of corners); Green Problem 19  
**Statement matches intent:** yes  
**Known status:** Published (Mandache's positive theorem; also part of the resolved C = 4 picture with FSSZ). Mis-tagged research open despite docstring citing the proof.  
**Difficulty:** math 7/10, Lean 9/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** ValidExponent's shape (exists K uniform in alpha, per-alpha eventual threshold in n) absorbs the literature's alpha^4 - o(1) form via K = 1/2, so ValidExponent 4 (hence sInf <= 4) follows from the published theorem. Note C <= 4 also cannot be short-cut via sInf-empty junk since that would require proving the valid set empty, which is false.  
**Flags:** mis-tagged research open (published result)  
**Next action:** Retag research solved; formalizing Mandache's positive result needs heavy regularity/analytic machinery - research-scale.

## `green_2` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/GreensOpenProblems/2.lean:54`  
**Statement:** Decide whether every set A of n integers (n large) contains a subset S of size at least (log n)^100 whose restricted sumset S +^ S is disjoint from A.  
**Source:** Green, 100 open problems (2024), Problem 2; Erdos 1965; Sanders, Canad. J. Math. 73 (2021); Ruzsa, Ramanujan J. 9 (2005)  
**Statement matches intent:** yes  
**Known status:** Open (Erdos-Moser sum-avoiding subset problem). Known: M(A) >> (log n)^(1+c) (Sanders 2021) and constructions with M(A) < exp(C sqrt(log n)) (Ruzsa 2005), consistent with either answer to the (log n)^100 question.  
**Difficulty:** math 9/10, Lean 9/10 · **Compute:** none · **Confidence:** high  
**Evidence:** maxRestrictedSumAvoidingSubsetSize = sup of card over the powerset filter is well-defined (empty set qualifies); restrictedSumset uses offDiag so s1 != s2 as in the source; eventual quantifier over n handles small-n junk of Real.log. answer() iff encoding faithful to the yes/no question.  
**Next action:** Leave open; progress = improving Sanders' exponent or pushing Ruzsa's construction below (log n)^K.

## `green_22` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/GreensOpenProblems/22.lean:70`  
**Statement:** Produce a bound function for N_0(r) (smallest N so that every r-colouring of [N] has x,y >= 3 with x+y and xy the same colour) that is little-o of the Green-Sawhney bound exp(exp(r^50)).  
**Source:** Green, 100 open problems (2024), Problem 22; Green-Sawhney, arXiv:2511.09365 (2025); Moreira, Ann. of Math. 185 (2017)  
**Statement matches intent:** suspect — Formalizing 'find reasonable bounds' as 'any o(exp(exp(r^50)))' is fragile: published round-exponent bounds almost always carry slack, so an o()-improvement (e.g. exp(exp(r^50))/r) is plausibly already implicit in the Green-Sawhney proof, making the formal statement much weaker than the intended qualitative improvement (e.g. single-exponential bounds). Echo ans := N_0 itself does not work (needs the unknown N_0 = o(GSB)), so it is not trivially closable.  
**Known status:** Intended problem open; [GrSa25] gives the first effective double-exponential bound, Moreira guarantees N_0 is well-defined.  
**Difficulty:** math 9/10, Lean 9/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** N_0 r = sInf; for the set-empty junk (sInf = 0) to help one would need to disprove Moreira's finitary corollary, which is a theorem, so no loophole. Second conjunct sits vacuously inside the eventually-quantifier but is r-independent, harmless. Fin r for r = 0 makes the coloring quantifier vacuous for N >= 1, giving N_0 0 = 1 - screened out by atTop.  
**Flags:** o(published-bound) improvement target likely extractable from source's own proof slack; x,y >= 3 convention should be checked against Green's exact statement  
**Next action:** Consider re-specifying the improvement target (e.g. exp(r^C) or exp(exp(r^eps))). As stated, first try extracting explicit slack from the GrSa25 proof.

## `conjecture` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/GreensOpenProblems/24.lean:86`  
**Statement:** Aaronson's conjecture: the maximum number of affine translates of {0,1,3} in an n-element integer set is (1/3 + o(1))n^2, i.e. gamma = limsup f(n)/n^2 = 1/3.  
**Source:** Aaronson, Maximising the number of solutions to a linear equation in a set of integers, Bull. LMS 51 (2019), p.579; Green Problem 24; Hardy-Littlewood (1928) bounds  
**Statement matches intent:** yes  
**Known status:** Open. Known 1/12 <= gamma <= 3/4 via Hardy-Littlewood-type bounds (in-file variants, tagged solved); the interval [n] achieves ~n^2/3 under this count, so the conjecture says intervals are asymptotically optimal.  
**Difficulty:** math 8/10, Lean 8/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** Count convention verified: filter over ordered pairs (x,y), x != y, x+3(y-x) in A enumerates (a,d) with d in Z \ {0}, exactly the ordered solutions (a, a+d, a+3d) of 2x+z=3y with distinct entries; interval [n] then gives ~n^2/6 for each sign of d, total n^2/3, consistent with the conjectured constant 1/3 - so the normalization matches Aaronson's solution count. gamma as limsup of a bounded real sequence is well-defined.  
**Next action:** Leave open; a first milestone would be formalizing the interval count to get gamma >= 1/3 (improving the stated 1/12 bound is already easy mathematically).

## `green_24` — Vacuously true / accidentally weakened (cat 4)

**File:** `FormalConjectures/GreensOpenProblems/24.lean:52`  
**Secondary category:** 8 (Deep but approachable research problem)  
**Statement:** Give, as an answer() term, the exact maximum number of affine translates of {0,1,3} that a set of n integers can contain, for every n.  
**Source:** Green, 100 open problems (2024), Problem 24; Aaronson, Bull. LMS 51 (2019)  
**Statement matches intent:** suspect — Doubly unfaithful: (1) the degenerate echo answer := max013AffineTranslates n closes the theorem by intro n; rfl, resolving nothing; (2) even under an honest-answer convention the statement demands an exact closed form for every n, far stronger than the source's asymptotic question (conjectured (1/3 + o(1))n^2), and such an exact formula is unlikely to exist.  
**Known status:** Intended problem open (Aaronson's conjecture gamma = 1/3, see variants.conjecture); formal statement trivially closable via echo.  
**Difficulty:** math 8/10, Lean 1/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Statement is literally 'forall n, f n = answer(sorry)' with f the def two lines above; answer elaborator imposes no closed-form constraint (checked Util/Answer.lean), so answer := f n typechecks and rfl closes.  
**Flags:** answer-echo loophole (rfl); exact-formula-for-all-n vs asymptotic source question  
**Next action:** Respec as the asymptotic question (the file's variants.conjecture already does this); flag the echo loophole to maintainers.

## `green_25` — Vacuously true / accidentally weakened (cat 4)

**File:** `FormalConjectures/GreensOpenProblems/25.lean:54`  
**Secondary category:** 8 (Deep but approachable research problem)  
**Statement:** Characterize, as an answer() set, exactly which functions k(N) have the property that every partition of [N] into k(N) parts has union of restricted sumsets of size at least N/10 (for large N).  
**Source:** Green, 100 open problems (2024), Problem 25; Erdos-Sarkozy-Sos, Irregularities of partitions (1989)  
**Statement matches intent:** suspect — The statement is 'S = answer(sorry)' for an explicitly defined set S of functions; the degenerate echo answer := S closes it by rfl. Under an honest-answer convention it demands an exact characterization of the threshold set of functions, well beyond the source's ask (narrow the gap between log log N and N/log N).  
**Known status:** Intended threshold problem open: property holds for k << log log N [ESS89] and fails for k of order N/log N [ESS89]; nothing in between is known.  
**Difficulty:** math 9/10, Lean 1/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Set-equality answer pattern with the LHS a closed term; rfl echo typechecks. Property25 bakes 1 <= k <= N into the predicate so no vacuity issue from nonexistent Finpartitions.  
**Flags:** answer-echo loophole (rfl); exact-characterization vs threshold-gap source question  
**Next action:** Respec as bound-improvement statements (the file's green_25.upper/.lower already do this); flag the echo loophole.

## `green_25.lower` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/GreensOpenProblems/25.lean:68`  
**Statement:** Conjecture: there is a threshold function growing faster than log log N such that every k(N) = O(that threshold) forces the union-of-restricted-sumsets property for large N.  
**Source:** Green, 100 open problems (2024), Problem 25 (contributed improvement conjecture over ESS89)  
**Statement matches intent:** yes  
**Known status:** Open. ESS89 proves the property for k = o(log log N); any asymptotically larger threshold is unknown.  
**Difficulty:** math 8/10, Lean 8/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** Checked repo notation: k ≪ ans is IsBigO atTop, so the statement asks that all k = O(ans) work - correct Vinogradov reading. bestLower =o ans forces a genuine asymptotic improvement, no echo possible.  
**Flags:** improvement-style conjecture authored by formalizer, not verbatim in source  
**Next action:** Leave open; milestone: property for k ~ C log log N with explicit constant, then (log log N)^(1+eps).

## `green_25.upper` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/GreensOpenProblems/25.lean:59`  
**Statement:** Conjecture: there is a partition-count function k(N) = o(N/log N) for which the union-of-restricted-sumsets property (size >= N/10) fails infinitely often.  
**Source:** Green, 100 open problems (2024), Problem 25 (contributed improvement conjecture over ESS89)  
**Statement matches intent:** yes  
**Known status:** Open. ESS89's failure construction needs Theta(N/log N) parts; whether fewer parts can defeat the N/10 bound is unknown.  
**Difficulty:** math 8/10, Lean 8/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** No echo loophole: the answer function must satisfy a genuine little-o improvement plus a failure proof. The eventual 1 <= ans N <= N side condition prevents junk failures of Property25 from its embedded range conjuncts at large N.  
**Flags:** improvement-style conjecture authored by formalizer, not verbatim in source  
**Next action:** Leave open; a first milestone is re-analyzing the ESS89 construction to see how far below N/log N it can be pushed.

## `green_26.variants.open` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/GreensOpenProblems/26.lean:81`  
**Statement:** Decide the Additive Basis Conjecture: for every prime p there is a constant C(p) such that any C(p) linear images of {0,1}^n in F_p^n sum to all of F_p^n.  
**Source:** Green, 100 open problems (2024), Problem 26; Jaeger-Linial-Payan-Tarsi, JCTB 56 (1992); Alon-Linial-Meshulam, JCTA 57 (1991); Yu, arXiv:2510.01300 (2025)  
**Statement matches intent:** yes  
**Known status:** Open for general p (the Jaeger-Linial-Payan-Tarsi additive basis conjecture). ALM91 give c(p) log n cubes; Yu (Oct 2025) resolved p = 3 with 4 cubes (whence the in-file 100-cube p=3 problem is tagged solved). General p remains open as of Jan 2026.  
**Difficulty:** math 9/10, Lean 9/10 · **Compute:** none · **Confidence:** high  
**Evidence:** IsCube = image of {0,1}^n under a linear automorphism, so a cube is exactly the set of subset-sums of a basis, and sum of C cubes = univ is precisely the additive-basis property for C bases. Quantifier order (forall p, exists C, forall n) matches C = C(p) in the conjecture. p = 2 case is trivially true (one cube suffices) and harmless inside the universal.  
**Next action:** Leave open; monitor whether Yu's method extends beyond p = 3 - that would be the natural next milestone.

## `green_27.equivalent` — Vacuously true / accidentally weakened (cat 4)

**File:** `FormalConjectures/GreensOpenProblems/27.lean:54`  
**Secondary category:** 8 (Deep but approachable research problem)  
**Statement:** Give, as an answer() function, the asymptotics (up to equivalence along primes) of m(p), the smallest size of a set A in Z/pZ, |A| >= 2, whose sumset A+A has no element with a unique representation.  
**Source:** Green, 100 open problems (2024), Problem 27; Bedert, Combinatorica 44 (2024); Straus, J. Number Theory 8 (1976)  
**Statement matches intent:** suspect — The degenerate echo answer := m closes the theorem by IsEquivalent.refl (m - m = 0 is little-o of anything), resolving nothing. Under an honest-answer convention it asks for the exact asymptotic order of m(p), which is open (known window: ~log p * sqrt(logloglog p)/logologloglog p up to (log p)^2 by Bedert).  
**Known status:** Intended determination of m(p) open; formal statement trivially closable via echo.  
**Difficulty:** math 9/10, Lean 1/10 · **Compute:** none · **Confidence:** high  
**Evidence:** IsEquivalent l m m holds by refl regardless of m's values (checked semantics: (m - m) = 0 =o m); answer elaborator imposes no closed-form restriction. m's sInf-junk (= 0) for tiny p is screened by the primesAtTop filter.  
**Flags:** answer-echo loophole (IsEquivalent.refl)  
**Next action:** Flag echo loophole; prefer the .lower/.upper improvement forms in the same file.

## `green_27.lower` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/GreensOpenProblems/27.lean:60`  
**Statement:** Propose a lower bound for m(p) asymptotically stronger than Bedert's log p * sqrt(logloglog p)/loglogloglog p while still O(m).  
**Source:** Green, 100 open problems (2024), Problem 27; Bedert, On unique sums in Abelian groups, Combinatorica 44 (2024), Theorem 3  
**Statement matches intent:** yes  
**Known status:** Open: improving Bedert's lower bound (conjecturally m(p) should be closer to (log p)^2, per the unique-sum literature).  
**Difficulty:** math 9/10, Lean 9/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** Little-o against the concrete Bedert-shape function forces a super-constant improvement; =O[primesAtTop] m keeps it a valid lower bound. HasNoUniqueRepresentation (allUniqueSums = empty) matches Bedert's m(p) definition including a+a representations and unordered pair identity.  
**Flags:** improvement-style spec authored by formalizer; verify lowerBest matches Bedert Thm 3 shape exactly  
**Next action:** Leave open. Echo ans := m fails (would need the open fact lowerBest =o m), so the encoding genuinely demands new mathematics.

## `green_27.upper` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/GreensOpenProblems/27.lean:67`  
**Statement:** Propose an upper bound for m(p) asymptotically smaller than Bedert's (log p)^2 that still dominates m.  
**Source:** Green, 100 open problems (2024), Problem 27; Bedert, Combinatorica 44 (2024), Theorem 5  
**Statement matches intent:** yes  
**Known status:** Open: beating the (log p)^2 construction.  
**Difficulty:** math 9/10, Lean 9/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** Encoding sound: ans =o upperBest plus m =O ans exactly says a strictly better upper bound exists. No junk-value path: m >= 2 along primes where the defining set is nonempty.  
**Next action:** Leave open. Echo ans := m fails (would need the open fact m =o (log p)^2).

## `green_28` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/GreensOpenProblems/28.lean:48`  
**Statement:** Decide whether independent finitely-supported integer random variables X, Y whose sum X+Y is uniform on its support must themselves be uniform on their supports.  
**Source:** Green, 100 open problems (2024), Problem 28; MathOverflow 339137  
**Statement matches intent:** yes  
**Known status:** Open. Equivalent to: if a product of two nonnegative-coefficient polynomials has all coefficients equal, must each factor have all coefficients equal (up to scaling)? No counterexample or proof known to me as of Jan 2026.  
**Difficulty:** math 8/10, Lean 8/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** indepSum via PMF bind is exactly the convolution of independent variables; IsUniformOnSupport via uniformOfFinset forces s = support automatically (uniformOfFinset has full support on s), so no degenerate-object loophole. Point masses are uniform on singletons, so shifts do not give spurious counterexamples.  
**Flags:** needs literature check for any post-2024 resolution  
**Next action:** Leave open; small-support cases are finite semialgebraic problems, so a computational attack on small cases (support sizes <= 5-6, exact algebra) could produce either a counterexample or confidence.

## `green_29` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/GreensOpenProblems/29.lean:40`  
**Statement:** Decide whether every K-approximate group A (arbitrary group) contains S with |S| >= K^(-O(1))|A| and S^8 contained in A^4.  
**Source:** Green, 100 open problems (2024), Problem 29; Breuillard-Green-Tao, Small doubling in groups (2013), Problem 6.5; Croot-Sisask (2010); Sanders (2010)  
**Statement matches intent:** yes  
**Known status:** Open: the polynomial-in-K version. The qualitative version with K-dependent constant |S| >>_K |A| is known (Croot-Sisask almost-periodicity / Sanders), formalized as the in-file solved variant.  
**Difficulty:** math 9/10, Lean 9/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Constants C, c quantified before G, K, A - correct for an absolute K^(-O(1)) bound. Uses Mathlib's IsApproximateSubgroup (symmetric, 1 in A, K-covering), which excludes the empty set; S^8 and A^4 are pointwise Finset powers as in the source.  
**Next action:** Leave open; the obstruction is making almost-periodicity arguments polynomially efficient in K in the nonabelian setting.

## `green_3` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/GreensOpenProblems/3.lean:30`  
**Statement:** Decide whether every open subset A of [0,1] with Lebesgue measure greater than 1/3 contains x, y, z with xy = z.  
**Source:** Green, 100 open problems (2024), Problem 3  
**Statement matches intent:** yes  
**Known status:** Open. The constant 1/3 is the conjectured threshold from Green's list; single-interval examples like (1/4, 1/2) (measure 1/4) avoid solutions, unions approach 1/3.  
**Difficulty:** math 8/10, Lean 8/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** A open in R and contained in Icc 0 1 forces A inside (0,1), so the trivial solutions x=y=z in {0,1} are automatically excluded and no distinctness side-condition is needed (x*y = x forces y = 1, impossible). volume A > 1/3 in ENNReal is the correct reading. answer() iff encoding faithful.  
**Next action:** Leave open; a milestone would be any measure threshold < 1 forcing a multiplicative triple in open sets.

## `green_31.lower` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/GreensOpenProblems/31.lean:53`  
**Statement:** Improve the lower bound F(N) >= sqrt(N) + O(1) for the largest Sidon subset of {1,...,N}: find ans with ans(N) - sqrt(N) -> infinity that lower-bounds F(N) for infinitely many N.  
**Source:** Ben Green, 100 open problems (2024), Problem 31; Erdos-Turan 1941; Singer 1938; related to Erdos Problem 30  
**Statement matches intent:** yes  
**Known status:** Genuinely open and considered hard: Singer difference sets give F(N) >= sqrt(N) + O(1) for infinitely many N, and no one has ever beaten the O(1) additive term, even infinitely often. Adjacent to Erdos #30 (F(N) = sqrt(N) + O(N^eps)?).  
**Difficulty:** math 9/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** IsSidon/maxSidonSubsetCard definitions in FormalConjecturesForMathlib/Combinatorics/Basic.lean checked; over N the definition is the standard Sidon property. No internal PRs target green_31 (pr_register greps for green_31/Sidon: none). ErdosProblems/30,43,44,155 use the same F but pose different questions, not duplicates.  
**Next action:** Keep open; no known avenue. Formalization audited: Tendsto(ans - sqrt) atTop plus frequent ans <= F correctly encodes 'break the O(1) barrier for infinitely many N'; F uses maxSidonSubsetCard over Icc 1 N in N (no char-2 issue here).

## `green_31.upper` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/GreensOpenProblems/31.lean:72`  
**Statement:** Improve the upper bound F(N) <= sqrt(N) + 0.98183 N^{1/4} + O(1) (Carter-Hunter-O'Bryant 2025), at least for infinitely many N: find ans that upper-bounds F infinitely often with ans - sqrt(N) <= c N^{1/4} + C for some c < 0.98183.  
**Source:** Ben Green, 100 open problems (2024), Problem 31; Balogh-Furedi-Roy 2023 (0.998); Carter-Hunter-O'Bryant, Acta Math. Hungar. 175 (2025) (0.98183)  
**Statement matches intent:** yes  
**Known status:** Open. The constant on N^{1/4} has moved recently (1 -> 0.998 BFR23 -> 0.98183 CHO25), so further incremental improvement is plausible research; eliminating the N^{1/4} term entirely is the famous hard version. No post-CHO25 improvement known to me (cutoff Jan 2026).  
**Difficulty:** math 8/10, Lean 10/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** Encoding audited: existential c < 0.98183 with eventual ans - sqrt(N) <= c N^{1/4} + C, plus frequent F <= ans, is a faithful reading of 'improve at least for infinitely many N'. Negative c allowed but only makes the task harder, no loophole.  
**Flags:** needs literature check (post-CHO25 constant improvements)  
**Next action:** Keep open; monitor Sidon-set literature for post-2025 improvements to the 0.98183 constant.

## `green_31.variants.abelian` — Vacuously true / accidentally weakened (cat 4)

**File:** `FormalConjectures/GreensOpenProblems/31.lean:128`  
**Secondary category:** 2 (Trivially or easily solvable)  
**Statement:** Decide whether every finite abelian group G contains a Sidon subset of size at least 0.01 sqrt(|G|). Intended open; but under the repo's IsSidon the statement is provably FALSE.  
**Source:** Ben Green, 100 open problems (2024), Problem 31 (comments)  
**Statement matches intent:** no — The repo definition IsSidon (Basic.lean:57) quantifies over ALL quadruples including i1=i2, j1=j2: taking i1=i2=x, j1=j2=y with x != y in F_2^n gives x+x = 0 = y+y but the conclusion forces x=y. Hence every subset of F_2^n with two distinct elements fails IsSidon, so all Sidon sets there have card <= 1. G = F_2^14 then violates 0.01*sqrt(16384) = 1.28 <= card. The intended question uses the group-Sidon convention that discounts 2-torsion coincidences (Babai-Sos style), under which F_2^n has Sidon sets of size ~sqrt(|G|) (graph of x^3 over F_{2^m}) and the question is genuinely open.  
**Known status:** Formal statement resolvable NOW with answer(False): counterexample G = F_2^14. The intended mathematical question remains open.  
**Difficulty:** math 8/10, Lean 4/10 · **Compute:** none · **Confidence:** high  
**Evidence:** IsSidon def read directly: forall (i1 in A)(j1 in A)(i2 in A)(j2 in A), i1+i2 = j1+j2 -> (i1=j1 and i2=j2) or (i1=j2 and i2=j1). Instantiation (x,y,x,y) with x+x=y+y=0 in F_2^n yields x=y. Fintype.card (F_2^14) = 16384, sqrt = 128 exactly, 0.01*128 = 1.28 > 1 >= card of any IsSidon set.  
**Flags:** definition admits degenerate collapse in 2-torsion groups; answer(sorry) iff encoding decidable via defect, not via the intended mathematics; intended conjecture remains open  
**Next action:** Report defect upstream: IsSidon needs the distinct-pair/group convention for 2-torsion groups. Meanwhile the formal theorem closes with answer := False, witness G := (Fin 14 -> ZMod 2), a two-element Sidon-violation lemma, and 0.01*Real.sqrt(2^14) = 1.28 > 1.

## `green_31.variants.lower_eventually` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/GreensOpenProblems/31.lean:61`  
**Statement:** Same lower-bound improvement but required for all sufficiently large N: ans(N) - sqrt(N) -> infinity and ans(N) <= F(N) eventually.  
**Source:** Ben Green, 100 open problems (2024), Problem 31 (eventual variant)  
**Statement matches intent:** yes  
**Known status:** Open and strictly harder than the frequent version: even F(N) >= sqrt(N) + O(1) for ALL large N is not known (best all-N bound is sqrt(N) - N^{0.2615...} via prime gaps), so this variant asks for more than the state of the art on two counts.  
**Difficulty:** math 9/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Quantifier structure (eventually vs frequently) is the only difference from green_31.lower; audited clean.  
**Next action:** Keep open.

## `green_31.variants.sidon_01n` — Vacuously true / accidentally weakened (cat 4)

**File:** `FormalConjectures/GreensOpenProblems/31.lean:138`  
**Secondary category:** 2 (Trivially or easily solvable)  
**Statement:** Decide whether there are Sidon subsets of {0,1}^n of size N^{0.51} (N = 2^n). Intended open; but under the repo's IsSidon in F_2^n every Sidon set has at most 1 element, so the formal statement is provably FALSE.  
**Source:** Ben Green, 100 open problems (2024), Problem 31 (comments); Cohen-Litsyn-Zemor 2001  
**Statement matches intent:** no — Same char-2 collapse as the abelian variant: in F_2^n, any two distinct x,y give x+x = 0 = y+y violating IsSidon, so card <= 1 < (2^n)^{0.51} for n >= 1. The binary-Sidon literature (CLZ01) defines B_2 sets via sums of DISTINCT elements, under which sets of size ~2^{n/2} exist and the N^{0.51}-vs-N^{0.5753} gap is the real open problem.  
**Known status:** Formal statement resolvable NOW with answer(False): no family S can satisfy IsSidon plus eventual card >= (2^n)^{0.51}. Intended question open. Side effect: the companion 'research solved' sidon_01n_clz01 upper bound becomes vacuously true (card <= 1) rather than encoding CLZ01.  
**Difficulty:** math 8/10, Lean 3/10 · **Compute:** none · **Confidence:** high  
**Evidence:** IsSidon instantiation (x,y,x,y) as above; (2^n)^{0.51} = 2^{0.51n} > 1 for n >= 1 while every IsSidon subset of F_2^n has card <= 1. CLZ01 constant 0.5753 in the neighbouring solved variant confirms the intended distinct-sum convention.  
**Flags:** definition admits degenerate collapse in char 2; answer-encoding trivialized (False); companion solved-variant sidon_01n_clz01 also vacuous under this definition; intended conjecture remains open  
**Next action:** Report defect upstream: use a distinct-pair Sidon/B_2 definition for F_2^n. Meanwhile the theorem closes with answer := False plus the two-element violation lemma and 1 < 2^{0.51 n}.

## `green_31.variants.upper_eventually` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/GreensOpenProblems/31.lean:83`  
**Statement:** Same upper-bound improvement below the CHO25 constant 0.98183, required for all sufficiently large N.  
**Source:** Ben Green, 100 open problems (2024), Problem 31; CHO25  
**Statement matches intent:** yes  
**Known status:** Open; this is the standard form in which BFR23/CHO25 improvements were actually proved (all large N), so the next improvement would likely close this variant and green_31.upper simultaneously.  
**Difficulty:** math 8/10, Lean 10/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** Same structure as green_31.upper with eventually in place of frequently; audited clean.  
**Flags:** needs literature check (post-CHO25 constant improvements)  
**Next action:** Keep open; monitor literature.

## `green_31.variants.zmod_p` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/GreensOpenProblems/31.lean:115`  
**Statement:** Decide whether for every prime p there is a Sidon subset of Z/pZ of size (1+o(1))sqrt(p).  
**Source:** Ben Green, 100 open problems (2024), Problem 31 (comments)  
**Statement matches intent:** yes  
**Known status:** Genuinely open per Green 2024: known constructions embed integer Sidon sets of size ~sqrt(p/2) ~ 0.707 sqrt(p) into Z/pZ; Singer perfect difference sets live in Z/(q^2+q+1)Z, not general prime moduli. Getting (1+o(1))sqrt(p) for all p is unresolved.  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** none · **Confidence:** high  
**Evidence:** For odd p the repo IsSidon does not degenerate (2 invertible in ZMod p, so x+x=y+y forces x=y). Exact-equality card = (1+o p) sqrt(p) just defines o p pointwise, no over-constraint.  
**Next action:** Keep open. Formalization faithful: single o(1) function along atTop forces card(S p)/sqrt(p) -> 1 along primes; the p=2 char-2 degeneracy of IsSidon is absorbed since o is unconstrained at any fixed p.

## `green_32` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/GreensOpenProblems/32.lean:82`  
**Statement:** For prime p and any A in Z/pZ of size floor(sqrt p), is there a dilate cA (c a unit) containing a gap of floor(100 sqrt p) consecutive non-elements, for all large p?  
**Source:** Ben Green, 100 open problems (2024), Problem 32; Shakan, SIAM J. Discrete Math. 34 (2020)  
**Statement matches intent:** yes  
**Known status:** Open. Shakan's polynomial-method result gives gaps of length ~2 sqrt(p) (the file's solved variants record this); pushing the constant from 2 to 100 is exactly Green's question and remains unresolved.  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** none · **Confidence:** high  
**Evidence:** HasGap(A, L) = exists x, x+i notin A for i < L: standard cyclic gap; gap length 100 sqrt(p) < p eventually so nondegenerate. No internal PRs (register greps: none).  
**Next action:** Keep open. Formalization audited: HasLargeGapDilate embeds 100 < omega p < p as provable conjuncts, which hold eventually for omega = sqrt, so no vacuity; floor(100 p / sqrt p) = floor(100 sqrt p) as intended; dilation by (ZMod p)-units matches 'dilate'.

## `green_32.variants.log_regime` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/GreensOpenProblems/32.lean:127`  
**Statement:** Decide whether the large-gap-dilate property holds for every omega asymptotic to 10 log p (sets of size ~10 log p, gaps of ~10 p / log p): Green says even this regime is unclear.  
**Source:** Ben Green, 100 open problems (2024), Problem 32 (comments)  
**Statement matches intent:** yes  
**Known status:** Open in both directions per Green 2024: Dirichlet/Bohr-set arguments handle omega <= c log p for small c, Szemeredi handles omega ~ cp; the 10 log p regime sits in the unresolved middle.  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** Same HasLargeGapDilate skeleton as green_32, audited; asymptotic equivalence ~[atTop] used correctly.  
**Next action:** Keep open. The universal quantification over all omega ~ 10 log p is a reasonable formalization of 'sets of size about 10 log p'; the embedded 100 < omega p conjunct holds eventually since 10 log p -> infinity, so no vacuity.

## `green_33` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/GreensOpenProblems/33.lean:39`  
**Statement:** Decide whether there are infinitely many q admitting A in Z/qZ with A + A = Z/qZ and |A| = (sqrt 2 + o(1)) sqrt q.  
**Source:** Green, 100 open problems (2024), Problem 33; Croot-Lev, Open problems in additive combinatorics (2007)  
**Statement matches intent:** yes  
**Known status:** Open. sqrt 2 * sqrt q is the unordered-pair counting barrier (|A|(|A|+1)/2 >= q); question is whether this perfect-covering density is attained infinitely often, a perfect-difference-set-style question. Known constructions give ~2 sqrt q.  
**Difficulty:** math 8/10, Lean 8/10 · **Compute:** small · **Confidence:** high  
**Evidence:** The forall-epsilon frequently-encoding is exactly equivalent to the existence of a subsequence q_i with |A_i|/sqrt(q_i) -> sqrt 2, a faithful rendering of 'infinitely many q with |A| = (sqrt 2 + o(1)) q^(1/2)'. In-file sanity theorem (q <= |A|^2) already proven without sorry.  
**Next action:** Leave open; computational search for optimal additive covers of Z/q for q up to a few thousand could inform the answer.

## `green_35.lower` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/GreensOpenProblems/35.lean:54`  
**Statement:** Improve a lower bound for c(p) = inf ||f*f||_p over probability densities on [0,1]: the formal content is proving strictly c(2) > sqrt(4/7) (Green 2001's constant) or c(inf) > 0.64 (Cloninger-Steinerberger).  
**Source:** Ben Green, 100 open problems (2024), Problem 35; Green, Acta Arith. 100 (2001); Cloninger-Steinerberger, Proc. AMS 145 (2017)  
**Statement matches intent:** yes  
**Known status:** Open per Green 2024: sqrt(4/7) (exact constant) at p=2 and 0.64 at p=infinity are the best published lower bounds; no improvement known to me by Jan 2026. NOTE: the well-publicized 2025 AlphaEvolve/Boyer-Li/Jaech autoconvolution improvements (arXiv 2506.16750, 2508.02803) concern the DIFFERENT Martin-O'Bryant Holder-ratio quantity ||f*f||_2^2/(||f*f||_inf ||f*f||_1), not c(p), so they do not resolve this.  
**Difficulty:** math 8/10, Lean 10/10 · **Compute:** medium · **Confidence:** medium  
**Evidence:** Answer-encoding audited: the first conjunct (forall p > 1, lb p <= c p) is vacuously satisfiable by lb := 0, so the entire content sits in the strict-improvement disjunct, which never mentions lb. Web searches (2 used) confirmed the 2025 autoconvolution papers target the Holder ratio (target constant 1, current 0.94136), a different normalization from c(p) in [0.64, 0.755].  
**Flags:** answer conjunct vacuous (lb := 0 satisfies it); real content is the strict-inequality disjunct; strictness hinges on whether 0.64 is CS17's exact or rounded constant - needs literature check  
**Next action:** Keep open, but check CS17's exact constant: if their proof certifies a value strictly above 0.64 (0.64 being a rounded-down presentation), the disjunct 0.64 < c(inf) would already be literature-solved (would become cat 5, research-scale formalization of an LP-assisted proof).

## `green_35.upper` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/GreensOpenProblems/35.lean:62`  
**Secondary category:** 6 (Computationally solvable with certificate)  
**Statement:** Improve the upper bound for c(inf) = inf sup(f*f) over probability densities on [0,1]: formal content reduces to proving c(inf) < 0.7505 strictly.  
**Source:** Ben Green, 100 open problems (2024), Problem 35; Matolcsi-Vinuesa, J. Math. Anal. Appl. 372 (2010)  
**Statement matches intent:** suspect — Baseline constant likely mis-transcribed: literature (per abstracts surfaced in search) reports the best construction as 1.50992 in the doubled normalization, i.e. c(inf) <= 0.75496, usually rounded 0.7549/0.755 - not 0.7505. If so, the file's companion 'research solved' c_inf_upper (c inf <= 0.7505) is NOT established, and green_35.upper demands an improvement strictly below 0.7505, which is stronger than 'improve the best known bound'. Statement remains open either way.  
**Known status:** Open. Improving the upper bound only requires exhibiting a better density (a finite step function with certified sup of autoconvolution), so this side is computational-construction territory; the 2010 record has stood, though the search-based methods of 2025 (simulated annealing/gradient, AlphaEvolve line) could plausibly be redirected at it.  
**Difficulty:** math 7/10, Lean 9/10 · **Compute:** medium · **Confidence:** medium  
**Evidence:** ub := c satisfies the first conjunct definitionally, so content = c(inf) < 0.7505. WebSearch: MV10 constructions reported as 1.50992/1.52 (i.e. ~0.755), no 1.501 found; Green's PDF returns 403 so his stated constant unverified.  
**Flags:** ub conjunct vacuous (ub := c); content is single strict inequality; baseline constant 0.7505 suspect vs literature 0.75496 - needs source check; upper-bound side is certificate-friendly (step function with rational arithmetic)  
**Next action:** First fix the constant against Green's list / MV10 (0.7549 vs 0.7505). Path to close: LP/annealing search for a step function f with exact rational autoconvolution sup below target; certificate = the step heights, kernel-checkable by rational arithmetic; then substantial measure-theory work to link to eLpNorm/convolution (the hard formal part).

## `green_36` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/GreensOpenProblems/36.lean:54`  
**Statement:** Do there exist, for arbitrarily large n, abelian groups H of size n^{2+o(1)} with subsets A_1..A_n, B_1..B_n, |A_i||B_i| >= n^{2-o(1)}, |A_i+B_i| = |A_i||B_i|, and each A_i+B_i disjoint from all A_j+B_k with j != k (Green's phrasing of the CKS simultaneous double product question)?  
**Source:** Ben Green, 100 open problems (2024), Problem 36; Cohn-Kleinberg-Szegedy-Umans, FOCS 2005, Problem 4.7  
**Statement matches intent:** yes  
**Known status:** Major open problem: CKS05 show such families with these parameters would imply matrix multiplication exponent omega = 2. The cap-set obstructions (Blasiak-Church-Cohn-Grochow-Naslund-Sawin-Umans 2017) only rule out bounded-exponent abelian groups for the triple product property and do not settle this; open as of Green 2024 and to my knowledge Jan 2026.  
**Difficulty:** math 10/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Quantifier audit: forall eps > 0, frequently n, exists H with n^{2-eps} <= |H| <= n^{2+eps} correctly encodes n^{2+o(1)} for arbitrarily large n; |A_i||B_i| >= n^{2-eps} forces nonempty sets, no degenerate witnesses. No internal PRs.  
**Next action:** Keep open; do not attempt. The file honestly separates Green's disjointness condition (this theorem) from CKS's (variant below).

## `green_36.variants.cks05` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/GreensOpenProblems/36.lean:65`  
**Statement:** Same existence question with the disjointness condition transcribed from CKS05 Definition 4.1 (A_i+B_j disjoint from A_j+B_k for i != k).  
**Source:** Cohn-Kleinberg-Szegedy-Umans, 'Group-theoretic algorithms for matrix multiplication', FOCS 2005, Definition 4.1 / Problem 4.7  
**Statement matches intent:** yes  
**Known status:** CKS Problem 4.7 open; affirmative answer implies omega = 2.  
**Difficulty:** math 10/10, Lean 10/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** Identical parameter skeleton to green_36, only the disjointness index condition differs (i != k vs j != k), matching the file's NOTE.  
**Flags:** needs source check of CKS 4.1 index convention  
**Next action:** Keep open; verify the CKS 4.1 index pattern against the published paper when possible.

## `green_37` — Vacuously true / accidentally weakened (cat 4)

**File:** `FormalConjectures/GreensOpenProblems/37.lean:47`  
**Secondary category:** 2 (Trivially or easily solvable)  
**Statement:** Determine exactly the minimum size m(N,k) of a set of naturals containing a k-term AP of common difference d for every d = 1..N. Formalized as IsLeast of the cardinality set at answer(sorry).  
**Source:** Ben Green, 100 open problems (2024), Problem 37  
**Statement matches intent:** no — The answer-encoding is tautologically closable: answer := Green37.m N k (the sInf of the very same set) satisfies IsLeast via Nat.sInf_mem once the set is shown nonempty (witness A = Finset.range ((k-1)*N+1), which contains the AP 0, d, ..., (k-1)d for every d <= N) plus Nat.sInf_le. Nothing forces a closed form, so the formal statement does not capture 'determine m(N,k)' - whose asymptotics are unknown even for k = 3 (k = 2 is the classical restricted difference basis problem, Theta(sqrt N)).  
**Known status:** Formal statement quickly provable via the self-referential answer; intended determination problem open.  
**Difficulty:** math 8/10, Lean 4/10 · **Compute:** none · **Confidence:** high  
**Evidence:** m is literally sInf of the IsLeast set (37.lean:40-41); Set.IsAPOfLengthWith audited (AP/Basic.lean:46): for d >= 1 the k points n*d (n < k) are distinct and lie in range((k-1)N+1), so the set of achievable cardinalities is nonempty and Nat.sInf_mem applies. answer() elaborates in context, so it may mention m, N, k - no guard against self-reference.  
**Flags:** tautological answer loophole (answer := m N k); intended problem is an open estimation question  
**Next action:** Report the spec defect upstream (answer should be constrained to a closed form, or the statement replaced by two-sided explicit bounds). If closing as-is: prove nonemptiness with range((k-1)N+1) and apply Nat.sInf_mem / Nat.sInf_le.

## `green_37_asymptotic` — Vacuously true / accidentally weakened (cat 4)

**File:** `FormalConjectures/GreensOpenProblems/37.lean:56`  
**Secondary category:** 2 (Trivially or easily solvable)  
**Statement:** Find a function f with m(N,k) = f(N) for all large N. Trivialized: answer := fun N => (m N k : R) closes it by rfl.  
**Source:** Ben Green, 100 open problems (2024), Problem 37 (asymptotic form)  
**Statement matches intent:** no — answer(sorry) : N -> R elaborates with k in scope, so fun N => (m N k : R) is admissible and the statement becomes eventually (m N k : R) = (m N k : R), provable by Filter.Eventually.of_forall (fun _ => rfl). Additionally, even a good-faith reading (eventual EXACT equality with a formula) over-demands relative to Green's 'estimate m(N,k)'.  
**Known status:** Formal statement provable in one line via self-referential answer; intended asymptotics open.  
**Difficulty:** math 8/10, Lean 1/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Read of 37.lean:56-58; no constraint ties answer to elementary/closed-form functions.  
**Flags:** tautological answer loophole; eventual exact equality is a mis-specification of 'determine asymptotic behavior'  
**Next action:** Report spec defect; replace with a genuine two-sided asymptotic statement (e.g. explicit upper/lower bound pairs, or IsTheta against a concrete elementary function).

## `green_37_bigO` — Trivially or easily solvable (cat 2)

**File:** `FormalConjectures/GreensOpenProblems/37.lean:68`  
**Secondary category:** 4 (Vacuously true / accidentally weakened)  
**Statement:** Find a big-O upper bound for m(N,k). As specified, any valid upper bound qualifies - including m itself.  
**Source:** Ben Green, 100 open problems (2024), Problem 37 (upper-bound form)  
**Statement matches intent:** no — Two quick closures: (a) tautological answer := fun N => (m N k : R), by Asymptotics.isBigO_refl; (b) legitimate answer := fun N => (N : R) + 1 with the covering witness A = range((k-1)N+1) giving m N k <= (k-1)N + 1 = O(N). Neither engages the open question of the true growth rate.  
**Known status:** Trivially/easily solvable as stated; intended sharp-upper-bound question open.  
**Difficulty:** math 8/10, Lean 1/10 · **Compute:** none · **Confidence:** high  
**Evidence:** isBigO_refl closes (a) in one tactic; for (b) the range((k-1)N+1) construction was audited against Set.IsAPOfLengthWith (elements n*d, n < k, distinct for d >= 1, all < (k-1)N+1).  
**Flags:** spec too weak: any upper bound qualifies; tautological answer loophole  
**Next action:** Close via isBigO_refl if a formal resolution is wanted, but better: report spec defect (statement should demand a bound of a specific sharp shape).

## `green_37_littleO` — Trivially or easily solvable (cat 2)

**File:** `FormalConjectures/GreensOpenProblems/37.lean:74`  
**Secondary category:** 4 (Vacuously true / accidentally weakened)  
**Statement:** Find a little-o strict upper bound for m(N,k). Any function growing faster than m qualifies, e.g. N^2, or even m(N,k)*N tautologically.  
**Source:** Ben Green, 100 open problems (2024), Problem 37 (strict upper-bound form)  
**Statement matches intent:** no — answer := fun N => (m N k : R) * N is littleO-valid for ANY f (||f N|| <= c * ||f N|| * N once N >= 1/c), needing no knowledge of m; alternatively answer := fun N => (N:R)^2 works via m N k <= (k-1)N+1. Either way the statement carries no mathematical content about m.  
**Known status:** Trivially/easily solvable as stated; intended problem (true growth) open.  
**Difficulty:** math 8/10, Lean 2/10 · **Compute:** none · **Confidence:** high  
**Evidence:** IsLittleO unfolds to forall c > 0, eventually ||m N k|| <= c * ||m N k * N||; with N >= ceil(1/c) this is immediate since values are nonnegative.  
**Flags:** spec too weak: any strict upper bound qualifies; quasi-tautological answer loophole  
**Next action:** Close via the f*N trick if desired; report spec defect upstream.

## `green_37_theta` — Vacuously true / accidentally weakened (cat 4)

**File:** `FormalConjectures/GreensOpenProblems/37.lean:62`  
**Secondary category:** 2 (Trivially or easily solvable)  
**Statement:** Find the Theta-class of m(N,k). Trivialized: answer := the function itself, closed by isTheta_refl.  
**Source:** Ben Green, 100 open problems (2024), Problem 37 (Theta form)  
**Statement matches intent:** no — answer := fun N => (m N k : R) gives f =Theta f, provable by Asymptotics.isTheta_refl. No constraint to a closed-form comparison function.  
**Known status:** Formal statement provable in one line; intended Theta-determination open (order of magnitude of m(N,k) unknown for k >= 3).  
**Difficulty:** math 8/10, Lean 1/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Read of 37.lean:62-64.  
**Flags:** tautological answer loophole  
**Next action:** Report spec defect; a meaningful version must quantify answer over a restricted grammar of functions or state concrete bounds.

## `green_38.lower` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/GreensOpenProblems/38.lean:73`  
**Secondary category:** 5 (Solved mathematically, not yet formalized)  
**Statement:** Improve the lower bound for the largest A in F_7^n with (A-A) meeting {-1,0,1}^n only at 0 (independent sets in strong powers of C_7): beat growth constant C_1 = 367^{1/5} ~ 3.2578.  
**Source:** Ben Green, 100 open problems (2024), Problem 38; Polak-Schrijver 2019 / Polak PhD thesis 2020 (367^{1/5}); Shannon capacity of C_7  
**Statement matches intent:** yes  
**Known status:** Open as of my Jan 2026 knowledge: alpha(C_7^box5) >= 367 (Polak-Schrijver) is the record, giving capacity >= 367^{1/5}. CAUTION: search surfaced arXiv 2607.21517 'Improved lower bounds for the Shannon capacity of odd cycles' (July 2026, post-cutoff, could not fetch - 403); if it beats 367^{1/5} for C_7, this becomes cat 5/6 with a concrete certificate to import.  
**Difficulty:** math 8/10, Lean 7/10 · **Compute:** large · **Confidence:** medium  
**Evidence:** IntersectsOnlyAtZero audited = independence in the n-th strong power of C_7 (adjacent iff all coordinate differences in {-1,0,1}); C_1, C_2 constants match Polak and Lovasz theta(C_7) = 7cos(pi/7)/(1+cos(pi/7)) ~ 3.3177. Encoding (ans eventually <= Largest, exists c > C_1 with c^n = O(ans)) faithfully demands a strict rate improvement.  
**Flags:** needs literature check: arXiv 2607.21517 (2026) may supersede 367^{1/5}  
**Next action:** Literature check arXiv 2607.21517 first. If a larger independent set S in C_7^box m with |S|^{1/m} > 367^{1/5} exists, close by: certificate = the set (finite, kernel-checkable membership/difference conditions), product construction A^k x {pt} for the eventual bound, ans n := v^{n-m}; the =O direction then follows with c := |S|^{1/m}.

## `green_38.upper` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/GreensOpenProblems/38.lean:81`  
**Statement:** Improve the upper bound below the Lovasz theta value C_2 = 7cos(pi/7)/(1+cos(pi/7)) ~ 3.3177 for the same quantity (Shannon capacity of C_7 upper bound).  
**Source:** Ben Green, 100 open problems (2024), Problem 38; Lovasz, IEEE Trans. IT 25 (1979), Corollary 5  
**Statement matches intent:** yes  
**Known status:** Recognized hard open problem: no known technique beats the Lovasz theta bound for odd cycles >= 7 (Haemers-type rank bounds are weaker here); any improvement would be a breakthrough in the Shannon-capacity program.  
**Difficulty:** math 9/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Encoding audited symmetrically to green_38.lower: Largest eventually <= ans and ans = O(c^n) for some c < C_2 demands a strict rate improvement below theta.  
**Next action:** Keep open; do not attempt.

## `green_39` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/GreensOpenProblems/39.lean:82`  
**Statement:** For random A in Z/pZ of size floor(sqrt p), does the proportion of such A coverable by at most 100*floor(sqrt p) translates tend to 1 as the prime p grows?  
**Source:** Ben Green, 100 open problems (2024), Problem 39; Bollobas-Janson-Riordan, RSA 38 (2011) (related)  
**Statement matches intent:** yes  
**Known status:** Open per Green 2024 (he states he cannot do it even with 1.01 in place of 100). Greedy covering gives ~sqrt(p) log p translates for random A; removing the log factor is the obstruction.  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** Test lemmas in file (native_decide, e.g. proportionCoverable 7 4 2 = 3/5) sanity-check the counting definition. BJR11 is cited as related, and Green still poses the question in 2024, so BJR11 does not settle it.  
**Flags:** needs literature check (whether BJR11-style second-moment methods have since resolved the O(sqrt p) regime)  
**Next action:** Keep open. Formalization audited: proportionCoverable's p=0 and k>p junk branches are unreachable for primes with k = Nat.sqrt p; counting over powersetCard k univ with exists T, |T| <= c, A + T = univ is exactly 'coverable by <= c translates'; Tendsto over the prime subtype atTop to nhds 1 encodes asymptotically almost surely.

## `green_39.variant_101` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/GreensOpenProblems/39.lean:95`  
**Statement:** Same covering question with only floor(1.01 * floor(sqrt p)) translates allowed - Green states he cannot answer even this.  
**Source:** Ben Green, 100 open problems (2024), Problem 39 (comments)  
**Statement matches intent:** yes  
**Known status:** Open in both directions (the truth value at 1.01 could plausibly be 'no' - near the entropy threshold - and even that is unknown).  
**Difficulty:** math 9/10, Lean 9/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Same skeleton as green_39 with c = floor(1.01 * k); 1.01 * sqrt(p) * sqrt(p) > p so no pigeonhole vacuity.  
**Next action:** Keep open.

## `green_39.variant_theta` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/GreensOpenProblems/39.lean:114`  
**Statement:** For every theta in (0, 1/2], is there C > 1 such that random A of size floor(p^theta) is a.a.s. coverable by floor(C p^{1-theta}) translates?  
**Source:** Ben Green, 100 open problems (2024), Problem 39 (comments), reinterpreted by the formalizers  
**Statement matches intent:** suspect — Deliberate, documented reinterpretation: Green's literal 'sqrt p replaced by p^theta' (with ~p^theta translates) is trivially false by pigeonhole for theta < 1/2, so the file substitutes O(p^{1-theta}) translates, which specializes to the main conjecture at theta = 1/2. Reasonable fix, but it is the formalizers' reading, not Green's text.  
**Known status:** Open; generalizes green_39 (existential C makes theta = 1/2 case weaker than the explicit-100 version).  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** Docstring NOTE in file records the pigeonhole issue and reinterpretation; C p^{1-theta} * p^theta ~ C p >= p so nondegenerate.  
**Flags:** documented prose-formal deviation (reinterpretation of ill-posed literal statement)  
**Next action:** Keep open; consider asking upstream to confirm the intended reading with Green's text.

## `green_4` — Vacuously true / accidentally weakened (cat 4)

**File:** `FormalConjectures/GreensOpenProblems/4.lean:31`  
**Secondary category:** 2 (Trivially or easily solvable)  
**Statement:** Exhibit a largest product-free subset of the alternating group A_n (for the given n). Formalized as MaximalFor ProdFree ncard at an answer(sorry) family.  
**Source:** Ben Green, 100 open problems (2024), Problem 4; arXiv:2205.15191 'On the largest product-free subsets of the alternating groups' (solves large n)  
**Statement matches intent:** no — Choice loophole: a maximizer exists for every n by finiteness (Set (alternatingGroup (Fin n)) is a finite type, ProdFree holds for the empty set, ncard is bounded), so answer := fun n => Classical.choose (exists_maximalFor ...) closes the theorem without any structural description - the formal statement never demands an explicit set. The intended problem (describe the extremal sets) is solved for large n in arXiv:2205.15191 (the file's own large_green_4 records its Theorem 1.1 as research solved) but the all-n version with explicit description is not captured by this encoding either way.  
**Known status:** Formal statement closable via nonconstructive finite-argmax choice; intended structural problem solved for large n externally, small/all-n crossover open.  
**Difficulty:** math 7/10, Lean 3/10 · **Compute:** none · **Confidence:** high  
**Evidence:** ProdFree audited (includes x*x notin S, standard); empty set is ProdFree so the candidate family is nonempty; alternatingGroup (Fin n) is a Fintype hence Set of it is Finite and ncard-argmax exists. answer() elaborator (Util/Answer.lean) imposes no constructivity constraint.  
**Flags:** nonconstructive tautological answer loophole; intended large-n case already solved in literature (arXiv:2205.15191)  
**Next action:** Report spec defect upstream (answer should be an explicit family, e.g. the extremalFamily construction, with a proof of optimality). To close as-is: prove exists S, MaximalFor ProdFree ncard S by Finite.exists_max over the subtype {S // ProdFree S}, then choose.

## `green_40` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/GreensOpenProblems/40.lean:61`  
**Statement:** For linear covering codes: f(r) is the liminf over n of the minimal density |V||H(r)|/2^n of subspaces V with V+H(r)=F_2^n. Does f(r) tend to infinity as r grows?  
**Source:** Ben Green, 100 open problems, https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf (Problem 40); Cohen-Honkala-Litsyn-Lobstein, Covering Codes (1997)  
**Statement matches intent:** yes  
**Known status:** Open. Only f(1)=1 is known (Hamming codes); best upper bound f(r) <= r^r/r!; f(2) <= 1.4238. No internal PR/campaign targets Green 40-62 (pr_register: only Green14 work).  
**Difficulty:** math 9/10, Lean 9/10 · **Compute:** none · **Confidence:** high  
**Evidence:** liminf-of-minDensity definition matches Green's f(r) ('infinite sequence of n's'); Tendsto to (nhds top) in ENNReal is the correct encoding of divergence; infimum nonempty since V=top always covers; no degenerate exploit found (f(0)=1 harmlessly).  
**Next action:** Keep as open research target; monitor covering-codes literature (Davydov-type constructions vs. lower-bound methods).

## `green_40.f_eq_one_for_all` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/GreensOpenProblems/40.lean:76`  
**Statement:** Is f(r)=1 for every radius r, i.e. do asymptotically perfect linear coverings exist for all radii?  
**Source:** Ben Green, 100 open problems, https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf (Problem 40)  
**Statement matches intent:** yes  
**Known status:** Open; Green notes the possibility f(r)=1 for all r has not been ruled out. Not even f(2)=1 is decided.  
**Difficulty:** math 9/10, Lean 9/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Quantifies over all r including r=0, but f(0)=1 provably (only V=univ covers with H(0)={0}), so no falsifying edge case; encoding faithful.  
**Next action:** Keep open; any resolution of f(2) would be the first step.

## `green_40.f_two_eq_one` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/GreensOpenProblems/40.lean:81`  
**Statement:** Is f(2)=1, i.e. are there asymptotically perfect linear coverings of F_2^n by radius-2 Hamming balls?  
**Source:** Ben Green, 100 open problems, https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf (Problem 40); best upper bound 1.4238 from [CHL97]/Davydov  
**Statement matches intent:** yes  
**Known status:** Open; best known upper bound f(2) <= 1.4238; for arbitrary (nonlinear) codes Struik proved the analogue = 1.  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Direct faithful encoding of the single open value; nonlinear case being solved (f_tilde(2)=1) marks the linear question as the genuine gap.  
**Next action:** Keep open; a construction-side attack (linear analogues of Struik's codes) is the identifiable avenue.

## `green_40.variants.all_n` — Vacuously true / accidentally weakened (cat 4)

**File:** `FormalConjectures/GreensOpenProblems/40.lean:130`  
**Secondary category:** 7 (Plausibly solvable with moderate formal work)  
**Statement:** Intended: does f_all(r) = limsup_n (minimal linear covering density) tend to infinity with r? As formalized it instead asks whether f_all r is eventually EXACTLY infinity.  
**Source:** Ben Green, 100 open problems, https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf (Problem 40)  
**Statement matches intent:** no — Target filter bug: in ENNReal (an OrderTop) Filter.atTop = pure top, so 'Tendsto f_all atTop atTop' says 'for all large r, limsup_n minDensity n r = top' - not divergence. The file's other two variants correctly use nhds top, showing this is a slip.  
**Known status:** The encoded statement is almost certainly refutable: for each fixed r, direct sums of ~r shortened-Hamming radius-1 covers give covering subspaces of density <= (2r)^r/r! (bounded) for all large n, so f_all r < top for every r and the 'eventually = top' claim is False. The intended limsup question remains open.  
**Difficulty:** math 3/10, Lean 7/10 · **Compute:** none · **Confidence:** high  
**Evidence:** atTop = pure top in any OrderTop: Ici top = {top} is in the filter base and is contained in every Ici a. Hence Tendsto f_all atTop atTop iff eventually f_all r = top. minDensity n r is finite for every n,r, and standard covering-code constructions bound it uniformly in n, making the limsup finite for each r.  
**Flags:** filter-target defect: atTop instead of nhds top on ENNReal codomain; resolvable with unintended answer False; intended problem stays open  
**Next action:** Fix the statement to 'Tendsto f_all atTop (nhds top)'. Alternatively the current statement can be legitimately closed with answer(False) by formalizing bounded-density covering constructions (shortened Hamming + direct sums) - moderate Lean work.

## `green_40.variants.arbitrary_subsets` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/GreensOpenProblems/40.lean:108`  
**Statement:** Same question for arbitrary (not necessarily linear) covering codes: does the liminf covering density f~(r) tend to infinity with r?  
**Source:** Ben Green, 100 open problems, https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf (Problem 40); Struik PhD thesis 1994 (f~(2)=1)  
**Statement matches intent:** yes  
**Known status:** Open; f~(2)=1 known (Struik); f~(r) <= f(r).  
**Difficulty:** math 9/10, Lean 9/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** Finset covering version uses the correct Tendsto ... (nhds top) encoding; infimum nonempty (V=univ Finset covers since 0 is in the ball).  
**Flags:** needs literature check: whether bounded-density coverings for all r (e.g. Krivelevich-Sudakov-Vu-type) already decide the nonlinear question  
**Next action:** Keep open.

## `green_41` — Vacuously true / accidentally weakened (cat 4)

**File:** `FormalConjectures/GreensOpenProblems/41.lean:66`  
**Secondary category:** 5 (Solved mathematically, not yet formalized)  
**Statement:** Quantitative pyjama problem: exhibit a bound ans(eps) on the number of rotations of the eps-pyjama set needed to cover the plane that is strictly below the Kravitz-Leng triple-exponential exp(exp(exp(eps^-C))).  
**Source:** Ben Green, 100 open problems, https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf (Problem 41); Manners, Inventiones 202 (2015); Kravitz-Leng, arXiv:2510.17744 (verified to exist)  
**Statement matches intent:** no — C-inflation loophole: the prover chooses C. Taking C := C0+1 (C0 the Kravitz-Leng exponent) and ans := exp(exp(exp(eps^-C0))) satisfies both conjuncts for eps<1, since eps^-C0 < eps^-C. So the statement follows from the existing KrLe bound and does not force any improvement.  
**Known status:** Formal statement is a consequence of Kravitz-Leng (Oct 2025, arXiv:2510.17744, confirmed real); the intended problem (genuinely better bounds, ideally eps^-C) remains open.  
**Difficulty:** math 8/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Strict inequality only against exp^3(eps^-C) with an existentially chosen C; monotonicity of eps^-C in C for 0<eps<1 gives the exploit. KrLe paper verified via web search.  
**Flags:** answer-encoding weaker than intended (quantifier over C inflatable); no Lean proof of any quantitative pyjama bound exists anywhere  
**Next action:** Tighten the spec (e.g. require ans = o of the KrLe bound for the SAME C, or demand a fixed iterated-exp level lower). Closing the current formal statement still requires formalizing quantitative pyjama - research-scale.

## `green_41.variants.exists_better_bound` — Vacuously true / accidentally weakened (cat 4)

**File:** `FormalConjectures/GreensOpenProblems/41.lean:77`  
**Secondary category:** 5 (Solved mathematically, not yet formalized)  
**Statement:** Existential version: is there some bound on minCopies(eps) strictly below the Kravitz-Leng triple-exponential? As encoded, taking ans := minCopies eps makes this equivalent to the KrLe bound itself with a larger C.  
**Source:** Ben Green, 100 open problems, https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf (Problem 41); Kravitz-Leng, arXiv:2510.17744  
**Statement matches intent:** no — With ans := minCopies eps the two conjuncts reduce to minCopies eps < exp^3(eps^-C), which holds by KrLe for any C > C0. So the RHS is True by known literature and carries no 'better bound' content.  
**Known status:** RHS provably True modulo Kravitz-Leng 2025; intended improvement question open.  
**Difficulty:** math 8/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Per-eps existential ans admits the trivial witness minCopies eps; strictness recovered by inflating C.  
**Flags:** answer-encoding trivializes 'better bound'  
**Next action:** Replace by a spec that quantifies the improvement (e.g. double-exponential or polynomial bound). Formal closure = answer(True) + formalizing KrLe (research-scale).

## `green_41.variants.polynomial_bound` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/GreensOpenProblems/41.lean:84`  
**Statement:** Do eps^-C rotations of the eps-pyjama set suffice to cover the plane, for some constant C?  
**Source:** Ben Green, 100 open problems, https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf (Problem 41); Kravitz-Leng arXiv:2510.17744 note eps^-C as Green's proposed intermediate goal; trivial lower bound eps^-1/2  
**Statement matches intent:** yes  
**Known status:** Genuinely open: best known upper bound is triple-exponential (KrLe 2025); heuristic truth ~eps^-1 log factors.  
**Difficulty:** math 9/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Faithful encoding: unrestricted C only helps monotonically, minCopies well-defined (covering set nonempty for eps>0 by Manners), Ioc 0 eps0 avoids junk eps<=0.  
**Next action:** Keep open; track follow-ups to Kravitz-Leng.

## `green_42` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/GreensOpenProblems/42.lean:85`  
**Statement:** Can the Cohn-Elkies linear-programming scheme prove the optimal circle-packing bound in dimension 2, i.e. does a magic function with f(0)/f^(0) = sqrt(3)/6 exist?  
**Source:** Ben Green, 100 open problems, https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf (Problem 42); Cohn-Elkies, Annals 2003; Viazovska 2017 (d=8); CKM 2017 (d=24); Sardari arXiv:2102.08753  
**Statement matches intent:** yes  
**Known status:** Famously open: dimension 2 is the only dimension besides 1, 8, 24 where the LP bound is even conjectured sharp; strong numerical evidence but no proof. Dims 8/24 magic functions exist (Viazovska; Lean formalizations linked in file).  
**Difficulty:** math 9/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Normalization cross-checked against known center densities in the file's solved variants: d=1 gives 1/2, d=8 gives 1/16, d=24 gives 1, and sqrt(3)/6 = hexagonal center density - consistent min-distance-2 convention. Mathlib Fourier junk values (non-integrable f gives fHat=0) are blocked by the 0 < fHat f 0 condition.  
**Flags:** attainment-vs-infimum reading noted; minor  
**Next action:** Keep open; Fourier interpolation on the plane (Sardari) is the identifiable avenue.

## `green_44` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/GreensOpenProblems/44.lean:39`  
**Statement:** Sieve [1,N] by removing floor(p_i/2) residue classes mod each of 1000 primes p_1<...<p_1000 < N^(9/10); must at most N/10 of [1,N] survive, for every such choice?  
**Source:** Ben Green, 100 open problems, https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf (Problem 44); Erdos 1980 survey  
**Statement matches intent:** yes  
**Known status:** Open; known affirmatively when all primes are below N^(1/2) via the large sieve (stated as solved variant in file). The N^(9/10) regime is beyond the large sieve.  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** p_999^10 < N^9 exactly encodes p < N^(9/10) over naturals; StrictMono gives distinctness; 10*card <= N is the exact rational inequality; no vacuity (instances exist for N > ~2*10^4).  
**Flags:** floor(p/2) vs (p+1)/2 convention for 'half' - transparent in docstring  
**Next action:** Keep open; connects to inverse large-sieve questions (Green 47).

## `green_46.improve_lower` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/GreensOpenProblems/46.lean:53`  
**Statement:** Improve, in the little-o sense, the best known lower bound x log x logloglog x/loglog x for the largest y such that [1,y] can be covered by one residue class mod p for each prime p <= x.  
**Source:** Ben Green, 100 open problems, https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf (Problem 46); Ford-Green-Konyagin-Maynard-Tao, JAMS 31 (2018); Rankin 1938  
**Statement matches intent:** yes  
**Known status:** Open. The stated bestLower is the FGKMT-2018 shape (Rankin's 1938 bound has an extra loglog factor in the denominator) - best known, but misattributed to [Ra38] in the def docstring.  
**Difficulty:** math 9/10, Lean 10/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** No degenerate witness: ans := maxY reduces the goal to bestLower = o(maxY), which is exactly the open improvement; sign tricks blocked by norm-based IsBigO/IsLittleO. maxY well-defined: union of one class per prime never covers all residues mod the primorial, so the coverable-y set is bounded.  
**Flags:** citation mislabel: bestLower is the FGKMT 2018 bound, not Rankin 1938  
**Next action:** Keep open (equivalent to improving long-gaps-between-primes lower bounds); fix the [Ra38] attribution to [FGK18].

## `green_46.improve_upper` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/GreensOpenProblems/46.lean:60`  
**Statement:** Improve, in the little-o sense, Iwaniec's upper bound y << x^2 for the same prime-residue covering problem.  
**Source:** Ben Green, 100 open problems, https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf (Problem 46); Iwaniec, Demonstratio Math. 11 (1978)  
**Statement matches intent:** yes  
**Known status:** Open; Iwaniec's x^2 (1978) is still the best known upper bound (Jacobsthal-type).  
**Difficulty:** math 9/10, Lean 10/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** ans := maxY reduces to maxY = o(x^2), the genuine open improvement; no exploit.  
**Flags:** needs literature check: any post-2024 improvement to Iwaniec's x^2  
**Next action:** Keep open.

## `green_46.improve_upper_conjectured` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/GreensOpenProblems/46.lean:67`  
**Statement:** Green's expectation that y << x^(1+o(1)): there is a function o(x) -> 0 with maxY = O(x^(1+o(x))).  
**Source:** Ben Green, 100 open problems, https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf (Problem 46)  
**Statement matches intent:** yes  
**Known status:** Open and far beyond current technology: even any o(x^2) improvement of Iwaniec is unknown; x^(1+o(1)) is the conjectured truth (Jacobsthal-type conjecture).  
**Difficulty:** math 9/10, Lean 10/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** Statement implies maxY << x^(2-delta) eventually, already open; encoding of x^(1+o(1)) via existential o(1) function is standard and faithful.  
**Next action:** Keep open; no known strategy closes the x^(1+o(1)) vs x^2 gap.

## `green_47` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/GreensOpenProblems/47.lean:46`  
**Statement:** Inverse large sieve conjecture (simplest instance): if A subset N occupies at most (p+1)/2 residue classes mod every large prime p, then either |A cap [X]| << sqrt(X)/log^100 X or A is contained in the integer image of a quadratic rational polynomial.  
**Source:** Ben Green, 100 open problems, https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf (Problem 47); Green-Harper, GAFA 24 (2014); Helfgott-Venkatesh 2009; Walsh 2012, 2014  
**Statement matches intent:** yes  
**Known status:** Recognized as a very hard open problem; partial results (Walsh: high-dimensional/box analogues, algebraicity of ill-distributed sets) remain far from the conjecture.  
**Difficulty:** math 9/10, Lean 10/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** Robustness checked: adding any nonsquare to the squares breaks the mod-p hypothesis for infinitely many p (non-residue classes), so no cheap counterexample; (p+1)/2 exact for odd p via Nat division; eventual-p hypothesis matches source; finite A satisfies conclusion 1 vacuously.  
**Next action:** Keep open.

## `green_50` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/GreensOpenProblems/50.lean:50`  
**Statement:** If A subset F_2^n has density alpha > 0, must the 10-fold sumset 10A contain a coset of a subspace of dimension at least n - O(log(1/alpha)), with an absolute constant?  
**Source:** Ben Green, 100 open problems, https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf (Problem 50)  
**Statement matches intent:** yes  
**Known status:** Open. In char 2, 10A contains 4A (pad with six copies of one element), so this is a polynomial-Bogolyubov-type statement; Sanders' log^4 codimension is the best known regime, and the question was listed open by Green in 2024, i.e. post-PFR (Gowers-Green-Manners-Tao).  
**Difficulty:** math 8/10, Lean 10/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** Quantifier order correct (one C for all n, A); Nonempty gives alpha>0; degenerate A (singletons, subsets of affine subspaces) checked consistent since log2(1/alpha) >= n - dim(span); 10 • A is the 10-fold Pointwise sumset as intended.  
**Flags:** needs literature check: post-2024 PFR-consequence papers may have settled O(log(1/alpha)) for bounded sumsets  
**Next action:** Keep open; investigate whether PFR-era techniques give O(log(1/alpha)) for enough summands - the natural avenue.

## `green_51` — Vacuously true / accidentally weakened (cat 4)

**File:** `FormalConjectures/GreensOpenProblems/51.lean:50`  
**Secondary category:** 8 (Deep but approachable research problem)  
**Statement:** Determine exactly, as a function of (n, alpha), the largest coset dimension guaranteed inside A+A for every A subset F_2^n of density >= alpha.  
**Source:** Ben Green, 100 open problems, https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf (Problem 51); Green, Restriction and Kakeya phenomena notes  
**Statement matches intent:** suspect — Exact-function-for-all-(n,alpha) reading is stronger than the source's asymptotic question, and the equation 'answer(sorry) = guaranteedMaxCosetDim' admits the tautological witness answer(guaranteedMaxCosetDim) closed by rfl; nothing in the elaborator forbids it.  
**Known status:** Intended asymptotic problem open: known coset dimension >> alpha n, and A+A can miss cosets of dimension n - sqrt(n).  
**Difficulty:** math 9/10, Lean 1/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Same answer-echo pattern batch 28 flagged for green_16/24/25/27; junk regimes included (alpha <= 0 and alpha > 1 give sInf of junk = 0), so an honest closed form must replicate junk values.  
**Flags:** answer-echo loophole (rfl); exact-value-for-all-parameters vs asymptotic source question  
**Next action:** Restate as bracketing asymptotics (as the file's solved variants do) or add a closed-form requirement; treat any rfl-style closure as illegitimate.

## `green_51.one_half` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/GreensOpenProblems/51.lean:71`  
**Statement:** Sanders' Question 5.1: if A subset F_2^n has density > 1/2 - k/sqrt(n), must A+A contain a coset of codimension O_k(1)?  
**Source:** Sanders, Acta Arith. 146 (2011), Question 5.1; Ben Green, 100 open problems, https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf (Problem 51 commentary)  
**Statement matches intent:** suspect — Source asks for a SUBSPACE of codimension O_C(1); the formalization (via guaranteedMaxCosetDim) only guarantees a coset/affine subspace - a weaker conclusion, so the encoded yes/no could in principle differ from the source question.  
**Known status:** Open; Sanders proved the density-(1/2 - c/sqrt(n)) case for small c.  
**Difficulty:** math 8/10, Lean 10/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** Quantifier structure (forall k, exists c, eventually n, forall alpha in range) matches O_C(1) uniformity; monotonicity of guaranteedMaxCosetDim in alpha makes the range quantifier sound.  
**Flags:** coset vs subspace conclusion mismatch (minor spec issue)  
**Next action:** Consider strengthening the conclusion to subspaces (0 is always in A+A, so this is plausibly equivalent but should be encoded, not assumed).

## `green_52` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/GreensOpenProblems/52.lean:35`  
**Statement:** If A subset F_2^n has an additive complement S of size K (A+S = everything), must A+A contain a coset of codimension bounded by a function of K alone?  
**Source:** Ben Green, 100 open problems, https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf (Problem 52)  
**Statement matches intent:** yes  
**Known status:** Open.  
**Difficulty:** math 8/10, Lean 10/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** Empty-affine-subspace exploit blocked: bottom has direction of finrank 0, so n <= 0 + c K fails for large n; K=0 vacuous since A + empty is not univ; c : N -> N correctly encodes O_K(1).  
**Next action:** Keep open.

## `green_52_log` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/GreensOpenProblems/52.lean:46`  
**Statement:** Strengthening: could A+A even contain a coset of codimension O(log K) under the same additive-complement hypothesis?  
**Source:** Ben Green, 100 open problems, https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf (Problem 52)  
**Statement matches intent:** yes  
**Known status:** Open.  
**Difficulty:** math 8/10, Lean 10/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** C, D free-sign reals chosen by prover; K=1 forces D >= 0 consistently; 0 < K guards log junk; same non-degeneracy as green_52.  
**Next action:** Keep open.

## `green_54` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/GreensOpenProblems/54.lean:44`  
**Statement:** Talagrand's convexity problem: if K is compact, balanced, and has Gaussian measure >= 0.99, must 10K contain a compact convex set of Gaussian measure >= 0.01 (uniformly in dimension)?  
**Source:** Ben Green, 100 open problems, https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf (Problem 54); Talagrand, 'Are all sets of positive measure essentially convex?', Oper. Theory Adv. Appl. 77 (1995)  
**Statement matches intent:** suspect — Source is finite-dimensional (R^n, gamma_n) with implicit uniformity in n; the file formalizes on R^N with the product Gaussian. Compact balanced K of measure 0.99 do exist there (products of growing intervals), so the statement is non-vacuous, but the equivalence of the infinite-dimensional form with the uniform finite-dimensional one (with these exact constants 0.99/0.01) is itself a nontrivial approximation argument, not encoded.  
**Known status:** Open; known false with 2K in place of 10K (Talagrand), as recorded in the file.  
**Difficulty:** math 9/10, Lean 10/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** Measure.infinitePi of standard Gaussians is the right gamma-infinity; Balanced/IsCompact/scalar dilation all standard; no degenerate C exploit found.  
**Flags:** infinite-dimensional reformulation of a uniform finite-dimensional source statement  
**Next action:** Either add the finite-dimensional uniform variant or record the equivalence argument; keep open.

## `green_58` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/GreensOpenProblems/58.lean:31`  
**Statement:** If A, B subset [1,N] both have at least N^0.49 elements (N large), must A+B contain a composite number - equivalently, can A+B consist entirely of primes?  
**Source:** Ben Green, 100 open problems, https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf (Problem 58); related to the Ostmann/inverse Goldbach circle of problems  
**Statement matches intent:** yes  
**Known status:** Open; known impossibility results for A+B all-prime require |A||B| beyond N-type barriers, and N^0.98 total is below them.  
**Difficulty:** math 9/10, Lean 10/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** All elements of A+B are >= 2, and Nat.Composite = (1 < n and not prime), so 'contains a composite' is exactly 'not all prime'; eventual-N encoding matches 'N large'; rpow threshold N^0.49 as in source.  
**Next action:** Keep open.

## `green_60` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/GreensOpenProblems/60.lean:31`  
**Statement:** Is there an absolute c > 0 such that every finite set A of perfect squares with |A| >= 2 satisfies |A+A| >= |A|^(1+c)?  
**Source:** Ben Green, 100 open problems, https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf (Problem 60); question on additive structure of squares (related to Erdos, Chang's theorem)  
**Statement matches intent:** yes  
**Known status:** Open; known lower bounds for sumsets of squares are only |A| times small log powers, far from |A|^(1+c).  
**Difficulty:** math 9/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Small-|A| cases only cap the constant (|A|=2 forces |A+A|=3 >= 2^(1+c), fine for small c) and cannot falsify the existential-c form; 0 allowed as a square is harmless.  
**Next action:** Keep open.

## `green_61` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/GreensOpenProblems/61.lean:38`  
**Statement:** Erdos-Newman: if A+A contains the first n squares, must |A| >= n^(1-o(1))?  
**Source:** Ben Green, 100 open problems, https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf (Problem 61); Erdos-Newman; known |A| >= n^(2/3-o(1)) and constructions with |A| << n/log^C n  
**Statement matches intent:** yes  
**Known status:** Open; gap between n^(2/3) lower bounds and n/polylog constructions.  
**Difficulty:** math 8/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** (Icc 1 n).image (sq) is exactly the first n squares; existential f -> 0 correctly encodes the n^(1-o(1)) claim since a minimizing A exists per n; n=1 edge case checked harmless.  
**Next action:** Keep open; TODO in file to add the two known partial results.

## `green_62` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/GreensOpenProblems/62.lean:36`  
**Statement:** Erdos-Odlyzko-Sarkozy conjecture: for every large prime p, every nonzero residue mod p is a product of two primes less than p.  
**Source:** Ben Green, 100 open problems, https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf (Problem 62); Erdos-Odlyzko-Sarkozy 1987  
**Statement matches intent:** yes  
**Known status:** Recognized hard open problem; not known even under GRH. Partial results: three-prime-product versions and almost-all residue classes are known (Walker, Shparlinski et al.). No repo duplicate (ErdosProblems/700 is a different Erdos-Szekeres problem).  
**Difficulty:** math 9/10, Lean 10/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** A = primes < p via (range p).filter Nat.Prime; a1 = a2 allowed as in source; cast of product equals product of casts in ZMod p; eventual-p encoding matches 'large prime'.  
**Next action:** Keep open.
