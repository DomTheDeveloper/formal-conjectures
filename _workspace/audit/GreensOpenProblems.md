# Audit detail — GreensOpenProblems

105 research-open declarations. Fields per problem: plain statement, source, category, match, status, action, difficulties, compute, confidence, evidence, flags.

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
**Statement:** F(N) is the size of the largest Sidon subset of {1,...,N}. Beat the classical lower bound F(N) >= sqrt(N) + O(1) for infinitely many N: exhibit ans with ans(N) - sqrt(N) -> infinity and ans(N) <= F(N) infinitely often.  
**Source:** Ben Green, '100 open problems' (2024), Problem 31; Erdos-Turan 1941; Singer 1938; cf. Erdos Problem 30  
**Statement matches intent:** yes  
**Known status:** Open and hard. Singer perfect difference sets give F(q^2+q+1) >= q+1 = sqrt(N) + O(1); nobody has beaten the additive O(1) even along a subsequence. This is the negation side of Erdos #30 (the $500 question 'is F(N) = sqrt(N) + O(1)?').  
**Difficulty:** math 9/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Encoding audited and equivalent to limsup_N (F N - sqrt N) = +infinity: given N_k with F(N_k)-sqrt(N_k) -> inf set ans := sqrt + d_k on [N_k, N_{k+1}) with d_k = inf_{j>=k}(F(N_j)-sqrt(N_j)); conversely the two conjuncts force F - sqrt -> inf along the frequent set. F = Finset.maxSidonSubsetCard (Icc 1 N) with the repo IsSidon (FormalConjecturesForMathlib/Combinatorics/Basic.lean:57); over N there is no 2-torsion so no char-2 degeneracy here. ErdosProblems/30,43,44,155 reuse the same F but ask different questions (not duplicates).  
**Next action:** Keep open; no known avenue. No internal work targets it (pr_register/campaign_register greps for green_31/Sidon: nothing; only an unrelated 'Audit Geode5' PR matched).

## `green_31.upper` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/GreensOpenProblems/31.lean:72`  
**Statement:** Improve, for infinitely many N, the upper bound F(N) <= sqrt(N) + 0.98183 N^{1/4} + O(1) (Carter-Hunter-O'Bryant 2025) to some constant c < 0.98183.  
**Source:** Ben Green, '100 open problems' (2024), Problem 31; Lindstrom 1969; Balogh-Furedi-Roy 2023 (0.998); Carter-Hunter-O'Bryant, Acta Math. Hungar. 175 (2025) (0.98183)  
**Statement matches intent:** yes  
**Known status:** Open. The N^{1/4} constant has moved recently (1 -> 0.998 -> 0.98183) so further incremental improvement is live research; removing the N^{1/4} term is the famous hard version. No post-CHO25 improvement known to me (cutoff Jan 2026).  
**Difficulty:** math 8/10, Lean 10/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** Statement unfolds to: exists c < 0.98183 and C with F(N) <= sqrt N + c N^{1/4} + C for infinitely many N (the eventual bound on ans meets the frequent set). Not a formal consequence of CHO25's eventual bound at c = 0.98183: gaining on the constant along a subsequence would need gaps of size ~k^{3/2} in M_k = min{N : F(N) = k}, which monotonicity alone does not give. Negative c is allowed but only makes the task harder - no loophole.  
**Flags:** needs literature check (post-CHO25 constants)  
**Next action:** Keep open; monitor the Sidon literature for a constant below 0.98183, then formalize (large analytic Lean project).

## `green_31.variants.abelian` — Vacuously true / accidentally weakened (cat 4)

**File:** `FormalConjectures/GreensOpenProblems/31.lean:128`  
**Secondary category:** 2 (Trivially or easily solvable)  
**Statement:** Decide whether every finite abelian group G has a Sidon subset of size at least 0.01 sqrt(|G|). Intended open, but under the repo's IsSidon the formal right-hand side is provably FALSE.  
**Source:** Ben Green, '100 open problems' (2024), Problem 31 (comments); cf. Babai-Sos 1985 (n^{1/3} known in general)  
**Statement matches intent:** no — IsSidon (Basic.lean:57) quantifies over ALL quadruples, including i1 = i2 and j1 = j2. In a group of exponent 2 take x != y: x + x = 0 = y + y, and the conclusion forces x = y. So every IsSidon subset of (ZMod 2)^n has card <= 1, while 0.01*sqrt(2^14) = 1.28 > 1. The intended (Babai-Sos / B_2) convention discounts these 2-torsion coincidences; under it F_2^n has Sidon sets of size ~sqrt(|G|) (graph of x -> x^3 over F_{2^m}) and Green's question is genuinely open.  
**Known status:** Formal theorem closable NOW with answer := False via the counterexample G = (Fin 14 -> ZMod 2). The intended mathematical question (0.01 sqrt(n) Sidon set in every abelian group) remains open - only ~n^{1/3} is known in general.  
**Difficulty:** math 8/10, Lean 3/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Read of FormalConjecturesForMathlib/Combinatorics/Basic.lean:57-58 plus the char-2 instantiation above; 𝔽₂/ZMod 2 modules satisfy x + x = 0 identically. Independently reproduces the defect recorded for this declaration in the earlier audit pass (_workspace/audit/data/final.json).  
**Flags:** major semantic mismatch: char-2 collapse of IsSidon; formal statement refutable while the intended conjecture is open  
**Next action:** Report the definition defect upstream (IsSidon needs a distinct-pair/group variant in even-order groups). To close as-is: instantiate G := Fin 14 -> ZMod 2, use Real.sqrt 16384 = 128 to force card S >= 2, pick x != y in S and apply the Sidon hypothesis at (x, y, x, y).

## `green_31.variants.lower_eventually` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/GreensOpenProblems/31.lean:61`  
**Statement:** Same lower-bound improvement as green_31.lower but for all sufficiently large N (i.e. liminf (F(N) - sqrt N) = infinity).  
**Source:** Ben Green, '100 open problems' (2024), Problem 31 (all-large-N variant)  
**Statement matches intent:** yes  
**Known status:** Strictly harder than green_31.lower: even F(N) >= sqrt(N) + O(1) for ALL large N is unknown (the best all-N bound is sqrt(N) - O(N^{5/16}) from Singer/Lindstrom plus prime gaps).  
**Difficulty:** math 9/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Identical skeleton to green_31.lower with 'eventually' replacing 'frequently'; audited clean, and Tendsto(ans - sqrt) atTop prevents any weak-ans loophole.  
**Next action:** Keep open.

## `green_31.variants.sidon_01n` — Vacuously true / accidentally weakened (cat 4)

**File:** `FormalConjectures/GreensOpenProblems/31.lean:138`  
**Secondary category:** 2 (Trivially or easily solvable)  
**Statement:** Decide whether {0,1}^n contains Sidon sets of size N^{0.51} (N = 2^n). Intended open, but under the repo's IsSidon every Sidon subset of F_2^n has at most one element, so the formal right-hand side is FALSE.  
**Source:** Ben Green, '100 open problems' (2024), Problem 31 (comments); Cohen-Litsyn-Zemor, JCTA 94 (2001) (upper bound N^{0.5753})  
**Statement matches intent:** no — Same char-2 collapse as the abelian variant: for x != y in F_2^n, x + x = 0 = y + y contradicts IsSidon, so card (S n) <= 1 < (2^n)^{0.51} for every n >= 1. The binary-Sidon (B_2) literature sums DISTINCT elements, under which sets of size ~2^{n/2} exist and the N^{0.51} vs N^{0.5753} gap is the real open problem.  
**Known status:** Formal theorem closable NOW with answer := False. Side effect: the companion 'research solved' theorem sidon_01n_clz01 becomes vacuously true (card <= 1) instead of encoding CLZ01.  
**Difficulty:** math 8/10, Lean 3/10 · **Compute:** none · **Confidence:** high  
**Evidence:** IsSidon read at Basic.lean:57; 𝔽₂ n = 𝔽 2 n (FormalConjecturesForMathlib/Data/ZMod/Fp.lean:34) is a ZMod 2 vector space. The neighbouring CLZ01 constant 0.5753 confirms the intended distinct-sum convention.  
**Flags:** major semantic mismatch: char-2 collapse of IsSidon; answer-encoding trivialized (False); collateral: sidon_01n_clz01 becomes vacuous  
**Next action:** Report defect upstream: use a distinct-pair Sidon/B_2 definition over F_2^n. To close as-is: at n = 1, (2^1)^{0.51} > 1 forces two distinct elements of S 1 and the IsSidon instantiation (x, y, x, y) gives False.

## `green_31.variants.upper_eventually` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/GreensOpenProblems/31.lean:83`  
**Statement:** Same improvement below the CHO25 constant 0.98183, required for all sufficiently large N.  
**Source:** Ben Green, '100 open problems' (2024), Problem 31; CHO25  
**Statement matches intent:** yes  
**Known status:** Open; this is the shape in which the BFR23/CHO25 improvements were actually proved (all large N), so the next literature improvement would close this and green_31.upper together.  
**Difficulty:** math 8/10, Lean 10/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** Same structure as green_31.upper with 'eventually'; audited clean.  
**Flags:** needs literature check (post-CHO25 constants)  
**Next action:** Keep open; monitor literature.

## `green_31.variants.zmod_p` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/GreensOpenProblems/31.lean:115`  
**Statement:** Decide whether for every prime p there is a Sidon subset of Z/pZ of size (1+o(1)) sqrt(p).  
**Source:** Ben Green, '100 open problems' (2024), Problem 31 (comments)  
**Statement matches intent:** yes  
**Known status:** Open per Green 2024. Singer/Bose-Chowla difference sets live in Z/(q^2+q+1)Z or Z/(q^2-1)Z, not in Z/pZ for a general prime; embedding an integer Sidon set into an interval of length p/2 only gives ~0.707 sqrt(p).  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Faithful: a single o with o =o[atTop] 1 forces card(S p)/sqrt p -> 1 along primes, and since o is otherwise unconstrained the exact equality card = (1+o p) sqrt p merely defines o pointwise, imposing nothing at any fixed p (so the p = 2 char-2 degeneracy of IsSidon is absorbed). For odd p, x + x = y + y implies x = y, so the repo IsSidon is the standard notion in Z/pZ.  
**Next action:** Keep open.

## `green_32` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/GreensOpenProblems/32.lean:82`  
**Statement:** For every large prime p and every A in Z/pZ with |A| = floor(sqrt p), is there a dilate cA (c a unit) containing floor(100 sqrt p) consecutive non-elements?  
**Source:** Ben Green, '100 open problems' (2024), Problem 32; Shakan, SIAM J. Discrete Math. 34 (2020) 2553-2555  
**Statement matches intent:** yes  
**Known status:** Open. Shakan's polynomial method gives a gap of floor(2p/|A| - 2) ~ 2 sqrt(p) (the file's solved variants); pushing the constant 2 to 100 is exactly Green's question.  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** none · **Confidence:** high  
**Evidence:** HasGap A L = exists x, forall i < L, x + i notin A (standard cyclic gap); floor(100 p / sqrt p) = floor(100 sqrt p) as intended, dilation by (ZMod p)-units matches 'dilate', and 100 sqrt p < p eventually so the conclusion is non-degenerate. The side conditions 100 < omega p and omega p < p sit in the CONCLUSION of HasLargeGapDilate rather than as hypotheses, but for omega = sqrt they hold for all large p, so nothing is lost here.  
**Flags:** minor spec issue: 100 < omega p < p asserted rather than assumed inside HasLargeGapDilate  
**Next action:** Keep open. No PR or campaign targets it.

## `green_32.variants.log_regime` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/GreensOpenProblems/32.lean:127`  
**Statement:** Decide the same dilate-gap property in the regime |A| ~ 10 log p (gaps of ~10p/log p demanded).  
**Source:** Ben Green, '100 open problems' (2024), Problem 32 (comments)  
**Statement matches intent:** yes  
**Known status:** Open in both directions per Green: Dirichlet/Bohr-set arguments handle |A| <= c log p only for small c, Szemeredi handles |A| ~ cp; 10 log p is the unresolved middle.  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** With k = 10 log p, simultaneous Dirichlet approximation only confines a dilate to an interval of length ~p/e^{1/10} ~ 0.9p, useless for a gap of 10p/log p, so the regime is genuinely uncovered by the two solved variants. The embedded 100 < omega p conjunct holds eventually since 10 log p -> infinity, so no vacuity; quantifying over all omega ~ 10 log p is a reasonable rendering of 'sets of size about 10 log p'.  
**Next action:** Keep open.

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
**Statement:** Improve a lower bound for c(p) = inf over probability densities f on [0,1] of ||f*f||_p; the formal content is proving c(2) > sqrt(4/7) or c(inf) > 0.64.  
**Source:** Ben Green, '100 open problems' (2024), Problem 35; Green, Acta Arith. 100 (2001); Cloninger-Steinerberger, Proc. AMS 145 (2017)  
**Statement matches intent:** yes  
**Known status:** Open per Green 2024: sqrt(4/7) at p = 2 and 0.64 at p = infinity are the best published lower bounds and I know of no improvement up to Jan 2026. The 2025 autoconvolution improvements that circulated (AlphaEvolve line, arXiv 2506.16750 / 2508.02803, per the earlier audit pass) concern the Martin-O'Bryant Holder ratio, a different quantity.  
**Difficulty:** math 8/10, Lean 10/10 · **Compute:** medium · **Confidence:** medium  
**Evidence:** c is an sInf over a nonempty set (the indicator of [0,1] qualifies), so no junk value; IsUnitIntervalDensity correctly encodes nonnegative, integrable, supported in [0,1], integral 1. Improving either published constant is genuine research on top of a heavy measure-theoretic formalization (eLpNorm of a convolution).  
**Flags:** decorative answer-hole in the first conjunct; needs literature check (exact CS17 constant)  
**Next action:** Keep open. Worth checking CS17's certified constant: if their proof yields something strictly above 0.64 (0.64 being a rounded presentation), the second disjunct is already literature-true and this becomes cat 5 (formalizing an LP/interval-arithmetic argument).

## `green_35.upper` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/GreensOpenProblems/35.lean:62`  
**Secondary category:** 6 (Computationally solvable with certificate)  
**Statement:** Improve the upper bound for c(inf) = inf over probability densities on [0,1] of sup(f*f); formally, prove c(inf) < 0.7505.  
**Source:** Ben Green, '100 open problems' (2024), Problem 35; Matolcsi-Vinuesa, J. Math. Anal. Appl. 372 (2010)  
**Statement matches intent:** suspect — Baseline constant likely mis-transcribed: the MV10 record is usually quoted as 1.50992 in the doubled normalization, i.e. c(inf) <= 0.75496 (~0.7549/0.755), not 0.7505 (this discrepancy was surfaced by the earlier audit pass's web search and I could not re-verify within my search budget). If so, the file's companion 'research solved' lemma c_inf_upper is not actually established and green_35.upper demands strictly more than 'beat the record'. Open either way.  
**Known status:** Open. Unlike the lower bound, improving the upper bound only needs an explicit better density (a step function with certified autoconvolution sup), so this side is construction/computation territory; the 2010 record has stood.  
**Difficulty:** math 7/10, Lean 9/10 · **Compute:** medium · **Confidence:** medium  
**Evidence:** ub := c satisfies the first conjunct definitionally, so the content is exactly c(inf) < 0.7505. Autoconvolution suprema of step functions are exactly computable, hence cat2 = 6.  
**Flags:** possible wrong constant vs MV10 (0.7505 vs ~0.75496); ub conjunct vacuous; content is a single strict inequality; needs literature check  
**Next action:** First reconcile the constant with Green's list / MV10. To attack: search for a step-function density with exact rational autoconvolution sup below the target; certificate = the step heights, kernel-checkable by rational arithmetic; then the measure-theory bridge to eLpNorm(inf) is the bulk of the Lean work.

## `green_36` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/GreensOpenProblems/36.lean:54`  
**Statement:** Do there exist, for arbitrarily large n, finite abelian groups H with |H| = n^{2+o(1)} and subsets A_1..A_n, B_1..B_n with |A_i||B_i| >= n^{2-o(1)}, |A_i+B_i| = |A_i||B_i|, and A_i+B_i disjoint from A_j+B_k whenever j != k?  
**Source:** Ben Green, '100 open problems' (2024), Problem 36; Cohn-Kleinberg-Szegedy-Umans, FOCS 2005, Problem 4.7  
**Statement matches intent:** yes  
**Known status:** Major open problem: such families would give matrix-multiplication exponent omega = 2. The cap-set/slice-rank obstructions (Blasiak-Church-Cohn-Grochow-Naslund-Sawin-Umans 2017) rule out some abelian routes for the triple product property but do not settle this; open as of Green 2024 and to my knowledge Jan 2026.  
**Difficulty:** math 10/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Quantifier audit: forall eps > 0, frequently n, exists H with n^{2-eps} <= Nat.card H <= n^{2+eps} plus per-i size bounds is a faithful rendering of n^{2+o(1)} / n^{2-o(1)} for arbitrarily large n. Degenerate escapes checked: the size condition excludes empty A_i; constant families A_i = A, B_i = B are excluded since Disjoint (A+B) (A+B) forces A+B empty; the natural product construction H = Z_m x Z_n, A_i = S x {i}, B_i = T x {-i} fails because |S+T| = |S||T| >= n^{2-eps} cannot fit in m <= n^{1+eps}.  
**Next action:** Keep open; do not attempt. The file honestly separates Green's phrasing (here) from CKS's (variant below).

## `green_36.variants.cks05` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/GreensOpenProblems/36.lean:65`  
**Statement:** Same existence question with the disjointness condition transcribed from CKS05 Definition 4.1: A_i+B_j disjoint from A_j+B_k for i != k (simultaneous double product property).  
**Source:** Cohn-Kleinberg-Szegedy-Umans, 'Group-theoretic algorithms for matrix multiplication', FOCS 2005, Def. 4.1 / Problem 4.7  
**Statement matches intent:** yes  
**Known status:** CKS Problem 4.7 is open; an affirmative answer implies omega = 2.  
**Difficulty:** math 10/10, Lean 10/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** Identical parameter skeleton to green_36; only the disjointness index pattern differs (i != k vs j != k), matching the file's NOTE.  
**Flags:** needs source check of CKS 4.1 index convention  
**Next action:** Keep open; verify the CKS 4.1 index convention against the paper and record it in the docstring.

## `green_37` — Vacuously true / accidentally weakened (cat 4)

**File:** `FormalConjectures/GreensOpenProblems/37.lean:47`  
**Secondary category:** 2 (Trivially or easily solvable)  
**Statement:** Determine exactly the least size m(N,k) of a set of naturals containing, for every d = 1..N, a k-term AP of common difference d.  
**Source:** Ben Green, '100 open problems' (2024), Problem 37  
**Statement matches intent:** no — Tautologically closable: answer := Green37.m N k, the sInf of the very set in the statement (defined at 37.lean:40-41, in scope with N, k). IsLeast then follows from Nat.sInf_mem (nonemptiness witness A = Finset.range ((k-1)*N+1), which contains 0, d, ..., (k-1)d for every d <= N) plus Nat.sInf_le. Nothing forces a closed form. It also over-demands in another direction: an exact value for every (N,k), whereas Green asks for the growth rate (unknown already for k = 3; k = 2 is the classical restricted difference basis problem, Theta(sqrt N)).  
**Known status:** Formal statement quickly provable via the self-referential answer; the intended determination problem is open.  
**Difficulty:** math 8/10, Lean 3/10 · **Compute:** none · **Confidence:** high  
**Evidence:** m is literally sInf of the IsLeast set; the achievable-cardinality set is upward closed (supersets of an AP-cover are AP-covers) so IsLeast is just min-attainment. Set.ContainsAP / IsAPOfLengthWith (FormalConjecturesForMathlib/Combinatorics/AP/Basic.lean:235) audited: for d >= 1 the k points i*d, i < k, are distinct and lie below (k-1)N+1.  
**Flags:** tautological answer loophole (answer := m N k); asks for an exact formula rather than the intended asymptotics  
**Next action:** Report the spec defect upstream (constrain the answer to a closed form, or replace by explicit two-sided bounds). To close as-is: nonemptiness via Finset.range ((k-1)*N+1), then Nat.sInf_mem / Nat.sInf_le.

## `green_37_asymptotic` — Vacuously true / accidentally weakened (cat 4)

**File:** `FormalConjectures/GreensOpenProblems/37.lean:56`  
**Secondary category:** 2 (Trivially or easily solvable)  
**Statement:** Find a function f with m(N,k) = f(N) for all large N.  
**Source:** Ben Green, '100 open problems' (2024), Problem 37 (asymptotic form)  
**Statement matches intent:** no — answer(sorry) : N -> R elaborates with k in scope, so answer := fun N => (m N k : R) is admissible and the goal becomes eventually (m N k : R) = (m N k : R), closed by Filter.Eventually.of_forall (fun _ => rfl). Even read in good faith, 'eventual exact equality with a formula' mis-states Green's request to estimate m(N,k).  
**Known status:** One-line provable via the self-referential answer; intended asymptotics open.  
**Difficulty:** math 8/10, Lean 1/10 · **Compute:** none · **Confidence:** high  
**Evidence:** 37.lean:56-58; nothing restricts the answer to closed-form/elementary functions.  
**Flags:** tautological answer loophole; eventual exact equality mis-specifies 'determine asymptotic behavior'  
**Next action:** Report spec defect; replace with a genuine two-sided asymptotic (explicit upper/lower bound pair, or IsTheta against a concrete elementary function).

## `green_37_bigO` — Trivially or easily solvable (cat 2)

**File:** `FormalConjectures/GreensOpenProblems/37.lean:68`  
**Secondary category:** 4 (Vacuously true / accidentally weakened)  
**Statement:** Find a big-O upper bound for m(N,k).  
**Source:** Ben Green, '100 open problems' (2024), Problem 37 (upper-bound form)  
**Statement matches intent:** no — Any upper bound qualifies, so the statement says nothing about the true growth. Two closures: (a) tautological, answer := fun N => (m N k : R) via Asymptotics.isBigO_refl; (b) legitimate but weak, answer := fun N => (N : R) + 1, since Finset.range ((k-1)*N+1) is an AP-cover giving m(N,k) <= (k-1)N + 1.  
**Known status:** Trivially solvable as stated; the intended sharp upper bound is open.  
**Difficulty:** math 8/10, Lean 1/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Route (b) audited against Set.ContainsAP / IsAPOfLengthWith (a = 0, difference d <= N, terms i*d < (k-1)N+1 for i < k).  
**Flags:** spec too weak: any upper bound qualifies; tautological answer loophole  
**Next action:** Close with isBigO_refl if a formal resolution is wanted; better, report the spec defect (the bound should have a prescribed sharp shape).

## `green_37_littleO` — Trivially or easily solvable (cat 2)

**File:** `FormalConjectures/GreensOpenProblems/37.lean:74`  
**Secondary category:** 4 (Vacuously true / accidentally weakened)  
**Statement:** Find a little-o (strict) upper bound for m(N,k).  
**Source:** Ben Green, '100 open problems' (2024), Problem 37 (strict upper-bound form)  
**Statement matches intent:** no — answer := fun N => ((m N k : R) + 1) * (N + 1) is little-o-valid for ANY nonnegative function with no knowledge of m (||f N|| <= c ||ans N|| once N + 1 >= 1/c); alternatively answer := fun N => (N : R)^2 via m(N,k) <= (k-1)N+1. Either way the statement carries no content about m.  
**Known status:** Trivially/easily solvable as stated; intended growth question open.  
**Difficulty:** math 8/10, Lean 2/10 · **Compute:** none · **Confidence:** high  
**Evidence:** IsLittleO unfolds to forall c > 0, eventually ||m N k|| <= c * ||ans N||; with the above ans and nonnegative values this holds for N >= ceil(1/c).  
**Flags:** spec too weak: any strict upper bound qualifies; quasi-tautological answer loophole  
**Next action:** Close with the (f+1)*(N+1) trick if desired; report the spec defect upstream.

## `green_37_theta` — Vacuously true / accidentally weakened (cat 4)

**File:** `FormalConjectures/GreensOpenProblems/37.lean:62`  
**Secondary category:** 2 (Trivially or easily solvable)  
**Statement:** Determine the Theta-class of m(N,k).  
**Source:** Ben Green, '100 open problems' (2024), Problem 37 (Theta form)  
**Statement matches intent:** no — answer := fun N => (m N k : R) gives f =Theta[atTop] f, closed by Asymptotics.isTheta_refl. No constraint ties the comparison function to a closed form.  
**Known status:** One-line provable; the intended order-of-magnitude question (unknown for k >= 3) is untouched.  
**Difficulty:** math 8/10, Lean 1/10 · **Compute:** none · **Confidence:** high  
**Evidence:** 37.lean:62-64; IsTheta is unconditionally reflexive.  
**Flags:** tautological answer loophole  
**Next action:** Report spec defect; a meaningful version must restrict the grammar of comparison functions or state concrete bounds.

## `green_38.lower` — Already solved externally (cat 1)

**File:** `FormalConjectures/GreensOpenProblems/38.lean:73`  
**Secondary category:** 6 (Computationally solvable with certificate)  
**Statement:** Improve the lower bound (growth constant C_1 = 367^{1/5} ~ 3.2578) for the largest A in F_7^n whose difference set meets {-1,0,1}^n only at 0 - equivalently, improve the lower bound on the Shannon capacity of C_7.  
**Source:** Ben Green, '100 open problems' (2024), Problem 38; Polak-Schrijver, IPL 143 (2019) (367 in C_7^5); NEW: arXiv:2607.21517, 'Improved lower bounds for the Shannon capacity of odd cycles' (July 2026)  
**Statement matches intent:** yes  
**Known status:** SOLVED EXTERNALLY (post-cutoff, July 2026). arXiv:2607.21517 constructs an independent set of size 134753 in C_7^{box 10} (plus 21909 in C_11^6 and 62530 in C_13^6), giving Theta(C_7) >= 134753^{1/10} > 3.258020 > 367^{1/5} ~ 3.257805; the constructions were found via iterated LLM interaction and are explicit. Note 134753 > 367^2 = 134689, so the improvement over C_1 is a norm_num-checkable numeric fact.  
**Difficulty:** math 6/10, Lean 8/10 · **Compute:** medium · **Confidence:** medium  
**Evidence:** Two independent web-search summaries of arXiv:2607.21517 report the sizes 134753 (C_7^10), 21909 (C_11^6), 62530 (C_13^6) and the bound Theta(C_7) >= 134753^{1/10} > 3.258020; arxiv.org returned 403 on direct fetch, so the abstract was not read verbatim. IntersectsOnlyAtZero is exactly independence in the n-th strong power of C_7, and the formal statement only needs SOME c > C_1 with c^n = O(ans) and ans <= LargestAdmissibleCardinality eventually - which supermultiplicativity of the certificate supplies.  
**Flags:** post-cutoff result; abstract not read verbatim (arXiv 403) - re-verify before relying; bulk of the Lean work is certificate extraction plus independence verification  
**Next action:** Import the certificate: (1) extract the explicit 134753-element subset S of F_7^10 from arXiv:2607.21517 and verify (S - S) meets {-1,0,1}^10 only at 0 (exploit the construction's algebraic/coset structure - a naive ~1.8e10-pair decide is out of reach); (2) prove admissibility is preserved under products and under padding with a zero coordinate, giving L(n) >= 134753^{floor(n/10)} >= c^n/134753 with c := 134753^{1/10}; (3) take ans n := c^n/134753, giving ans <= L eventually and (fun n => c^n) =O ans with constant 134753; (4) c > C_1 reduces to 134753 > 367^2. Then flip the category and verify the build.

## `green_38.upper` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/GreensOpenProblems/38.lean:81`  
**Statement:** Improve the upper bound below the Lovasz theta value C_2 = 7cos(pi/7)/(1+cos(pi/7)) ~ 3.3177 for the same quantity (upper bound on the Shannon capacity of C_7).  
**Source:** Ben Green, '100 open problems' (2024), Problem 38; Lovasz, IEEE Trans. IT 25 (1979), Corollary 5  
**Statement matches intent:** yes  
**Known status:** Recognized hard open problem: no technique is known that beats the Lovasz theta bound for odd cycles C_k, k >= 7 (Haemers-type rank bounds are weaker here). The July 2026 lower-bound progress (arXiv:2607.21517) does not touch the upper side.  
**Difficulty:** math 9/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Encoding audited symmetrically to green_38.lower: L <= ans eventually plus ans =O(c^n) with c < C_2 demands a strict exponential-rate improvement below theta. LargestAdmissibleCardinality is a well-defined sSup (the file proves nonemptiness and boundedness), so no junk values.  
**Next action:** Keep open; do not attempt.

## `green_39` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/GreensOpenProblems/39.lean:82`  
**Statement:** For a uniformly random A in Z/pZ with |A| = floor(sqrt p), does the probability that A can be covered by at most 100*floor(sqrt p) translates tend to 1 as the prime p grows?  
**Source:** Ben Green, '100 open problems' (2024), Problem 39; Bollobas-Janson-Riordan, Random Structures Algorithms 38 (2011)  
**Statement matches intent:** yes  
**Known status:** Open per Green 2024 (he states he cannot answer it even with 100 replaced by 1.01). Heuristics point to 'no': a fixed T of size 100 sqrt p leaves ~p e^{-100} points uncovered while there are only ~exp(50 sqrt p log p) candidate T, but making the first-moment argument rigorous needs independence nobody can establish; the fractional bound p/|A| = sqrt p is off by the usual log factor.  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** proportionCoverable is an exact counting definition (powersetCard k univ, filtered by exists T with |T| <= c and A + T = univ); its p = 0 and k > p junk branches are unreachable for primes with k = Nat.sqrt p, and the division is by C(p,k) != 0. In-file native_decide tests (e.g. proportionCoverable 7 4 2 = 3/5) sanity-check it. Tendsto over the prime subtype atTop to nhds 1 is the right 'asymptotically almost surely'.  
**Flags:** needs literature check (whether BJR11-style methods now cover the |A| = sqrt p regime)  
**Next action:** Keep open.

## `green_39.variant_101` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/GreensOpenProblems/39.lean:95`  
**Statement:** Same covering question with only floor(1.01 * floor(sqrt p)) translates allowed.  
**Source:** Ben Green, '100 open problems' (2024), Problem 39 (comments)  
**Statement matches intent:** yes  
**Known status:** Open in both directions; Green explicitly says he cannot answer this version either. 1.01 sqrt(p) translates sits just above the counting threshold |A||T| >= p, so a positive answer would be a near-perfect-covering phenomenon.  
**Difficulty:** math 9/10, Lean 9/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Same skeleton as green_39 with c = floor(1.01 * Nat.sqrt p); 1.01 sqrt(p) * sqrt(p) > p so there is no pigeonhole vacuity, and the floor conventions do not degrade the question.  
**Next action:** Keep open.

## `green_39.variant_theta` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/GreensOpenProblems/39.lean:114`  
**Statement:** For every theta in (0,1/2], is there C > 1 such that a random A in Z/pZ of size floor(p^theta) is almost surely coverable by floor(C p^{1-theta}) translates?  
**Source:** Ben Green, '100 open problems' (2024), Problem 39 (comments), reinterpreted by the formalizers (see the file's NOTE)  
**Statement matches intent:** suspect — Documented reinterpretation: Green's literal 'sqrt p replaced by p^theta' (with ~C p^theta translates) is trivially false by pigeonhole for theta < 1/2, so the file substitutes C p^{1-theta} translates, specializing to the main conjecture at theta = 1/2. Sensible, but it is the formalizers' reading, not Green's text; the existential C also makes the theta = 1/2 instance weaker than green_39's explicit 100.  
**Known status:** Open; same log-factor obstruction as green_39 for every theta (heuristically 'no' for each fixed C, since p^theta >> C e^C log p).  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** The file's NOTE records the pigeonhole issue and the reinterpretation; C p^{1-theta} * p^theta ~ C p >= p so the reinterpreted question is non-degenerate.  
**Flags:** documented prose-formal deviation (reinterpretation of an ill-posed literal statement)  
**Next action:** Keep open; ask upstream to confirm the intended reading against Green's text.

## `green_4` — Vacuously true / accidentally weakened (cat 4)

**File:** `FormalConjectures/GreensOpenProblems/4.lean:31`  
**Secondary category:** 2 (Trivially or easily solvable)  
**Statement:** Exhibit a largest product-free subset of the alternating group A_n (formalized as MaximalFor ProdFree ncard applied to an answer(sorry) family S n).  
**Source:** Ben Green, '100 open problems' (2024), Problem 4; Keevash-Lifshitz-Minzer, arXiv:2205.15191 (solves large n)  
**Statement matches intent:** no — Nonconstructive-choice loophole: alternatingGroup (Fin n) is a finite type, so Set (alternatingGroup (Fin n)) is finite, ProdFree holds of the empty set, and ncard is bounded; a cardinality-maximizer therefore exists for every n (Set.Finite.exists_maximalFor) and answer := fun n => Classical.choose (that existence) closes the theorem with no structural description at all. The intended problem - describing the extremal sets - is not captured. The statement also demands optimality for EVERY n while the literature settles only large n.  
**Known status:** Formal statement closable by finite argmax + choice. The intended structural problem is solved for large n externally (arXiv:2205.15191, recorded in the same file as large_green_4, still sorry); the small-n / crossover range is covered by no published result and is not reachable by computation (KLM's n_0 is far beyond exhaustive search).  
**Difficulty:** math 8/10, Lean 4/10 · **Compute:** none · **Confidence:** high  
**Evidence:** ProdFree (4.lean:28) is the standard no-x*y=z condition and holds vacuously for the empty set; MaximalFor P f a means P a plus no P-element has strictly larger f-value, which any argmax satisfies. Set.ncard is exact here since all sets are finite (no infinite-set ncard = 0 junk). answer() imposes no constructivity constraint.  
**Flags:** nonconstructive answer loophole: no explicit extremal family demanded; demands all n while KLM22 covers only large n  
**Next action:** Report the spec defect upstream (the answer should be an explicit family such as extremalFamily x I together with a proof of optimality). To close as-is: Set.Finite.exists_maximalFor over {S | ProdFree S} with the empty set as nonemptiness witness, then Classical.choice.

## `green_40` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/GreensOpenProblems/40.lean:61`  
**Statement:** For linear covering codes: f(r) is the liminf over n of the minimal density |V|*|H(r)|/2^n over subspaces V of F_2^n with V + H(r) = F_2^n. Does f(r) tend to infinity as r grows?  
**Source:** Ben Green, 100 open problems, https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf (Problem 40); Cohen-Honkala-Litsyn-Lobstein, Covering Codes (1997); Davydov 1990  
**Statement matches intent:** yes  
**Known status:** Open. Only f(1)=1 is known (Hamming codes); best upper bound f(r) <= r^r/r! ~ e^r; f(2) <= 1.4238. No internal PR/campaign targets Green 40-62 (pr_register.json contains only Green14/W(3,20) work; campaign_register.json lists no Green 40-62 target).  
**Difficulty:** math 9/10, Lean 9/10 · **Compute:** none · **Confidence:** high  
**Evidence:** liminf-of-minDensity matches Green's f(r) ('there exists an infinite sequence of n's'); Tendsto to (nhds top) in ENNReal is the correct encoding of divergence; the iInf is over a nonempty family since V = top always covers, so no empty-iInf junk; f(0)=1 harmlessly true.  
**Next action:** Keep as open research target; monitor covering-code literature (Davydov-type constructions vs lower-bound methods). Cheap formal by-products: minDensity >= 1 by counting, and f 0 = 1.

## `green_40.f_eq_one_for_all` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/GreensOpenProblems/40.lean:76`  
**Statement:** Is f(r) = 1 for every radius r, i.e. do asymptotically perfect linear coverings exist for all radii?  
**Source:** Ben Green, 100 open problems, https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf (Problem 40: 'the possibility that f(r)=1 for all r has not been ruled out')  
**Statement matches intent:** yes  
**Known status:** Open; incompatible with an affirmative answer to green_40. Not even f(2)=1 is decided.  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Quantifies over all r including r=0, but f(0)=1 provably (H(0)={0} forces V=univ, density exactly 1), so there is no falsifying edge case and no trivializing one; density >= 1 by counting, so 'f r = 1' is the genuine extremal question.  
**Next action:** Keep open; any resolution of f(2) decides this statement, so it is strictly easier than green_40.

## `green_40.f_two_eq_one` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/GreensOpenProblems/40.lean:81`  
**Statement:** Is f(2) = 1, i.e. are there asymptotically perfect linear coverings of F_2^n by radius-2 Hamming balls?  
**Source:** Ben Green, 100 open problems, https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf (Problem 40); best upper bound 1.4238 from [CHL97]/Davydov  
**Statement matches intent:** yes  
**Known status:** Open; best known upper bound f(2) <= 1.4238; for arbitrary (nonlinear) codes Struik proved the analogue f-tilde(2) = 1, so the subspace restriction carries the whole difficulty.  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Direct faithful encoding of a single open value of the same faithful f; no quantifier, junk-value or normalisation issue.  
**Next action:** Keep open; the construction-side attack (linear analogues of Struik's codes) is the identifiable avenue. The recorded upper bound f 2 <= 1.4238 is the realistic Lean target in this file.

## `green_40.variants.all_n` — Vacuously true / accidentally weakened (cat 4)

**File:** `FormalConjectures/GreensOpenProblems/40.lean:130`  
**Secondary category:** 7 (Plausibly solvable with moderate formal work)  
**Statement:** Intended: does f_all(r) = limsup_n (minimal linear covering density) tend to infinity with r? As formalized it instead asks whether f_all r is eventually EXACTLY infinity.  
**Source:** Ben Green, 100 open problems, https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf (Problem 40, 'all n' variant)  
**Statement matches intent:** no — Target-filter defect: ENNReal has a greatest element, so Filter.atTop = principal {top}. Hence 'Tendsto f_all atTop atTop' says 'for all large r, limsup_n minDensity n r = top', not divergence. The file's other two variants correctly use nhds top, showing this is a slip.  
**Known status:** The encoded statement is almost certainly refutable: minDensity n r is finite for every n (take V = top), and for each fixed r direct sums of shortened radius-1 Hamming covers give covering subspaces of density bounded uniformly in n, so f_all r < top for every r and the 'eventually = top' claim is False. The intended limsup question remains open.  
**Difficulty:** math 3/10, Lean 7/10 · **Compute:** none · **Confidence:** high  
**Evidence:** atTop = iInf over a of principal (Ici a); with a = top, Ici top = {top}, and this is the least member of the family, so atTop = principal {top} and Tendsto f_all atTop atTop iff eventually f_all r = top. This is strictly stronger than the intended unboundedness in r.  
**Flags:** filter-target defect: atTop instead of nhds top on an ENNReal codomain; resolvable with the unintended answer False; intended problem stays open  
**Next action:** Fix the statement to 'Tendsto f_all atTop (nhds top)'. Alternatively the current statement can be legitimately closed with answer(False) by formalizing bounded-density covering constructions - moderate-to-large Lean work with no Mathlib coding-theory support.

## `green_40.variants.arbitrary_subsets` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/GreensOpenProblems/40.lean:108`  
**Statement:** Same question for arbitrary (not necessarily linear) covering codes: does the liminf covering density f-tilde(r) tend to infinity with r?  
**Source:** Ben Green, 100 open problems, https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf (Problem 40); Struik PhD thesis 1994 (f-tilde(2)=1)  
**Statement matches intent:** yes  
**Known status:** Open; f-tilde(2) = 1 known (Struik); f-tilde(r) <= f(r).  
**Difficulty:** math 9/10, Lean 9/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** hammingBallFinset/IsCoveringFinset mirror the Set versions and use the same normalisation, so f-tilde <= f is an iInf over a superset; V = Finset.univ always covers so the iInf is nonempty; correct Tendsto ... (nhds top) encoding (unlike the all_n variant).  
**Flags:** needs literature check: whether known bounded-density nonlinear constructions already decide the nonlinear question  
**Next action:** Keep open. f_tilde_le_f is a cheap sanity lemma (iInf over a larger index family).

## `green_41` — Vacuously true / accidentally weakened (cat 4)

**File:** `FormalConjectures/GreensOpenProblems/41.lean:66`  
**Secondary category:** 5 (Solved mathematically, not yet formalized)  
**Statement:** Quantitative pyjama problem: exhibit a bound ans on the number of rotations of the width-eps pyjama set needed to cover the plane that lies strictly below the Kravitz-Leng triple exponential exp(exp(exp(eps^-C))).  
**Source:** Ben Green, 100 open problems, https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf (Problem 41); Manners, Inventiones 202 (2015) 239-270; Kravitz-Leng, 'Quantitative pyjama', arXiv:2510.17744 (existence and statement verified by web search)  
**Statement matches intent:** no — Two independent loopholes make this a restatement of the known bound rather than an improvement. (i) C-inflation: the prover chooses C, so taking C := C0 + 1 (C0 the Kravitz-Leng exponent) and ans := exp^3(eps^-C0) satisfies both conjuncts for eps < 1, since eps^-C0 < eps^-C. (ii) Answer scope: the answer(sorry) : R hole sits under the binders for C, eps0 and eps, so ans := (minCopies eps : R) is legal and makes the first conjunct le_refl.  
**Known status:** The formal statement is a consequence of Kravitz-Leng (Oct 2025; 'exp(exp(exp(eps^{-O(1)}))) rotations suffice', confirmed by search); the intended problem (a genuinely better bound, ideally eps^-C) remains open. Note that a genuinely eps-independent answer would make the statement FALSE, since a density argument gives minCopies eps >= 1/(2 eps).  
**Difficulty:** math 8/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Strict inequality is only against exp^3(eps^-C) with an existentially chosen C; monotonicity of eps^-C in C for 0<eps<1 gives the exploit. coveringCopies/minCopies themselves are faithful (rotation by exp(i theta) of the eps-neighbourhood of the integer vertical lines; sInf non-junk because minCopies_set_nonempty is asserted for eps>0).  
**Flags:** answer-encoding weaker than intended (C inflatable; ans may depend on eps); no Lean proof of any quantitative pyjama bound exists anywhere  
**Next action:** Tighten the spec (require ans to be o of the KrLe bound for every C, or fix a lower iterated-exponential level). Even the current weakened statement needs a Lean formalization of quantitative pyjama - research-scale, nothing exists.

## `green_41.variants.exists_better_bound` — Vacuously true / accidentally weakened (cat 4)

**File:** `FormalConjectures/GreensOpenProblems/41.lean:77`  
**Secondary category:** 1 (Already solved externally)  
**Statement:** Existential version: is there some bound on minCopies(eps) strictly below the Kravitz-Leng triple exponential? As encoded, taking ans := minCopies eps makes it equivalent to the KrLe bound itself.  
**Source:** Ben Green, 100 open problems, https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf (Problem 41); Kravitz-Leng, arXiv:2510.17744  
**Statement matches intent:** no — With ans := minCopies eps the two conjuncts collapse to minCopies eps < exp^3(eps^-C), which holds by Kravitz-Leng for any C > C0. The RHS is therefore TRUE by known literature and carries no 'better bound' content, contradicting the docstring's claim that this is an existential version of the main problem.  
**Known status:** RHS provably True modulo Kravitz-Leng 2025 (verified by search); the intended improvement question is open. Duplicates the file's own green_41.variants.kravitz_leng, which is already tagged 'research solved'.  
**Difficulty:** math 3/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Pure logic: an inner existential over R with a lower bound and a strict upper bound is equivalent to the single inequality minCopies eps < RHS, i.e. the KrLe theorem verbatim.  
**Flags:** existential witness trivializes 'better bound'; statement duplicates a solved sibling  
**Next action:** Replace by a spec that quantifies the improvement (double-exponential or polynomial), or delete as a duplicate. Formal closure would be answer(True) plus a formalization of KrLe - research-scale.

## `green_41.variants.polynomial_bound` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/GreensOpenProblems/41.lean:84`  
**Statement:** Do eps^-C rotations of the width-eps pyjama set suffice to cover the plane, for some constant C?  
**Source:** Ben Green, 100 open problems, https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf (Problem 41); Kravitz-Leng arXiv:2510.17744  
**Statement matches intent:** yes  
**Known status:** Genuinely open and the natural next target after Kravitz-Leng: the truth lies between the easy lower bound minCopies eps >> 1/eps and the triple-exponential upper bound.  
**Difficulty:** math 9/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Only statement in file 41 with real content: minCopies is compared against a fixed polynomial family, so no existential witness can trivialize it; Ioc 0 eps0 avoids junk eps <= 0.  
**Next action:** Keep open; track follow-ups to Kravitz-Leng. A realistic Lean milestone is the density lower bound minCopies eps >= ceil(1/(2 eps)).

## `green_42` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/GreensOpenProblems/42.lean:85`  
**Secondary category:** 8 (Deep but approachable research problem)  
**Statement:** Can the Cohn-Elkies linear-programming scheme prove the optimal circle-packing bound in dimension 2, i.e. does a magic function with f(0)/fhat(0) = sqrt(3)/6 exist?  
**Source:** Ben Green, 100 open problems, https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf (Problem 42); Cohn-Elkies, Annals 157 (2003) 689-714; Viazovska 2017 (d=8); CKMRV 2017 (d=24); Sardari arXiv:2102.08753  
**Statement matches intent:** yes  
**Known status:** Famously open: dimension 2 is, besides 1, 8 and 24, the only dimension where the LP bound is even conjectured sharp; strong numerics, no proof. Fourier interpolation on the plane (Sardari) is the identifiable avenue.  
**Difficulty:** math 10/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Normalisation cross-checks: with the spatial constraint at norm >= 2 (radius-1 spheres) the Cohn-Elkies bound is center density <= f(0)/fhat(0) with no 2^d factor, and the file's recorded values 1/2 (d=1; e.g. f = (2-|x|)_+ gives 2/4), 1/16 (E8), 1 (Leech) and sqrt(3)/6 = 1/(2 sqrt 3) (hexagonal) are the correct center densities. Fourier junk (non-integrable f giving fHat = 0) is blocked by the 0 < fHat f 0 condition, so the division is safe.  
**Flags:** attainment-vs-infimum reading of 'the scheme proves the optimal bound' (minor)  
**Next action:** Keep open. Lean effort in this file is better spent importing the linked math-inc Sphere-Packing-Lean results for the solved d=8 and d=24 variants; they give nothing for d=2.

## `green_44` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/GreensOpenProblems/44.lean:39`  
**Statement:** Sieve [1,N] by removing floor(p_i/2) residue classes mod each of 1000 increasing primes p_1 < ... < p_1000 < N^(9/10); must at most N/10 of [1,N] survive, for every such choice?  
**Source:** Ben Green, 100 open problems, https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf (Problem 44); Erdos, 'A survey of problems in combinatorial number theory', Ann. Discrete Math. 6 (1980) 89-115  
**Statement matches intent:** yes  
**Known status:** Open in the stated range; Green notes it is affirmative when all primes are below N^(1/2) via the large sieve, which is the file's solved variant. The N^(9/10) regime is beyond the large sieve.  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** p 999 ^ 10 < N ^ 9 encodes p_1000 < N^(9/10) exactly over the naturals; StrictMono plus primality gives 1000 distinct primes >= 2, and since the 1000th prime is 7919 the hypothesis forces N >= about 22000, so the statement is not vacuous and has no small-N degeneracy; 10 * remaining.card <= N avoids division. The classical squares/non-residue obstruction survives only at size ~sqrt(N), well below N/10, so there is no cheap counterexample.  
**Flags:** floor(p/2) vs (p+1)/2 convention for 'half' - transparent in the docstring  
**Next action:** Keep open; connects to the inverse large sieve (Green 47). The large-sieve variant is the realistic Lean target but needs a large-sieve inequality with explicit constants, absent from Mathlib.

## `green_46.improve_lower` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/GreensOpenProblems/46.lean:53`  
**Secondary category:** 8 (Deep but approachable research problem)  
**Statement:** Improve, in the little-o sense, the best known lower bound x log x logloglog x / loglog x for the largest y such that [1,y] can be covered by one residue class mod p for each prime p <= x.  
**Source:** Ben Green, 100 open problems, https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf (Problem 46); Ford-Green-Konyagin-Maynard-Tao, 'Long gaps between primes', JAMS 31 (2018) 65-105  
**Statement matches intent:** yes  
**Known status:** Open; equivalent to improving the long-gaps-between-primes lower bound, which has stood since 2014-2018 and is described by its authors as the limit of current methods. The def docstring misattributes the formula to [Ra38] (a label absent from the module reference list); Rankin's 1938 bound has (loglog x)^2 in the denominator, so the coded bound is FGKMT's.  
**Difficulty:** math 10/10, Lean 10/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** IsCoveredByResidues is faithful (one class a p per prime p <= x, covering [1,y]); maxY is well-defined and not junk because the product over p<=x of (1-1/p) is positive, so the coverable-y set is bounded. The << notation is the repo's Vinogradov abbreviation for Asymptotics.IsBigO atTop on N -> R (FormalConjecturesForMathlib/Analysis/Asymptotics/Basic.lean:25). No degenerate witness: sign tricks are blocked by the norm-based IsLittleO.  
**Flags:** citation mislabel: bestLower is the FGKMT 2018 bound, not Rankin 1938; [Ra38] is a dangling label  
**Next action:** Keep open (cat 9); fix the [Ra38] attribution to [FGK18].

## `green_46.improve_upper` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/GreensOpenProblems/46.lean:60`  
**Statement:** Improve, in the little-o sense, Iwaniec's upper bound y << x^2 for the same prime-residue covering problem.  
**Source:** Ben Green, 100 open problems, https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf (Problem 46); Iwaniec, 'On the problem of Jacobsthal', Demonstratio Math. 11 (1978) 225-232  
**Statement matches intent:** yes  
**Known status:** Open; Iwaniec's Jacobsthal bound (1978) is still the best known and no o(x^2) improvement is known to me.  
**Difficulty:** math 10/10, Lean 10/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** Same faithful maxY as improve_lower; bestUpper = x^2 matches Iwaniec's (log P)^2 after the standard change of variables log P(x) ~ x.  
**Flags:** needs literature check: any post-1978 improvement to Iwaniec's x^2  
**Next action:** Keep open (cat 9). Even the recorded solved variant maxY << x^2 is unformalized and would be a large project.

## `green_46.improve_upper_conjectured` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/GreensOpenProblems/46.lean:67`  
**Statement:** Green's expectation that y << x^(1+o(1)): there is a function o with o(x) -> 0 and maxY = O(x^(1+o(x))).  
**Source:** Ben Green, 100 open problems, https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf (Problem 46: 'it seems very likely that y << x^{1+o(1)}')  
**Statement matches intent:** yes  
**Known status:** Open and far beyond current technology: the statement implies maxY << x^(2-delta), which is already unknown; x^(1+o(1)) is the conjectured truth.  
**Difficulty:** math 10/10, Lean 10/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** o =o[atTop] (fun _ => 1) correctly encodes o(x) -> 0 and the bound uses rpow on the real cast, so there is no natural-power truncation. The existential over o cannot be abused: a large o weakens the bound but the little-o condition forbids o from staying away from 0. This is the only non-answer statement in the file.  
**Next action:** Keep open; no known strategy closes the x^(1+o(1)) vs x^2 gap.

## `green_47` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/GreensOpenProblems/47.lean:46`  
**Secondary category:** 8 (Deep but approachable research problem)  
**Statement:** Inverse large sieve (simplest instance): if A subset N occupies at most (p+1)/2 residue classes mod every large prime p, must either |A cap [X]| << sqrt(X)/log^100 X, or A be contained in the integer image of a quadratic rational polynomial?  
**Source:** Ben Green, 100 open problems, https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf (Problem 47); Green-Harper, GAFA 24 (2014) 1167-1203; Helfgott-Venkatesh 2009; Walsh 2012, GAFA 2014  
**Statement matches intent:** yes  
**Known status:** Recognized very hard open problem; partial results (Walsh's algebraicity of ill-distributed sets, high-dimensional analogues, Helfgott-Venkatesh) remain far from the conjecture.  
**Difficulty:** math 10/10, Lean 10/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** (p+1)/2 in N is exact for odd p (p+1 even) and the hypothesis is only imposed eventually, so no truncation artefact. Robustness checked: A = squares satisfies the hypothesis with equality and lands in the second disjunct (so the statement is neither vacuous nor cheaply false), while adding a nonsquare breaks the mod-p hypothesis for infinitely many p. Finite A satisfy the first disjunct since sqrt(X)/log^100 X -> infinity. The 'quadratic map Q -> Q' is a single degree-2 rational polynomial evaluated at integers, matching the source.  
**Next action:** Keep open. Formal progress needs the Green-Harper machinery, far from Mathlib.

## `green_50` — Vacuously true / accidentally weakened (cat 4)

**File:** `FormalConjectures/GreensOpenProblems/50.lean:50`  
**Secondary category:** 8 (Deep but approachable research problem)  
**Statement:** If A subset F_2^n has density alpha > 0, must the 10-fold sumset 10A contain a coset of a subspace of dimension at least n - C log_2(1/alpha) for an absolute constant C?  
**Source:** Ben Green, 100 open problems, https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf (Problem 50)  
**Statement matches intent:** suspect — The notation '10 • A' for A : Finset (F_2 n) is ambiguous and may not mean the tenfold sumset. Under 'open scoped Pointwise' two instances supply SMul N (Finset (F_2 n)): Finset.smulFinset (elementwise, A.image (10 • .)) and AddMonoid.toNatSMul coming from the pointwise Finset.addMonoid (the tenfold sumset). Finset.smulFinset is declared much later in Mathlib than AddMonoid.toNatSMul and equal-priority instances are tried most-recent-first, so the elementwise reading is the more likely resolution - and in characteristic 2 it gives A.image (fun _ => 0) = {0}.  
**Known status:** The intended question is open (with the sumset reading 10A contains 4A, since padding with six copies of a fixed element adds 6a = 0 in characteristic 2, so this is a polynomial-Bogolyubov / Sanders-regime question). Nothing in this fork targets it. If the elementwise reading is what Lean picks, the formal statement is refutable in a few lines and the file must be fixed.  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** Refutation under the elementwise reading: take n = 1, A = univ, so alpha = 1 and logb 2 1 = 0; then 10 • A = {0}, a coset v +v W inside {0} forces W = bot with finrank 0, and the required inequality reads 1 - C*0 <= 0, false for every C. Hence the answer would be False and closable quickly - certainly not Green's problem. Everything else is faithful: quantifier order (one C for all n and A), A.Nonempty giving alpha > 0, Finset.dens and Real.logb 2 with no division by zero.  
**Flags:** instance ambiguity: pointwise-monoid nsmul (sumset) vs Finset.smulFinset (elementwise) for '10 • A' - potentially trivializing in characteristic 2; module docstring conflates 'pointwise scalar multiplication' with 'iterated addition of a set'; needs literature check: post-2024 PFR-era work may bear on O(log(1/alpha)) codimension for bounded sumsets  
**Next action:** Run 'set_option pp.all true in #check @Green50.green_50' (or #print the statement) as soon as a build is available. If 10 • A elaborates via Finset.smulFinset, rewrite as an explicit tenfold sumset and re-audit as cat 8. Do not attempt a proof before this is settled.

## `green_51` — Vacuously true / accidentally weakened (cat 4)

**File:** `FormalConjectures/GreensOpenProblems/51.lean:50`  
**Secondary category:** 8 (Deep but approachable research problem)  
**Statement:** Determine exactly, as a function of (n, alpha), the largest coset dimension guaranteed inside A+A for every A subset F_2^n of density at least alpha.  
**Source:** Ben Green, 100 open problems, https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf (Problem 51); Green, 'Restriction and Kakeya phenomena' notes; Sanders, Acta Arith. 146 (2011)  
**Statement matches intent:** suspect — 'answer(sorry) = guaranteedMaxCosetDim' admits the tautological witness answer(guaranteedMaxCosetDim), closed by rfl; nothing in the elaborator forbids it. Moreover the exact-function-for-all-(n,alpha) reading is stronger than the source's asymptotic question, and the junk regimes (alpha > 1 gives sInf of the empty set = 0) would have to be reproduced by any honest closed form.  
**Known status:** The intended asymptotic problem is open: A+A must contain a coset of dimension >>_alpha n, and need not contain one of dimension n - sqrt(n) (both recorded as solved variants in the file).  
**Difficulty:** math 9/10, Lean 1/10 · **Compute:** none · **Confidence:** high  
**Evidence:** maxCosetDim (FormalConjecturesForMathlib/Combinatorics/Additive/Coset.lean:21) is sSup of finrank S.direction over affine subspaces S contained in A; guaranteedMaxCosetDim n alpha is the sInf of that over A with A.dens >= alpha. The answer hole has type N -> R -> N and is unconstrained in shape.  
**Flags:** answer-echo loophole (closable by rfl); exact-value-for-all-parameters vs asymptotic source question; sInf junk value 0 for alpha > 1 (no 0 < alpha <= 1 hypothesis)  
**Next action:** Restate as bracketing asymptotics (as the file's own solved variants do) or add a closed-form requirement; treat any rfl-style closure as illegitimate. Same answer-echo pattern already flagged in batch 28 for green_16/24/25/27.

## `green_51.one_half` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/GreensOpenProblems/51.lean:71`  
**Statement:** Sanders' Question 5.1: if A subset F_2^n has density above 1/2 - k/sqrt(n), must A+A contain a coset of codimension bounded in terms of k only?  
**Source:** Sanders, 'Green's sumset problem at density one half', Acta Arith. 146 (2011) 91-101, Question 5.1; Ben Green, 100 open problems (Problem 51 commentary)  
**Statement matches intent:** suspect — The source asks for a SUBSPACE of codimension O_C(1); via guaranteedMaxCosetDim the formalization only guarantees a coset (affine subspace), a weaker conclusion, so the encoded yes/no could in principle differ from the source question. (In characteristic 2, 0 is always in A+A, which makes the two plausibly equivalent - but that is assumed, not encoded.)  
**Known status:** Open (Sanders' Question 5.1); Sanders handled density exactly 1/2, and the 1/2 - k/sqrt(n) regime is the stated open extension.  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** Quantifier structure (forall k > 0, exists c, eventually n, forall admissible alpha) correctly encodes the O_k(1) uniformity; the eventually-in-n quantifier keeps 1/2 - k/sqrt(n) positive so no degenerate nonpositive alpha is forced; monotonicity of guaranteedMaxCosetDim in alpha makes the alpha-range quantifier sound.  
**Flags:** coset vs subspace conclusion mismatch (minor spec issue); inherits the sInf junk convention of guaranteedMaxCosetDim outside 0 < alpha <= 1  
**Next action:** Consider strengthening the conclusion to subspaces; keep open. A trivial sanity milestone is alpha = 1 (A = univ gives codimension 0).

## `green_52` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/GreensOpenProblems/52.lean:35`  
**Statement:** If A subset F_2^n has an additive complement S of size K (A + S = everything), must A+A contain a coset of codimension bounded by a function of K alone?  
**Source:** Ben Green, 100 open problems, https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf (Problem 52)  
**Statement matches intent:** yes  
**Known status:** Open; closely related to Problem 51 and to quantitative Bogolyubov-type theorems in F_2^n. No formalization and no fork PR.  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** Quantifier order correct (c : N -> N chosen before n, K, A, S), so c K correctly encodes O_K(1). Degenerate cases are self-excluding: K = 0 gives S empty and A + empty = empty, not univ; A empty likewise fails the hypothesis. The empty-affine-subspace exploit is blocked because bot has direction of finrank 0, so n <= 0 + c K fails for large n.  
**Flags:** AffineSubspace can be the empty bot; harmless here, but a nonempty side condition would be cleaner  
**Next action:** Keep open. Cheap sanity lemma worth adding: K = 1 forces A = F_2^n, hence codimension 0.

## `green_52_log` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/GreensOpenProblems/52.lean:46`  
**Statement:** Strengthening: could A+A even contain a coset of codimension O(log K) under the same additive-complement hypothesis?  
**Source:** Ben Green, 100 open problems, https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf (Problem 52)  
**Statement matches intent:** yes  
**Known status:** Open, and strictly stronger than green_52.  
**Difficulty:** math 9/10, Lean 9/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** 0 < K guards the Real.log junk value (and K = 0 is vacuous anyway); C and D are free-sign reals chosen by the prover, the correct rendering of O(log K) + O(1), and a negative C only makes the claim harder; same non-degeneracy analysis as green_52.  
**Next action:** Keep open; resolve green_52 first.

## `green_54` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/GreensOpenProblems/54.lean:44`  
**Secondary category:** 8 (Deep but approachable research problem)  
**Statement:** Talagrand's convexity problem: if K is compact, balanced, and has Gaussian measure at least 0.99, must 10K contain a compact convex set of Gaussian measure at least 0.01?  
**Source:** Ben Green, 100 open problems, https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf (Problem 54); M. Talagrand, 'Are all sets of positive measure essentially convex?', Oper. Theory Adv. Appl. 77 (1995)  
**Statement matches intent:** suspect — The docstring states the finite-dimensional problem (K in R^n, gamma_n, constants uniform in n) while the Lean statement lives on R^N with the infinite product Gaussian. Compact balanced K of measure 0.99 do exist there (products of growing intervals), so the statement is non-vacuous, but IsCompact means product-topology compactness, and the equivalence with the uniform finite-dimensional form at these exact constants is a nontrivial approximation argument that is not encoded.  
**Known status:** Open (Talagrand's question); known false with 2K in place of 10K, as recorded in the file.  
**Difficulty:** math 10/10, Lean 10/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** Measure.infinitePi of standard Gaussians is the right gamma-infinity; Balanced R K matches 'lambda K subset K for |lambda| <= 1'; (10:R) • K is the correct dilate; thresholds are ENNReal literals compared in the right directions; no degenerate C exploit found (C must have measure at least 0.01, so C empty or a point is excluded).  
**Flags:** infinite-dimensional reformulation of a uniform finite-dimensional source statement; compactness is with respect to the product topology on N -> R, not a norm topology  
**Next action:** Add the finite-dimensional uniform-in-n variant (or record the equivalence argument); keep open.

## `green_58` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/GreensOpenProblems/58.lean:31`  
**Statement:** If A, B subset [1,N] both have at least N^0.49 elements (N large), must A+B contain a composite number - equivalently, can A+B consist entirely of primes?  
**Source:** Ben Green, 100 open problems, https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf (Problem 58); Ostmann / inverse Goldbach circle of problems  
**Statement matches intent:** yes  
**Known status:** Open; the exponent 1/2 is the barrier reachable by sieve/large-sieve arguments, and 0.49 sits just below it, which is why Green poses it.  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** Nat.Composite is the repo abbreviation '1 < n and not n.Prime' (FormalConjecturesForMathlib/Data/Nat/Prime/Composite.lean:22); since all elements of A+B are at least 2, 'contains a composite' is exactly 'not all prime', with no junk from 0 or 1. Sizes use rpow on the real cast (no natural-power truncation) and the eventually-N quantifier matches 'N large'.  
**Next action:** Keep open. A worthwhile weaker formal target is the same statement with exponent 1/2 + delta.

## `green_60` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/GreensOpenProblems/60.lean:31`  
**Statement:** Is there an absolute c > 0 such that every finite set A of perfect squares with at least 2 elements satisfies |A+A| >= |A|^(1+c)?  
**Source:** Ben Green, 100 open problems, https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf (Problem 60)  
**Statement matches intent:** yes  
**Known status:** Open; known lower bounds for sumsets of squares give only |A| times small log powers, far from |A|^(1+c).  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** none · **Confidence:** high  
**Evidence:** IsSquare on N is the right predicate and 0 as a square is harmless; 2 <= A.card excludes the degenerate singleton; the inequality uses rpow on the real cast so there is no natural-power truncation. Since min |A+A| >= 2|A| - 1 always, small cardinalities only cap the constant and cannot falsify the existential-c form, so the content is genuinely asymptotic with c uniform - faithful.  
**Next action:** Keep open. Sanity variants could record that |A| = 2 forces |A+A| = 3, so small cases never obstruct.

## `green_61` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/GreensOpenProblems/61.lean:38`  
**Statement:** Erdos-Newman: if A+A contains the first n squares, must |A| >= n^(1-o(1))?  
**Source:** Ben Green, 100 open problems, https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf (Problem 61); Erdos-Newman; known |A| >= n^(2/3-o(1)), and constructions with |A| <<_C n/log^C n  
**Statement matches intent:** yes  
**Known status:** Open; the gap between the n^(2/3) lower bound and the n/polylog constructions is the content.  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** none · **Confidence:** high  
**Evidence:** (Finset.Icc 1 n).image (. ^ 2) is exactly the first n squares; A ranges over all finite sets of naturals with no artificial support restriction; the existential f -> 0 correctly encodes n^(1-o(1)), and since f may be arbitrarily large on any finite initial segment, quantifying over all n >= 1 rather than only large n creates no falsifying small-n obligation.  
**Next action:** Keep open; the file has a TODO to add the two known partial results. Formalizing the n^(2/3-o(1)) bound (a Cauchy-Schwarz/additive-energy argument) is a plausible medium-difficulty milestone.

## `green_62` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/GreensOpenProblems/62.lean:36`  
**Secondary category:** 8 (Deep but approachable research problem)  
**Statement:** Erdos-Odlyzko-Sarkozy conjecture: for every large prime p, every nonzero residue mod p is a product of two primes less than p.  
**Source:** Ben Green, 100 open problems, https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf (Problem 62); Erdos-Odlyzko-Sarkozy 1987  
**Statement matches intent:** yes  
**Known status:** Recognized hard open problem; not known even under GRH. Partial results: three-prime-product versions (Ramare-Walker) and almost-all residues/primes. No duplicate statement elsewhere in the repo.  
**Difficulty:** math 9/10, Lean 10/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** A = (Finset.range p).filter Nat.Prime is exactly the primes below p; x ranges over 1 <= x < p, i.e. all nonzero residues; a1 = a2 is allowed as in the source; a1, a2 < p prime are nonzero in ZMod p so no degenerate factorisation exists; the eventually-p quantifier with the p.Prime guard renders 'for all sufficiently large primes'.  
**Flags:** needs literature check: confident the two-prime EOS conjecture is still open, but post-2024 progress not re-verified  
**Next action:** Keep open. Tractable variants to add: the 'almost all p' or 'three primes' versions, both theorems.

## `green_7.variants.positive_density` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/GreensOpenProblems/7.lean:38`  
**Statement:** Ulam's sequence 1, 2, 3, 4, 6, 8, 11, 13, ... (each term the least integer larger than the previous with a unique representation as a sum of two earlier distinct terms) is asked to have positive (upper) density in the naturals.  
**Source:** Ben Green, '100 open problems' (2024), Problem 7; erdosproblems.com/342; OEIS A002858  
**Statement matches intent:** yes  
**Known status:** Open. erdosproblems.com lists Erdos 342 as state=open as of 2026-07-26 (scratchpad/erdos_states.json). Numerically the density is ~0.07398 and Steinberger's Fourier quasi-periodicity phenomenon is unexplained; no nontrivial lower bound on the density (indeed not even a(n) = O(n)) is proved. No PR in the 262-PR fork register and no campaign in campaign_register.json touches Green 7 / Erdos 342.  
**Difficulty:** math 9/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** IsUlamSequence pins a unique sequence (verified by hand for n <= 4 and by the file's own test lemmas a0..a3). upperDensity is limsup |S ∩ [0,b)| / b (FormalConjecturesForMathlib/Data/Set/Density.lean:56). Statement = 'the (upper) density of the Ulam set is positive', which is precisely Green's Problem 7 / Erdos 342(iii) negated. No known approach.  
**Flags:** duplicate-modulo-negation of FormalConjectures/ErdosProblems/342.lean:erdos_342.parts.iii; upper density used where 'positive density' would more naturally be lower density / natural density (minor spec weakening)  
**Next action:** Leave open. Only cheap repo-level work available: note that this statement is the exact logical complement of FormalConjectures/ErdosProblems/342.lean:erdos_342.parts.iii (upperDensity = 0), so the two answer(sorry) slots must receive opposite truth values; consider cross-linking them so a future resolution updates both.

## `NoKInLine` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/GreensOpenProblems/72.lean:61`  
**Statement:** For every k > 2 and every N >= k, the N x N integer grid contains (k-1)N points no k of which are collinear (and no more), i.e. the trivial pigeonhole upper bound (k-1)N is attained.  
**Source:** Ben Green, '100 open problems' (2024), Problem 72 (generalised in-repo); Wikipedia 'No-three-in-line problem'; [GK2025] Grebennikov–Kwan, arXiv:2510.17743  
**Statement matches intent:** suspect — This is a repo-invented generalisation, not Green's Problem 72 verbatim, and it is stated in the direction that experts believe is FALSE at k = 3: the Guy–Kelly heuristic (Guy & Kelly 1968, constant corrected by Guy 1971) predicts that the maximum no-three-in-line set in [N]^2 has size (c+o(1))N with c = (2*pi^2/3)^(1/3) ≈ 1.874 < 2, so NoKInLineFor 3 N should fail for all large N. The declaration therefore asks the prover to establish something conjecturally false. Also note the file's module docstring ('Given N < 2 and a more than 2*N points ... are there 3 of the points on a common line?') is garbled and describes the trivially-true pigeonhole direction (which is the separate `allowedSetSize_le`), not the open existence direction actually formalised here.  
**Known status:** Open in the strict sense (no counterexample is known for any single N even at k=3; the trivial 2N upper bound has never been improved), but believed false for k=3 and large N. Grebennikov–Kwan (arXiv:2510.17743, cited in the file) prove the k-analogue only for astronomically large constant k. No PR/campaign in this fork targets it; PR #122 ('feat: add solved monochromatic checkerboard no-three-in-line bound', open, unmerged) proves a different, restricted statement (<= 2n-4 for one checkerboard colour class) and does not close this.  
**Difficulty:** math 10/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** AllowedSet/AllowedSetSize were checked: the sup set is nonempty and bounded (s ⊆ [N]^2), so sSup over ℕ is well behaved; not_collinear over exactly-k-element subsets correctly forbids k collinear points since any line with > k points contains a k-subset. Sanity check AllowedSetSize 4 4 = 12 (delete the permutation {(0,0),(1,2),(2,1),(3,3)}, which meets both long diagonals) confirms the k=4, N=4 instance. The k=3 instance is green_72 below.  
**Flags:** stated in the direction contradicted by the Guy–Kelly heuristic (believed false for k=3, large N); sibling declaration `no_k_in_line_big` (line 86, category research solved) is FALSE as stated: it omits the N >= k hypothesis, so e.g. k = 10^37+1, N = 1 gives AllowedSetSize k 1 = 1 while (k-1)*N = 10^37; module docstring garbled ('Given N < 2') and describes the easy pigeonhole direction, not this statement; ℕ-subtraction in (k-1)*N is harmless here only because hk : 2 < k  
**Next action:** Leave open; consider restating as an answer(sorry) question (as the `eventually` variant does) rather than a theorem to be proved, since the expected truth value is False. Also fix the module docstring.

## `green_72` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/GreensOpenProblems/72.lean:67`  
**Statement:** The no-three-in-line problem: for every N >= 3 one can place 2N points on the N x N grid with no three collinear (and 2N is the maximum).  
**Source:** Ben Green, '100 open problems' (2024), Problem 72; Wikipedia 'No-three-in-line problem'; Guy & Kelly (1968)  
**Statement matches intent:** suspect — The formal statement 'AllowedSetSize 3 N = 2N for all N >= 3' is a correct rendering of the classical no-three-in-line CONJECTURE, but it is widely believed false for large N (Guy–Kelly heuristic: max ≈ 1.874N). Green's problem 72 is more plausibly asking for the opposite (prove 2N is not attainable for large N), and the module docstring describes yet a third, trivially-true statement. Proving green_72 as written would contradict the standard heuristic.  
**Known status:** Open. Constructions attaining 2N are known only for N <= 46 (Flammenkamp 1992; extended by later searches — the file's `no_three_in_line_le` claims N <= 60), and no improvement over the trivial 2N upper bound is known for any N. No fork PR or campaign targets this statement (PR #122 is the checkerboard variant, unmerged and a different statement).  
**Difficulty:** math 10/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** green_72 is exactly the k=3 instance of NoKInLine. Definitions audited (see NoKInLine entry): no junk-value, indexing or finiteness defect found in AllowedSet/AllowedSetSize. The obstruction is mathematical, not formal.  
**Flags:** stated in the direction contradicted by the Guy–Kelly heuristic; module docstring mismatch (describes the trivial upper-bound direction)  
**Next action:** Leave open; recommend converting to an answer(sorry) formulation and repairing the module docstring. A tractable adjacent contribution would be to formalise the pigeonhole bound `allowedSetSize_le` and a concrete N=3..6 construction rather than the conjecture itself.

## `green_72.variants.eventually` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/GreensOpenProblems/72.lean:74`  
**Statement:** Is it true that for all sufficiently large N, the N x N grid admits 2N points with no three collinear?  
**Source:** Ben Green, '100 open problems' (2024), Problem 72; Guy & Kelly (1968) heuristic  
**Statement matches intent:** yes  
**Known status:** Open, and this is the sharp form of the question: the expected answer is False (Guy–Kelly), but nobody has proved any upper bound better than the trivial 2N for large N, so neither direction is currently provable. No PR/campaign in this fork.  
**Difficulty:** math 10/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Statement uses Filter.atTop over ℕ; NoKInLineFor 3 N = (AllowedSetSize 3 N = 2*N) with no ℕ-subtraction hazard (3-1 = 2 exactly). Both truth values are open; disproving requires beating the trivial upper bound, which is a long-standing open problem.  
**Flags:** expected answer is False; the sibling non-variant theorems green_72 / NoKInLine assert the believed-false direction as goals  
**Next action:** Leave open. Realistic progress would be a formalisation of the Guy–Kelly counting heuristic, but it is a heuristic, not a proof; no formal milestone is available.

## `green_77` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/GreensOpenProblems/77.lean:35`  
**Statement:** Heilbronn's triangle problem: given n points in the unit disc, must some three of them form a triangle of area at most n^{-2+o(1)}? Equivalently, is the extremal quantity alpha(n) equal to n^{-2+o(1)}?  
**Source:** Ben Green, '100 open problems' (2024), Problem 77; erdosproblems.com/507; [KPS82] Komlos–Pintz–Szemeredi; [CPZ23/24] Cohen–Pohoata–Zakharov  
**Statement matches intent:** suspect — The asymptotic encoding (∃ o → 0 with alpha ≪ n^{-2+o(n)}) is a correct reading of 'n^{-2+o(1)}'. The suspicion is in the imported definition Erdos507.minTriangleArea: it takes the infimum over `t : Affine.Triangle ℝ ℝ²` with vertices in S, and Affine.Triangle demands affinely independent points, so DEGENERATE (collinear) triples are silently excluded. The classical Heilbronn quantity is the min over all triples of distinct points, which is 0 as soon as three points of S are collinear. Hence alpha as defined is >= the true alpha (configurations containing three collinear points are not penalised). The intended sup is almost certainly unchanged (collinear configurations look suboptimal), but this is unproved and is a genuine definitional deviation.  
**Known status:** Open. erdosproblems.com lists Erdos 507 as state=open as of 2026-07-26. Best known: alpha(n) ≫ log n / n^2 (KPS82) and alpha(n) ≪ n^{-7/6+o(1)} (Cohen–Pohoata–Zakharov 2023/24). The gap between n^{-7/6} and n^{-2} is enormous. No PR or campaign in this fork touches Green 77 / Erdos 507.  
**Difficulty:** math 10/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** alpha is defined in FormalConjectures/ErdosProblems/507.lean:50 as sSup of minTriangleArea over n-point non-collinear subsets of the closed unit ball; ≪ is Asymptotics.IsBigO atTop coerced to ℕ → ℝ (FormalConjecturesForMathlib/Analysis/Asymptotics/Basic.lean:25), so the junk values alpha 0 = alpha 1 = alpha 2 = 0 (empty sSup) are asymptotically irrelevant. The mathematical content is the famous Heilbronn upper-bound question.  
**Flags:** Affine.Triangle in Erdos507.minTriangleArea excludes degenerate/collinear triples — alpha may be larger than the literature quantity; alpha n = 0 for n <= 2 by sSup of the empty set (harmless for IsBigO atTop)  
**Next action:** Leave open. Repo-level fix worth doing: make Erdos507.minTriangleArea range over all 3-element subsets (assigning area 0 to collinear triples) so that alpha matches the literature, then re-check the dependent statements in 507.lean and 77.lean.

## `green_85` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/GreensOpenProblems/85.lean:41`  
**Statement:** Carbery's rectangle (box) problem: is there an absolute constant c > 0 such that every open subset A of the unit square with measure alpha contains the four corners of an axis-parallel rectangle of area at least c*alpha^2?  
**Source:** Ben Green, '100 open problems' (2024), Problem 85; [CCW99] Carbery–Christ–Wright §6; [Ke00] Keleti; [KKM02] Katz–Krop–Maggioni; [Mu02] Mubayi Conj. 1.4; [CPZ20] Conlon–Pohoata–Zakharov  
**Statement matches intent:** yes  
**Known status:** Listed as open in Green's 2024 problem list; a targeted web search found no post-2024 resolution (nothing conclusive returned — treat as unconfirmed). The easy Cauchy–Schwarz bound c*alpha^2 / log(1/alpha) is recorded in the same file as `green_85_loose`; closing the log gap is the content of the problem, and it is the 2-dimensional shadow of the Erdos box problem / Mubayi's hypergraph Turan conjecture. No PR or campaign in this fork touches it.  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** Formalisation is faithful and non-degenerate as argued above. The mathematics is a well-known analysis/combinatorics problem with substantial literature (five references in the file) and only a logarithmic gap between the known bound and the conjecture, which is why it is cat 8 rather than 9.  
**Flags:** needs literature check: could not confirm 2024–2026 status of Carbery's rectangle problem by search  
**Next action:** Leave open. Identifiable avenue: formalise the Cauchy–Schwarz `green_85_loose` bound first (a genuinely reachable milestone, category research solved), and look for a counterexample construction in the Keleti / Katz–Krop–Maggioni line of work, which would settle the answer as False.

## `green_9_ii` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/GreensOpenProblems/9.lean:51`  
**Statement:** Is r_5(N), the largest size of a subset of {1,...,N} with no nontrivial 5-term arithmetic progression, bounded by N (log N)^{-c} for some c > 0?  
**Source:** Ben Green, '100 open problems' (2024), Problem 9(ii)  
**Statement matches intent:** yes  
**Known status:** Open. The best known bound for k >= 5 is Leng–Sah–Sawhney, 'Improved bounds for Szemeredi's theorem' (arXiv:2402.17995), r_k(N) ≪ N exp(-(log log N)^{c_k}) with c_k = 2^{-2^{k+9}} < 1; since (log log N)^{c_k} = o(log log N), that bound is WEAKER than any fixed power of log N, so it does not answer 9(ii). A Kelley–Meka-type input for 5-APs would be needed. No PR/campaign in this fork.  
**Difficulty:** math 9/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Definitions in FormalConjecturesForMathlib/Combinatorics/AP/Basic.lean:200,255 checked; the ENat.card = l clause in IsAPOfLengthWith rules out degenerate APs, so no vacuity/weakening loophole. Mathematically this is the notorious 'logarithmic barrier for longer progressions'.  
**Flags:** sibling green_9_i (line 44) attributes the r_3 power-of-log bound to [BlSi20]; Bloom–Sisask only give (log N)^{-1-c}, the (log N)^{-10} bound is Kelley–Meka  
**Next action:** Leave open (cat 9). Note in passing that the sibling `green_9_i` in the same file credits [BlSi20] for r_3(N) ≪ N (log N)^{-10}, which Bloom–Sisask does NOT give (they reach (log N)^{-1-c}); the correct citation is Kelley–Meka (2023).

## `green_9_iii` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/GreensOpenProblems/9.lean:60`  
**Secondary category:** 9 (Major open problem / currently infeasible)  
**Statement:** Is r_4(F_5^n), the largest 4-AP-free subset of the vector space F_5^n, bounded by N^{1-c} for some c > 0, where N = 5^n?  
**Source:** Ben Green, '100 open problems' (2024), Problem 9(iii); Green–Tao, 'New bounds for Szemeredi's theorem I: progressions of length 4 in finite field geometries'  
**Statement matches intent:** yes  
**Known status:** Open. Best known is Green–Tao's N/(log N)^c for 4-APs in F_q^n; polynomial savings (N^{1-c}) are not known, and the Croot–Lev–Pach / Ellenberg–Gijswijt polynomial method is not known to extend past 3-APs. No PR/campaign in this fork.  
**Difficulty:** math 9/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** AP definitions audited (see green_9_ii). The finite-field 4-AP problem is a well-known testbed with partial results (Green–Tao log savings, U^3 inverse theorem) but no polynomial bound; hence cat 8 with 9 as secondary.  
**Next action:** Leave open. This is the most 'approachable' of the three parts of Problem 9 (finite-field model, small cases n = 1,2,3 are finite computations that could seed a formal library of exact values), but the asymptotic question needs a genuinely new idea; first realistic milestone would be a formal r_4(F_5^1), r_4(F_5^2) computation, which does not touch the conjecture itself.

## `green_94` — Major open problem / currently infeasible (cat 9)

**File:** `FormalConjectures/GreensOpenProblems/94.lean:46`  
**Secondary category:** 8 (Deep but approachable research problem)  
**Statement:** Erdos' similarity problem for the geometric sequence: must every measurable set of positive Lebesgue measure in R contain an affine copy a*{1, 1/2, 1/4, ...} + b with a nonzero?  
**Source:** Ben Green, '100 open problems' (2024), Problem 94; erdosproblems.com/120 ($100 prize)  
**Statement matches intent:** yes  
**Known status:** Open. erdosproblems.com lists Erdos 120 as state=open (prize $100) as of 2026-07-26 (scratchpad/erdos_states.json). The geometric sequence {2^{-n}} is the case Erdos specifically singled out and it has resisted all recent progress (Kolountzakis–Papageorgiou; Gallagher–Lai–Weber; Cruz–Lai–Pramanik constructions of large avoiding sets of full Hausdorff dimension but not positive measure). The expected answer is False. No PR/campaign in this fork.  
**Difficulty:** math 9/10, Lean 10/10 · **Compute:** none · **Confidence:** high  
**Evidence:** green_94_outer_measure in the same file already carries answer(False) and an upstream formal proof, and the ONLY difference is the MeasurableSet hypothesis — a deliberate and correct separation, not a duplication. The measurable case is the actual $100 Erdos problem and remains open.  
**Flags:** closely related to (but not a duplicate of) FormalConjectures/ErdosProblems/120.lean:erdos_120, which states the general similarity problem  
**Next action:** Leave open. Worth cross-referencing FormalConjectures/ErdosProblems/120.lean:erdos_120 (the general '∀ infinite A, Erdos120For A' form) — green_94 is the negation of Erdos120For applied to the single set {2^{-n}}, so the two answer slots are linked; adding that link is the only cheap action.
