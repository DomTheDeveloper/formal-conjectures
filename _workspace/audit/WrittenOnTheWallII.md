# Audit detail — WrittenOnTheWallII

21 research-open declarations. Fields per problem: plain statement, source, category, match, status, action, difficulties, compute, confidence, evidence, flags.

## `conjecture100` — Already solved internally (cat 0)

**File:** `FormalConjectures/WrittenOnTheWallII/GraphConjecture100.lean:75`  
**Secondary category:** 4 (Vacuously true / accidentally weakened)  
**Statement:** For a connected graph G, the independence number satisfies alpha(G) <= ceil((max_v l(v) + 0.5*length(complement of G))/2), where l(v) is the independence number of N(v) and 'length' is formalised as the L2 norm of the complement degree sequence.  
**Source:** WOWII #100 (status O), http://cms.uhd.edu/faculty/delavinae/research/wowII/all.html#conj100  
**Statement matches intent:** suspect — The module docstring says 'length(Gbar)' is interpreted as the DIAMETER of the complement (Gᶜ.ediam) and adds hGc : Gᶜ.Connected to keep that finite, but the actual Lean statement uses `degreeL2Norm Gᶜ` = sqrt(sum of squares of complement degrees). The fork's own proof file states: 'It does not claim to prove the differently documented diameter formulation.' Under the L2 reading the hGc hypothesis is unnecessary (a gratuitous weakening); under the diameter reading the statement is much stronger and unproved.  
**Known status:** A complete, sorry-free Lean proof of exactly the degreeL2Norm statement (with only G.Connected, no Gᶜ.Connected) exists in the fork: PR #52 'Audit WOWII 100 exact formalization' (branch agent/solve-wowii-100) adds FormalConjectures/WrittenOnTheWallII/GraphConjecture100ForkProof.lean (arithmetic_ceiling_bound) and GraphConjecture100Complete.lean (theorem conjecture100, ~343 lines, double-counting + Cauchy). Follow-ups #56/#57/#58 report a clean pinned Lean 4.27 build and axiom audit; upstream PR google-deepmind/formal-conjectures#4515 is the submission.  
**Difficulty:** math 5/10, Lean 4/10 · **Compute:** none · **Confidence:** high  
**Evidence:** PR #52 diff read in full: proof goes via a maximum independent set S (a clique in Gᶜ), double counting incidences between S and Sᶜ, deg_Gᶜ(s) >= |S|-1+r(s), deg_Gᶜ(t) >= |S|-L, then a polynomial ceiling bound. Independent sanity check: any max independent set of size A is a clique in Gᶜ, so sum deg_Gᶜ^2 >= A(A-1)^2, giving RHS >= sqrt(A)(A-1)/4 >= A already for A >= 17 — consistent with the statement being genuinely provable in this encoding.  
**Flags:** prose/formal mismatch: docstring says diam(Gᶜ) (ediam) while the statement uses degreeL2Norm Gᶜ; hypothesis hGc : Gᶜ.Connected is justified only by the (unused) diameter reading and weakens the theorem; canonical file still @[category research open] with sorry although a fork proof exists  
**Next action:** Port GraphConjecture100ForkProof.lean + GraphConjecture100Complete.lean from branch agent/solve-wowii-100 onto main (as a ForkProof wrapper like 143/316), close conjecture100 by `exact conjecture100 G h` (the proof is strictly stronger: no hGc needed), verify the build, and separately FIX the module docstring, which documents a different invariant than the theorem states.

## `conjecture103` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/WrittenOnTheWallII/GraphConjecture103.lean:42`  
**Statement:** For a connected graph G, the independence number is at most floor(b(G) - ln(average eccentricity)), where b(G) is the number of vertices of a largest induced bipartite subgraph.  
**Source:** WOWII #103, DeLaVina, Written on the Wall II (Graffiti.pc), http://cms.dt.uh.edu/faculty/delavinae/research/wowII/  
**Statement matches intent:** yes  
**Known status:** No fork PR, branch or campaign touches 103; no external proof known. Genuinely open WOWII conjecture.  
**Difficulty:** math 6/10, Lean 8/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** Since a maximum independent set S is itself induced-bipartite and S plus one adjacent vertex still is, b >= alpha + 1, so the content is exactly ln(ecc_avg) <= b - alpha. Any shortest path is induced and bipartite, giving b >= diam+1 >= ecc_avg+1; the residual difficulty is the joint bound. No division-by-zero or truncation issues (Fintype.card >= 2 so averageEccentricity > 0, Real.log of a value >= 1).  
**Next action:** Attack via b(G) >= alpha(G) + alpha(G - S) for a maximum independent set S, plus the induced shortest path of diam+1 vertices; reduce to the small-diameter cases ecc_avg <= e^2 where b - alpha >= 3 must be shown. First milestone: formalise b(G) >= alpha(G) + 1 and b(G) >= diam(G) + 1.

## `conjecture133` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/WrittenOnTheWallII/GraphConjecture133.lean:47`  
**Statement:** For a connected graph G, the largest induced path has at least rad(G) + floor(average local independence)^{chi_C4(G)} vertices, where chi_C4 is 1 when G is C4-free and 0 otherwise.  
**Source:** WOWII #133, DeLaVina, Written on the Wall II (Graffiti.pc)  
**Statement matches intent:** yes  
**Known status:** Open; no fork PR/branch/campaign for 133.  
**Difficulty:** math 6/10, Lean 8/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** When G contains a 4-cycle, cC4 = 0 and the RHS collapses to rad + floor(l)^0 = rad + 1, which is trivially true (a geodesic from a centre vertex to a vertex at distance rad is an induced path on rad+1 vertices) — so half of the statement is free. 0^0 = 1 in Lean, so no junk-value problem. Checked K_n, K_{1,m}, friendship graphs and Petersen: all satisfy it, several tightly.  
**Flags:** half of the statement (graphs containing a C4) is trivially true  
**Next action:** Split as the file already suggests: the C4-containing branch is essentially free; concentrate on the C4-free branch path(G) >= rad(G) + floor(l(G)). First milestone: a Lean lemma 'shortest paths are induced', giving path(G) >= rad(G)+1.

## `conjecture141` — Plausibly solvable with moderate formal work (cat 7)

**File:** `FormalConjectures/WrittenOnTheWallII/GraphConjecture141.lean:41`  
**Secondary category:** 8 (Deep but approachable research problem)  
**Statement:** For a connected graph G, the largest induced tree has at least floor(girth/2) - 1 + max_v l(v) vertices, where l(v) is the independence number of the neighbourhood of v.  
**Source:** WOWII #141, DeLaVina, Written on the Wall II (Graffiti.pc)  
**Statement matches intent:** yes  
**Known status:** Open; no fork PR/branch for 141. Substantial reusable Lean infrastructure exists in WOWII/GraphConjecture143*.lean (largest-induced-tree lower-bound lemmas such as finset_card_le_largestInducedTreeSize, exists_max_induced_tree_containing).  
**Difficulty:** math 5/10, Lean 7/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** tree(G) >= maxL + 1 is elementary (star at the arg-max vertex), which already settles all graphs of girth <= 5; for larger girth the standard fact 'the ball of radius floor((g-1)/2) induces a forest' supplies the extra floor(g/2)-2 vertices. Acyclic case is trivial since girth = 0 and tree = n.  
**Next action:** Prove: (i) tree(G) >= maxL + 1 by exhibiting the induced star {v} ∪ A for a maximum independent A ⊆ N(v); (ii) for cyclic G, extend that star by a geodesic of length floor(girth/2) - 2 whose vertices cannot create chords without contradicting the girth. Reuse WOWII/GraphConjecture143Leaves/Boundary lemmas. First milestone: the induced-star lemma tree(G) >= maxL + 1.

## `conjecture142` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/WrittenOnTheWallII/GraphConjecture142.lean:42`  
**Statement:** For a connected graph G, the largest induced tree has at least (2/3)*girth(G) + ecc(B) vertices, where B is the set of boundary (maximum-eccentricity) vertices and ecc(B) the maximum distance from a vertex to B.  
**Source:** WOWII #142, DeLaVina, Written on the Wall II (Graffiti.pc)  
**Statement matches intent:** yes  
**Known status:** Open; no fork PR/branch for 142.  
**Difficulty:** math 6/10, Lean 8/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** For vertex-transitive / self-centred graphs (cycles, Petersen, complete multipartite) B = V, ecc(B) = 0 and the claim reduces to tree >= (2/3)girth, implied by tree >= girth-1 for girth >= 3. Checked K_n (2 <= 2, tight), K_{m,m}, C_n, Petersen.  
**Next action:** Baseline lemma tree(G) >= girth(G) - 1 (a shortest cycle minus one vertex is an induced path); then the content is to gain ecc(B) - girth/3 more vertices. Explore graphs where B is small (asymmetric graphs) since B = V forces ecc(B)=0 and the statement reduces to the baseline.

## `conjecture143` — Already solved internally (cat 0)

**File:** `FormalConjectures/WrittenOnTheWallII/GraphConjecture143.lean:43`  
**Statement:** For a connected graph G whose second-smallest degree sigma is positive, girth(G) + 1 <= tree(G) * sigma(G), where tree(G) is the largest induced tree size.  
**Source:** WOWII #143, http://cms.uhd.edu/faculty/delavinae/research/wowII/all.html#conj143  
**Statement matches intent:** yes  
**Known status:** SOLVED inside this fork. Merged PR #46 'Add fork-hosted Lean proofs for WOWII 143 and 316' added WOWII/GraphConjecture143{Proof,Next,Leaves,Boundary,CycleAttach,ZZFinal}.lean with theorem conjecture143_proved, and FormalConjectures/WrittenOnTheWallII/GraphConjecture143ForkProof.lean restates the canonical statement verbatim and closes it with `exact conjecture143_proved G h hσ`. No `sorry` anywhere in WOWII/ (grep verified); the WOWII lib is a lakefile target. Campaign register: campaign wowii-143, proof_state complete-proof-in-repo.  
**Difficulty:** math 5/10, Lean 1/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Read WOWII/GraphConjecture143ZZFinal.lean: conjecture143_proved has exactly the canonical signature and hypotheses, proved by case split on acyclicity and on sigma = 1 vs sigma >= 2, using only ordinary tactics (no native_decide, no axioms declared).  
**Flags:** canonical file still marked @[category research open] with sorry despite the in-repo proof  
**Next action:** Replace the `sorry` in GraphConjecture143.lean by `exact conjecture143_proved G h hσ` (or import the ForkProof wrapper), flip the category to research solved, and verify the build plus `#print axioms` (no lake build possible in this container).

## `conjecture144` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/WrittenOnTheWallII/GraphConjecture144.lean:44`  
**Statement:** For a connected graph G, the largest induced tree has at least girth(G) - 1 + ecc(centre(G)) vertices, where ecc(centre) is the maximum distance from a non-centre vertex to the centre set.  
**Source:** WOWII #144, DeLaVina, Written on the Wall II (Graffiti.pc)  
**Statement matches intent:** yes  
**Known status:** Open; no fork PR/branch for 144.  
**Difficulty:** math 6/10, Lean 8/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** Hand-checked C6 + pendant (girth 6, ecc(centre) = 1, tree = 6, bound 6 — tight), C3 with a tail of length p, K_n and Petersen. The baseline tree >= girth - 1 covers all self-centred graphs where ecc(centre) = 0.  
**Next action:** Prove the baseline tree(G) >= girth(G) - 1 first (shortest cycle minus a vertex is an induced path), then attach a geodesic from the centre; the gain must be exactly ecc(centre) <= radius. Reuse the induced-tree machinery from WOWII/GraphConjecture143*.lean.

## `conjecture145` — Already solved internally (cat 0)

**File:** `FormalConjectures/WrittenOnTheWallII/GraphConjecture145.lean:75`  
**Statement:** For a connected graph G with positive minimum local independence number of the complement, 2*ecc(B) <= tree(G)*lMin(complement of G), where B is the boundary vertex set and tree(G) the largest induced tree size.  
**Source:** WOWII #145, DeLaVina, Written on the Wall II (Graffiti.pc)  
**Statement matches intent:** yes  
**Known status:** SOLVED in the fork ecosystem: fork PR #62 'Mark WOWII 145 solved'; _certificates/145Certificate.md (in this repo) documents a pinned Lean 4.27.0 build with axiom audit [propext, Classical.choice, Quot.sound]; the standalone proof is at DomTheDeveloper/crl commit 2ee448ba… math/wowii145/WOW145/145.lean; verification PRs #59/#60 and crl PR #190. Campaign wowii-145 marks proof_state 'certificates-only' (proof only on branch agent/solve-wowii-145-current and in the external repo).  
**Difficulty:** math 6/10, Lean 3/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** _certificates/145Certificate.md read in full: it is a self-produced novelty/priority audit asserting a complete kernel-checked proof of the exact theorem; nothing in this repository contains the proof itself, so the claim is unreproduced here.  
**Flags:** proof lives only on a branch / external repo — verify before trusting; self-produced audit certificate, not independently reproduced  
**Next action:** Recover branch agent/solve-wowii-145-current (or fetch DomTheDeveloper/crl 145.lean), add a ForkProof wrapper in the style of GraphConjecture143ForkProof.lean, rebuild and re-run the axiom audit, then close the canonical statement.

## `conjecture146` — Already solved internally (cat 0)

**File:** `FormalConjectures/WrittenOnTheWallII/GraphConjecture146.lean:59`  
**Secondary category:** 1 (Already solved externally)  
**Statement:** For a connected graph G with positive radius of its square, 2*ecc(B) <= tree(G)*rad(G^2), where B is the boundary vertex set, tree(G) the largest induced tree size and G^2 the graph square.  
**Source:** WOWII #146, DeLaVina, Written on the Wall II (Graffiti.pc)  
**Statement matches intent:** yes  
**Known status:** Fork PR #53 'Superseded: WOWII Conjecture 146 proof development' (branch solve-wowii-146) was closed with the explanation: 'to avoid duplicating the existing upstream Lean proof submission google-deepmind/formal-conjectures#4505. That upstream PR proves the exact current Conjecture 146 statement and includes a kernel-checked standalone Lean artifact, full-build verification, and an axiom audit.'  
**Difficulty:** math 6/10, Lean 3/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** PR #53 body in pr_register.json; no proof artefact for 146 exists on this repo's main branch. Structurally the statement is close to 145 (same 2*eccSet(B) <= tree * X shape), which also has a proof, making the claim plausible.  
**Flags:** needs literature check: upstream PR #4505 not inspectable from this session  
**Next action:** Fetch google-deepmind/formal-conjectures PR #4505, confirm it targets this exact statement (same hypotheses hrad and h), then port or await the upstream merge; if it does not, revive branch solve-wowii-146.

## `conjecture160` — False / refutable as stated (cat 3)

**File:** `FormalConjectures/WrittenOnTheWallII/GraphConjecture160.lean:61`  
**Secondary category:** 0 (Already solved internally)  
**Statement:** For a connected graph G, the maximum number of leaves of a spanning tree is at least max_v l(v) + max_v T(v) * c_{C4}(G), where T(v) counts triangles at v; the file codes c_{C4}(G) as the NUMBER of induced 4-cycles.  
**Source:** WOWII #160, DeLaVina, Written on the Wall II (Graffiti.pc); correction discussed in upstream issue google-deepmind/formal-conjectures#4423  
**Statement matches intent:** no — The WOWII invariant chi_{C4}(G) is a CHARACTERISTIC FUNCTION (1 if G has no 4-cycle, 0 otherwise), not the count of induced 4-cycles. The file uses `countInducedC4 G`, which turns a bounded correction term into an unbounded one and makes the statement false. Fork PR #11 ('Fix WOWII 160 C4-free characteristic', citing upstream issue #4423) proposes exactly this repair; the sibling file GraphConjecture133.lean already uses the characteristic-function convention.  
**Known status:** FALSE as formalised. Fork PR #4 'disprove(WrittenOnTheWallII): Graph Conjecture 160' (branch disprove-wowii-160) gives the counterexample K_{2,3} plus one edge inside the 3-part, edge set {02,03,04,12,13,14,24} on Fin 5.  
**Difficulty:** math 2/10, Lean 3/10 · **Compute:** small · **Confidence:** high  
**Evidence:** Verified the counterexample by hand: for that 5-vertex graph max_v l(v) = 2 (each neighbourhood has independence 2), max_v T(v) = 2 (vertices 2 and 4 lie in triangles 024 and 124), and there are exactly 2 induced 4-cycles (0-2-1-3-0 and 0-3-1-4-0; 0-2-1-4-0 has chord 24). RHS = 2 + 2*2 = 6, while Ls(G) <= n-1 = 4 for any 5-vertex graph. Under the corrected chi_{C4} reading the graph contains a 4-cycle so chi = 0 and the bound becomes the true 2 <= Ls.  
**Flags:** mis-transcribed invariant: countInducedC4 instead of the C4-free characteristic function; statement is refutable by a 5-vertex graph; the INTENDED WOWII 160 remains open  
**Next action:** Either (a) merge the PR #11 correction (replace countInducedC4 by the C4-free indicator) and keep the theorem research open, or (b) merge PR #4 and mark the current statement disproved. Recommend (a)+(b): fix the invariant AND record the counterexample to the mis-transcribed version.

## `conjecture19` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/WrittenOnTheWallII/GraphConjecture19.lean:43`  
**Statement:** For a connected graph G, the largest induced bipartite subgraph has at least floor(average eccentricity + max_v l(v)) vertices.  
**Source:** WOWII #19 (open), DeLaVina, Written on the Wall II (Graffiti.pc)  
**Statement matches intent:** yes  
**Known status:** Open; no fork PR/branch/campaign for 19. Listed as open in the directory README.  
**Difficulty:** math 7/10, Lean 8/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** Hand-tested several extremal families: for the star K_{1,n-1} the bound is exactly attained (floor(2 - 1/n + n - 1) = n = b); for C5 with m pendant leaves at one vertex it is again exactly attained (m+4 = b); for a triangle with m pendants it is exactly attained. This razor-sharp behaviour indicates a genuine, nontrivial conjecture rather than a formalisation slip. sSup over a finite range of ℝ is well defined here.  
**Next action:** Attack via b(G) >= maxL + 1 (an induced star is bipartite) and b(G) >= diam(G) + 1 (a geodesic is induced and bipartite); the difficulty is combining the two additively. First milestone: formalise both baselines.

## `conjecture194` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/WrittenOnTheWallII/GraphConjecture194.lean:41`  
**Statement:** If a connected graph G satisfies alpha(G) <= 1 + (average over v of the independence number of N(v)), then G has a Hamiltonian path.  
**Source:** WOWII #194, DeLaVina, Written on the Wall II (Graffiti.pc)  
**Statement matches intent:** yes  
**Known status:** Open; no fork PR/branch for 194.  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** small · **Confidence:** medium  
**Evidence:** The obvious candidate counterexamples are the non-traceable complete bipartite graphs K_{n,n+2}: there alpha = n+2 and 1 + l_avg = n+2 - 1/(n+1), i.e. the hypothesis fails by exactly 1/(n+1) — the conjecture is sharp on this family. Complete split graphs K_kappa + empty_{kappa+2} also fail the hypothesis comfortably. Conclusion uses Mathlib's Walk.IsHamiltonian correctly; Nontrivial α excludes the degenerate one-vertex case.  
**Next action:** Chvatal-Erdos style approach: a counterexample needs alpha >= kappa + 2 while l_avg >= alpha - 1. Small cases alpha <= 2 are already known traceable. Milestone: formalise 'connected + alpha(G) <= 2 implies traceable', then push to alpha = 3.

## `conjecture198a` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/WrittenOnTheWallII/GraphConjecture198a.lean:40`  
**Statement:** If a connected graph G satisfies b(G) <= 2 + average eccentricity, where b(G) is the largest induced bipartite subgraph size, then G has a Hamiltonian path.  
**Source:** WOWII #198a, DeLaVina, Written on the Wall II (Graffiti.pc)  
**Statement matches intent:** yes  
**Known status:** Open; no fork PR/branch for 198a.  
**Difficulty:** math 8/10, Lean 9/10 · **Compute:** small · **Confidence:** medium  
**Evidence:** Non-vacuous: K_n satisfies the hypothesis (b = 2, ecc_avg = 1) and is traceable. Sharpness check on the smallest non-traceable tree K_{1,3}: b = 4, 2 + ecc_avg = 3.75, so the hypothesis fails by 0.25; three cliques glued at a cut vertex gives b = 6 versus 2 + ecc_avg = 4. No degenerate-object or division issue (Fintype.card >= 2).  
**Next action:** Note b(G) >= alpha(G) + 1, so the hypothesis forces alpha <= 1 + ecc_avg; combine with Chvatal-Erdos-type traceability. Milestone: formalise b(G) >= alpha(G)+1 and the alpha <= 2 traceability lemma.

## `conjecture2` — Already solved internally (cat 0)

**File:** `FormalConjectures/WrittenOnTheWallII/GraphConjecture2.lean:40`  
**Statement:** For a connected graph G, the maximum number of leaves over all spanning trees satisfies Ls(G) >= 2*(l(G) - 1), where l(G) is the average over v of the independence number of N(v).  
**Source:** WOWII #2 (open), DeLaVina, Written on the Wall II (Graffiti.pc); directory README entry 2  
**Statement matches intent:** yes  
**Known status:** SOLVED inside this fork. PR #82 'Completed audit: WOWII 2 proof stack' (branch audit/c2-counting-2026-07-22; clean upstream patch preserved on submit/wowii2-solved-clean) contains a full sorry-free proof in ProofAudit/2_*.lean ending in `theorem conjecture2_complete`, with #print axioms on every lemma and a written architecture note (ProofAudit/C2_PROOF.md).  
**Difficulty:** math 5/10, Lean 3/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Read the whole PR #82 diff. The mathematics is sound and self-contained: choosing a maximum independent set I_v in each N(v) gives |N(v) ∪ N(u)| >= a(v) + deg(u) for u in I_v; double counting with c(u) = #{v : u ∈ I_v} <= deg(u) plus two Cauchy-Schwarz steps gives M >= 2S/n = 2*l(G); and a double-star seed extended to a spanning tree gives M <= Ls(G) + 2.  
**Flags:** canonical file still @[category research open] with sorry; proof lives only on a branch  
**Next action:** Port ProofAudit/2_*.lean (counting core, local choice, double count, double-star spanning-tree bridge, tree leaf identity) into the repo (or a WOWII/ module), close conjecture2 with conjecture2_complete, and verify the build and axiom audit.

## `conjecture200` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/WrittenOnTheWallII/GraphConjecture200.lean:41`  
**Statement:** If a connected graph G has largest induced tree of size exactly ceil(1 + average local independence), then G has a Hamiltonian path.  
**Source:** WOWII #200, DeLaVina, Written on the Wall II (Graffiti.pc)  
**Statement matches intent:** yes  
**Known status:** Open; no fork PR/branch for 200.  
**Difficulty:** math 7/10, Lean 9/10 · **Compute:** small · **Confidence:** medium  
**Evidence:** Non-vacuous: K_n (tree = 2 = ceil(1+1)) and K_{m,m} (tree = m+1 = ceil(1+m)) satisfy the hypothesis and are traceable. The non-traceable K_{m,m+2} has tree = m+3 but ceil(1 + l_avg) = m+2, so the hypothesis fails by exactly one — sharp again. Nontrivial α rules out degenerate cases.  
**Next action:** First formalise tree(G) >= maxL + 1 >= ceil(1 + l_avg) (induced star at the arg-max vertex); this converts the hypothesis into an extremal condition. Then classify the extremal graphs (K_n and K_{m,m} attain it) and show they are traceable.

## `conjecture217` — Plausibly solvable with moderate formal work (cat 7)

**File:** `FormalConjectures/WrittenOnTheWallII/GraphConjecture217.lean:55`  
**Secondary category:** 5 (Solved mathematically, not yet formalized)  
**Statement:** If a connected graph G on more than one vertex satisfies Ls(G) <= 4*[residue(G) = 2] + 2 (Ls = maximum number of leaves over spanning trees), then G has a Hamiltonian path.  
**Source:** WOWII #217, http://cms.uhd.edu/faculty/delavinae/research/wowII/all.html#conj217  
**Statement matches intent:** yes  
**Known status:** Fork PR #71 'C217 mathematical solution and four-certificate Lean reduction' claims: 'Mathematics: complete' (proof archived under _certificates/WOWII217/, which is NOT present on this repo's main branch) with the Lean source complete up to four finite LRAT certificates; supporting audits in PRs #68, #84, #85, #86, #90; PR #24 ran an exhaustive census of all 11,117 connected graphs on 8 vertices with no counterexample reported. All PRs are closed, nothing merged.  
**Difficulty:** math 6/10, Lean 7/10 · **Compute:** medium · **Confidence:** medium  
**Evidence:** Key observation: for a connected graph on >= 2 vertices every spanning tree has >= 2 leaves, so when residue(G) != 2 the hypothesis forces Ls(G) = 2, i.e. the leaf-maximising spanning tree is a path — the conclusion is immediate. All the content is the residue = 2 branch with Ls <= 6, which the fork reduced to a bounded-order case analysis.  
**Flags:** fork claims a complete human proof but the _certificates/WOWII217/ directory is absent from main; unverified  
**Next action:** Formalise the free half first (residue != 2 implies Ls <= 2 implies a 2-leaf spanning tree, i.e. a Hamiltonian path), then recover the C217 branch modules (Bondy-Chvatal path closure, degree <= Ls, max-degree-2 traceability, order <= 14 bound) and discharge the four finite certificates with bv_decide/LRAT.

## `conjecture291` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/WrittenOnTheWallII/GraphConjecture291.lean:108`  
**Secondary category:** 6 (Computationally solvable with certificate)  
**Statement:** For a connected graph G on more than 2 vertices, the total domination number is at most k + (number of vertices attaining the minimum triangle count), where k is the first Havel-Hakimi step at which a zero appears.  
**Source:** WOWII #291, DeLaVina, Written on the Wall II (Graffiti.pc)  
**Statement matches intent:** suspect — The file's own docstring concedes that its k ('first step at which a zero appears') is 'strictly weaker than n - residue(G)'. Since k occurs on the RIGHT-hand side of a <=, a smaller k makes the formal statement STRICTLY STRONGER than the version with n - residue. If DeLaVina's k is the number of Havel-Hakimi reduction steps (n - residue), the Lean statement is a strengthening that may well be false while the intended conjecture survives.  
**Known status:** Open; no fork PR/branch/campaign for 291. The WOWII definition of k could not be checked (cms.uhd.edu and cms.dt.uh.edu both return HTTP 403 from this environment).  
**Difficulty:** math 7/10, Lean 8/10 · **Compute:** medium · **Confidence:** low  
**Evidence:** Hand-computed two chains of triangles with a pendant vertex (where freqMinTriangles = 1, the worst case for the RHS): for the 7-vertex example k = 3, gamma_t = 4, RHS = 4 (tight); for the 10-vertex example k = 4, gamma_t = 4, RHS = 5. Tightness at freq = 1 plus the acknowledged non-standard k is exactly the pattern that produces false formalisations. Triangle-free graphs are safe since then freq = n >= gamma_t.  
**Flags:** needs literature check: WOWII's definition of k (first-zero step vs n - residue) is unresolved; source page returns 403; if the intended k is n - residue, the Lean statement is a strict strengthening and may be false  
**Next action:** First settle the reading of k against the WOWII definitions popup. Then run an exhaustive search over all connected graphs on n <= 9 or 10 vertices (nauty geng, ~250k graphs at n=9) computing gamma_t, the first-zero Havel-Hakimi step and the min-triangle frequency; a counterexample would be small if it exists, and its absence would justify formalising.

## `conjecture316` — Already solved internally (cat 0)

**File:** `FormalConjectures/WrittenOnTheWallII/GraphConjecture316.lean:38`  
**Statement:** If a connected graph G has at least as many pendant (degree-1) vertices as the average degree of its complement, then G is well totally dominated (all minimal total dominating sets have the same size).  
**Source:** WOWII #316, DeLaVina, Written on the Wall II (Graffiti.pc)  
**Statement matches intent:** yes  
**Known status:** SOLVED inside this fork. Merged PR #46 added WOWII/WotW316*.lean (8 modules) with `theorem conjecture316_solved` whose statement and hypotheses are character-for-character the canonical ones, and FormalConjectures/WrittenOnTheWallII/GraphConjecture316ForkProof.lean closes the canonical statement with `exact conjecture316_solved G hG h`. No `sorry` anywhere in WOWII/ (grep verified). Campaign wowii-316: proof_state complete-proof-in-repo.  
**Difficulty:** math 5/10, Lean 1/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Read WOWII/WotW316Final.lean header and the ForkProof wrapper: the proof is a structural case analysis (pendant vertices adjacent or not, core vertices, clique partitions) with ordinary tactics, no native_decide. Note the statement deliberately omits [Nontrivial α]; for a one-vertex type the hypothesis holds and the conclusion is vacuously true (no total dominating set exists), so nothing degenerate slips through.  
**Flags:** canonical file still @[category research open] with sorry despite the in-repo proof  
**Next action:** Replace the `sorry` in GraphConjecture316.lean by `exact conjecture316_solved G hG h`, flip the category to research solved, and verify the build plus `#print axioms` (no lake build available in this container).

## `conjecture40` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/WrittenOnTheWallII/GraphConjecture40.lean:40`  
**Statement:** For a nontrivial connected graph G, the largest induced forest satisfies f(G) >= ceil((p(G) + b(G) + 1)/2), where p is the path cover number and b the largest induced bipartite subgraph size.  
**Source:** WOWII #40 (open), DeLaVina, Written on the Wall II (Graffiti.pc); directory README entry 9  
**Statement matches intent:** yes  
**Known status:** Open; no fork PR/branch/campaign for 40. Listed as open in the directory README.  
**Difficulty:** math 7/10, Lean 8/10 · **Compute:** none · **Confidence:** medium  
**Evidence:** Hand-checked the complete bipartite family, which is extremal throughout: K_{m,m} (p=1, b=2m, f=m+1, bound m+1), K_{m,m+1} (bound m+2 = f), K_{m,m+2} (p=2, bound m+3 = f), K_{2,6} (p=4, b=8, bound 7 = f), and K_n (bound 2 = f). Equality on an infinite family shows the constant and the +1 are exactly right, i.e. this is a genuine sharp conjecture, not a transcription slip.  
**Next action:** Baseline: f(G) >= ceil(b(G)/2) (the larger side of an induced bipartite subgraph is independent, hence an induced forest); the content is the extra (p+1)/2. First milestone: that baseline plus f(G) >= alpha(G).

## `conjecture59` — False / refutable as stated (cat 3)

**File:** `FormalConjectures/WrittenOnTheWallII/GraphConjecture59.lean:43`  
**Secondary category:** 0 (Already solved internally)  
**Statement:** For a connected graph G, the largest induced forest satisfies f(G) >= ceil(sqrt(residue(G) * b(G))), where residue is the Havel-Hakimi residue and b the largest induced bipartite subgraph size.  
**Source:** WOWII #59, DeLaVina, Written on the Wall II (Graffiti.pc); residue: Favaron, Maheo, Sacle (1991)  
**Statement matches intent:** yes  
**Known status:** FALSE. The fork built an explicit 18-vertex counterexample: a connected graph with residue = 10, b >= 17 and every induced forest of size <= 13, while ceil(sqrt(10*17)) = ceil(13.038) = 14. See fork PRs #78 (branch agent/solve-wowii-59), #161, #227 (audit/wowii59-clean-final) and the still-open #233 (audit/wowii59-clean-current); campaign wowii-59 lists workflows wowii59-clean-audit.yml / wowii59-source-repair.yml and the branches still exist. The finite parts (residue value, 25-cycle covering certificate bounding every induced forest) are discharged by bv_decide/LRAT with a plain-decide fallback.  
**Difficulty:** math 4/10, Lean 6/10 · **Compute:** medium · **Confidence:** medium  
**Evidence:** Arithmetic of the claimed counterexample checks out: 10*17 = 170, sqrt(170) = 13.038…, ceil = 14 > 13 = f(G). The described structure (ten-vertex bipartite core + universal hub + seven leaves) plausibly yields b >= 17 by deleting the hub and f <= 13 via a cycle-cover certificate. The campaign register warns that parts of the final source are generated by CI workflows that patch and push the .lean file, so the exact artefact must be rebuilt before trusting it.  
**Flags:** statement is refuted by an explicit finite counterexample built in this fork; counterexample relies on bv_decide/LRAT certificates produced by CI-patched sources — rebuild and re-audit; needs literature check: cannot confirm the transcription of WOWII 59 (source page 403), so the original conjecture may differ  
**Next action:** Recover branch audit/wowii59-clean-final (or agent/solve-wowii-59), rebuild the one-file disproof against current main, and rewrite the canonical theorem as an explicit refutation (`¬ ∀ ...` with the Fin 18 witness) marked research solved.

## `conjecture61` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/WrittenOnTheWallII/GraphConjecture61.lean:42`  
**Statement:** For a connected graph G, the largest induced forest satisfies f(G) >= residue(G) + ceil(diam(G)/3).  
**Source:** WOWII #61, DeLaVina, Written on the Wall II (Graffiti.pc); residue: Favaron, Maheo, Sacle (1991)  
**Statement matches intent:** yes  
**Known status:** Open; no fork PR/branch for 61 (note the sibling conjecture 59, which uses the same invariants, was refuted in this fork — 61 should be stress-tested against that 18-vertex graph and similar constructions).  
**Difficulty:** math 7/10, Lean 8/10 · **Compute:** small · **Confidence:** medium  
**Evidence:** Checked K_n (residue 1, diam 1, f = 2, bound 2 — tight), K_{m,m} (residue 2 for m=3, diam 2, f = 4), P_5 (residue 2, diam 4, bound 4 <= 5), and the WOWII 59 counterexample shape (universal hub gives diam <= 2, so residue 10 + 1 = 11 <= 13 = f). residue <= alpha <= f is a theorem, so only the diameter term is at issue.  
**Flags:** sibling conjecture 59 with the same invariants is false — worth a counterexample search before investing in a proof  
**Next action:** Start from the known residue(G) <= alpha(G) <= f(G) (Favaron-Maheo-Sacle) and try to gain ceil(diam/3) by adding roughly every third vertex of a diametral geodesic to a maximum independent set. Also run a small exhaustive search (n <= 10) as a sanity check given that WOWII 59 turned out false.
