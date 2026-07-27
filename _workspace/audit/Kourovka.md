# Audit detail — Kourovka

2 research-open declarations. Fields per problem: plain statement, source, category, match, status, action, difficulties, compute, confidence, evidence, flags.

## `kourovka.«19.25»` — Vacuously true / accidentally weakened (cat 4)

**File:** `FormalConjectures/Kourovka/19_25.lean:37`  
**Secondary category:** 3 (False / refutable as stated)  
**Statement:** If two finite groups of the SAME ORDER have equal values of sum_{g} phi(order g) and one of them is simple, must the other be simple?  
**Source:** Kourovka Notebook Problem 19.25 (B. Curtin, G. R. Pourgholi), arXiv:1401.0300  
**Statement matches intent:** no — The hypothesis '|G| = |H|' from the source ('two finite groups of the same order') is MISSING from the Lean statement. Only the equality of the totient sums is assumed.  
**Known status:** Intended Kourovka question is open. The Lean RHS as written is FALSE: G = Multiplicative (ZMod 5) (simple, order 5) has sum_{g} phi(ord g) = 1 + 4*phi(5) = 1 + 16 = 17, and H = (ZMod 3) x (ZMod 3) (order 9, NOT simple) has 1 + 8*phi(3) = 1 + 16 = 17. So one may take answer := False and refute the RHS, closing the formal problem without touching the real one. No PR/campaign entry for Kourovka.  
**Difficulty:** math 7/10, Lean 4/10 · **Compute:** none · **Confidence:** high  
**Evidence:** Sum identity: sum_{g in G} phi(ord g) = sum over cyclic subgroups C of phi(|C|)^2. Z/5 gives 1 + 4^2 = 17; (Z/3)^2 has four order-3 cyclic subgroups giving 1 + 4*2^2 = 17. Orders 5 vs 9 differ, so the missing same-order hypothesis is exactly what is exploited.  
**Flags:** missing hypothesis |G| = |H| (major semantic mismatch: answer-encoding becomes decidable by an 8-element counterexample); closing the Lean statement as written would NOT resolve Kourovka 19.25  
**Next action:** Repair first: add the hypothesis Nat.card G = Nat.card H (and, for good measure, [Fintype H] nonemptiness is already implied). Only then triage the repaired statement (expected cat 8).

## `kourovka.«20.76»` — Deep but approachable research problem (cat 8)

**File:** `FormalConjectures/Kourovka/20_76.lean:30`  
**Statement:** If every abelian normal subgroup of a finite p-group G has order at most p^k, must every abelian subgroup of G have order at most p^(2k)?  
**Source:** Kourovka Notebook Problem 20.76 (L. Pyber), arXiv:1401.0300  
**Statement matches intent:** yes  
**Known status:** Open. Related known results (Alperin, Thompson, A. Mann) bound |G| by a function of k, so only the sharpness of the exponent 2k is at issue. No formal proof; nothing in pr_register.json / campaign_register.json; no duplicate in repo.  
**Difficulty:** math 7/10, Lean 8/10 · **Compute:** small · **Confidence:** medium  
**Evidence:** Statement is well-formed: IsPGroup p G + Finite G + h on normal abelian subgroups; conclusion over all abelian subgroups. answer(sorry) is a genuine yes/no with no shortcut visible; small-order search (p^n, n <= 7) could look for counterexamples via GAP-style enumeration.  
**Flags:** needs literature check on whether Pyber's question has been answered since 2018  
**Next action:** Leave open; a realistic first milestone is the k = 1 case (all abelian normal subgroups of order <= p implies every abelian subgroup has order <= p^2), which is classical and formalizable.
