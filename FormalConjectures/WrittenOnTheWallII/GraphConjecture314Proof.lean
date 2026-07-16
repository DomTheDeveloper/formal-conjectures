import WOWII.ZZGraphConjecture314Final

/-!
Verification harness for the CRL proof of Written on the Wall II Graph
Conjecture 314. The example checks the exact upstream theorem type, while the
axiom printout exposes every transitive axiom used by the proof term.
-/

namespace WrittenOnTheWallII.GraphConjecture314

open Classical SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α]

example [Nontrivial α]
    (G : SimpleGraph α) [DecidableRel G.Adj]
    (hG : G.Connected)
    (hTriFree : ∀ a b c : α,
      G.Adj a b → G.Adj b c → G.Adj c a → False)
    (hPath : largestInducedPathSize G ≤ 4) :
    IsWellTotallyDominated G := by
  exact conjecture314_proved G hG hTriFree hPath

#print axioms conjecture314_proved

end WrittenOnTheWallII.GraphConjecture314
