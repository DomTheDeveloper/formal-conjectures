# Statement defects and potentially permanent holds

These lanes have green regression, counterexample, or audit work, but the literal Lean declaration does not faithfully encode the intended mathematical problem. They may remain in `almost-ready/` indefinitely until maintainers accept a corrected statement.

| Problem | Verified finding | Required resolution |
|---|---|---|
| Lander–Parkin–Selfridge | PR #267 gives a green regression witness: unrestricted naturals permit `k=1`, `n=0`, `m=0`, making both sums empty and forcing the false conclusion `1 ≤ 0` | Add explicit positivity hypotheses for `k`, `n`, and `m`, preserve the intended quantifier structure, and build the corrected canonical declaration green. |
| Erdős 545 | PR #255 proves the literal isolated-vertex counterexample family `singleEdgeRamseyNumber r = r + 2` with a green exact audit | Decide whether the intended problem excludes isolated vertices or constrains graph order; submit either the literal disproof or the corrected statement with clear scope. |
| Erdős 332 | PR #268 proves the unrestricted existential “sufficient condition” is vacuous by choosing the predicate constantly false | Constrain what counts as an acceptable condition before any meaningful solution can be stated. |
| Erdős 633 | PR #269 proves the unrestricted set-valued answer is tautological by choosing the comprehension of the defining property | Replace the answer type or require an explicit geometric classification. |
| Dedekind formula | PRs #263 and #265 show the literal function-valued answer can be chosen as `M`, while the intended Kisielewicz formula still depends on an admitted theorem | Specify the intended closed formula and remove the admitted dependency before claiming a mathematical solution. |
| Moving-sofa literal uniqueness | PRs #264 and #265 prove that volume cannot characterize one exact set among all measurable sets, because singleton changes preserve volume; the exact Gerver wrapper also inherits `sorryAx` | Restrict to admissible moving sofas, choose an appropriate equivalence such as equality modulo null sets, and eliminate the admitted Gerver-constant dependency. |

A green proof of a malformed literal statement is evidence for statement repair, not automatic permission to mark the intended conjecture solved.