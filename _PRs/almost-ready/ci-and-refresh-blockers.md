# CI, current-main, and integration blockers

These lanes have substantial proof or submission work already completed, but a red, pending, skipped, or stale exact integration gate prevents promotion.

| Problem | Strongest current evidence | Blocking gate |
|---|---|---|
| OEIS A100434 corrected auxiliary identities | Immutable proof `62e6f3a6e10df56aae85528037eb57488a4b2855`; latest-main audit PR #292, head `5d2f8abc0b3da2dc7d1f49275503fa906db80267`; copyright run `30291121096` green | Full Lean build `30291119466` is still pending/in progress. Do not promote until it completes green. |
| Kagey Problem 137 / OEIS A226247 | Clean one-file package PR #226, head `f83ba3e852486b8ccff07e23ce026a4eca0c5370`; substantial proof already linked | Full Lean build `30031457504` failed. Diagnose, refresh onto current GDM main, and obtain a green exact package audit. |
| OEIS A343881 | Complete immutable disproof and one-file package exist; package head `5d2ac75ac51c197581341c68f95b2d54f4ddb4a0` | Targeted package audit `30021831086` and full build `30021831074` failed. |
| First five A317940 values | PR #286; immutable head `7f19c892cc0e328736c106d270444e4bfb0e1191`; focused ProofPlaygrond run `30214340477` green | Repository-wide integration build is red; the exact one-file patch must pass before upstream promotion. |
| Dimension-2 and dimension-3 SIC-POVM benchmarks | PR #266; exact four-theorem focused audit green with only standard axioms | Repository-wide `lake --wfail build` failed on the branch; isolate or repair the integration failure and compress the 31-commit development into a clean patch. |
| Classical Euler brick witness | PR #288; exact witness `(44,117,240)` with diagonals `125,244,267` | Focused Euler-brick audit `30214627367` failed. Fix the theorem package before treating the arithmetic proof as green. |
| Litt most-unfair fair-binary-word theorem | Final audit PR #239, head `09eb3486c2254b5359963767d4d95133bdd4d132` | Targeted audit `30036767922` failed; identify the exact failing proof/import and rerun the no-hole/no-trust gate. |
| WOWII 59 counterexample | Clean current-main audit PR #233, head `f4477d6544a58f24b7ec21a7b856d85c621a4257` | Targeted audit `30035875072` failed. The explicit graph/cycle-cover proof cannot be promoted until the exact theorem compiles cleanly. |
| WOWII 65 solved-status resubmission | Prior GDM PR #4441 closed unmerged; one-file external proof was reported sorry-free | Rebuild the exact current theorem on latest GDM main, preserve review context, and produce a fresh green one-file submission. |

Promotion requires an exact green head. A green proof artifact does not override a red or pending submission build.