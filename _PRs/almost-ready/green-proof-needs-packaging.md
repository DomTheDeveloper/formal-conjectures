# Green proofs needing canonical packaging

Every lane below has a green focused proof and clean axiom footprint, but is not `ready/` because the canonical declaration, proof-length packaging, latest integration build, or upstream PR text is incomplete.

| Problem | Strongest verified state | Final blocker |
|---|---|---|
| Unitary-perfect examples | PR #273; proof `e2b0f213c1afd4451bdc4f5be9ee0265e2c16870`; run `30211997936`; proves `87360` and `146361946186458562560000` | Replace the two canonical admitted bodies with a focused wrapper or immutable `formal_proof` package, then run full current-main CI. |
| Minimum overlap `M(2)=1` | PR #274; proof `b7ed2e79b8626936752a4e789ea1de300b74cec2`; run `30212008331` | Restore the canonical `Erdos36.M_two` declaration in one clean file and rerun integration. |
| Two-color van der Waerden base values | PR #275; proof `69ba9d07479dfaca6eee121ea91a0182849a4297`; run `30212019209`; proves `W 1 = 1` and `W 2 = 3` | Replace the two canonical admitted declarations and prepare the upstream package. |
| Weak Giuga prime-divisor criterion | PR #283; head `f2ad674f64ac1980c74cac4404871ea7fff035b8`; run `30213363291` | Restore the canonical body and clean inherited deprecation/unused-simp warnings. |
| Erdős 100 nine-point Piepmeyer witness | PR #284; head `ac6d0f804114149b70673549d2d8494eeab9195c`; run `30213263093` | Restore the canonical declaration with the exact explicit witness and package the substantial proof. |
| Erdős 1084 dimension-one value | PR #285; head `8bd9c48b60533cfbeb50c60d28e893a6c7ef3a9d`; run `30213292071`; proves `f 1 n = n - 1` | Restore the canonical declaration and replay on current main. |
| OEIS A080170 gcd/prime-power equivalence | PR #287; head `ca28a389683ebfa9154c55019aaa0b1fd2fdd21a`; run `30213920030` | Package the complete historical proof under the repository proof-length policy and replace the admitted catalog body. |
| Erdős 12 prime-square good set | PR #289; head `b43b12d674de0c879c64b82176a64a231f1a73e3`; run `30214058880` | Restore the canonical theorem and modernize one deprecated `ZMod` lemma without changing semantics. |
| Erdős 828 totient classification | PR #290; head `59604dd67b7a3c7d1eb7f328dac2dbe70cfbf10e`; run `30214195665` | Restore the canonical theorem `φ n ∣ n ↔ ...`, then run the full integration gate. |
| Wolstenholme's theorem | PR #291; head `72f11e9b23fae95b206b2d35c1d9a7abdd014f45`; focused audit `30214501194` green | Convert the historical replay into a clean canonical restoration patch and run the repository-wide build. |

All listed focused theorem audits report only the standard axioms `[propext, Classical.choice, Quot.sound]` and no `sorryAx` or compiler-trust dependency.