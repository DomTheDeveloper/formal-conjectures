# Read the consolidated source

[Main.lean](Main.lean) combines the code from thirteen final modules into 1,237 lines. Its imports supply the arithmetic results used by the proof. The complete import-only source contains 16,588,178 lines including those imports. In that package the other 164,451 Lean files have their original contents.

The smallest packaged variant also uses the earlier source rewrites. It contains 16,323,888 Lean lines across 164,452 files. The [source receipt](source-receipt.json) identifies both complete trees and their archive checksums. The [GitHub build](https://github.com/DomTheDeveloper/formal-conjectures/actions/runs/44960247690) publishes the source archives and runs stock Lean on the import-only package. The full source build of the variant with the earlier rewrites remains outstanding.

The [verified seventeen-module proof](https://github.com/DomTheDeveloper/formal-conjectures/releases/tag/rh-ordinary-native-3eaf53b19177) contains the full arithmetic support for ordinary RH. Lean 4.33.1 replayed all 1,175,724 declaration records.

The [isolated reflection proofs](../analytic-reflection) show where the analytic argument uses arithmetic. The [source generator](../two-headers) provides the original Git revision, build instructions and dependency checks.
