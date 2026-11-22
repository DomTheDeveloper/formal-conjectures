# Reduced source for the five Riemann hypothesis statements

Reconstruct **15,478,802 Lean lines in 163,641 project modules** from Levent Alpöge’s pinned release. This removes 1,895,413 lines (10.91%) and 11,546 modules. The counts include every project-specific import and use the same external Lean and Mathlib dependencies on both sides.

| Source | Project modules | Project lines | Verification |
| --- | ---: | ---: | --- |
| Author’s release | 175,187 | 17,374,215 | Published source and kernel checks |
| [400-line entry](CompactRH.lean) with its original dependencies | 164,428 | 16,595,834 | All five statements compiled and replayed in stock Lean |
| Source reconstructed here | 163,641 | 15,478,802 | Every source byte authenticated, every native header checked, and 83 shortened modules with individual compiler checks. A full clean build remains outstanding. |

The entry uses the arithmetic hypotheses to establish nonvanishing for Dirichlet L-functions to the right of the critical line. Specializing to the trivial character gives ordinary RH. The 400-line file reconstructs enough of the arithmetic argument to drop 10,760 of the original files in all. A [nine-line entry](short/OrdinaryRH.lean) uses an existing theorem to do more of the assembly. Its original imports bring its total to 17,373,786 lines. The [seventeen-line entry](short/Riemann.lean) gives all five statements. [Original source](https://github.com/leanprover-community/riemann-hypothesis/tree/40e56bab026552e089d7afcfeff08d2defb9c005) · [400-line native replay](https://github.com/DomTheDeveloper/ProofPlaygrond/actions/runs/44931804542/job/136929834005)

## Reconstruct and audit

Clone this repository and the pinned upstream project. From this directory, run the following with Python 3.9 or later and Git. The output directory must be new.

```sh
git clone https://github.com/leanprover-community/riemann-hypothesis original
python3 materialize.py original reduced
```

Omitting `reduced` reads and verifies every source file in memory. The original checkout may be on another branch because the materializer opens the pinned Git tree directly. The compressed changes are a distribution format. Reconstructing them produces 900,710,896 bytes of ordinary Lean source with ordered SHA-256 fingerprint `f24045c06732e9797163e99d6221ee9b93c130ad4aa8e463b7195a713e19dbc1`.

The standard Lean 4.33.1 commands to build that source and replay its entry are

```sh
cd reduced
lake exe mathlib/cache get
lake build CompactRH
lake env leanchecker -v CompactRH
```

## Verification coverage

Stock Lean’s native import parser read all 163,641 reconstructed files. Independently comparing the parsed imports and original Git objects found 75,376 byte-identical modules. For 9,306 of them, every project file reachable through imports is also byte-identical. Those 9,306 modules contain 859,175 lines. The checkout pins match for the compiler and external packages. [Counts and module fingerprints](verification.json)

The 51 modules named in the source volume completed individual native compilation or reused a compilation of the identical source. Another 30 shortened modules in this tree exactly match separate GitHub builds, including their pinned Mathlib-only imports. All 30 were compared against their originals. Two further shortened files exactly match individually compiled sources recorded in the earlier native verification. Those two used Lean’s default compiler options. The three selections are disjoint. [Earlier native source checks](../measurements.json) The 400-line entry was replayed against its original dependency objects. The smallest source tree still needs all its changed dependencies built together. [Native comparison of the 33-file batch containing the additional 30](https://github.com/DomTheDeveloper/formal-conjectures/actions/runs/44962979280/job/137028098093)

On GNU/Linux, reproduce the import and transitive-source comparison from this directory. Use the project's pinned Lean executable on PATH.

```sh
set -o pipefail
find reduced/src -type f -name '*.lean' -printf '%P\n' | LC_ALL=C sort |
  lean --run CheckHeaders.lean reduced/src | python3 check_reuse.py original reduced
```

The complete ordinary-RH kernel proof separately passed stock Lean in 17 native modules containing 1,175,724 declaration records. The reduced five-statement kernel proof passed an independent ConLeche check against the official challenge. [Ordinary-RH proof objects and verdicts](https://github.com/DomTheDeveloper/formal-conjectures/releases/tag/rh-ordinary-native-3eaf53b19177) · [Five-statement comparison and released verdict](https://github.com/DomTheDeveloper/formal-conjectures/releases/tag/rh-kernel-c06133e527f9)

## Two individual reductions

The longest original file has a separate verified edition of 16,112 lines, down from 17,981. Removing repeated setup preserved all 2,087 compiled declaration records, including the original theorem proofs. This individual rewrite was checked against its 147 original project dependencies. The full source package above uses a different, 17,628-line revision of this file. [16,112-line source](../individual-files/IsAdmissibleSplittingCharPairMulTwist.lean) · [Exact native comparison](https://github.com/DomTheDeveloper/formal-conjectures/actions/runs/44961908533/job/137022362423)

The [free-module quotient proof](short/FreeModuleQuotient.lean) shrank from 2,516 lines to 23 (99.09%). Stock Lean compiled and replayed it. Comparison of the exported objects confirmed the original mathematical proposition. The replacement names two originally anonymous hypotheses. The proof changes scalars to the quotient ring and then uses the coordinate isomorphism to reduce each coordinate modulo the larger ideal.

The 400-line arithmetic assembly adapts David Sanftenberg’s Apache-2.0 work. [License](LICENSE-CompactRH)
