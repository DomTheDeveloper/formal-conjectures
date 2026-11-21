# Dropping unused imports from the Riemann hypothesis proof

The original source at commit `40e56bab026552e089d7afcfeff08d2defb9c005` contains 17,374,215 lines in 175,187 Lean modules. Two import headers bring in large collections of results about other subjects. The first contains a zeta reflection argument and the second assembles the hypotheses for an automorphy argument. The explicit dependencies for their proof terms and the published inventory for the five final theorems make it possible to drop 10,723 original files. Consolidating the thirteen affected modules into a single source for `Main` then removes twelve more files. All 164,451 external project modules in the import-only package are the original, unchanged Git sources.

| Source variant | Lean lines | Lean modules | Lines removed |
| --- | ---: | ---: | ---: |
| Published | 17,374,215 | 175,187 | |
| Two import cuts and one consolidated root | 16,588,178 | 164,452 | 786,037 |
| Same cuts plus earlier proof and import rewrites | 16,323,888 | 164,452 | 1,050,327 |

The independently generated archives retain exactly the source dependencies reachable from `Main`. The source inventory retains every project constant in the published five-theorem proof, including the module used for the one-parameter homomorphism result. The combined variant also applies the earlier readable rewrites outside the thirteen affected modules. Its compilation status is separate from the native check of the import-only variant.

The [packaging and verification workflow](../../../.github/workflows/rh-fused-source.yml) computes and checks both source digests. Its native job selects the original compiled objects for the 164,451 unchanged modules and compiles the consolidated source. The root checks all five theorem types and prints their axiom inventories. A successful native run writes `native.json`, the source digest, the theorem names, and the compiler's version.

To reproduce the archives locally, install Python 3.11 or later, Git and Zstandard, then run the following from this directory. Use a clone containing the pinned original revision and the [v0.2 constant inventory](https://github.com/james-shore/rh-proof-dependencies/releases/tag/v0.2).

```bash
python3 build.py /path/to/original constants.csv.gz two --archives
python3 fuse.py /path/to/original two fused --archives
```

The complete, published, stock-Lean-replayed proof of ordinary RH is [available separately as 17 native modules](https://github.com/DomTheDeveloper/formal-conjectures/releases/tag/rh-ordinary-native-3eaf53b19177).
