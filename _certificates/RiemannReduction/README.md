# Simplifying Alpöge’s Lean proof of the Riemann hypothesis

This directory rebuilds a shorter Lean source tree and generates 17 kernel proof articles from Levent Alpöge’s published release. It also contains a short Lean deduction of ordinary RH from an explicit bound on a weighted prime sum.

| Quantity | Published release | Reduced, all five conclusions | Reduced, ordinary RH alone |
|---|---:|---:|---:|
| Lean source lines | 17,374,215 | 17,107,305 | — |
| Lean source files | 175,187 | 175,187 | — |
| Kernel declaration records | 1,468,418 | 1,172,294 | 1,172,274 |
| Distinct expression records in the export | 1,065,214,335 | 1,048,298,917 | 1,048,296,913 |
| Uncompressed kernel export, bytes | 61,570,595,788 | 60,520,686,934 | 60,520,564,304 |

The source patch preserves theorem statements and removes 251,383 redundant imports. It shortens 2,133 proofs using an earlier theorem with the same exported proposition and universe parameters. Reapplying the patch reproduces the measured tree digest across every source file. The independent kernel reduction works directly on proof terms. Its five public roots are ordinary RH, the zeta zero statement, and the three Dirichlet L-function statements in the original challenge. The original export contains exactly the three standard axiom declarations `propext`, `Classical.choice` and `Quot.sound`.

## The mathematical idea

Let `Λ` be the von Mangoldt function. For a prime power `n = p^k`, its contribution to the smoothed count is `log(p) · (y/n − 1)` when `n ≤ y`. After subtracting the main term, the resulting error is

$$
G(y)=\sum_{n\le y}\Lambda(n)(y/n-1)-y\log y+(1+\gamma)y.
$$

Imagine a zeta zero with real part 0.60. Its contribution creates a pole of the Mellin transform of this error. The localized Landau theorem then forces an excursion above any fixed multiple of $y^{0.55}$ somewhere in every sufficiently late interval $[Y,Y^{3/2}]$. The arithmetic construction produces arbitrarily late intervals where the error stays below one such multiple throughout. Choosing an exponent between ½ and the real part of any proposed zero excludes every zero to the right. The functional equation supplies the other half of RH.

The 49-line [PrimeWindows.lean](PrimeWindows.lean) formalizes the implication from these window bounds to Mathlib’s ordinary RH. Lean 4.33.1 checks it with the standard three axioms. Its explicit hypothesis is the arithmetic estimate.

The hard estimate comes from divisibility. A nonzero algebraic integer divisible by many prime ideals must have a large norm. The proof compares this lower bound with an upper bound from a chain of theta lifts. The choice of chain length balances errors that grow with the length and errors that shrink with it. Ordinary zeta uses the trivial character in the final prime sum. The arithmetic work that delivers its bound still uses auxiliary characters and fields. [Alpöge’s note](https://alpo.ge/remark.pdf) · [Annotated mathematical guide](https://github.com/nasqret/riemann-rev)

## Download the 17 source volumes

The [17 downloadable archives](https://github.com/DomTheDeveloper/formal-conjectures/releases/tag/rh-source-ae2ba3a2e34e) contain the complete shortened source organized by topic, including the build configuration. Extract all 17 into one directory with `for f in *.tar.zst; do tar --zstd -xf "$f"; done`. Together they contain 175,187 Lean modules. The materializer decompressed every archived file and compared it with the shortened project. The [volume manifest](source-volumes.json) lists each topic, line count and SHA-256.

## Materialize the shorter Lean source

Run these commands from this directory. The patch applier needs Python 3 and Git. It reads the pinned Git objects, includes the original project configuration and writes all 175,187 Lean files to a new directory. Omitting the output directory checks the full tree fingerprint in memory.

```bash
git clone https://github.com/leanprover-community/riemann-hypothesis archive
python3 apply_source.py archive reduced-source
cd reduced-source
lake build Main
```

The 919,424-byte patch encodes edits against the original Git revision. The proof source and its dependency remain necessary to reconstruct the project. The full source tree digest, input pins, line counts and hashes of both unpartitioned kernel exports are in [measurements.json](measurements.json).

## Generate the proof and run Lean

Install a C++20 compiler, libzstd, the zstd CLI, Python 3 and Lean 4.36.0. From this directory, generate the complete proof. The ordinary-RH variant uses `ordinary` in place of `all` in the second command and `ordinary-share` in the third.

```bash
curl -fL https://math.mit.edu/~drew/grh/solution.ndjson.zst -o original.zst
bash reduce.sh original.zst build all share
bash emit.sh original.zst build all-share | leanchecker --from-export /dev/stdin
```

To write the 17 compressed kernel articles, run the loop below. Change the last argument from `emit` to `check` to stream each article directly through Lean. The GitHub workflow checks the parts across four runners. Each runner reuses one download and index.

```bash
for i in $(seq 1 17); do
  bash parts.sh original.zst build "$i" 17 emit
done
```

## What each check establishes

- **Whole kernel export.** The reducer traces types, values, universe parameters, projections, inductives and recursor rules. When two theorems share a kernel type and universe parameters, it can reuse the earlier proof. The reference run uses stock `leanchecker`. A second run uses the independent Lean implementation ConLeche in verified mode and compares all five statements with the published challenge. [Whole-proof run](https://github.com/DomTheDeveloper/formal-conjectures/actions/runs/44917310333)
- **Seventeen proof articles.** Every retained declaration belongs to one index interval. Its owner must check its entire body. A later interval may use an earlier theorem through its checked statement. Definitions and inductive declarations keep their bodies. The splitter also retains proof bodies needed by definitions and theorem types. If the kernel identifies another declaration needing reduction, the splitter restores its actual dependency closure and rechecks the part. The coverage auditor checks every boundary, checks that every temporary assumption is an earlier theorem, and checks that all 1,172,294 retained records have an owner. A green coverage job means that all 17 native kernel runs passed. [Corrected 17-part run](https://github.com/DomTheDeveloper/formal-conjectures/actions/runs/44924258184). In the [first run](https://github.com/DomTheDeveloper/formal-conjectures/actions/runs/44919932054), part 1 passed and parts 2 through 5 failed at `Rat.instEncodable`. Lean accepted that rational-number definition in isolation and in the corrected part 2 prefix once its computational proof bodies were restored
- **Native check of the endpoint.** A local stock Lean run accepted a smaller interval containing all five public conclusions. It checked 1,010 owned records and used 13,842 earlier theorem headers. That check alone certifies the final interval. Its counts and verdict are recorded in [measurements.json](measurements.json).
- **Every source theorem replacement.** A separate stock Lean run checked all 2,133 proposed uses of earlier theorems at the original propositions and universe parameters. It built a native proof for each substitution and supplied 26,019 supporting theorem statements as temporary headers. Reproduce this check with `bash check_source_reuse.sh original.zst build` after running `reduce.sh`. This checks the mathematical substitutions. Rebuilding the source also exercises tactic elaboration and the import graph.
- **Every deleted import.** Lean 4.33.1 parsed every original and revised module header. A separate reachability check confirmed that each of the 251,383 removed imports was already available through an earlier retained public import in the revised graph. This covers all 175,187 source modules and 83,202 changed headers. The check preserves the order and visibility of the retained imports.
- **Lean source.** The source patch and kernel reducer are separate transformations. Source reproduction verifies the bytes of the patch output. Stock Lean compiled three rewritten modules. The largest measured sample went from 532 lines to 381. The full import and arithmetic proof-term checks run separately from these source compiler checks. Compiling a final theorem against existing imports does not substitute for checking its dependencies.
- **Baseline.** The original proof has its own published compilation and independent kernel verification record. [Original verification files](https://math.mit.edu/~drew/grh/) · [Pinned Lean source](https://github.com/leanprover-community/riemann-hypothesis/tree/40e56bab026552e089d7afcfeff08d2defb9c005)

The small regression test exercises theorem sharing, cross-part dependencies and binder names. It also checks that the native kernel rejects a deliberately mistyped proof on both a regular file and a pipe.

```bash
python3 test_reduce.py
```


## Additional certificate compression

The ordinary-RH export can share another 2,283,655 identical expression records after dropping unused name-table entries and local binder labels. The resulting stream has 1,046,013,258 expression records and 59,524,488,006 bytes before compression. Its SHA-256 is `fc7e5faebdc3affadcb02f9505bf9f96a256dd55d1a042ad134be278acecec14`. The full replays linked above use the larger export. To reproduce this additional candidate after selecting ordinary RH, run these commands.

```bash
python3 dictionary.py build/index build/ordinary-share
bash emit.sh original.zst build ordinary-share | build/slice intern 22 > ordinary-compact.ndjson
```
