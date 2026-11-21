# Simplifying Alpöge’s Lean proof of the Riemann hypothesis

The [17 readable Lean chapters](chapters) derive ordinary RH from Levent Alpöge’s published arithmetic. They total 474 lines, including two optional mathematical explanations. The proof path to the final theorem occupies 427 lines across 15 of the chapters. For the full original project and its five headline conclusions, the reductions are as follows.

| Quantity | Published | Challenge-preserving reduction |
|---|---:|---:|
| Lean source lines | 17,374,215 | 17,086,632 |
| Lean source files | 175,187 | 175,187 |
| Kernel declaration records | 1,468,418 | 1,175,732 |
| Distinct expression records in the export | 1,065,214,335 | 1,048,304,687 |
| Uncompressed kernel export, bytes | 61,570,595,788 | 60,521,386,737 |

The first source pass preserves theorem statements and removes 251,383 redundant imports. It shortens 2,133 proofs using an earlier theorem with the same exported proposition and universe parameters. Reapplying the patch reproduces the measured tree digest across every source file. The independent kernel reduction works directly on proof terms. Its five public roots are ordinary RH, the zeta zero statement, and the three Dirichlet L-function statements in the original challenge. The original export contains exactly the three standard axiom declarations `propext`, `Classical.choice` and `Quot.sound`.

The first complete independent replay checked all 1,172,294 solution declarations and then rejected the official challenge comparison at `riemannHypothesis`. The comparator found a difference in the library declarations its type reads. The revised reduction preserves all 53,721 shared declarations from the official challenge, including the original names and bodies of 3,425 theorems that the first pass shared. ConLeche in verified mode accepted the revised proof and matched all five original statements against the published challenge. [First comparison](https://github.com/DomTheDeveloper/formal-conjectures/actions/runs/44917310333) · [Accepted five-theorem comparison](https://github.com/DomTheDeveloper/formal-conjectures/actions/runs/44933951202/job/136936415029)

## The ordinary-RH deduction in 17 readable files

Chapter 17 constructs both arithmetic inputs and concludes Mathlib’s `RiemannHypothesis` with no hypotheses. Its source imports reach 175,174 original modules. Its compiled proof reaches 1,175,685 original supporting declarations and omits the author’s five headline proofs. The source audit matched all 38 new declarations used in the proof to their complete exported bodies. The largest arithmetic input supplies the geometric data for the theta lifts and reaches 757,173 declarations. [Source and intuition](chapters) · [Source audit](https://github.com/DomTheDeveloper/formal-conjectures/actions/runs/44941516939/job/136959535553) · [Native endpoint verification](https://github.com/DomTheDeveloper/formal-conjectures/actions/runs/44940612477/job/136956744233)

## Native Lean proof modules

The [native module workflow](https://github.com/DomTheDeveloper/formal-conjectures/actions/workflows/rh-native-modules.yml) partitions the authentic reduced proof into 17 modules. Each declaration has one owner. The graph pass moves prerequisites into an earlier module when necessary and checks that the union covers the entire selected proof. Every module after the first imports its predecessor. All proofs retain their bodies. The writer reads back every serialized `.olean` file and compares its constants and imports with the parsed export. The unmodified Lean 4.33.1 `leanchecker` then replays each module independently. The workflow publishes 17 native objects only after all owners pass.

To check the released objects locally, put each decompressed `PartN.olean` under `RHBatches/` and run the following from its parent directory with Lean 4.33.1 on the path.

```bash
export LEAN_PATH="$PWD"
for part in {0..16}; do leanchecker "RHBatches.Part$part" || exit 1; done
```

## Readable individual proofs

Thirty-two algebra and analysis modules shrank from 49,705 to 29,032 lines. Lean rechecked their original and rewritten proof terms in disjoint namespaces. Its kernel compared 344 public declaration types, their universe parameters, and every named argument and its visibility. It also checked definitional equality of all 186 public definition bodies. Both versions use Mathlib at the pinned revision.

The [26-line module quotient proof](refinements/FreeModuleQuotient.lean) replaces a 2,516-line file. If the coordinates of a module are free modulo an ideal $I$, reducing them modulo a larger ideal $K$ gives coordinates on its quotient. Tensoring with $S/K$ performs that reduction. Tensor product commutes with finite products, and $I$ already acts as zero on each new coordinate. The [17-line zeta reflection proof](refinements/RhOfRight.lean) replaces a 62-line argument. The completed zeta function has the same value at $s$ and $1-s$, so a nontrivial zero strictly left of the critical line would give a zero strictly right of it. Both replacements use only Mathlib.

Run `python3 refine_source.py archive refined` to reconstruct the 17,086,632-line project. Omit `refined` to verify its fingerprint in memory. To repeat the compiled comparison, run `lake exe cache get` in the pinned source checkout and then `lake env python3 /path/to/refinements/verify.py "$PWD" /path/to/verification-output`. [Machine-readable results](refinements/results.json) · [GitHub rebuild](https://github.com/DomTheDeveloper/formal-conjectures/actions/workflows/rh-readable-source.yml)

## The mathematical idea

Let `Λ` be the von Mangoldt function. For a prime power `n = p^k`, its contribution to the smoothed count is `log(p) · (y/n − 1)` when `n ≤ y`. After subtracting the main term, the resulting error is

$$
G(y)=\sum_{n\le y}\Lambda(n)(y/n-1)-y\log y+(1+\gamma)y.
$$

Imagine a zeta zero with real part 0.60. Its contribution creates a pole of the Mellin transform of this error. The localized Landau theorem then forces an excursion above any fixed multiple of $y^{0.55}$ somewhere in every sufficiently late interval $[Y,Y^{3/2}]$. The arithmetic construction produces arbitrarily late intervals where the error stays below one such multiple throughout. Choosing an exponent between ½ and the real part of any proposed zero excludes every zero to the right. The functional equation supplies the other half of RH.

The [36-line analytic proof](PrimeWindows.lean) deduces Mathlib’s ordinary RH from these window bounds. The complete project import closure of the implication was rebuilt from the shortened source. Lean 4.33.1 reported the three standard axioms. The full export contained 59,527 declaration records. Stock Lean 4.36.0 and ConLeche in verified mode accepted its shortened 55,294-record proof, with all dependencies and no temporary theorem assumptions. [Download the checked certificate](https://github.com/DomTheDeveloper/formal-conjectures/releases/download/rh-source-e96c40c44137/prime-window-proof.ndjson.zst) · [Kernel verdicts](https://github.com/DomTheDeveloper/formal-conjectures/releases/download/rh-source-e96c40c44137/prime-window-kernels.txt) · [GitHub rebuild](https://github.com/DomTheDeveloper/formal-conjectures/actions/runs/44938455264)

The hard estimate comes from divisibility. A nonzero algebraic integer divisible by many prime ideals must have a large norm. The proof compares this lower bound with an upper bound from a chain of theta lifts. For a prime-counting scale $X$ and a chain of $m$ lifts, the competing error terms have sizes $X/m$ and $m$, up to small power losses. Choosing $m$ near $\sqrt X$ makes both errors square-root sized. Ordinary zeta uses the trivial character in the final prime sum. The arithmetic work that delivers its bound still uses auxiliary characters and fields. [Alpöge’s note](https://alpo.ge/remark.pdf) · [Annotated mathematical guide](https://github.com/nasqret/riemann-rev)

## Download the 17 source volumes

The [further simplified source release](https://github.com/DomTheDeveloper/formal-conjectures/releases/tag/rh-source-e96c40c44137) contains the 17,086,632-line project. Each of the 17 archives was decoded and its files were compared byte for byte with the refactored project.

The first pass is available in [17 downloadable archives](https://github.com/DomTheDeveloper/formal-conjectures/releases/tag/rh-source-ae2ba3a2e34e). They contain 17,107,305 source lines and the complete build configuration. Extract all 17 into one directory with `for f in *.tar.zst; do tar --zstd -xf "$f"; done`. Together they contain 175,187 Lean modules. The materializer decompressed every archived file and compared it with the shortened project. The [volume manifest](source-volumes.json) lists each topic, line count and SHA-256.

## Materialize the shorter Lean source

Run these commands from this directory. The patch applier needs Python 3 and Git. It reads the pinned Git objects, includes the original project configuration and writes all 175,187 Lean files to a new directory. Omitting the output directory checks the full tree fingerprint in memory.

```bash
git clone https://github.com/leanprover-community/riemann-hypothesis archive
python3 apply_source.py archive reduced-source
cd reduced-source
lake build Main
```

The 919,424-byte patch encodes edits against the original Git revision. The proof source and its dependency remain necessary to reconstruct the project. The first-pass source tree digest, input pins, line counts and hashes of both unpartitioned kernel exports are in [measurements.json](measurements.json).

## Generate the proof and run Lean

Install a C++20 compiler, libzstd, the zstd CLI, Python 3 and the independently implemented checker ConLeche. The commands below reproduce the challenge-preserving five-theorem proof. Decompressing the proof to disk requires about 61 GB in addition to the input and search index. The GitHub workflow uses a compressed filesystem for the proof.

```bash
curl -fL https://math.mit.edu/~drew/grh/solution.ndjson.zst -o original.zst
curl -fL https://math.mit.edu/~drew/grh/challenge.ndjson.zst -o challenge.zst
bash reduce.sh original.zst build all share
bash guard_solution.sh challenge.zst build protected
bash emit.sh original.zst protected all-share > protected.ndjson
zstd -dcq --long=31 challenge.zst > challenge.ndjson
con-leche --verified --compare challenge.ndjson protected.ndjson
```

The independent checker revision is `5ea446d5c79d23ef1f954215d094db2162f1ab6f`, built with Lean 4.36.0. The native modules use the author's Lean 4.33.1. The SHA-256 of the complete protected export is `c06133e527f9962f8c0c759e8dcc2007ae0d86535e165fa7453a0956624fa94d`.

To write the 17 compressed kernel articles, run the loop below. Change the last argument from `emit` to `check` to stream each article directly through Lean. The GitHub workflow checks the parts across four runners. Each runner reuses one download and index.

```bash
for i in $(seq 1 17); do
  bash parts.sh original.zst build "$i" 17 emit
done
```

## What each check establishes

- **Whole kernel export.** The reducer traces types, values, projections, inductives and recursor rules. The final protected reduction passed ConLeche in verified mode against all five official challenge statements. An earlier monolithic stock `leanchecker` run lost its hosted runner. The native module build splits the stock replay across separate runners. [Accepted complete comparison](https://github.com/DomTheDeveloper/formal-conjectures/actions/runs/44933951202/job/136936415029)
- **Seventeen proof articles.** Every retained declaration belongs to one index interval. Its owner must check its entire body. A later interval may use an earlier theorem through its checked statement. Definitions and inductive declarations keep their bodies. The splitter also retains proof bodies needed by definitions and theorem types. If the kernel identifies another declaration needing reduction, the splitter restores its actual dependency closure and rechecks the part. The coverage auditor checks every boundary, checks that every temporary assumption is an earlier theorem, and checks that all 1,172,294 retained records have an owner. A green coverage job means that all 17 native kernel runs passed. [Corrected 17-part run](https://github.com/DomTheDeveloper/formal-conjectures/actions/runs/44924258184). In the [first run](https://github.com/DomTheDeveloper/formal-conjectures/actions/runs/44919932054), part 1 passed and parts 2 through 5 failed at `Rat.instEncodable`. Lean accepted that rational-number definition in isolation and in the corrected part 2 prefix once its computational proof bodies were restored
- **Native check of the endpoint.** A local stock Lean run accepted a smaller interval containing all five public conclusions. It checked 1,010 owned records and used 13,842 earlier theorem headers. That check alone certifies the final interval. Its counts and verdict are recorded in [measurements.json](measurements.json).
- **Every source theorem replacement.** A separate stock Lean run checked all 2,133 proposed uses of earlier theorems at the original propositions and universe parameters. It built a native proof for each substitution and supplied 26,019 supporting theorem statements as temporary headers. Reproduce this check with `bash check_source_reuse.sh original.zst build` after running `reduce.sh`. This checks the mathematical substitutions. Rebuilding the source also exercises tactic elaboration and the import graph.
- **Every deleted import.** Lean 4.33.1 parsed every original and revised module header. A separate reachability check confirmed that each of the 251,383 removed imports was already available through an earlier retained public import in the revised graph. This covers all 175,187 source modules and 83,202 changed headers. The check preserves the order and visibility of the retained imports.
- **Lean source.** The source patch and kernel reducer are separate transformations. Source reproduction verifies the bytes of the patch output. Stock Lean compiled three rewritten modules. The largest measured sample went from 532 lines to 381. The 32 further mathematical rewrites have their own compiler and public declaration comparisons. The complete 175,187-module rewritten source tree still awaits a clean source build.
- **Baseline.** The original proof has its own published compilation and independent kernel verification record. [Original verification files](https://math.mit.edu/~drew/grh/) · [Pinned Lean source](https://github.com/leanprover-community/riemann-hypothesis/tree/40e56bab026552e089d7afcfeff08d2defb9c005)

The small regression test exercises theorem sharing, cross-part dependencies and binder names. It also checks that the native kernel rejects a deliberately mistyped proof on both a regular file and a pipe.

```bash
python3 test_reduce.py
```


## Replay the mathematical explanation

With the original project's two analytic imports compiled, `check_prime_windows.sh` recompiles [PrimeWindows.lean](PrimeWindows.lean), exports its declarations and dependencies, and runs both kernels. Pass the project, a working directory, and the paths to lean4export, Lean 4.36.0's leanchecker and ConLeche. The exporter revision used here is `15f6055e299ad5b89345e533cc2192f4cc00f659`.

```bash
bash check_prime_windows.sh archive window-check /path/to/lean4export /path/to/leanchecker /path/to/con-leche
```

## Additional certificate compression

The ordinary-RH export can share another 2,283,655 identical expression records after dropping unused name-table entries and local binder labels. The resulting stream has 1,046,013,258 expression records and 59,524,488,006 bytes before compression. Its SHA-256 is `fc7e5faebdc3affadcb02f9505bf9f96a256dd55d1a042ad134be278acecec14`. The full replays linked above use the larger export. To reproduce this additional candidate after selecting ordinary RH, run these commands.

```bash
python3 dictionary.py build/index build/ordinary-share
bash emit.sh original.zst build ordinary-share | build/slice intern 22 > ordinary-compact.ndjson
```
