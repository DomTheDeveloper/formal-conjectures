# Ordinary RH in 17 Lean chapters

The 474 lines in [RH17](RH17) give a zeta-specific deduction from the published arithmetic theory. The last theorem has type `RiemannHypothesis` with no hypotheses. It builds its arithmetic inputs from the Galois, cohomology, and theta-lift results in the archive. Its source imports reach 175,174 original project modules with 17,373,725 source lines, in addition to Mathlib. The 17 chapters include two optional explanations. The dependency path ending at chapter 17 contains 15 chapters and 427 lines.

## Where to read the argument

[Chapter 1](RH17/S01_PrimeSum.lean) writes out a weighted count of prime powers. A prime power $p^k\le y$ contributes $\log(p)(y/p^k-1)$. Subtract the expected main term to get the error $G(y)$.

[Chapter 10](RH17/S10_ForcedExcursion.lean) explains what would happen if zeta had a zero with real part 0.60. For every fixed $C$, every sufficiently late interval $[Y,Y^{3/2}]$ would contain some $y$ with $G(y)>C y^{0.55}$. The zero produces a pole in a transform of the prime sum. In logarithmic coordinates the weights used to detect it can be concentrated inside each such interval.

[Chapter 15](RH17/S15_ArithmeticWindows.lean) supplies intervals on which the opposite inequality holds everywhere. At the arithmetic stage the exponent is $1/2+(d+l+7)\varepsilon$. The losses $d,l$ are fixed first. For any $\theta>1/2$, choose $\varepsilon$ small enough to fit below $\theta$, then choose a window beyond any prescribed starting point. This argument even takes $C=1$. The two conclusions contradict one another on that window. [Chapter 9](RH17/S09_Reflection.lean) uses the functional equation to cover zeros on the left as well.

[Chapter 11](RH17/S11_ChainLength.lean) verifies the numerical reason for a chain of about $\sqrt X$ theta lifts. Divisibility at finite places gives a lower bound on the norm of a nonzero algebraic integer. The upper estimate along the chain contains terms of sizes $X/m$ and $m$. Their sum is minimized at $m=\sqrt X$. The large geometric construction delivers an arithmetic object for which this comparison applies. [Alpöge's explanation](https://alpo.ge/remark.pdf)

## Compile the source

From a checkout of the published project at `40e56bab026552e089d7afcfeff08d2defb9c005`, install its pinned Lean 4.33.1 and fetch its Mathlib cache. The following command builds the required project imports, compiles all 17 chapters and prints the axiom audit of the final theorem.

```bash
bash /path/to/chapters/build_chapters.sh "$PWD" /path/to/output-oleans
```

## Reconstruct the independent check

The GitHub source job recompiles all 17 chapters and compares every new definition, theorem type and proof body with the input to the independent kernel. Its temporary arithmetic interfaces are discarded at export. The separate whole-proof job restores and checks all supporting declarations.

The proof-term file `chapters.ndjson.zst` supplies the 38 new declaration names used by the final proof. The linker checks that every other constant is present in the authenticated original and rejects a new axiom or a name collision. It traces the full proofs of those prerequisites, removes the original headline results and checks the remaining graph for the prohibited final names and their exact exported proposition IDs. The official ordinary-RH challenge is obtained by deleting the four other challenge statements. Its underlying Mathlib definitions and its statement of RH retain their original bytes.

The commands below run from the parent `RiemannReduction` directory. They use the two original exports from [Andrew Sutherland's verification archive](https://math.mit.edu/~drew/grh/) and the pinned checker documented in the parent README.

```bash
bash reduce.sh original.zst build all share
bash chapters/prepare.sh challenge.zst build chapters-build
{ bash emit.sh original.zst chapters-build ordinary-chapters && cat chapters-build/extension.ndjson; } > ordinary-chapters.ndjson
python3 chapters/ordinary_challenge.py challenge.zst ordinary-challenge.ndjson
con-leche --verified --compare ordinary-challenge.ndjson ordinary-chapters.ndjson
```

To regenerate the proof-term supplement from the compiled chapters, build the module `Export` from lean4export revision `15f6055e299ad5b89345e533cc2192f4cc00f659`. In the published project's `lake env`, add the chapter object directory and the exporter's `.lake/build/lib/lean` directory to `LEAN_PATH`. Then run the following with Lean 4.33.1. The exporter emits precisely the additional declarations referenced by the new root.

```bash
lean --run /path/to/chapters/ThinExport.lean /path/to/build/index/names.tsv \
  RH17.S17_RiemannHypothesis RH17.riemannHypothesisFromPublishedArithmetic > chapters.ndjson
```

[Full kernel comparison on GitHub](https://github.com/DomTheDeveloper/formal-conjectures/actions/workflows/rh-proof-chapters.yml)
