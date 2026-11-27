# Verification of the distinct-zero corollary

@domthedeveloper formalized `riemannZeta.distinct_prop_lt` with the witness `17/20`. The proof compares distinct critical-line zeros with all distinct zeros on the same interval `(T, 2T]`. Mathlib proves the containing closed rectangle has finitely many zeta zeros, so taking the cardinality of the subset gives the required inequality. The bridge imports only Mathlib.

The quantitative input is Kristian Muri Knausgård’s dyadic lower bound of 85.4225%. Its published certificate includes Alpöge’s RH theorem. RH enters through that certificate. The bridge takes the quantitative estimate as its sole analytic input. [Certificate and upstream kernel reports](https://github.com/josusanmartin/riemann/releases/tag/compact-rh-854225-v1)

## Check the application and the target

Run `python3 Proofs/DistinctZeros/check_interface.py`. The script fetches digest-pinned sources and checks the exact application in `Result.lean` with the published quantitative theorem as an explicit parameter. It reads that parameter’s type from the published Lean source. It constructs the reference independently from DeepMind’s statement and counting definitions.

| Check on November 27, 2026 | Result | AXLE request |
| --- | --- | --- |
| Lean 4.33.1 | Passed | `2a7b2709-d9d5-4acf-acda-ebc6a0b0e64c` |
| Lean 4.35.0 | Passed | `aed2b5bb-616d-4f35-b4ec-e11cc1c9838c` |
| Lean 4.35.0, reference deliberately changed to include height zero | Rejected for a target-type mismatch | `f3a1e7d3-c45b-422a-a529-8435b73cc7ad` |

Both positive runs reported zero errors, warnings, or failed declarations. The axiom list for the implication contained `propext`, `Classical.choice`, and `Quot.sound`.

## Replay the closed theorem

With the pinned Linux Lean 4.35.0 toolchain and the upstream compact verification runtime installed, run `bash Proofs/DistinctZeros/verify.sh /path/to/runtime`. The script compiles the archived estimate, links the compact RH implementation, and exports the closed theorem. The upstream comparator matches that theorem against an independently generated reference and audits its transitive axioms. Lean’s default kernel checks the resulting export.

The upstream published replay accepted the numerical input in both Lean and nanoda. We reproduced the SHA-256 digests of its uncompressed exports. A fresh local replay exceeded the available memory. The complete closed theorem has not received a fresh end-to-end kernel verdict in this checkout.

| Upstream export | SHA-256 |
| --- | --- |
| Reference | `ab79018d7607a8eb7fbb3091f3b8591c4965cdcf284516b053c48072f8fc79f0` |
| Solution | `e4c9866f587abbeb141cc631136b3ae88a2bbf53f83aa3eb02752d1d19ab8c95` |
