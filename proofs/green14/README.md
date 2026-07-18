# Green14 `W(3,t)` certificate family

This directory preserves expanded, independently verified certificates for the 20 open Formal Conjectures statements `Green14.W_3_20_lower` through `Green14.W_3_39_lower`.

For each `t`, `green14_cert_data.py` records the 1-based positions colored `0`; every other position is colored `1`. `verify_green14.py` exhaustively checks that the `0` class contains no 3-term arithmetic progression and the `1` class contains no `t`-term arithmetic progression.

Run:

```bash
python3 proofs/green14/verify_green14.py
```

A coloring of `[1,N]` with these properties proves `W(3,t) > N`. Therefore a word of length `B-1` proves `W(3,t) ≥ B`, while a word of length `B` proves `W(3,t) > B`.

Source: Ahmed, Kullmann, and Snevily, *On the van der Waerden numbers w(2; 3, t)*, Appendix A. The run-length encodings were reconstructed into exact finite certificates and then checked independently.

This directory establishes the finite combinatorial certificates. A subsequent Lean patch must connect the verified finite predicate to `Set.IsAPOfLength` and the `sInf` definition of `Green14.W` before claiming kernel-checked completion of the original Lean theorems.
