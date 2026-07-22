# Color-restriction audit

This branch extends the complete `N = 6`, `D = 3` certificate proof with a coefficient-independent color-restriction theorem and the `D = 5` / all-`D ≥ 3` integer and trinary consequences.

The focused pull-request workflow downloads and hash-checks the 47 LRAT certificates, replays `verify.sh`, compiles `QuantumGraphColorRestriction.lean` with the certificate directory on `LEAN_PATH`, prints the terminal theorem axioms, and rejects `sorryAx`.
