# W(3,20) exact certificate work

This directory contains deterministic tooling for the exact upper-bound proof.
The unrestricted DIMACS instance has 389 variables and 41,426 clauses.  The
cube decomposition fixes variables 193 through 198 and exhausts all 64 possible
assignments.  Each leaf must be refuted by a checked LRAT certificate; the 64
assignments are a complete partition of the original assignment space.
