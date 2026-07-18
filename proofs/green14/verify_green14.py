#!/usr/bin/env python3
"""Dependency-free checker for Green14 W(3,t), t=20,...,39."""
from green14_cert_data import CERTIFICATES


def find_ap(bits: str, value: str, length: int):
    n = len(bits)
    for start in range(n):
        max_step = (n - 1 - start) // (length - 1)
        for step in range(1, max_step + 1):
            if all(bits[start + i * step] == value for i in range(length)):
                return start + 1, step
    return None


def main() -> None:
    for t, (relation, bound, zero_positions) in sorted(CERTIFICATES.items()):
        length = bound - 1 if relation == "≥" else bound
        zero_set = set(zero_positions)
        bits = "".join("0" if i in zero_set else "1" for i in range(1, length + 1))
        zero_ap = find_ap(bits, "0", 3)
        one_ap = find_ap(bits, "1", t)
        assert zero_ap is None, (t, "color-0 3-AP", zero_ap)
        assert one_ap is None, (t, f"color-1 {t}-AP", one_ap)
        print(f"PASS t={t}: W(3,{t}) {relation} {bound}; length={length}; zeros={len(zero_set)}")
    print(f"All {len(CERTIFICATES)} certificates verified.")


if __name__ == "__main__":
    main()
