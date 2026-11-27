"""Emit a Lean certificate for a contiguous strip of Sun's cube inequalities.

Python supplies candidate masks and counts. Lean must establish each mask equals
its independently proved sieve and must recompute its population count.
The generated file can be checked directly with lake env lean.
"""
from math import isqrt
from pathlib import Path

FIRST = 141
LAST = 200
BLOCK = 65_536
LIMIT = (LAST + 1) ** 3
BOUND = isqrt(LIMIT)
SOURCE = Path("A038098/PackedCases.lean")

def primes_up_to(limit):
    primes = bytearray(b"\x01") * (limit + 1)
    primes[:2] = b"\x00\x00"
    for p in range(2, isqrt(limit) + 1):
        if primes[p]:
            size = (limit - p*p) // p + 1
            primes[p*p::p] = b"\x00" * size
    return primes

def composite_bits(block):
    packed = bytearray((len(block) + 7) // 8)
    for index, prime in enumerate(block):
        if not prime:
            packed[index >> 3] |= 1 << (index & 7)
    return int.from_bytes(packed, "little")

def emit():
    prime = primes_up_to(LIMIT)
    ps = [p for p in range(2, BOUND + 1) if prime[p]]
    out = ["module", "public import A038098.Wide", "public import Mathlib.Data.Rat.Cast.Order",
           "", "public section", "namespace Sun.PackedCases", "open Sun.CubeSieve",
           "set_option maxRecDepth 100000", "set_option maxHeartbeats 0", ""]
    # A literal divisor list avoids recomputing primality at each bit operation.
    out += [f"private def divisors : List ℕ := {ps}",
            f"private theorem list_ok : primeList {BOUND} = divisors := by decide +kernel", ""]
    a = BOUND
    count = len(ps)
    out.extend([f"private theorem pi_{a} : Nat.primeCounting {a} = {count} := by decide +kernel", ""])
    for n in range(FIRST, LAST+2):
        cube = n**3
        while a < cube:
            b = min(a + BLOCK, cube)
            width = b-a
            words = (width+15)//16
            block = prime[a+1:b+1]
            mask = composite_bits(block)
            total = count + block.count(1)
            assert mask.bit_count() + total-count == width
            out += [f"private theorem pi_{b} : Nat.primeCounting {b} = {total} := by",
                    f"  apply primeCounting_extend_packed (a := {a}) (v := {count}) (width := {width})",
                    f"    (b := {BOUND}) (r := 16) (t := {words}) (total := {total}) pi_{a}",
                    "    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)",
                    "  unfold packedBlockCount",
                    "  rw [list_ok]",
                    f"  have hm : (compositeMask ({a}+1) {width} divisors) % (1 <<< {width}) = {hex(mask)} := by decide +kernel",
                    "  rw [hm]",
                    "  decide +kernel", ""]
            count, a = total, b
    out += ["def Cube (n : ℕ) : Prop := (((n+1)^3).primeCounting : ℚ) / (((n+1)^3:ℕ):ℚ) <",
            "  ((n^3).primeCounting : ℚ) / ((n^3:ℕ):ℚ)", ""]
    for n in range(FIRST, LAST+1):
        x,y = n**3,(n+1)**3
        out += [f"private theorem cube_{n} : Cube {n} := by",
                f"  change (Nat.primeCounting {y} : ℚ) / {y} < (Nat.primeCounting {x} : ℚ) / {x}",
                f"  rw [pi_{x},pi_{y}]", "  decide +kernel", ""]
    ns = range(FIRST,LAST+1)
    out += [f"theorem checked_cubes (n : ℕ) (lo : {FIRST} ≤ n) (hi : n ≤ {LAST}) : Cube n := by",
            "  have h : " + " ∨ ".join(f"n = {n}" for n in ns) + " := by omega",
            "  rcases h with (" + "|".join("rfl" for _ in ns) + ")"]
    out += [f"  · exact cube_{n}" for n in ns]
    out += ["", "end Sun.PackedCases", "#print axioms Sun.PackedCases.checked_cubes", ""]
    SOURCE.write_text("\n".join(out), encoding="utf-8")

if __name__ == "__main__":
    emit()
