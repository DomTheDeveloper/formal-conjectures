"""Emit a Lean certificate for a contiguous strip of Sun's cube inequalities.

Python supplies candidate masks and counts. Lean must establish each mask equals
its independently proved sieve and must recompute its population count.
The generated file can be checked directly with lake env lean.
"""
from math import isqrt
from pathlib import Path

FIRST = 2
LAST = 200
BLOCK = 65_536
LIMIT = (LAST + 1) ** 3
BOUND = isqrt(LIMIT)
DIR = Path("A038098/Certificate")
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
    DIR.mkdir(parents=True, exist_ok=True)
    modules = []
    prime = primes_up_to(LIMIT)
    ps = [p for p in range(2, BOUND + 1) if prime[p]]
    out = ["module", "public import A038098.Trial", "public import Mathlib.Data.Rat.Cast.Order",
           "", "@[expose] public section", "namespace Sun.PackedCases", "open Sun.CubeSieve",
           "set_option maxRecDepth 100000", "set_option maxHeartbeats 0", ""]
    # A literal divisor list avoids recomputing primality at each bit operation.
    out += [f"def divisors : List ℕ := {ps}",
            f"theorem list_ok : primeList {BOUND} = divisors := by",
            f"  rw [primeList_eq_trial (q := {isqrt(BOUND)}) (by decide)]",
            "  decide +kernel", ""]
    def save(name, lines):
        path = DIR / (name + ".lean")
        path.write_text("\n".join(lines + ["end Sun.PackedCases", ""]), encoding="utf-8")
        modules.append(path)
    def next_file():
        return ["module", f"public import A038098.Certificate.{modules[-1].stem}", "@[expose] public section",
                "namespace Sun.PackedCases", "open Sun.CubeSieve",
                "set_option maxRecDepth 100000", "set_option maxHeartbeats 0", ""]
    save("Divisors", out)
    out = next_file()
    a = BOUND
    count = len(ps)
    out.extend([f"theorem pi_{a} : Nat.primeCounting {a} = {count} := by",
                "  rw [primeCounting_eq_length,list_ok]", "  decide +kernel", ""])
    save("Base", out)
    out = next_file()
    block_number = 0
    for n in range(FIRST, LAST+2):
        cube = n**3
        if cube <= BOUND:
            if cube != BOUND:
                out += [f"theorem pi_{cube} : Nat.primeCounting {cube} = {sum(prime[:cube+1])} := by",
                        f"  rw [primeCounting_prefix (b := {BOUND}) (by decide),list_ok]",
                        "  decide +kernel", ""]
                save(f"Small{n:03}",out)
                out = next_file()
            continue
        while a < cube:
            b = min(a + BLOCK, cube)
            width = b-a
            words = (width+15)//16
            block = prime[a+1:b+1]
            mask = composite_bits(block)
            total = count + block.count(1)
            assert mask.bit_count() + total-count == width
            out += [f"private theorem mask_{b} : compositeMask ({a}+1) {width} divisors % (1<<<{width}) = {hex(mask)} :=",
                    "  by decide +kernel",
                    f"private theorem count_{b} : {width}-addLanes 16 {words} {hex(mask)} 16+{count}={total} :=",
                    "  by decide +kernel",
                    f"theorem pi_{b} : Nat.primeCounting {b} = {total} :=",
                    f"  extend_certificate (a := {a}) (v := {count}) (width := {width}) (stop := {b})",
                    f"    (b := {BOUND}) (r := 16) (t := {words}) (total := {total}) (by decide) pi_{a} list_ok",
                    f"    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) mask_{b} count_{b}", ""]
            count, a = total, b
            block_number += 1
            if block_number % 2 == 0 or b == cube:
                save(f"Block{block_number:03}", out)
                out = next_file()
    out += ["def Cube (n : ℕ) : Prop := (((n+1)^3).primeCounting : ℚ) / (((n+1)^3:ℕ):ℚ) <",
            "  ((n^3).primeCounting : ℚ) / ((n^3:ℕ):ℚ)", ""]
    out += ["private theorem cube_of_counts {n x y p q : ℕ} (hx : n^3 = x) (hy : (n+1)^3 = y)",
            "    (hpx : x.primeCounting = p) (hpy : y.primeCounting = q)",
            "    (h : (q:ℚ)/(y:ℚ) < (p:ℚ)/(x:ℚ)) : Cube n := by",
            "  unfold Cube", "  rw [hx,hy,hpx,hpy]", "  exact h", ""]
    for n in range(FIRST, LAST+1):
        x,y = n**3,(n+1)**3
        out += [f"private theorem cube_{n} : Cube {n} :=",
                f"  cube_of_counts (n := {n}) (x := {x}) (y := {y}) (by decide) (by decide) pi_{x} pi_{y} (by decide +kernel)", ""]
    out += [f"theorem checked_cubes (n : ℕ) (lo : {FIRST} ≤ n) (hi : n ≤ {LAST}) : Cube n := by"]
    def split(lo, hi, indent):
        if lo == hi:
            out.append(f"{indent}have he : n = {lo} := by omega")
            out.append(f"{indent}exact he.symm ▸ cube_{lo}")
            return
        mid = (lo + hi) // 2
        out.append(f"{indent}by_cases cut_{mid} : n ≤ {mid}")
        out.append(f"{indent}·")
        split(lo, mid, indent + "  ")
        out.append(f"{indent}·")
        split(mid + 1, hi, indent + "  ")
    split(FIRST, LAST, "  ")
    out += ["", "end Sun.PackedCases", "#print axioms Sun.PackedCases.checked_cubes", ""]
    SOURCE.write_text("\n".join(out), encoding="utf-8")
    (DIR / "modules.txt").write_text("\n".join(str(p) for p in modules) + "\n", encoding="utf-8")

if __name__ == "__main__":
    emit()
