#!/usr/bin/env python3
"""Generate explicit sorry-free Lean proof terms from a compact Chomp strategy certificate.

The C++ producer and this generator are untrusted. Every generated theorem contains the complete
normal-play proof term: each opponent move is case-split explicitly, the selected reply is proved
to be a legal Chomp move, and the reply points to an already-defined losing theorem of lower area.
Lean's kernel is the final checker.
"""

from __future__ import annotations

import argparse
import shutil
import struct
from pathlib import Path

Position = tuple[int, ...]


def read_u64s(path: Path, magic: bytes, record_width: int) -> list[tuple[int, ...]]:
    data = path.read_bytes()
    if len(data) < 16 or data[:8] != magic:
        raise ValueError(f"bad certificate header: {path}")
    count = struct.unpack_from("<Q", data, 8)[0]
    expected = 16 + count * 8 * record_width
    if len(data) != expected:
        raise ValueError(f"bad certificate length: {path}: {len(data)} != {expected}")
    records: list[tuple[int, ...]] = []
    offset = 16
    for _ in range(count):
        records.append(struct.unpack_from("<" + "Q" * record_width, data, offset))
        offset += 8 * record_width
    return records


def unpack_position(value: int) -> Position:
    return tuple((value >> (6 * index)) & 63 for index in range(10))


def pack_position(position: Position) -> int:
    if len(position) != 10:
        raise ValueError(position)
    value = 0
    previous = 63
    for index, row in enumerate(position):
        if not 0 <= row <= 42 or row > previous:
            raise ValueError(position)
        value |= row << (6 * index)
        previous = row
    return value


def bite(position: Position, row: int, target: int) -> Position:
    return position[:row] + tuple(min(value, target) for value in position[row:])


def moves(position: Position):
    for row in range(10):
        lower = 1 if row == 0 else 0
        for target in range(lower, position[row]):
            yield row, target, bite(position, row, target)


def find_move(parent: Position, child: Position) -> tuple[int, int]:
    for row, target, result in moves(parent):
        if result == child:
            return row, target
    raise ValueError(f"not a legal move: {parent} -> {child}")


def lean_list(position: Position) -> str:
    return "[" + ", ".join(str(value) for value in position) + "]"


def theorem_name(index: int, width: int) -> str:
    return f"lose_{index:0{width}d}"


def move_term(row: int, target: int) -> list[str]:
    return [
        "          exact KernelCertificate.Outcome.winning",
        "            (by",
        f"              refine ⟨{row}, {target}, by decide, by decide, by simp, ?_⟩",
        "              rfl)",
    ]


def generate_theorem(
    index: int,
    position: Position,
    response: dict[int, int],
    carrier_index: dict[int, int],
    name_width: int,
) -> str:
    lines = [
        "/-- Generated losing proof from the explicit closed response strategy. -/",
        "@[category test, AMS 5]",
        f"theorem {theorem_name(index, name_width)} :",
        f"    KernelCertificate.Outcome Move {lean_list(position)} false := by",
        "  apply KernelCertificate.Outcome.losing",
        "  intro q hq",
        "  rcases hq with ⟨row, target, hrow, htarget, hpoison, rfl⟩",
        "  interval_cases row",
    ]

    for row in range(10):
        bound = position[row]
        lines.append("  ·")
        if bound == 0:
            lines.append("    omega")
            continue
        lines.append("    simp at htarget")
        if row == 0:
            lines.append("    have htarget_pos : 0 < target := hpoison rfl")
        lines.append("    interval_cases target")
        lower = 1 if row == 0 else 0
        for target in range(lower, bound):
            child = bite(position, row, target)
            child_key = pack_position(child)
            if child_key not in response:
                raise ValueError(
                    f"missing response for theorem {index}, move ({row},{target}), child {child}"
                )
            reply_key = response[child_key]
            if reply_key not in carrier_index:
                raise ValueError(f"reply not in carrier: {reply_key}")
            reply_index = carrier_index[reply_key]
            if reply_index >= index:
                raise ValueError(
                    f"nondecreasing dependency: theorem {index} -> {reply_index}"
                )
            reply = unpack_position(reply_key)
            if sum(reply) >= sum(position):
                raise ValueError(f"area did not decrease: {position} -> {reply}")
            reply_row, reply_target = find_move(child, reply)
            lines.append("    ·")
            lines.extend(move_term(reply_row, reply_target))
            lines.append(f"            {theorem_name(reply_index, name_width)}")

    return "\n".join(lines) + "\n"


def write_chunk(
    output_dir: Path,
    chunk_index: int,
    first_index: int,
    last_index: int,
    theorems: list[str],
) -> None:
    module = f"Chunk{chunk_index:03d}"
    path = output_dir / f"{module}.lean"
    if chunk_index == 0:
        import_line = "import FormalConjectures.OEIS.A147983.Game"
    else:
        import_line = (
            "import FormalConjectures.OEIS.A147983.Generated."
            f"Chunk{chunk_index - 1:03d}"
        )
    path.write_text(
        f"{import_line}\n\n"
        f"/-! Generated explicit Chomp losing proofs {first_index} through {last_index}. -/\n\n"
        "set_option maxHeartbeats 0\n"
        "set_option maxRecDepth 100000\n\n"
        "namespace OeisA147983.Generated\n\n"
        + "\n".join(theorems)
        + "\nend OeisA147983.Generated\n"
    )


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("carrier", type=Path)
    parser.add_argument("responses", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("--chunk-size", type=int, default=100)
    args = parser.parse_args()

    carrier_records = read_u64s(args.carrier, b"CHCARR02", 1)
    response_records = read_u64s(args.responses, b"CHRESP02", 2)
    carrier_keys = [record[0] for record in carrier_records]
    if len(carrier_keys) != len(set(carrier_keys)):
        raise ValueError("duplicate carrier position")
    positions = [unpack_position(key) for key in carrier_keys]
    expected_order = sorted(carrier_keys, key=lambda key: (sum(unpack_position(key)), key))
    if carrier_keys != expected_order:
        raise ValueError("carrier is not sorted by area and packed value")
    response = dict(response_records)
    if len(response) != len(response_records):
        raise ValueError("duplicate opponent position in response table")
    carrier_index = {key: index for index, key in enumerate(carrier_keys)}

    roots = [
        (42, 42, 42, 42, 35, 35, 35, 35, 35, 35),
        (42, 42, 42, 42, 42, 42, 29, 29, 29, 29),
        (42, 42, 42, 42, 42, 42, 42, 25, 25, 25),
    ]
    root_indices = []
    for root in roots:
        key = pack_position(root)
        if key not in carrier_index:
            raise ValueError(f"root absent from carrier: {root}")
        root_indices.append(carrier_index[key])

    if args.output.exists():
        shutil.rmtree(args.output)
    args.output.mkdir(parents=True)
    name_width = max(6, len(str(max(0, len(positions) - 1))))

    chunk_theorems: list[str] = []
    chunk_index = 0
    first_index = 0
    for index, position in enumerate(positions):
        chunk_theorems.append(
            generate_theorem(index, position, response, carrier_index, name_width)
        )
        if len(chunk_theorems) == args.chunk_size or index + 1 == len(positions):
            write_chunk(
                args.output,
                chunk_index,
                first_index,
                index,
                chunk_theorems,
            )
            chunk_index += 1
            first_index = index + 1
            chunk_theorems = []

    final_import = (
        "import FormalConjectures.OEIS.A147983.Generated."
        f"Chunk{chunk_index - 1:03d}"
    )
    root_names = [theorem_name(index, name_width) for index in root_indices]
    (args.output.parent / "ConcreteProof.lean").write_text(
        f"{final_import}\n\n"
        "/-! Sorry-free kernel proof of the OEIS A147983 three-opening Chomp result. -/\n\n"
        "set_option maxHeartbeats 0\n"
        "set_option maxRecDepth 100000\n\n"
        "namespace OeisA147983\n\n"
        "/-- The first displayed child has an explicit finite losing strategy. -/\n"
        "@[category test, AMS 5]\n"
        "theorem child₁_is_losing : IsPPosition child₁ := by\n"
        "  refine ⟨?_⟩\n"
        f"  simpa [child₁] using Generated.{root_names[0]}\n\n"
        "/-- The second displayed child has an explicit finite losing strategy. -/\n"
        "@[category test, AMS 5]\n"
        "theorem child₂_is_losing : IsPPosition child₂ := by\n"
        "  refine ⟨?_⟩\n"
        f"  simpa [child₂] using Generated.{root_names[1]}\n\n"
        "/-- The third displayed child has an explicit finite losing strategy. -/\n"
        "@[category test, AMS 5]\n"
        "theorem child₃_is_losing : IsPPosition child₃ := by\n"
        "  refine ⟨?_⟩\n"
        f"  simpa [child₃] using Generated.{root_names[2]}\n\n"
        "/-- The 10 × 42 rectangle has at least three distinct winning opening moves. -/\n"
        "@[category research solved, AMS 5]\n"
        "theorem chomp_10_by_42_has_three_winning_openings :\n"
        "    IsWinningOpening rectangle child₁ ∧\n"
        "      IsWinningOpening rectangle child₂ ∧\n"
        "      IsWinningOpening rectangle child₃ ∧\n"
        "      child₁ ≠ child₂ ∧ child₁ ≠ child₃ ∧ child₂ ≠ child₃ :=\n"
        "  three_openings_of_losing child₁_is_losing child₂_is_losing child₃_is_losing\n\n"
        "end OeisA147983\n"
    )

    total_moves = sum(sum(1 for _ in moves(position)) for position in positions)
    print(
        f"GENERATED carrier={len(positions)} responses={len(response)} "
        f"move_cases={total_moves} chunks={chunk_index} roots={root_indices}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
