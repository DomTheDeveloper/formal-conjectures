#!/usr/bin/env python3
"""Generate sharded packed Lean data for the OEIS A147983 sparse strategy checker.

The C++ carrier producer and this script are untrusted.  Before writing any Lean source, this
script independently replays every legal opponent move, verifies the recorded response is a legal
bite into the carrier, checks strict area decrease, and packs only the response carrier index and
reply move.  Lean's `SparseStrategyData.Valid` proposition remains the final trusted check.
"""

from __future__ import annotations

import argparse
import shutil
import struct
from pathlib import Path

Position = tuple[int, ...]

POSITION_MAGIC = b"CHCARR02"
RESPONSE_MAGIC = b"CHRESP02"
NEXT_MODULUS = 1 << 20
ROW_SHIFT = 20
TARGET_SHIFT = 24


def read_records(path: Path, magic: bytes, width: int) -> list[tuple[int, ...]]:
    data = path.read_bytes()
    if len(data) < 16 or data[:8] != magic:
        raise ValueError(f"bad certificate header: {path}")
    count = struct.unpack_from("<Q", data, 8)[0]
    expected = 16 + count * width * 8
    if len(data) != expected:
        raise ValueError(f"bad certificate length: {path}: {len(data)} != {expected}")
    return [
        struct.unpack_from("<" + "Q" * width, data, 16 + index * width * 8)
        for index in range(count)
    ]


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


def legal_moves(position: Position):
    for row in range(10):
        lower = 1 if row == 0 else 0
        for target in range(lower, position[row]):
            yield row, target, bite(position, row, target)


def find_move(parent: Position, child: Position) -> tuple[int, int]:
    for row, target, result in legal_moves(parent):
        if result == child:
            return row, target
    raise ValueError(f"not a legal move: {parent} -> {child}")


def pack_reply(next_index: int, row: int, target: int) -> int:
    if not 0 <= next_index < NEXT_MODULUS:
        raise ValueError(f"carrier index exceeds 20-bit allocation: {next_index}")
    if not 0 <= row < 10 or not 0 <= target < 43:
        raise ValueError((next_index, row, target))
    return next_index | (row << ROW_SHIFT) | (target << TARGET_SHIFT)


def lean_array(values: list[int], per_line: int = 12) -> str:
    lines = []
    for start in range(0, len(values), per_line):
        lines.append("  " + ", ".join(str(value) for value in values[start : start + per_line]))
    return "#[\n" + ",\n".join(lines) + "\n]"


def write_reply_chunk(output: Path, index: int, values: list[int]) -> None:
    name = f"ReplyChunk{index:03d}"
    (output / f"{name}.lean").write_text(
        "import FormalConjectures.OEIS.A147983.SparseStrategyData\n\n"
        "/-! Generated packed Chomp response codes. -/\n\n"
        "namespace OeisA147983.GeneratedSparse\n\n"
        f"def replyChunk{index:03d} : Array ℕ := {lean_array(values)}\n\n"
        "end OeisA147983.GeneratedSparse\n"
    )


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("carrier", type=Path)
    parser.add_argument("responses", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("--reply-chunk-size", type=int, default=100_000)
    args = parser.parse_args()

    carrier_records = read_records(args.carrier, POSITION_MAGIC, 1)
    response_records = read_records(args.responses, RESPONSE_MAGIC, 2)
    carrier_keys = [record[0] for record in carrier_records]
    if len(carrier_keys) != len(set(carrier_keys)):
        raise ValueError("duplicate carrier position")
    positions = [unpack_position(key) for key in carrier_keys]
    expected_order = sorted(carrier_keys, key=lambda key: (sum(unpack_position(key)), key))
    if carrier_keys != expected_order:
        raise ValueError("carrier is not sorted by area and packed value")
    if len(carrier_keys) >= NEXT_MODULUS:
        raise ValueError("carrier does not fit packed 20-bit next index")

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

    offsets = [0]
    packed_replies: list[int] = []
    reused_response_keys: set[int] = set()
    for parent_index, parent in enumerate(positions):
        for _, _, opponent in legal_moves(parent):
            opponent_key = pack_position(opponent)
            if opponent_key not in response:
                raise ValueError(f"missing response from carrier index {parent_index}: {opponent}")
            reply_key = response[opponent_key]
            if reply_key not in carrier_index:
                raise ValueError(f"reply leaves carrier: {opponent} -> {unpack_position(reply_key)}")
            reply = unpack_position(reply_key)
            reply_row, reply_target = find_move(opponent, reply)
            if sum(reply) >= sum(parent):
                raise ValueError(f"two-ply area failed: {parent} -> {opponent} -> {reply}")
            packed_replies.append(
                pack_reply(carrier_index[reply_key], reply_row, reply_target)
            )
            reused_response_keys.add(opponent_key)
        offsets.append(len(packed_replies))

    if reused_response_keys != set(response):
        extras = len(set(response) - reused_response_keys)
        raise ValueError(f"response table has {extras} unreachable extra entries")

    if args.output.exists():
        shutil.rmtree(args.output)
    args.output.mkdir(parents=True)

    (args.output / "PositionData.lean").write_text(
        "import FormalConjectures.OEIS.A147983.SparseStrategyData\n\n"
        "/-! Generated packed Chomp carrier positions and sparse offsets. -/\n\n"
        "namespace OeisA147983.GeneratedSparse\n\n"
        f"def positionCodes : Array ℕ := {lean_array(carrier_keys)}\n\n"
        f"def responseOffsets : Array ℕ := {lean_array(offsets)}\n\n"
        "end OeisA147983.GeneratedSparse\n"
    )

    chunks = []
    for chunk_index, start in enumerate(range(0, len(packed_replies), args.reply_chunk_size)):
        values = packed_replies[start : start + args.reply_chunk_size]
        write_reply_chunk(args.output, chunk_index, values)
        chunks.append(chunk_index)

    imports = ["import FormalConjectures.OEIS.A147983.GeneratedSparse.PositionData"]
    imports += [
        f"import FormalConjectures.OEIS.A147983.GeneratedSparse.ReplyChunk{index:03d}"
        for index in chunks
    ]
    chunk_names = ",\n  ".join(f"replyChunk{index:03d}" for index in chunks)
    (args.output.parent / "ConcreteSparseData.lean").write_text(
        "\n".join(imports)
        + "\n\n/-! Generated packed sparse strategy data; validity is proved separately. -/\n\n"
        + "namespace OeisA147983.GeneratedSparse\n\n"
        + f"def replyChunkSize : ℕ := {args.reply_chunk_size}\n\n"
        + "def replyChunks : Array (Array ℕ) := #[\n  "
        + chunk_names
        + "\n]\n\n"
        + "def replyCode (index : ℕ) : ℕ :=\n"
        + "  (replyChunks.getD (index / replyChunkSize) #[]).getD (index % replyChunkSize) 0\n\n"
        + "def certificate : SparseStrategyData :=\n"
        + "  { positions := positionCodes\n"
        + "    offsets := responseOffsets\n"
        + "    replyCode := replyCode }\n\n"
        + f"def rootIndices : List ℕ := {root_indices}\n\n"
        + "end OeisA147983.GeneratedSparse\n"
    )

    print(
        f"GENERATED carrier={len(carrier_keys)} replies={len(packed_replies)} "
        f"unique_opponents={len(response)} chunks={len(chunks)} roots={root_indices}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
