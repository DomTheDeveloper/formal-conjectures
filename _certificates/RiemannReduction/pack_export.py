"""Pack the complete reduced export into 17 byte ranges and verify their round trip."""
import argparse
from hashlib import file_digest, sha256
import json
from pathlib import Path
import subprocess
import sys

EXPORT = Path(__file__).with_name('measurements.json')
RANGES = 17
BLOCK = 2**20


def pack(source, out, expected_bytes, expected_hash, count=RANGES):
    out.mkdir(parents=True, exist_ok=False)
    rolling = sha256()
    members = []
    for ordinal in range(count):
        start = expected_bytes * ordinal // count
        end = expected_bytes * (ordinal + 1) // count
        path = out / f'rh-proof-{ordinal + 1:02d}-of-{count:02d}.zst'
        with subprocess.Popen(['zstd', '-q', '-T2', '--long=27', '-9', '-o', str(path)],
                              stdin=subprocess.PIPE) as encoder:
            left = end - start
            while left:
                data = source.read(min(BLOCK, left))
                if not data:
                    raise ValueError(f'The input ended inside {path.name}')
                rolling.update(data)
                encoder.stdin.write(data)
                left -= len(data)
            encoder.stdin.close()
            if encoder.wait():
                raise RuntimeError(f'Compression failed for {path.name}')
        with path.open('rb') as stream:
            compressed_hash = file_digest(stream, 'sha256').hexdigest()
        members.append(dict(name=path.name, first_byte=start, end_byte=end,
                            compressed_bytes=path.stat().st_size, sha256=compressed_hash))
    if source.read(1) or rolling.hexdigest() != expected_hash:
        raise ValueError('Input length or full export SHA-256 differs')
    recovered = sha256()
    recovered_bytes = 0
    for member in members:
        with subprocess.Popen(['zstd', '-dcq', '--long=27', str(out / member['name'])],
                              stdout=subprocess.PIPE) as decoder:
            while data := decoder.stdout.read(BLOCK):
                recovered.update(data)
                recovered_bytes += len(data)
            if decoder.wait() or recovered_bytes != member['end_byte']:
                raise ValueError(f'Corrupt export range {member["name"]}')
    if recovered.hexdigest() != expected_hash:
        raise ValueError('Decompressed export differs')
    return dict(bytes=recovered_bytes, sha256=expected_hash, parts=members)


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('output', type=Path)
    args = p.parse_args()
    full = json.loads(EXPORT.read_text())['all_five']
    result = pack(sys.stdin.buffer, args.output, full['bytes'], full['sha256'])
    result['declaration_records'] = full['declaration_records']
    manifest = args.output / 'export-manifest.json'
    manifest.write_text(json.dumps(result, indent=2) + '\n')
