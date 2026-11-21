"""Build, replay and publish the closed ordinary-RH proof in 17 native modules."""
from hashlib import file_digest
import json
from pathlib import Path
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parent
CERTIFICATE = '3eaf53b191772193311d4ee225159ab3e25d3f877311a867508f77dec41bae97'


def digest(path):
    with path.open('rb') as stream:
        return file_digest(stream, 'sha256').hexdigest()


def check(path, expected):
    if digest(path) != expected:
        raise ValueError(f'SHA-256 mismatch for {path}')


def write(path, value):
    path.write_text(json.dumps(value, indent=2) + '\n')


def prepare(original, output, builder, supplements):
    output.mkdir(exist_ok=True, parents=True)
    seen = []
    parts = []
    delta = HERE / 'native-delta.tsv'
    for i in range(17):
        base = json.loads((original / f'Part{i}.json').read_text())
        filename = f'Part{i}.olean.zst'
        expected_module = f'RHBatches.Part{i}'
        imports = [f'RHBatches.Part{i-1}'] if i else []
        if (base['module'], base['imports'], base['filename']) != (expected_module, imports, filename):
            raise ValueError(f'Incorrect parent module {i}')
        compressed = original / filename
        check(compressed, base['compressed_sha256'])
        with tempfile.TemporaryDirectory(dir=output.parent) as temp:
            old = Path(temp) / 'base.olean'
            new = Path(temp) / 'ordinary.olean'
            subprocess.run(['zstd', '-dq', compressed, '-o', old], check=True)
            check(old, base['sha256'])
            prior = imports[0] if imports else '-'
            run = subprocess.run([builder, old, new, expected_module, prior,
                                  delta, supplements if i == 16 else '-'], text=True, stdout=subprocess.PIPE, check=True)
            lines = run.stdout.splitlines()
            removed = [r.removeprefix('removed\t') for r in lines[:-1] if r.startswith('removed\t')]
            if len(removed) != len(lines)-1:
                raise ValueError('Unexpected module conversion output')
            status, reported = lines[-1].split('\t')
            additions = 43 if i == 16 else 0
            if int(reported) != base['constants'] - len(removed) + additions:
                raise ValueError(f'Incorrect constant count for {expected_module}')
            row = dict(index=i, module=expected_module, imports=imports, filename=filename,
                       parent_sha256=base['sha256'], removed=removed, new_constants=additions,
                       declaration_records=base['declaration_records']-len(removed)+additions, constants=int(reported))
            if status == 'rebuilt' and new.is_file():
                compressed = output / filename
                subprocess.run(['zstd', '-q', '-T2', '-6', new, '-o', compressed], check=True)
                row.update(sha256=digest(new), compressed_sha256=digest(compressed), bytes=new.stat().st_size)
            elif status == 'unchanged' and not (removed or additions or new.exists()):
                row.update({k:base[k] for k in ('sha256', 'compressed_sha256', 'bytes')})
            else:
                raise ValueError(f'Unexpected conversion status for {expected_module}: {status}')
            row['compressed_bytes'] = compressed.stat().st_size
            seen.extend(removed)
            parts.append(row)
            print(f'{expected_module}: removed {len(removed)}, added {additions}, retained {row["constants"]} constants', flush=True)
    expected = [s[5:] for s in delta.read_text().splitlines() if s.startswith('drop\t')]
    if len(seen) != 51 or sorted(seen) != sorted(expected) or sum(p['declaration_records'] for p in parts) != 1175724:
        raise ValueError('Full reduced proof differs from its audited closure')
    write(output/'ordinary-native-plan.json', dict(lean_version='4.33.1', declaration_records=1175724,
          original_declarations=1175685, new_chapter_declarations=38, public_aliases=1,
          independent_export_sha256=CERTIFICATE, modules=parts))


def archives(original, patches):
    plan = json.loads((patches/'ordinary-native-plan.json').read_text())
    if plan['independent_export_sha256'] != CERTIFICATE or len(plan['modules']) != 17:
        raise ValueError('Unexpected proof plan')
    for part in plan['modules']:
        changed = patches / part['filename']
        yield part, changed if changed.is_file() else original / part['filename']


def unpack(original, patches, destination):
    objects = destination/'RHBatches'
    objects.mkdir(exist_ok=True, parents=True)
    for part, archive in archives(original, patches):
        check(archive, part['compressed_sha256'])
        native = objects / f'Part{part["index"]}.olean'
        subprocess.run(['zstd', '-dq', archive, '-o', native], check=True)
        check(native, part['sha256'])
        for p in {original/part['filename'], archive}:
            p.unlink(missing_ok=True)


def release(original, patches, verdicts, result):
    result.mkdir(exist_ok=True, parents=True)
    plan = json.loads((patches/'ordinary-native-plan.json').read_text())
    for part, archive in archives(original, patches):
        check(archive, part['compressed_sha256'])
        verdict = (verdicts/f'native-{part["index"]}.txt').read_text().strip()
        if verdict != f'Lean 4.33.1 accepted {part["module"]} {part["sha256"]}':
            raise ValueError(f'Missing kernel verdict for {part["module"]}')
        plan['modules'][part['index']]['native_verdict'] = verdict
        archive.rename(result/part['filename'])
    write(result/'ordinary-native-manifest.json', plan)


if __name__ == '__main__':
    command, *args = sys.argv[1:]
    {'prepare':prepare, 'unpack':unpack, 'release':release}[command](*(Path(p).resolve() for p in args))
