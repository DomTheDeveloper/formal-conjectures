"""Record proof coverage, compressed-object checksums and native kernel verdicts."""
import argparse
import hashlib
import json
import re
from pathlib import Path

PARTS = 17
RECORDS = 1_175_732


def digest(path):
    with path.open('rb') as f:
        return hashlib.file_digest(f, 'sha256').hexdigest()


def dump(path, data):
    path.write_text(json.dumps(data, indent=2) + '\n')


def read(path):
    return json.loads(path.read_text())


def plan(root):
    owners = (root / 'plan/owners.bin').read_bytes()
    rows = {}
    for part, records, expressions in re.findall(
            r'^stage (\d+): (\d+) records, (\d+) expressions$', (root / 'plan.log').read_text(), re.M):
        rows[int(part)] = int(records), int(expressions)
    if set(rows) != set(range(PARTS)):
        raise ValueError('Incomplete stage plan')
    entries = []
    for i in range(PARTS):
        records, expressions = rows[i]
        if not records or records != owners.count(i):
            raise ValueError(f'Declaration ownership mismatch in part {i}')
        fragment = root / f'fragments/stage-{i}.ndjson.zst'
        entries.append(dict(index=i, module=f'RHBatches.Part{i}',
                            imports=[f'RHBatches.Part{i-1}'] if i else [],
                            declaration_records=records, expression_records=expressions,
                            fragment_sha256=digest(fragment)))
    total = sum(x['declaration_records'] for x in entries)
    if total != RECORDS or total != len(owners) - owners.count(255):
        raise ValueError('Incomplete declaration coverage')
    dump(root / 'module-plan.json', dict(lean_version='4.33.1', declaration_records=total,
         original_solution_zst_sha256='61a8938ad5f5e57397c1c0e3b954916af546d9004ade01c3555744a681b05381',
         challenge=read(root / 'protected/index/preservation.json'), modules=entries))


def encode(root, i):
    entry = read(root / 'module-plan.json')['modules'][i]
    obj = root / f'Part{i}.olean'
    archive = root / f'Part{i}.olean.zst'
    expected = entry['declaration_records']
    match = re.fullmatch(fr'RHBatches\.Part{i}: serialized (\d+) constants\n',
                         (root / 'serialize.log').read_text())
    if not match or int(match.group(1)) < expected:
        raise ValueError(f'Incomplete module {i}')
    entry.update(constants=int(match.group(1)), filename=archive.name, bytes=obj.stat().st_size,
                 sha256=digest(obj), compressed_bytes=archive.stat().st_size, compressed_sha256=digest(archive))
    dump(root / f'Part{i}.json', entry)


def combine(root):
    result = read(root / 'module-plan.json')
    for i, planned in enumerate(result['modules']):
        module = read(root / f'Part{i}.json')
        if any(module[k] != v for k, v in planned.items()):
            raise ValueError(f'Module {i} differs from its plan')
        if digest(root / module['filename']) != module['compressed_sha256']:
            raise ValueError(f'Module {i} differs from the replayed object')
        verdict = (root / f'native-{i}.txt').read_text().strip()
        if verdict != 'Lean 4.33.1 accepted ' + module['module'] + ' ' + module['sha256']:
            raise ValueError(f'Missing native verdict for module {i}')
        module['native_kernel_verdict'] = verdict
        result['modules'][i] = module
    result['native_checker'] = 'leanchecker (Lean 4.33.1), all 17 owning modules'
    dump(root / 'module-manifest.json', result)


if __name__ == '__main__':
    args = argparse.ArgumentParser(description=__doc__)
    args.add_argument('step', choices=('plan', 'encode', 'combine'))
    args.add_argument('directory', type=Path)
    args.add_argument('part', type=int, nargs='?')
    opts = args.parse_args()
    if opts.step == 'plan':
        plan(opts.directory)
    elif opts.step == 'encode':
        encode(opts.directory, opts.part)
    else:
        combine(opts.directory)
