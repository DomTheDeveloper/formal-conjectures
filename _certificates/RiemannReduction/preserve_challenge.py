"""Keep the official challenge's named library declarations intact during theorem sharing."""
from array import array
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys

from catalog import DECLS, TARGETS

CHALLENGE_SHA256 = 'bd484ac9886a96f26b1d9a7a59ebd45b7a70d102c015d4f31f9302bbdd6ab2b9'


def challenge_constants(archive):
    names = ['']
    constants = set()
    digest = hashlib.sha256()
    with subprocess.Popen(['zstd', '-dcq', '--long=31', str(archive)], stdout=subprocess.PIPE) as z:
        for raw in z.stdout:
            digest.update(raw)
            key = raw[2:raw.index(b'"', 2)]
            if key == b'in':
                row = json.loads(raw)
                if row['in'] != len(names):
                    raise ValueError('Non-contiguous challenge name table')
                part = row.get('str', row.get('num'))
                suffix = part['str'] if 'str' in part else str(part['i'])
                parent = names[part['pre']]
                names.append(parent + '.' + suffix if parent else suffix)
            elif key.decode() in DECLS:
                value = json.loads(raw)[key.decode()]
                if isinstance(value, list):
                    if len(value) != 1:
                        raise ValueError('Unsupported declaration grouping')
                    value = value[0]
                members = value['types'] + value['ctors'] + value['recs'] if key == b'inductive' else [value]
                constants.update(names[v['name']] for v in members)
        if z.wait():
            raise ValueError('Incomplete challenge decompression')
    if digest.hexdigest() != CHALLENGE_SHA256 or not set(TARGETS).issubset(constants):
        raise ValueError('Wrong official challenge')
    return constants


def words(file):
    value = array('I')
    with file.open('rb') as src:
        value.fromfile(src, file.stat().st_size // 4)
    if sys.byteorder != 'little':
        value.byteswap()
    return value


def write_words(path, values):
    if sys.byteorder != 'little':
        values.byteswap()
    with path.open('wb') as out:
        values.tofile(out)


def protect(challenge, index, out):
    protected = challenge_constants(challenge)
    out.mkdir(parents=True, exist_ok=True)
    if out.resolve() == index.resolve():
        raise ValueError('The guarded index needs a separate directory')
    ids = set()
    seen = set()
    with (index / 'names.tsv').open() as stream:
        for line in stream:
            n, _, name = line.rstrip('\n').split('\t', 2)
            if name in protected:
                ids.add(int(n))
                seen.add(name)
    missing = sorted(protected - seen)
    allowed = {'sorryAx'}
    if set(missing) - allowed:
        raise ValueError(f'Original solution is missing challenge declarations: {missing[:20]}')
    canon = words(index / 'canonical.bin')
    table = words(index / 'declarations.bin')
    changes = bodies = 0
    for n in ids:
        changes += canon[n] != n
        canon[n] = n
    p = 0
    while p < len(table):
        count, expressions, references, alternate = table[p:p + 4]
        if alternate and any(n in ids for n in table[p + 4:p + 4 + count]):
            table[p + 3] = 0
            bodies += 1
        p += 4 + count + expressions + references
    if p != len(table):
        raise ValueError('Malformed declaration index')
    write_words(out / 'canonical.bin', canon)
    write_words(out / 'declarations.bin', table)
    for source in index.iterdir():
        if source.name in {'canonical.bin', 'declarations.bin', 'complete'} or not source.is_file():
            continue
        target = out / source.name
        if not target.exists():
            target.symlink_to(source.resolve())
    (out / 'challenge-roots.txt').write_text(''.join(f'{n}\n' for n in sorted(ids)))
    result = dict(challenge_sha256=CHALLENGE_SHA256, challenge_constants=len(protected),
                  common_original_constants=len(ids), challenge_only=missing,
                  original_references_restored=changes, original_theorem_bodies_restored=bodies)
    (out / 'preservation.json').write_text(json.dumps(result, indent=2) + '\n')
    return result


if __name__ == '__main__':
    cli = argparse.ArgumentParser(description=__doc__)
    cli.add_argument('challenge', type=Path)
    cli.add_argument('index', type=Path)
    cli.add_argument('output', type=Path)
    a = cli.parse_args()
    print(json.dumps(protect(a.challenge, a.index, a.output), sort_keys=True))
