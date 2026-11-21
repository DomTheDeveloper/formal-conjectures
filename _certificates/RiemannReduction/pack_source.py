"""Write 17 complete source volumes and verify every archived file against the patch output."""
import argparse
from contextlib import ExitStack
from hashlib import sha256
import io
import json
from pathlib import Path
import subprocess
import tarfile
from apply_source import run


TOPICS = (
    'entry-points', 'basic-lemmas-and-positivity', 'formalism', 'ground-theory',
    'companion-theory', 'reciprocity-theory', 'automorphic-arithmetic',
    'automorphic-spectrum', 'weil-bound', 'etale-cohomology-and-discrete-groups',
    'resolution-of-singularities', 'abelian-variety-foundations', 'divisor-proofs',
    'inertia-eigenvalues', 'iwasawa-decomposition', 'twisted-operators',
    'other-abelian-variety-proofs',
)
PROJECT = {'BuildAid': 1, 'Supplements': 1, 'Lemmata': 2, 'PositivityTheory': 2, 'Formalism': 3,
           'GroundTheory': 4, 'CompanionTheory': 5, 'ReciprocityTheory': 6}
DEVELOPMENT = {'AutomorphicArithmetic': 7, 'AutomorphicSpectrum': 8, 'WeilBound': 9,
               'EtaleCohomology': 10, 'DiscreteGroups': 10, 'ResolutionOfSingularities': 11}
ABELIAN = {'DivisorProofs': 13, 'InertiaEigenvalues': 14, 'IwasawaDecomposition': 15,
           'TwistedOperators': 16}


def volume(name):
    parts = name.split('/')
    if len(parts) <= 2:
        return 1
    if parts[1] in PROJECT:
        return PROJECT[parts[1]]
    if parts[1] == 'Development' and parts[2] in DEVELOPMENT:
        return DEVELOPMENT[parts[2]]
    if parts[1:3] != ['Development', 'AbelianVarietyTheory']:
        raise ValueError(f'Unexpected source directory: {name}')
    if parts[3] != 'Proofs':
        return 12
    return ABELIAN.get(parts[4], 17)


def pack(repo, out):
    out.mkdir(parents=True, exist_ok=False)
    paths = [out / f'{i:02d}-{title}.tar.zst' for i, title in enumerate(TOPICS, 1)]
    contents = {}
    counts = [dict(files=0, lean_files=0, lean_lines=0) for _ in paths]
    with ExitStack() as files:
        encoders = [files.enter_context(subprocess.Popen(
            ['zstd', '-q', '-T1', '-8', '-o', str(path)], stdin=subprocess.PIPE)) for path in paths]
        archives = [files.enter_context(tarfile.open(fileobj=p.stdin, mode='w|',
                                                     format=tarfile.GNU_FORMAT)) for p in encoders]

        def add(name, data):
            if name in contents:
                raise ValueError(f'Duplicate source file: {name}')
            index = volume(name) - 1
            contents[name] = sha256(data).digest()
            entry = tarfile.TarInfo(name)
            entry.mode = 0o644
            entry.size = len(data)
            archives[index].addfile(entry, io.BytesIO(data))
            counts[index]['files'] += 1
            if name.endswith('.lean'):
                counts[index]['lean_files'] += 1
                counts[index]['lean_lines'] += data.count(b'\n')

        source = run(repo, None, visit=add)
    if any(p.returncode for p in encoders):
        raise RuntimeError('A zstd encoder failed')
    for i, path in enumerate(paths, 1):
        with subprocess.Popen(['zstd', '-dcq', path], stdout=subprocess.PIPE) as p:
            with tarfile.open(fileobj=p.stdout, mode='r|') as archive:
                for entry in archive:
                    if not entry.isfile() or volume(entry.name) != i:
                        raise ValueError(f'Invalid entry: {entry.name}')
                    data = archive.extractfile(entry).read()
                    if sha256(data).digest() != contents.pop(entry.name, None):
                        raise ValueError(f'Source recovery mismatch for {entry.name}')
            # Consume all trailing zero blocks before closing the decoder.
            while p.stdout.read(65536):
                pass
            if p.wait():
                raise RuntimeError(f'Corrupt archive: {path}')
        counts[i-1].update(file=path.name, bytes=path.stat().st_size, sha256=sha256(path.read_bytes()).hexdigest())
    if contents or sum(c['lean_lines'] for c in counts) != source['reduced_lines']:
        raise ValueError('Incomplete archived source')
    return dict(source=source, volumes=counts)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('repo', type=Path)
    parser.add_argument('output', type=Path, help='new directory for the 17 archives')
    args = parser.parse_args()
    print(json.dumps(pack(args.repo, args.output), indent=2))
