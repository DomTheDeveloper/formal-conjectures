"""Run inside the pinned upstream Lake environment to rebuild and compare the algebra modules."""
import argparse
from pathlib import Path
import json
import os
import subprocess
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))
from refine_source import read_refinements, rewrite

FLAGS = ['--tstack=400000', '-DautoImplicit=false', '-DrelaxedAutoImplicit=false',
         '-DmaxSynthPendingDepth=3', '-Dpp.unicode.fun=true', '-DmaxHeartbeats=4000000']


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('repo', type=Path)
    parser.add_argument('output', type=Path)
    args = parser.parse_args()
    repo, out = args.repo.resolve(), args.output.resolve()
    out.mkdir(parents=True, exist_ok=True)
    items = read_refinements()
    rows = []
    for item in items:
        name = item['module']
        rel = Path(*name.split('.')).with_suffix('.lean')
        original = repo / 'src' / rel
        shortened = out / 'src' / rel
        data = original.read_bytes()
        if not data.startswith(b'import Mathlib\n') or item['changed_in_base']:
            raise ValueError(f'Unsupported import or baseline in {name}')
        shortened.parent.mkdir(parents=True, exist_ok=True)
        shortened.write_bytes(rewrite(data, item))
        objects = []
        for file, root, stage in [(original, repo / 'src', 'original'), (shortened, out / 'src', 'reduced')]:
            obj = (out / stage / rel).with_suffix('.olean')
            obj.parent.mkdir(parents=True, exist_ok=True)
            subprocess.run(['lean', *FLAGS, '-R', str(root), '-o', str(obj), str(file)], check=True)
            objects.append(str(obj))
        rows.append('\t'.join([name, *objects]))
    spec = out / 'objects.tsv'
    spec.write_text('\n'.join(rows) + '\n')
    verdict = out / 'kernel-verdicts.jsonl'
    subprocess.run(['lean', '-DmaxRecDepth=100000', '-DmaxHeartbeats=4000000', str(HERE / 'CompareSource.lean')],
                   env=os.environ | {'RH_COMPARE_FILES': str(spec), 'RH_COMPARE_OUTPUT': str(verdict)}, check=True)
    checked = [json.loads(line) for line in verdict.read_text().splitlines()]
    if [r['module'] for r in checked] != [r['module'] for r in items]:
        raise ValueError('Missing a kernel verdict')
    if any(r['failures'] or not r['publicDeclarations'] for r in checked):
        raise ValueError('A public declaration differs')
    print(f"{len(items)} modules rebuilt and compared, including {sum(r['publicDeclarations'] for r in checked)} public declarations.")


if __name__ == '__main__':
    main()
