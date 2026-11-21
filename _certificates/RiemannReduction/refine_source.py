"""Apply the readable, kernel-compared refinements on top of the reproduced source tree."""
import argparse
from hashlib import sha256
import json
from pathlib import Path

import apply_source

HERE = Path(__file__).resolve().parent / 'refinements'


def read_refinements():
    return json.loads((HERE / 'edits.json').read_text())


def rewrite(data, item):
    if sha256(data).hexdigest() != item['before_sha256']:
        raise ValueError(f'Unexpected input for {item["module"]}')
    lines = data.decode().splitlines(keepends=True)
    stop = len(lines)
    if item.get('file'):
        if Path(item['file']).name != item['file']:
            raise ValueError('Invalid refinement filename')
        data = (HERE / item['file']).read_bytes()
    else:
        for start, count, replacement in reversed(item['edits']):
            if not (0 <= start <= start + count <= stop):
                raise ValueError(f'Invalid edit in {item["module"]}')
            lines[start:start + count] = [replacement]
            stop = start
        data = ''.join(lines).encode()
    if sha256(data).hexdigest() != item['after_sha256']:
        raise ValueError(f'Unexpected output for {item["module"]}')
    return data


def run(repo, output, visit=None):
    items = read_refinements()
    edits = {f"src/{r['module'].replace('.', '/')}.lean": r for r in items}
    if len(edits) != len(items):
        raise ValueError('Duplicate module in the refinements')
    if output is not None:
        output.mkdir(parents=True, exist_ok=False)
    tree = sha256()
    lines = 0

    def receive(name, data):
        nonlocal lines
        if name in edits:
            data = rewrite(data, edits.pop(name))
        if name.startswith('src/') and name.endswith('.lean'):
            tree.update(name[4:].encode() + b'\0' + sha256(data).digest())
            lines += data.count(b'\n')
        if visit is not None:
            visit(name, data)
        if output is not None:
            target = output / name
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(data)

    baseline = apply_source.run(repo, None, receive)
    if edits:
        raise ValueError('Some refined modules were absent from the baseline')
    delta = sum(r['before_lines'] - r['after_lines'] for r in items)
    if lines != baseline['reduced_lines'] - delta:
        raise ValueError('Aggregate line counts differ')
    return {**baseline, 'base_tree_sha256': baseline['tree_sha256'],
            'base_changed_files': baseline['changed_files'],
            'refined_modules': len(items), 'reduced_lines': lines,
            'changed_files': baseline['changed_files'] + sum(not r['changed_in_base'] for r in items),
            'tree_sha256': tree.hexdigest()}


if __name__ == '__main__':
    cli = argparse.ArgumentParser(description=__doc__)
    cli.add_argument('repo', type=Path)
    cli.add_argument('output', type=Path, nargs='?', help='new directory to create')
    args = cli.parse_args()
    print(json.dumps(run(args.repo, args.output), sort_keys=True))
