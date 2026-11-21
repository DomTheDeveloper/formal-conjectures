"""Verify every removed import against the reduced graph parsed by Lean itself."""
from collections import defaultdict
from graphlib import TopologicalSorter
import json
import sys


def audit(lines, batch=2048):
    ids = {}
    graph = {}
    removed = defaultdict(list)
    files = changed = 0

    def ident(name):
        return ids.setdefault(name, len(ids))

    for line in lines:
        path, old_header, new_header = json.loads(line)
        name = path.removesuffix('.lean').replace('/', '.')
        mod = ident(name)
        if mod in graph:
            raise ValueError(f'Duplicate module {name}')
        mode, old = old_header
        new_mode, new = new_header if new_header is not None else old_header
        if mode != new_mode:
            raise ValueError(f'Changed module visibility in {name}')
        files += 1
        changed += new_header is not None
        eligible = []
        pos = 0
        for imp in old:
            dep = ident(imp[0])
            normal = imp[1:] == [False, True, False]
            if pos < len(new) and imp == new[pos]:
                pos += 1
                if normal:
                    eligible.append(dep)
            else:
                if not normal or not eligible:
                    raise ValueError(f'Missing import with no preceding public import in {name}')
                removed[dep].append((mod, len(eligible)))
        if pos != len(new):
            raise ValueError(f'Added, reordered or changed import in {name}')
        graph[mod] = tuple(eligible)

    # Each bit represents one queried target. In topological order, compute exactly
    # which targets are exported by each retained import. External modules are leaves.
    ordered = [(m, graph.get(m, ())) for m in TopologicalSorter(graph).static_order()]
    targets = list(removed)
    verified = 0
    for start in range(0, len(targets), batch):
        chunk = targets[start:start + batch]
        reachable = [0] * len(ids)
        for bit, dep in enumerate(chunk):
            reachable[dep] = 1 << bit
        for mod, deps in ordered:
            mark = reachable[mod]
            for dep in deps:
                mark |= reachable[dep]
            reachable[mod] = mark
        for bit, dep in enumerate(chunk):
            mask = 1 << bit
            for mod, prefix in removed[dep]:
                if not any(reachable[d] & mask for d in graph[mod][:prefix]):
                    names = {value: key for key, value in ids.items()}
                    raise ValueError(f'{names[mod]} loses access to {names[dep]}')
                verified += 1
    return dict(source_modules=files, changed_headers=changed, removed_imports=verified,
                distinct_removed_module_names=len(targets), graph_vertices=len(ordered))


if __name__ == '__main__':
    report = audit(sys.stdin)
    expected = (175187, 251383)
    if (report['source_modules'], report['removed_imports']) != expected:
        raise ValueError(f'Coverage differs from the measured source patch: {report}')
    print(json.dumps(report, sort_keys=True))
