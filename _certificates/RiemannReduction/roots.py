#!/usr/bin/env python3
"""Resolve the comparison targets and kernel primitives in this export."""
import argparse
import json
from pathlib import Path
from catalog import PRIMITIVES, TARGETS

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('catalog', type=Path)
parser.add_argument('target', help='all, ordinary, or one fully qualified declaration name')
args = parser.parse_args()
catalog = json.loads((args.catalog/'catalog.json').read_text())
names = dict(catalog['targets'])
want = TARGETS if args.target == 'all' else [TARGETS[0] if args.target == 'ordinary' else args.target]
missing = set(want)-names.keys()
if missing:
    with (args.catalog/'names.tsv').open() as source:
        for row in source:
            idx, kind, name = row.rstrip('\n').split('\t', 2)
            if name in missing:
                if name in names: raise ValueError(f'Ambiguous declaration {name}')
                names[name] = int(idx)
if not all(n in names for n in want):
    raise SystemExit(f'Unknown targets {set(want)-names.keys()}')
for n in [*PRIMITIVES, *want]:
    if n in names:
        print(names[n])
