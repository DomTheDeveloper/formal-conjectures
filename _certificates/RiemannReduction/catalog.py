#!/usr/bin/env python3
"""Index declaration signatures in an authenticated lean4export v3.1 stream."""
import argparse
import array
import json
from pathlib import Path
import struct
import sys

PRIMITIVES = """Quot Quot.mk Quot.lift Quot.ind propext Quot.sound Classical.choice
Nat.add Nat.sub Nat.mul Nat.pow Nat.gcd Nat.div Nat.mod Nat.beq Nat.ble Nat.land Nat.lor
Nat.xor Nat.shiftLeft Nat.shiftRight String.ofList Char.ofNat List eagerReduce Nat String
String.mk Char optParam autoParam semiOutParam outParam""".split()
TARGETS = ["riemannHypothesis", "riemannZeta_eq_zero_re", "LFunction_ne_zero_of_half_lt_re",
           "LFunction_eq_zero_re", "LFunction_eq_zero_re_of_isPrimitive"]
DECLS = {"thm", "def", "opaque", "quot", "inductive", "axiom"}

def write_words(out, items):
    data = array.array('I', items)
    if sys.byteorder != 'little':
        data.byteswap()
    data.tofile(out)

def catalog(stream, folder):
    folder.mkdir(exist_ok=True, parents=True)
    names = ['']
    ids = {}
    canonical = {}
    reorder = array.array('I', [0])
    counts = {k: 0 for k in DECLS}
    identical = replaced = ndecl = 0
    with (folder/'declarations.bin').open('wb') as out, (folder/'names.tsv').open('w') as inventory:
        for raw in stream:
            rec = json.loads(raw)
            if 'in' in rec:
                idx = rec['in']
                if idx != len(names):
                    raise ValueError('Nonconsecutive name index')
                part = rec.get('str', rec.get('num'))
                suffix = part.get('str', str(part.get('i')))
                full = names[part['pre']] + '.' + suffix if part['pre'] else suffix
                names.append(full)
                reorder.append(idx)
                if full in INTEREST:
                    ids[full] = idx
                continue
            key, value = next(iter(rec.items()))
            if key not in DECLS:
                continue
            if isinstance(value, list):
                if len(value) != 1:
                    raise ValueError(f'Unsupported {key} record group')
                value = value[0]
            members = value['types'] + value['ctors'] + value['recs'] if key == 'inductive' else [value]
            node_names = [v['name'] for v in members]
            required_expr = [v['type'] for v in members]
            required_names = set()
            alt_body = 0
            for v in members:
                required_names.update(v.get('all', []))
                required_names.update(v.get('ctors', []))
                if 'induct' in v: required_names.add(v['induct'])
                for rule in v.get('rules', []):
                    required_expr.append(rule['rhs'])
                    required_names.add(rule['ctor'])
                if 'value' in v:
                    required_expr.append(v['value'])
            if key == 'thm':
                signature = (value['type'], tuple(value['levelParams']))
                earlier = canonical.setdefault(signature, (value['name'], value['value']))
                if earlier[0] != value['name']:
                    reorder[value['name']] = earlier[0]
                    alt_body = earlier[1]
                    replaced += 1
                    identical += (earlier[1] == value['value'])
            refs = sorted(required_names.difference(node_names))
            write_words(out, [len(node_names), len(required_expr), len(refs), alt_body, *node_names, *required_expr, *refs])
            for name in node_names:
                print(name, key, names[name].replace('\n','\\n').replace('\t','\\t'), sep='\t', file=inventory)
            counts[key] += len(node_names)
            ndecl += 1
    with (folder/'canonical.bin').open('wb') as dest:
        if sys.byteorder != 'little': reorder.byteswap()
        reorder.tofile(dest)
    stats = dict(records=ndecl, constants=sum(counts.values()), names=len(names), by_kind=counts,
                 duplicate_theorem_types=replaced, identical_proofs=identical, targets=ids)
    (folder/'catalog.json').write_text(json.dumps(stats, indent=2, sort_keys=True)+'\n')
    return stats

INTEREST = set(PRIMITIVES + TARGETS + ['RiemannHypothesis','Formalism.VW.rh_of_right',
                                        'Deduction.mellin_ramp','Deduction.zeroFree_of_rpow_window'])

if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('directory', type=Path)
    opts=p.parse_args()
    print(json.dumps(catalog(sys.stdin.buffer, opts.directory), indent=2), flush=True)
