"""Link a thin Lean export to a checked dependency closure without adding any axioms."""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys

KINDS = {'axiom', 'def', 'thm', 'opaque', 'quot', 'inductive'}
HEADLINES = {'riemannHypothesis', 'riemannZeta_eq_zero_re', 'LFunction_ne_zero_of_half_lt_re',
             'LFunction_eq_zero_re', 'LFunction_eq_zero_re_of_isPrimitive'}


def read_zstd(path):
    with subprocess.Popen(['zstd', '-dcq', '--long=31', str(path.resolve(strict=True))], stdout=subprocess.PIPE) as z:
        yield from z.stdout
        if z.wait():
            raise ValueError(f'Incomplete input {path}')


def dump(f, obj):
    f.write((json.dumps(obj, ensure_ascii=False, sort_keys=True, separators=(',', ':')) + '\n').encode())


def declaration(row):
    key, = row.keys()
    if key not in KINDS:
        raise ValueError(f'Unexpected declaration {key}')
    v = row[key]
    if isinstance(v, list):
        if len(v) != 1:
            raise ValueError('Unsupported declaration group')
        v = v[0]
    return key, v


def members(k, v):
    return v['types'] + v['ctors'] + v['recs'] if k == 'inductive' else [v]


def component(row):
    numeric = 'num' in row
    v = row['num' if numeric else 'str']
    return v['pre'], v['i' if numeric else 'str']


def content(front):
    names = [(0, '')]
    defined, refs = set(), set()
    exprs, levels = 0, 0
    for raw in read_zstd(front):
        row = json.loads(raw)
        if 'in' in row:
            numeric = row['in']
            parent, part = component(row)
            if numeric != len(names) or parent >= numeric:
                raise ValueError('Noncontiguous name table')
            names.append((parent, part))
        elif 'il' in row:
            levels += 1
            if row['il'] != levels:
                raise ValueError('Noncontiguous universes')
        elif 'ie' in row:
            if row['ie'] != exprs:
                raise ValueError('Noncontiguous expressions')
            exprs += 1
            if 'const' in row:
                refs.add(row['const']['name'])
            if 'proj' in row:
                refs.add(row['proj']['typeName'])
        elif 'meta' not in row:
            k, v = declaration(row)
            if k == 'axiom':
                raise ValueError('A thin proof must never introduce an axiom')
            for m in members(k, v):
                if m['name'] in defined:
                    raise ValueError('Repeated definition')
                defined.add(m['name'])
                refs.update(m.get('all', []))
                refs.update(m.get('ctors', []))
                if 'induct' in m:
                    refs.add(m['induct'])
                refs.update(r['ctor'] for r in m.get('rules', []))
    full = ['']
    for parent, piece in names[1:]:
        full.append((full[parent] + '.' if parent else '') + str(piece))
    return names, full, defined, refs - defined, exprs, levels


def scan(index, front, out, root, alias):
    out.mkdir(parents=True, exist_ok=True)
    names, full, defined, external, nex, nlev = content(front)
    if alias and alias not in full:
        if '.' in alias:
            raise ValueError('The optional public alias must be a root declaration')
        names.append((0, alias))
        full.append(alias)
    if root not in full or full.index(root) not in defined:
        raise ValueError('The new theorem is absent')
    if len(set(full)) != len(full):
        raise ValueError('Ambiguous new printable name')
    external_names = {full[n] for n in external}
    forbidden = HEADLINES & external_names
    if forbidden:
        raise ValueError(f'New proof depends on original headline theorem {forbidden}')
    declared_names = {full[n] for n in defined}
    if declared_names & HEADLINES:
        raise ValueError('Attempt to overwrite original conclusion')
    positions = {edge: i for i, edge in enumerate(names) if i}
    if len(positions) != len(names) - 1:
        raise ValueError('Repeated name component')
    # Read genuine structural names. A numeric suffix differs from a string suffix.
    matched = {0: 0}
    names_out = [None] * len(names)
    names_out[0] = 0
    last = 0
    for raw in read_zstd(index / 'names-declarations.zst'):
        if not raw.startswith(b'{"in":'):
            continue
        rec = json.loads(raw)
        if rec['in'] != last + 1:
            raise ValueError('Noncontiguous input names')
        last = rec['in']
        p, piece = component(rec)
        if p in matched and (matched[p], piece) in positions:
            i = positions[matched[p], piece]
            matched[last] = i
            names_out[i] = last
    if last + 1 != (index / 'canonical.bin').stat().st_size // 4:
        raise ValueError('Incomplete original name table')
    dict_count = last + 1
    lookup = {}
    with (index / 'names.tsv').open() as f:
        for line in f:
            n, _, name = line.rstrip('\n').split('\t', 2)
            if name in declared_names:
                raise ValueError(f'Thin export collides with original declaration {name}')
            if name in external_names or (alias and name == alias):
                lookup[name] = int(n)
    if not external_names.issubset(lookup):
        raise ValueError(f'Missing dependencies {external_names - lookup.keys()}')
    for i in external:
        if names_out[i] != lookup[full[i]]:
            raise ValueError(f'Different structural name for {full[i]}')
    if alias and (alias not in lookup or names_out[full.index(alias)] != lookup[alias]):
        raise ValueError('Missing public challenge name')
    with (out / 'new-names.ndjson').open('wb') as f:
        for i, (p, piece) in enumerate(names):
            if names_out[i] is not None:
                continue
            last += 1
            names_out[i] = last
            obj = {'num': {'pre': names_out[p], 'i': piece}} if isinstance(piece, int) else {'str': {'pre': names_out[p], 'str': piece}}
            dump(f, dict(obj, **{'in': last}))
    roots = sorted((lookup[n], n) for n in external_names)
    (out / 'external.tsv').write_text(''.join(f'{i}\t{n}\n' for i, n in roots))
    (out / 'root-ids.txt').write_text(''.join(f'{i}\n' for i, _ in roots))
    meta = dict(new_root=root, root_name=full.index(root), public_alias=alias,
                alias_name=full.index(alias) if alias else None, original_names=dict_count,
                extra_name_count=last + 1 - dict_count, declaration_names=len(defined),
                external_constants=len(roots), expression_records=nex, universe_records=nlev,
                thin_sha256=hashlib.file_digest(front.open('rb'), 'sha256').hexdigest())
    (out/'link-plan.json').write_text(json.dumps(meta, indent=2)+'\n')
    (out/'name-map.json').write_text(json.dumps(names_out))
    print(json.dumps(meta))


def shift_decl(v, table, ex):
    for k in ('name', 'induct', 'ctor'):
        if k in v:
            v[k] = table[v[k]]
    for k in ('all', 'ctors', 'levelParams'):
        if k in v:
            v[k] = [table[n] for n in v[k]]
    for k in ('type', 'value', 'rhs'):
        if k in v:
            v[k] += ex
    for r in v.get('rules', []):
        shift_decl(r, table, ex)


def tail(out, front, selection, last_level):
    meta = json.loads((out / 'link-plan.json').read_text())
    with front.open('rb') as f:
        if hashlib.file_digest(f, 'sha256').hexdigest() != meta['thin_sha256']:
            raise ValueError('Unexpected thin proof')
    table = json.loads((out / 'name-map.json').read_text())
    bits = (selection / 'exprs.bits').read_bytes()
    old = int.from_bytes(bits[4:], 'little').bit_count()
    upper = old + meta['expression_records']
    if upper >= 2**32 or (selection / 'dictionary.bits').is_file():
        raise ValueError('Expected original name dictionary and a 32-bit expression index')
    def level(i):
        return i + last_level if i else 0
    root_type = None
    dst = sys.stdout.buffer
    dst.write((out / 'new-names.ndjson').read_bytes())
    for raw in read_zstd(front):
        r = json.loads(raw)
        if 'meta' in r or 'in' in r:
            continue
        if 'il' in r:
            r['il'] = level(r['il'])
            if 'param' in r:
                r['param'] = table[r['param']]
            elif 'succ' in r:
                r['succ'] = level(r['succ'])
            else:
                key, = set(r) - {'il'}
                if key not in ('max', 'imax'):
                    raise ValueError(key)
                r[key] = list(map(level, r[key]))
        elif 'ie' in r:
            r['ie'] += old
            k, = set(r) - {'ie'}
            v = r[k]
            if k == 'sort':
                r[k] = level(v)
            elif k == 'const':
                v['name'] = table[v['name']]
                v['us'] = list(map(level, v['us']))
            elif k in ('lam', 'forallE', 'letE'):
                v['name'] = table[v['name']]
                for field in ('type', 'body', 'value'):
                    if field in v:
                        v[field] += old
            elif k == 'app':
                v['fn'] += old
                v['arg'] += old
            elif k == 'proj':
                v['typeName'] = table[v['typeName']]
                v['struct'] += old
            elif k not in ('bvar', 'natVal', 'strVal'):
                raise ValueError(f'Unrecognized expression {k}')
        else:
            k, v = declaration(r)
            for m in members(k, v):
                is_root = m['name'] == meta['root_name']
                shift_decl(m, table, old)
                if is_root:
                    if k != 'thm' or m['levelParams'] or root_type is not None:
                        raise ValueError('Unexpected main theorem signature')
                    root_type = m['type']
        dump(dst, r)
    if root_type is None:
        raise ValueError('Absent root body')
    if meta['public_alias']:
        alias = table[meta['alias_name']]
        dump(dst, {'ie': upper, 'const': {'name': table[meta['root_name']], 'us': []}})
        dump(dst, {'thm': {'all': [alias], 'name': alias, 'levelParams': [], 'type': root_type, 'value': upper}})


if __name__ == '__main__':
    cli = argparse.ArgumentParser(description=__doc__)
    sub = cli.add_subparsers(dest='step', required=True)
    prepare = sub.add_parser('scan')
    for item in ['index', 'thin', 'directory']:
        prepare.add_argument(item, type=Path)
    prepare.add_argument('root')
    prepare.add_argument('--alias', default='')
    build = sub.add_parser('tail')
    for item in ['directory', 'thin', 'selection']:
        build.add_argument(item, type=Path)
    build.add_argument('last_level', type=int)
    a = cli.parse_args()
    if a.step == 'scan':
        scan(a.index, a.thin, a.directory, a.root, a.alias)
    else:
        tail(a.directory, a.thin, a.selection, a.last_level)
