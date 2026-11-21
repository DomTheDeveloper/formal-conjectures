"""Compare every new declaration, allowing only renaming of local bound variables and table reindexing."""
from hashlib import sha256
import json
from pathlib import Path
import sys

from link_tail import component, declaration, read_zstd


def fingerprint(kind, data):
    encoded = json.dumps([kind, data], sort_keys=True, separators=(',', ':'), ensure_ascii=False).encode()
    return sha256(encoded).hexdigest()


def inventory(path):
    names = [fingerprint('name', [])]
    levels = [fingerprint('zero', [])]
    exprs = []
    declarations = {}
    for raw in read_zstd(path):
        row = json.loads(raw)
        if 'meta' in row:
            continue
        if 'in' in row:
            index = row.pop('in')
            parent, piece = component(row)
            if index != len(names):
                raise ValueError('Bad name index')
            names.append(fingerprint('name', [names[parent], piece]))
        elif 'il' in row:
            index = row.pop('il')
            (tag, arg), = row.items()
            if index != len(levels):
                raise ValueError('Bad level index')
            if tag == 'param':
                arg = names[arg]
            elif tag == 'succ':
                arg = levels[arg]
            elif tag in ('max', 'imax'):
                arg = [levels[i] for i in arg]
            else:
                raise ValueError(tag)
            levels.append(fingerprint(tag, arg))
        elif 'ie' in row:
            index = row.pop('ie')
            (tag, arg), = row.items()
            if index != len(exprs):
                raise ValueError('Bad expression index')
            if tag in ('forallE', 'lam', 'letE'):
                # Kernel terms refer to bound variables by de Bruijn index. Their labels are display names.
                del arg['name']
                for k in ('type', 'body', 'value'):
                    if k in arg:
                        arg[k] = exprs[arg[k]]
            elif tag == 'const':
                arg['name'] = names[arg['name']]
                arg['us'] = [levels[i] for i in arg['us']]
            elif tag == 'app':
                arg['fn'] = exprs[arg['fn']]
                arg['arg'] = exprs[arg['arg']]
            elif tag == 'sort':
                arg = levels[arg]
            elif tag == 'proj':
                arg['typeName'] = names[arg['typeName']]
                arg['struct'] = exprs[arg['struct']]
            elif tag not in ('bvar', 'natVal', 'strVal'):
                raise ValueError(tag)
            exprs.append(fingerprint(tag, arg))
        else:
            tag, data = declaration(row)
            if tag not in ('thm', 'def', 'opaque') or data.get('isUnsafe', False):
                raise ValueError(f'Unexpected declaration {tag}')
            name = data['name'] = names[data['name']]
            if name in declarations:
                raise ValueError('Duplicate declaration')
            data['all'] = [names[n] for n in data['all']]
            data['levelParams'] = [names[n] for n in data['levelParams']]
            data['type'] = exprs[data['type']]
            data['value'] = exprs[data['value']]
            declarations[name] = fingerprint(tag, data)
    return declarations


if __name__ == '__main__':
    a, b = (inventory(Path(s)) for s in sys.argv[1:])
    if not a or a != b:
        raise SystemExit(f'Chapter proofs differ: {len(a.keys() ^ b.keys())} names, '
                         f'{sum(a[k] != b[k] for k in a.keys() & b.keys())} common declarations')
    print(f'All {len(a)} declarations from source match the linked checked input, including complete proof bodies.')
