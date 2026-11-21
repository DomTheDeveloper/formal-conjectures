"""Trace the original declarations needed by each input of the ordinary-RH proof."""
import argparse
from concurrent.futures import ThreadPoolExecutor
import json
from pathlib import Path
import subprocess
import tempfile

from choose_roots import positions
from link_tail import component, declaration, read_zstd

HERE = Path(__file__).resolve().parent
ROOT = 'RH17.riemannHypothesisFromPublishedArithmetic'
CONDITIONAL = 'RH17.riemannHypothesisOfArithmetic'


def chapter_references(front):
    names, expressions, declarations, local_values = [''], [], {}, {}
    for raw in read_zstd(front):
        row = json.loads(raw)
        if 'in' in row:
            p, word = component(row)
            names.append((names[p] + '.' if p else '') + str(word))
        elif 'ie' in row:
            row.pop('ie')
            (kind, data), = row.items()
            refs = set()
            if kind == 'const':
                refs.add(names[data['name']])
            elif kind == 'proj':
                refs = expressions[data['struct']] | {names[data['typeName']]}
            elif kind in ('app', 'forallE', 'lam', 'letE'):
                for field in ('fn', 'arg', 'type', 'body', 'value'):
                    if field in data:
                        refs.update(expressions[data[field]])
                if kind == 'letE':
                    local_values.setdefault(names[data['name']], []).append(expressions[data['value']])
            elif kind not in ('bvar', 'natVal', 'strVal', 'sort'):
                raise ValueError(f'Unexpected expression {kind}')
            expressions.append(refs)
        elif 'il' not in row and 'meta' not in row:
            _, value = declaration(row)
            declarations[names[value['name']]] = expressions[value['type']] | expressions[value['value']]
    prerequisites, seen, queue = set(), set(), [CONDITIONAL]
    while queue:
        name = queue.pop()
        if name in seen:
            continue
        seen.add(name)
        if name in declarations:
            queue.extend(declarations[name])
        else:
            prerequisites.add(name)
    if declarations[ROOT] & declarations.keys() != {CONDITIONAL}:
        raise ValueError('The chapter endpoint changed')
    return prerequisites, declarations[ROOT] - declarations.keys(), local_values


def read_bits(path):
    return int.from_bytes(path.read_bytes()[4:], 'little')


def measure(index, selected, lookup, slicer, work, jobs):
    implied, terminal, let_values = chapter_references(HERE/'chapters.ndjson.zst')
    ids = {name: int(i) for i, name in (r.split('\t') for r in lookup.read_text().splitlines())}
    if set(ids) != implied | terminal or len(ids) != 501:
        raise ValueError('Source dependencies differ from the authenticated linked proof')
    groups = {'Deduction once the two arithmetic inputs are supplied': implied}
    labels = {'row':'Galois compatibility', 'hX':'Arithmetic covolume estimate',
              'P':'Global eigenform hypotheses', 'F':'Local theta hypotheses', 'matching':'Theta integral matching',
              'hL':'Local Langlands input for the covolume construction', 'green':'Green functions from regular characters',
              'chains':'From the definite-side geometry to theta chains'}
    for local, label in labels.items():
        value, = let_values[local]
        if not value or not value.issubset(terminal):
            raise ValueError(f'Unexpected input to {local}')
        groups[label] = value
    groups['Local Langlands existence'] = {'UpperTheory.Zero.LLC.recTExists'}
    groups['Cohomology window from Galois compatibility'] = {'UpperTheory.One.vwin_of_row'}
    groups['Existence of the definite-side geometric data'] = {'UpperTheory.Lit.nonempty_hyps_definite_side_of_closed_bound'}
    groups['Local bounds at two and three'] = {'UpperTheory.N.boundAtTwoThree_linked_of_recT'}
    groups['Dependence of the local parameters'] = {'GlobalTheory.Mem.Top.Bl.parametersOfDependence'}
    final_inputs = {name for group in list(groups.values())[1:] for name in group}
    groups['Remaining types and providers'] = terminal - final_inputs
    ids_by_group = {label:{ids[n] for n in roots} for label, roots in groups.items()}
    ids_by_group['Original Mathlib challenge'] = set(map(int, (index/'challenge-roots.txt').read_text().splitlines())) - positions(index).keys()

    def trace(group):
        label, roots = group
        with tempfile.TemporaryDirectory(dir=work) as temp:
            directory = Path(temp)
            subprocess.run([slicer, 'mark', index, directory, 'share'], text=True,
                           input=''.join(f'{n}\n' for n in sorted(roots)), check=True)
            return label, read_bits(directory/'decls.bits')

    with ThreadPoolExecutor(max_workers=jobs) as executor:
        closure = dict(executor.map(trace, ids_by_group.items()))
    total = 0
    for bits in closure.values():
        total |= bits
    if total != read_bits(selected/'decls.bits') or total.bit_count() != 1175685:
        raise ValueError('The union of the measured inputs differs from the ordinary-RH proof')
    results = {}
    for label, bits in closure.items():
        other = 0
        for name, data in closure.items():
            if name != label:
                other |= data
        results[label] = dict(direct_roots=len(ids_by_group[label]), including_shared=bits.bit_count(),
                              exclusive=(bits & ~other).bit_count())
    return dict(original_declarations=total.bit_count(), groups=results)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    for argument in ('index', 'selection', 'external_names', 'slicer', 'scratch', 'result'):
        parser.add_argument(argument, type=Path)
    parser.add_argument('--jobs', type=int, default=2)
    a = parser.parse_args()
    a.scratch.mkdir(exist_ok=True, parents=True)
    result = measure(a.index, a.selection, a.external_names, a.slicer, a.scratch, a.jobs)
    a.result.write_text(json.dumps(result, indent=2) + '\n')
