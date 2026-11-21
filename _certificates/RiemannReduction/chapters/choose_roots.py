"""Resolve arithmetic prerequisites and check the original five final theorems are absent."""
import json
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from preserve_challenge import words
from catalog import TARGETS

FORBIDDEN = set(TARGETS) | {
    'rhOfAll', 'allChi', 'critAll', 'claimAll',
    'UpperTheory.FinalTheorems.riemannHypothesis',
    'UpperTheory.FinalTheorems.everyCharacter',
    'UpperTheory.FinalTheorems.everyCharacter_of_row',
    'UpperTheory.riemannHypothesis_of_everyCharacter',
    'UpperTheory.LiteratureTheorems.every_character_of_literature_of_vWin',
    'UpperTheory.Top.zeroFreeAll_of_topG',
}


def positions(index):
    found = {}
    with (index / 'names.tsv').open() as f:
        for line in f:
            n, _, name = line.rstrip('\n').split('\t', 2)
            if name in FORBIDDEN:
                found[int(n)] = name
    if not set(TARGETS).issubset(found.values()):
        raise ValueError('Incomplete original target index')
    return found


def inclusion(index, external):
    forbid = positions(index)
    protected = {int(x) for x in (index / 'challenge-roots.txt').read_text().splitlines()}
    outside = {int(x) for x in external.read_text().splitlines()}
    if outside & forbid.keys():
        raise ValueError('The proposed proof cites an original final result')
    for n in sorted((protected | outside) - forbid.keys()):
        print(n)


def audit(index, selected):
    forbid = positions(index)
    buf = (selected / 'decls.bits').read_bytes()
    table = words(index/'declarations.bin')
    p = d = 0
    selected = set()
    prohibited_types = set()
    selected_types = {}
    while p < len(table):
        nn, ne, nr, _ = table[p:p+4]
        i = p+4
        names = table[i:i+nn]
        typ = table[i+nn]
        if names[0] in forbid:
            prohibited_types.add(typ)
        if buf[4+d//8] & (1 << (d%8)):
            selected.update(names)
            if nn == 1:
                selected_types.setdefault(typ,names[0])
        p += 4 + nn + ne + nr
        d += 1
    if selected & forbid.keys():
        raise ValueError(f'Original conclusions present in dependency closure: {[forbid[n] for n in selected & forbid.keys()]}')
    shared_types = {selected_types[t] for t in prohibited_types & selected_types.keys()}
    if shared_types:
        aliases = []
        with (index/'names.tsv').open() as f:
            for line in f:
                n,_,name=line.rstrip('\n').split('\t',2)
                if int(n) in shared_types: aliases.append(name)
        raise ValueError(f'An original unconditional theorem with the same exported proposition is already used: {aliases}')
    print(json.dumps(dict(original_headline_declarations_in_closure=0,
                          original_unconditional_alias_types_in_closure=0, original_alias_types_checked=len(prohibited_types),
                          selected_declaration_records=int.from_bytes(buf[4:],'little').bit_count())))


if __name__ == '__main__':
    step, index, target = sys.argv[1:]
    if step == 'roots':
        inclusion(Path(index), Path(target))
    else:
        audit(Path(index), Path(target))
