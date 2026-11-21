#!/usr/bin/env python3
"""Regenerate a shorter Lean source tree from the published release and its export catalog."""
import argparse
from array import array
from imports import Imports
import json
from pathlib import Path
import re
import subprocess
import sys
import tarfile

SOURCE_REV = '40e56bab026552e089d7afcfeff08d2defb9c005'
IDENT = r"[\w'][\w'.]*"
THEOREM = re.compile(rf"^(?:theorem|lemma)\s+({IDENT})(?=\s|:|\(|\[|\{{)")
SCOPE = re.compile(rf"^(namespace|(?:noncomputable )?section)(?:\s+({IDENT}))?\s*(?:--.*)?$")
END = re.compile(rf"^end(?:\s+({IDENT}))?\s*(?:--.*)?$")
BOUNDARY = re.compile(r"^(?:theorem|lemma|def|abbrev|instance|structure|class|inductive|opaque|axiom|"
                      r"namespace|section|end|open|variable|include|omit|universe|noncomputable|private|"
                      r"protected|scoped|local|set_option|attribute|infix\w*|notation|macro|example|"
                      r"export|mutual|deriving|initialize|alias|syntax|elab|irreducible_def)\b|^(?:@\[|#|/-|--)")
IMPORT = re.compile(r"^import\s+([^\s]+)\s*(?:--.*)?$")
EXTRA = re.compile(r"^\s*(?:where|termination_by|decreasing_by|finally)\b", re.M)

def archive(repo):
    cmd = ['git', '-C', str(repo), 'archive', SOURCE_REV, 'src']
    with subprocess.Popen(cmd, stdout=subprocess.PIPE) as proc:
        with tarfile.open(fileobj=proc.stdout, mode='r|') as files:
            for entry in files:
                if entry.name.endswith('.lean'):
                    yield entry.name[4:-5].replace('/', '.'), files.extractfile(entry).read().decode()
        if proc.wait():
            raise RuntimeError('git archive failed')

def theorem_groups(index):
    mapping = array('I')
    with (index/'canonical.bin').open('rb') as f:
        mapping.fromfile(f, (index/'canonical.bin').stat().st_size // 4)
    if sys.byteorder != 'little':
        mapping.byteswap()
    shared = {old for i, old in enumerate(mapping) if old != i}
    groups = {}
    with (index/'names.tsv').open() as f:
        for row in f:
            i, kind, name = row.rstrip('\n').split('\t', 2)
            if kind == 'thm' and mapping[int(i)] in shared and re.fullmatch(IDENT, name):
                groups[name] = mapping[int(i)]
    return groups

def declarations(lines, groups):
    stack = []
    # Only unmodified, public theorem commands with a name present in the kernel inventory.
    for i, line in enumerate(lines):
        if not line or line[0].isspace():
            continue
        text = line.rstrip()
        if m := SCOPE.fullmatch(text):
            stack.append((m[2] or '') if m[1] == 'namespace' else '')
        elif END.fullmatch(text):
            if stack:
                stack.pop()
        elif m := THEOREM.match(text):
            name = m[1]
            full = name[7:] if name.startswith('_root_.') else '.'.join([*(s for s in stack if s), name])
            if full in groups:
                yield i, name, full, groups[full]

def body_end(lines, start):
    i = start + 1
    while i < len(lines) and (not lines[i].strip() or lines[i][0].isspace()):
        i += 1
    if i < len(lines) and not BOUNDARY.match(lines[i]):
        return None
    while i > start + 1 and not lines[i - 1].strip():
        i -= 1
    chunk = ''.join(lines[start:i])
    # A where/termination block can introduce names used by later source commands.
    if ':=' not in chunk or EXTRA.search(chunk) or '/-' in chunk or '-/' in chunk:
        return None
    # Attributes, scoped options, and attached documentation require their original command.
    j = start - 1
    while j >= 0 and not lines[j].strip():
        j -= 1
    if j >= 0 and (lines[j].rstrip().endswith((' in', ']', '-/'))):
        return None
    return i

def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('repo', type=Path)
    p.add_argument('index', type=Path)
    p.add_argument('--overlay', type=Path, help='write changed modules under this directory, with src/ paths')
    p.add_argument('--manifest', type=Path)
    p.add_argument('--stats', type=Path)
    opts = p.parse_args()
    groups = theorem_groups(opts.index)
    imports, inventory = {}, {}
    for module, source in archive(opts.repo):
        lines = source.splitlines(keepends=True)
        imports[module] = [m[1] for line in lines if (m := IMPORT.fullmatch(line.rstrip()))]
        candidates = list(declarations(lines, groups))
        if candidates:
            inventory[module] = candidates
    graph = Imports(imports)
    order = [m for m in graph.order if m in imports]
    # Reuse an earlier proof only when its module is already visible to this source.
    earliest, by_module, replacements = {}, {}, {}
    for module in order:
        available = {}
        for dep in imports[module]:
            available.update(by_module.get(dep, {}))
        local = {}
        for i, rel, full, group in inventory.get(module, []):
            previous = local.get(group) or available.get(group) or earliest.get(group)
            if previous and previous[1] != full and graph.reaches(module, previous[0]):
                replacements.setdefault(module, {})[i] = (rel, full, *previous)
            entry = (module, full)
            local.setdefault(group, entry)
            earliest.setdefault(group, entry)
        if local:
            by_module[module] = local
    totals = dict(original_modules=0, original_lines=0, reduced_lines=0, original_bytes=0, reduced_bytes=0,
                  changed_modules=0, shortened_theorems=0, redundant_imports=0, added_module_imports=0)
    manifest = opts.manifest.open('w') if opts.manifest else None
    for module, source in archive(opts.repo):
        lines = source.splitlines(keepends=True)
        totals['original_modules'] += 1
        totals['original_lines'] += source.count('\n')
        totals['original_bytes'] += len(source.encode())
        proposed = replacements.get(module, {})
        changes, mappings = [], []
        # Keep the original theorem statement, including its source-level implicit arguments.
        # Kernel expression IDs intentionally identify more terms than the surface syntax does.
        if graph.mathlib[module]:
            for start, (rel, full, owner, proof) in proposed.items():
                end = body_end(lines, start)
                if end is None or end - start < 2:
                    continue
                chunk = ''.join(lines[start:end])
                delimiter = re.search(r':=\s*by[ \t]*(?:\n|$)', chunk)
                if not delimiter or ':=' in chunk[:delimiter.start()]:
                    continue
                header = chunk[:delimiter.start()]
                if not header.strip() or ' where' in header:
                    continue
                term = f'@_root_.{proof}'
                body = f':= by\n  first | exact {term} | solve_by_elim (maxDepth := 16) [{term}]\n'
                rewritten = header + body
                if len(rewritten.encode()) >= len(chunk.encode()) or rewritten.count('\n') >= chunk.count('\n'):
                    continue
                changes.append((start, end, rewritten))
                mappings.append((full, proof))
        header = [i for i, line in enumerate(lines) if IMPORT.fullmatch(line.rstrip())]
        dropped = graph.redundant(imports[module])
        for offset in dropped:
            ix = header[offset]
            # Preserve any original end-of-line comment as a comment.
            comment = lines[ix].partition('--')[2]
            changes.append((ix, ix+1, '--'+comment if comment else ''))
        if changes and not source.startswith('module\n'):
            patched = lines.copy()
            for start, end, replacement in sorted(changes, reverse=True):
                patched[start:end] = [replacement]
            new = ''.join(patched)
            if new.count('\n') < source.count('\n') and len(new.encode()) < len(source.encode()):
                totals['changed_modules'] += 1
                totals['shortened_theorems'] += len(mappings)
                totals['redundant_imports'] += len(dropped)
                if opts.overlay:
                    path = opts.overlay / 'src' / (module.replace('.', '/') + '.lean')
                    path.parent.mkdir(parents=True, exist_ok=True)
                    path.write_text(new)
                if manifest:
                    manifest.write(json.dumps([module, [imports[module][i] for i in dropped], mappings], separators=(',',':'))+'\n')
                source = new
        totals['reduced_lines'] += source.count('\n')
        totals['reduced_bytes'] += len(source.encode())
    if manifest: manifest.close()
    output = json.dumps(totals, indent=2, sort_keys=True)+'\n'
    if opts.stats: opts.stats.write_text(output)
    print(output, end='')

if __name__ == '__main__':
    main()
