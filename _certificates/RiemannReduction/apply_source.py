#!/usr/bin/env python3
"""Materialize the complete shortened Lean project from the pinned source alone."""
import argparse
import hashlib
import json
import lzma
from pathlib import Path
import subprocess
import tarfile

HERE=Path(__file__).resolve().parent
REV='40e56bab026552e089d7afcfeff08d2defb9c005'

def run(repo, output):
    with lzma.open(HERE/'source-edits.jsonl.xz','rt') as patch:
        edits=dict(json.loads(line) for line in patch)
    if output is not None:
        output.mkdir(parents=True,exist_ok=False)
    tree=hashlib.sha256()
    original_lines=reduced_lines=files=changed=0
    with subprocess.Popen(['git','-C',str(repo),'archive',REV],stdout=subprocess.PIPE) as proc:
        with tarfile.open(fileobj=proc.stdout,mode='r|') as archive:
            for entry in archive:
                if entry.isdir():
                    continue
                path=Path(entry.name)
                if not entry.isfile() or path.is_absolute() or '..' in path.parts:
                    raise RuntimeError(f'Unexpected source archive member {entry.name}')
                data=archive.extractfile(entry).read()
                if entry.name.startswith('src/') and entry.name.endswith('.lean'):
                    original_lines+=data.count(b'\n')
                    rel=entry.name[4:]
                    if rel in edits:
                        lines=data.decode().splitlines(keepends=True)
                        stop=len(lines)
                        for start,count,text in reversed(edits.pop(rel)):
                            if start<0 or count<0 or start+count>stop:
                                raise RuntimeError(f'Invalid source edit for {rel}')
                            lines[start:start+count]=[text]
                            stop=start
                        data=''.join(lines).encode()
                        changed+=1
                    files+=1
                    reduced_lines+=data.count(b'\n')
                    tree.update(rel.encode()+b'\0'+hashlib.sha256(data).digest())
                if output is not None:
                    target=output/path
                    target.parent.mkdir(parents=True,exist_ok=True)
                    target.write_bytes(data)
        if proc.wait():
            raise RuntimeError(f'git archive {REV} failed')
    if edits:
        raise RuntimeError('Source edits remained unapplied')
    result={'source_revision':REV,'source_files':files,'changed_files':changed,'original_lines':original_lines,
            'reduced_lines':reduced_lines,'tree_sha256':tree.hexdigest()}
    expected=json.loads((HERE/'measurements.json').read_text())['source']
    for key,value in result.items():
        if expected[key]!=value:
            raise RuntimeError(f'{key} mismatch. Expected {expected[key]}, found {value}')
    return result

if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('repo',type=Path,help='local clone of leanprover-community/riemann-hypothesis')
    p.add_argument('output',type=Path,nargs='?',help='new directory to create; omit to audit without writing')
    args=p.parse_args()
    print(json.dumps(run(args.repo,args.output),sort_keys=True))
