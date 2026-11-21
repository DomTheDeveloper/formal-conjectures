"""Check proof sharing and its negative control with the unmodified Lean kernel."""
import argparse
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
from catalog import catalog
from dictionary import prepare, select

def fixture():
    # The proposition is ∀ P : Prop, P → P. Its proof is fun P h => h.
    rows = [{'meta': {'exporter': {'name':'lean4export', 'version':'3.1.0'},
                      'lean': {'githash':'', 'version':'4.33.1'}, 'format':{'version':'3.1.0'}}}]
    for i, n in enumerate(['P', 'firstProof', 'secondProof', 'publicResult', 'usesResult'], 1):
        rows.append({'in':i, 'str':{'pre':0,'str':n}})
    rows.extend([{'ie':0,'sort':0},{'ie':1,'bvar':0},{'ie':2,'bvar':1}])
    def binder(i, kind, name, typ, body):
        return {'ie':i,kind:{'name':name,'type':typ,'body':body,'binderInfo':'default'}}
    def theorem(name, proof):
        return {'thm':{'name':name,'type':4,'value':proof,'all':[name],'levelParams':[]}}
    rows.extend([binder(3,'forallE',0,1,2),binder(4,'forallE',1,0,3),
                 binder(5,'lam',0,1,1),binder(6,'lam',1,0,5),theorem(2,6),
                 {'ie':7,'const':{'name':2,'us':[]}},theorem(3,7),
                 {'ie':8,'const':{'name':3,'us':[]}},theorem(4,8)])
    rows.extend([{'ie':9,'const':{'name':4,'us':[]}},binder(10,'forallE',0,4,4),
                 binder(11,'lam',0,4,9),{'thm':{'name':5,'all':[5],'levelParams':[],'type':10,'value':11}}])
    # The duplicate lambda has exactly the same children and binder annotations.
    rows.insert(-1, binder(12,'lam',0,4,9))
    rows[-1]['thm']['value']=12
    return rows

def main():
    args = argparse.ArgumentParser(description=__doc__)
    args.add_argument('--checker', default='leanchecker')
    opts = args.parse_args()
    checker = shutil.which(opts.checker)
    if not checker:
        raise SystemExit('Lean 4.36 leanchecker is required')
    with tempfile.TemporaryDirectory() as d:
        root = Path(d)
        index = root/'index'
        raw = b''.join((json.dumps(x,sort_keys=True,separators=(',',':'))+'\n').encode() for x in fixture())
        original = root/'original.ndjson'
        original.write_bytes(raw)
        stats = catalog(raw.splitlines(), index)
        assert stats['duplicate_theorem_types'] == 2
        binary = root/'slice'
        subprocess.run(['g++','-std=c++20','-O2',str(HERE/'slice.cpp'),'-lzstd','-o',str(binary)],check=True)
        subprocess.run([binary,'index',index],input=raw,check=True)
        subprocess.run([checker,'--from-export',original],check=True)
        rewritten=subprocess.check_output([binary,'intern','12'],input=raw)
        distinct=root/'interned.ndjson'
        distinct.write_bytes(rewritten)
        assert sum('"ie":' in x for x in rewritten.decode().splitlines()) == 12
        subprocess.run([checker,'--from-export',distinct],check=True)
        for mode, expected in [('plain',3),('share',1)]:
            dest=root/mode
            subprocess.run([binary,'mark',index,dest,mode],input=b'4\n',check=True)
            new = subprocess.check_output([binary,'emit',index,dest],input=raw)
            proof=root/(mode+'.ndjson')
            proof.write_bytes(new)
            parsed = [json.loads(line) for line in new.splitlines()]
            assert sum('thm' in d for d in parsed) == expected
            assert parsed[-1]['thm']['name'] == 4
            subprocess.run([checker,'--from-export',proof],check=True)
        # The allocator places every proof in its own interval. Only prior intervals
        # can supply a temporary theorem header to a later one.
        prepare(index, [line for line in raw.splitlines() if b'"in":' in line or line.startswith(b'{"thm":')])
        subprocess.run([binary,'mark',index,root/'whole', 'plain'],input=b'5\n',check=True)
        for part in range(4):
            dest=root/f'part-{part}'
            subprocess.run([binary,'shard',index,root/'whole',dest,str(part),'4'],input=b'',check=True)
            select(index,dest)
            part_raw=subprocess.check_output([binary,'emit',index,dest],input=raw)
            candidate=root/f'part-{part}.ndjson'
            candidate.write_bytes(part_raw)
            subprocess.run([checker,'--from-export',candidate],check=True)
            cut=[int(n) for n in (dest/'cut.txt').read_text().split()]
            assert cut[:4] == [part,4,part,part+1]
            if part==3:
                assert cut[4]==1 and b'"axiom"' in part_raw
        # Replacing the body by Prop gives the wrong type and the kernel must reject it.
        parsed[-1]['thm']['value'] = 0
        broken=root/'broken.ndjson'
        broken.write_text(''.join(json.dumps(x,separators=(',',':'))+'\n' for x in parsed))
        negative = subprocess.run([checker,'--from-export',broken],capture_output=True,text=True)
        if negative.returncode == 0 or 'mismatch' not in (negative.stderr+negative.stdout).lower():
            raise RuntimeError(f'Invalid proof negative control failed: {negative}')
        pipe_control = subprocess.run([checker,'--from-export','/dev/stdin'],input=broken.read_text(),capture_output=True,text=True)
        if pipe_control.returncode == 0 or 'mismatch' not in (pipe_control.stdout+pipe_control.stderr).lower():
            raise RuntimeError('Checker did not reject the invalid proof on standard input')
        print('Both slices and all fixture parts passed. Lean rejected the mistyped proof from a file and a pipe.')

if __name__ == '__main__':
    main()
