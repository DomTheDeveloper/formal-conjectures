"""Build 2,133 native proof checks using the actual source theorem types and universe binders."""
import argparse
import json
import lzma
from pathlib import Path
import subprocess

HERE=Path(__file__).resolve().parent

def prepare(index, work):
    with lzma.open(HERE/'source-reuse.json.xz','rt') as f:
        pairs=json.load(f)
    wanted={n for pair in pairs for n in pair}
    names={}
    with (index/'names.tsv').open() as f:
        for line in f:
            i,k,n=line.rstrip('\n').split('\t',2)
            if n in wanted:
                if k!='thm' or n in names: raise ValueError(n)
                names[n]=int(i)
    if len(wanted)!=len(names): raise ValueError('missing source theorem')
    ids=set(names.values())
    types={}
    with subprocess.Popen(['zstd','-dcq',str(index/'names-declarations.zst')],stdout=subprocess.PIPE) as z:
        for row in z.stdout:
            if row.startswith(b'{"thm":'):
                t=json.loads(row)['thm']
                if t['name'] in ids: types[t['name']]=(t['type'],t['levelParams'])
        if z.wait(): raise RuntimeError('decompression failed')
    records=[]
    for target,provider in pairs:
        t,p=names[target],names[provider]
        if types[t]!=types[p]:
            raise ValueError(f'Proposition or universe mismatch between {target} and {provider}')
        records.append((p,*types[t]))
    work.mkdir(parents=True,exist_ok=True)
    (work/'reused.json').write_text(json.dumps(records,separators=(',',':')))
    (work/'required.txt').write_text(''.join(f'{i}\n' for i in sorted(ids)))
    print(f'{len(records)} proposition and universe signatures matched')

def ranks(path,queries):
    raw=memoryview(path.read_bytes())[4:]
    answer={}
    pos=seen=0
    for n in sorted(set(queries)):
        i,b=divmod(n,8)
        seen+=int.from_bytes(raw[pos:i],'little').bit_count()
        if not raw[i] & (1<<b): raise ValueError(f'{path} missing reference {n}')
        answer[n]=seen+(raw[i] & ((1<<b)-1)).bit_count()
        pos=i
    return answer, seen+int.from_bytes(raw[pos:],'little').bit_count()

def append(work):
    specs=json.loads((work/'reused.json').read_text())
    levels={}
    for line in (work/'universe-levels.ndjson').read_text().splitlines():
        rec=json.loads(line)
        levels[rec['param']]=rec['il']
    names,count=ranks(work/'dictionary.bits',[n for p,_,us in specs for n in [p,*us]])
    exprs,first=ranks(work/'exprs.bits',[t for _,t,_ in specs])
    def emit(row): print(json.dumps(row,sort_keys=True,separators=(',',':')))
    emit({'in':count,'str':{'pre':0,'str':'RiemannReduction_SourceTypeAudit_20261121'}})
    for i,(p,t,us) in enumerate(specs):
        n=count+1+i
        emit({'in':n,'num':{'pre':count,'i':i}})
        emit({'ie':first+i,'const':{'name':names[p],'us':[levels[u] for u in us]}})
        emit({'thm':{'name':n,'all':[n],'type':exprs[t],'value':first+i,'levelParams':[names[u] for u in us]}})

if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('operation',choices=['prepare','append'])
    p.add_argument('index',type=Path)
    p.add_argument('work',type=Path)
    args=p.parse_args()
    if args.operation=='prepare': prepare(args.index,args.work)
    else: append(args.work)
