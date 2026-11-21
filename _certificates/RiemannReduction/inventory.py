"""Count retained constants and verify public roots against the export's own name table."""
from array import array
import argparse
from collections import Counter
import json
from pathlib import Path
import struct
import sys
from catalog import TARGETS

def inventory(directory, selections):
    bits = {s.name:(s/'decls.bits').read_bytes()[4:] for s in selections}
    stats = {s.name:{'retained_constants':Counter(),'axioms':[],'public_roots':[]} for s in selections}
    table=array('I')
    with (directory/'declarations.bin').open('rb') as f:
        table.fromfile(f,(directory/'declarations.bin').stat().st_size//4)
    if sys.byteorder!='little':
        table.byteswap()
    p=i=0
    with (directory/'names.tsv').open() as names:
        while p<len(table):
            nn,ne,nr,_=table[p:p+4]
            for j in range(nn):
                n,k,name=next(names).rstrip('\n').split('\t',2)
                if int(n)!=table[p+4+j]:
                    raise ValueError('Declaration/name order mismatch')
                for profile,mask in bits.items():
                    if mask[i//8] & (1<<(i%8)):
                        out=stats[profile]
                        out['retained_constants'][k]+=1
                        if k=='axiom': out['axioms'].append(name)
                        if name in TARGETS:
                            if k!='thm': raise ValueError(f'{name} is not a theorem')
                            out['public_roots'].append(name)
            i+=1; p+=4+nn+ne+nr
        if next(names,None) is not None:
            raise ValueError('Extra names')
    return stats

if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('index',type=Path);p.add_argument('selections',type=Path,nargs='+')
    args=p.parse_args()
    print(json.dumps(inventory(args.index,args.selections),indent=2,sort_keys=True))
