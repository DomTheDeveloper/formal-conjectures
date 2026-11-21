"""Check coverage and the direction of the temporary theorem assumptions in a proof part."""
import argparse
import json
from pathlib import Path
import struct

def bits(path):
    data=path.read_bytes()
    count,=struct.unpack_from('<I',data)
    if len(data)!=4+8*((count+63)//64):
        raise ValueError('wrong bitset size')
    return count, int.from_bytes(data[4:],'little')

def audit(index, whole, part):
    ordinal, parts, lo, hi, nstubs=map(int,(part/'cut.txt').read_text().split())
    n, original=bits(whole/'decls.bits')
    _, actual=bits(part/'decls.bits')
    _, headers=bits(part/'stubs.bits')
    if (lo,hi)!=(n*ordinal//parts,n*(ordinal+1)//parts):
        raise ValueError('incorrect interval')
    span=((1<<(hi-lo))-1)<<lo
    if (actual & span)!=(original & span) or actual & ~original:
        raise ValueError('missing owned declaration or unexpected dependency')
    if (headers>>lo) or headers & ~actual or headers.bit_count()!=nstubs:
        raise ValueError('non-earlier or absent proof at a cut')
    kinds=(index/'declaration-kinds.bin').read_bytes()
    names=(index/'names.tsv').open()
    with names:
        axioms=sorted(line.rstrip('\n').split('\t',2)[2] for line in names if '\taxiom\t' in line)
    if axioms!=['Classical.choice','Quot.sound','propext']:
        raise ValueError('unexpected original axioms')
    if len(kinds)!=n:
        raise ValueError('wrong kind table')
    header_bytes=headers.to_bytes((n+7)//8,'little')
    if any(not kinds[i] for i in range(lo) if (header_bytes[i//8] >> (i%8)) & 1):
        raise ValueError('a temporary assumption was not a theorem')
    xcount, exprs=bits(part/'exprs.bits')
    return dict(part=ordinal+1,parts=parts,first_record=lo,end_record=hi,
                owned_records=(original & span).bit_count(),total_records=actual.bit_count(),
                temporary_theorem_headers=nstubs,expressions=exprs.bit_count(),
                foundation_axioms=axioms)
if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    for name in ['index','whole','part']: p.add_argument(name,type=Path)
    a=p.parse_args()
    print(json.dumps(audit(a.index,a.whole,a.part),sort_keys=True))
