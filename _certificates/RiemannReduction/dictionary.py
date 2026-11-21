"""Keep structural constant and universe names, together with each name's parents."""
from array import array
import argparse
import json
from pathlib import Path
import struct
import sys

def prepare(directory, stream):
    parents = array('I', [0])
    levels = set()
    for raw in stream:
        entry = json.loads(raw)
        if 'in' in entry:
            if entry['in'] != len(parents):
                raise RuntimeError('name index mismatch')
            parents.append(entry.get('str', entry.get('num'))['pre'])
        else:
            tag, value = next(iter(entry.items()))
            if isinstance(value,list):
                value = value[0]
            members = value['types'] + value['ctors'] + value['recs'] if tag == 'inductive' else [value]
            for member in members:
                levels.update(member['levelParams'])
    if sys.byteorder != 'little':
        parents.byteswap()
    with (directory/'name-parents.bin').open('wb') as f:
        parents.tofile(f)
    (directory/'universe-names.json').write_text(json.dumps(sorted(levels)))

def select(directory, selection):
    parents = array('I')
    with (directory/'name-parents.bin').open('rb') as f:
        parents.fromfile(f,(directory/'name-parents.bin').stat().st_size//4)
    if sys.byteorder != 'little':
        parents.byteswap()
    raw = (selection/'names.bits').read_bytes()
    count, = struct.unpack_from('<I', raw)
    if count != len(parents):
        raise ValueError('incorrect name table')
    bits = bytearray(raw[4:])
    def put(n):
        bits[n//8] |= 1 << (n%8)
    put(0)
    for n in json.loads((directory/'universe-names.json').read_text()):
        put(n)
    for n in range(count-1,0,-1):
        if bits[n//8] & (1 << (n%8)):
            put(parents[n])
    (selection/'dictionary.bits').write_bytes(raw[:4]+bits)
    print(f'{sum(b.bit_count() for b in bits)} names retained out of {count}')

if __name__ == '__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('index',type=Path)
    p.add_argument('selection',type=Path,nargs='?')
    args=p.parse_args()
    if args.selection:
        select(args.index,args.selection)
    else:
        prepare(args.index,sys.stdin.buffer)
