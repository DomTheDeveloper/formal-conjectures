"""Extract the original ordinary-RH challenge, preserving its mathematical declarations byte for byte."""
from hashlib import sha256
from pathlib import Path
import json
import sys

from link_tail import HEADLINES, read_zstd, component

CHALLENGE_SHA = 'bd484ac9886a96f26b1d9a7a59ebd45b7a70d102c015d4f31f9302bbdd6ab2b9'

def extract(original, result):
    names = ['']
    found = set()
    types = {}
    digest = sha256()
    with result.open('wb') as out:
        for raw in read_zstd(original):
            digest.update(raw)
            if raw.startswith(b'{"in":'):
                row = json.loads(raw)
                parent, name = component(row)
                if row['in'] != len(names):
                    raise ValueError('Name index mismatch')
                names.append((names[parent] + '.' if parent else '') + str(name))
            if raw.startswith((b'{"axiom":', b'{"thm":')):
                row = json.loads(raw)
                key, = row
                n = names[row[key]['name']]
                if n in HEADLINES:
                    found.add(n)
                    types[n] = key
                    if n != 'riemannHypothesis':
                        continue
            out.write(raw)
    if digest.hexdigest() != CHALLENGE_SHA or found != HEADLINES:
        raise ValueError('Official challenge hash or target set differs')
    print(json.dumps(types, sort_keys=True))

if __name__ == '__main__':
    extract(Path(sys.argv[1]), Path(sys.argv[2]))
