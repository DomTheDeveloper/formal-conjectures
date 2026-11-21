"""Restore the authenticated project imports needed to elaborate chapters 1 through 16."""
from concurrent.futures import ThreadPoolExecutor
from hashlib import sha256
from pathlib import Path
import gzip
import json
import re
import subprocess
import sys
import time
import urllib.request

HOST = 'https://rh-cache.taucetiproject.org'
MANIFEST = HOST + '/bootstrap/e50d09817ad81469f737e8f637561e6ccf86c670/modules.jsonl.gz'
DIGEST = '292caa386a620d935cfc736b56fcceaab9fe7073086693b62e899c1ee4725f04'
IMPORT = re.compile(r'^\s*(?:(?:public|meta)\s+)*import\s+([\w.\x27]+)', re.M)
CHAPTERS = Path(__file__).resolve().parent / 'RH17'


def imports(project):
    queue = [name for f in sorted(CHAPTERS.glob('S*.lean'))[:-1]
             for name in IMPORT.findall(f.read_text())]
    found = set()
    while queue:
        name = queue.pop()
        if name in found:
            continue
        path = (project / 'src' / name.replace('.', '/')).with_suffix('.lean')
        if path.is_file():
            found.add(name)
            queue.extend(IMPORT.findall(path.read_text()))
    if len(found) != 1418:
        raise ValueError(f'The pinned source import graph changed: {len(found)} modules')
    return found


def get(url, expected):
    for attempt in range(4):
        try:
            request = urllib.request.Request(url, headers={'User-Agent': 'RiemannHypothesisCache/1.0'})
            with urllib.request.urlopen(request, timeout=90) as stream:
                data = stream.read()
            if sha256(data).hexdigest() != expected:
                raise ValueError(f'Unexpected SHA-256 for {url}')
            return data
        except OSError:
            if attempt == 3:
                raise
            time.sleep(2 ** attempt)


def restore(project, tmp, leantar):
    found = imports(project)
    rows = gzip.decompress(get(MANIFEST, DIGEST)).splitlines()
    header = json.loads(rows[0])
    tree = subprocess.check_output(['git', '-C', project, 'rev-parse', 'HEAD:src'], text=True).strip()
    if header['source_tree'] != tree or header['toolchain'] != 'leanprover/lean4:v4.33.1':
        raise ValueError('The cache source tree or toolchain differs from the checkout')
    selected = [r for line in rows[1:] if (r := json.loads(line))[0] in found]
    if {r[0] for r in selected} != found or len(selected) != len(found):
        raise ValueError('Incomplete module inventory')
    tmp.mkdir(parents=True, exist_ok=True)

    def archive(row):
        name, dep_hash, blob, digest = row
        if not re.fullmatch(r'[\da-f]{16}\.ltar', blob):
            raise ValueError('Unexpected cache artifact name')
        path = tmp / blob
        if not path.is_file() or sha256(path.read_bytes()).hexdigest() != digest:
            url = HOST + '/artifacts/leanprover-community/riemann-hypothesis/' + blob[:-5] + '.art'
            path.write_bytes(get(url, digest))
        module = Path(*name.split('.')).parent
        dirs = [project / '.lake/build' / d / module for d in ['lib/lean', 'ir']]
        for d in dirs:
            d.mkdir(parents=True, exist_ok=True)
        return dict(file=str(path), hash=dep_hash, base=list(map(str, dirs)))

    with ThreadPoolExecutor(max_workers=12) as pool:
        jobs = list(pool.map(archive, selected))
    subprocess.run([leantar, '--jobs', '4', '-f', '-x', '-j', '-'], input=json.dumps(jobs),
                   text=True, cwd=project, check=True)
    print(f'Restored {len(jobs)} pinned original project imports')


def build_from_source(project):
    targets = {name for f in sorted(CHAPTERS.glob('S*.lean'))[:-1]
               for name in IMPORT.findall(f.read_text())
               if (project / 'src' / name.replace('.', '/')).with_suffix('.lean').is_file()}
    subprocess.run(['lake', 'build', *['+' + name + ':olean' for name in sorted(targets)]],
                   cwd=project, check=True)


if __name__ == '__main__':
    project = Path(sys.argv[1]).resolve()
    try:
        restore(project, Path(sys.argv[2]).resolve(), sys.argv[3])
    except OSError as exc:
        print(f'Project cache unavailable ({exc}). Compiling all 1,418 imports from source.', flush=True)
        build_from_source(project)
