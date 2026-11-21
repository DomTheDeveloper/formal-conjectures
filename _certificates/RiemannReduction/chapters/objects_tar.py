"""Stream the authenticated original project objects into a mountable image."""
import hashlib
import json
from pathlib import Path
import runpy
import subprocess
import sys
import tarfile


class HashedReader:
    def __init__(self, stream):
        self.stream = stream
        self.digest = hashlib.sha256()

    def read(self, size):
        data = self.stream.read(size)
        self.digest.update(data)
        return data


def write_objects(source, target, expected, helpers):
    prefix = helpers['PREFIX']
    retained = checked = byte_count = 0
    with tarfile.open(fileobj=source, mode='r|', bufsize=1 << 20) as archive, \
            tarfile.open(fileobj=target, mode='w|', bufsize=1 << 20) as output:
        output.copybufsize = 256 << 10
        for member in archive:
            if member.isdir():
                continue  # tar2sqfs creates the directories for retained paths.
            name = helpers['clean_path'](member.name)
            digest = expected.pop(name, None)
            if not member.isfile() or digest is None:
                raise ValueError(f'Unexpected or duplicate input file {name}')
            with archive.extractfile(member) as payload:
                reader = HashedReader(payload)
                if name.endswith('.olean'):
                    info = tarfile.TarInfo(name.removeprefix(prefix))
                    info.mode, info.size = 0o444, member.size
                    output.addfile(info, reader)
                    retained += 1
                    byte_count += info.size
                else:
                    while reader.read(1 << 20):
                        pass
                if reader.digest.hexdigest() != digest:
                    raise ValueError(f'Published object SHA-256 mismatch for {name}')
            checked += 1
            if checked % 25000 == 0:
                print(f'Authenticated {checked} published files', file=sys.stderr, flush=True)
        if expected:
            raise ValueError(f'Missing {len(expected)} published files')
    return dict(checked=checked, retained=retained, retained_bytes=byte_count)


def main():
    upstream, directory = map(Path, sys.argv[1:])
    helpers = runpy.run_path(str(upstream))
    archive = directory / 'oleans.tar.zst'
    manifest = directory / 'olean-manifest.sha256'
    for path in (manifest, archive):
        helpers['verify_download'](path, path.name)
    expected = helpers['read_manifest'](manifest)
    with subprocess.Popen(['zstd', '-dcq', '--long=31', archive], stdout=subprocess.PIPE) as decoder:
        try:
            counts = write_objects(decoder.stdout, sys.stdout.buffer, expected, helpers)
            while decoder.stdout.read(1 << 20):
                pass
        finally:
            decoder.stdout.close()
        if decoder.wait() != 0:
            raise ValueError('Decompression failed')
    if counts['checked'] != 350374 or counts['retained'] != 175187:
        raise ValueError(f'Unexpected published inventory: {counts}')
    print(json.dumps(counts), file=sys.stderr, flush=True)


if __name__ == '__main__':
    main()
