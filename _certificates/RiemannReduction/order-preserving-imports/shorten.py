"""Remove earlier-reachable public imports while preserving all retained Lean proof bodies."""
import argparse
import hashlib
import io
import json
import lzma
import subprocess
import sys
import tarfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / "reflection-imports"))
from trim import archive_output

INPUT = "8df99505773cd2a1e92e7904788a84181eda4216117a39f57870511c6e1a591e"
PATCH = "ea94f686d91aa6faac1908ea6493d51e642f9311f8f7152a6f4b222ef5e7bdfd"

def sha(path):
    with path.open("rb") as handle:
        return hashlib.file_digest(handle, "sha256").hexdigest()

def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("input_archive", type=Path)
    p.add_argument("output", type=Path)
    args = p.parse_args()
    patch = HERE.parent / "source-edits.jsonl.xz"
    if sha(args.input_archive) != INPUT or sha(patch) != PATCH:
        raise ValueError("Pinned input or rewrite inventory mismatch")
    with lzma.open(patch, "rt") as f:
        edits = dict(json.loads(row) for row in f)
    out = args.output.resolve()
    out.mkdir(parents=True, exist_ok=True)
    revised = out / "changed-src"
    revised.mkdir(exist_ok=False)
    output_archive = out / "Riemann_Proof_Preserving_Source.tar.zst"
    modules = []
    files = lines = changed = deleted = 0
    digest = hashlib.sha256()
    with subprocess.Popen(["zstd", "-qdc", str(args.input_archive)], stdout=subprocess.PIPE) as decoder:
        with tarfile.open(fileobj=decoder.stdout, mode="r|", bufsize=1<<20) as input_tar, archive_output(output_archive) as output_tar:
            for item in input_tar:
                path = item.name
                data = input_tar.extractfile(item).read()
                if path.startswith("src/") and path.endswith(".lean"):
                    rel = path[4:]
                    files += 1
                    if rel != "Main.lean":
                        modules.append(rel)
                    proposed = edits.get(rel) if rel != "Main.lean" else None
                    if proposed:
                        before = data.splitlines(keepends=True)
                        stop = next((i for i,l in enumerate(before) if not l.startswith(b"import ")),len(before))
                        header = before[:stop]
                        drops = [(start,count) for start,count,txt in proposed
                                 if not txt and 0 <= start < start+count <= stop]
                        if drops:
                            last = len(header)
                            for start,count in reversed(drops):
                                if start+count > last:
                                    raise ValueError(f"Overlapping import edits in {rel}")
                                del header[start:start+count]
                                last = start
                                deleted += count
                            changed += 1
                            # The body after the contiguous initial import list is copied without any edit.
                            data = b"".join(header) + b"".join(before[stop:])
                            dest = revised / rel
                            dest.parent.mkdir(parents=True,exist_ok=True)
                            dest.write_bytes(data)
                    lines += data.count(b"\n")
                digest.update(path.encode()+b"\0"+hashlib.sha256(data).digest())
                meta = tarfile.TarInfo(path)
                meta.size = len(data)
                output_tar.addfile(meta,io.BytesIO(data))
        if decoder.wait():
            raise RuntimeError("Failed to read input archive")
    if (files,lines,changed,deleted,len(modules))!=(164452,16360125,75620,228053,164451):
        raise ValueError("File, line or import count mismatch")
    (out/"external-paths.txt").write_text("".join(p+"\n" for p in sorted(modules)))
    report={"original_source_lines":17374215,"remaining_lines":lines,"lines_removed":17374215-lines,
            "remaining_files":files,"unchanged_root_sha256":"06d4c700d45a64cb67354449b0dc38156d872000f8adf98700fdd7df2db88dc1",
            "extra_import_lines_removed":deleted,"changed_external_headers":changed,
            "external_modules":len(modules),"source_sha256":digest.hexdigest(),"archive_sha256":sha(output_archive)}
    (out/"source.json").write_text(json.dumps(report,indent=2)+"\n")
    print(json.dumps(report,indent=2))

if __name__=="__main__":
    main()
