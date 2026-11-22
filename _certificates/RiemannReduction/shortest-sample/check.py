"""Kernel-replay all 104 source replacements after both closed projects have compiled."""
import json
import os
from pathlib import Path
import subprocess
import sys

HERE=Path(__file__).resolve().parent
work=Path(sys.argv[1]).resolve()
spec=json.loads((work/"selection.json").read_text())
roots=spec["roots"]
paths=[]
for module in roots:
    rel=Path(*module.split(".")).with_suffix(".olean")
    a,b=[work/stage/".lake/build/lib/lean"/rel for stage in ("original","shortened")]
    if not a.is_file() or not b.is_file(): raise ValueError(f"Missing compiled file {module}")
    paths.append("\t".join([module,str(a),str(b)]))
    subprocess.run(["leanchecker",module],cwd=work/"shortened",env=os.environ,check=True)
pairs=work/"pairs.tsv"
pairs.write_text("\n".join(paths)+"\n")
report=work/"public-comparisons.jsonl"
subprocess.run(["lean","-DmaxRecDepth=100000","--run",str(HERE/"Compare.lean"),str(pairs),str(report)],check=True)
rows=[json.loads(r) for r in report.read_text().splitlines()]
if len(rows)!=104 or [r["module"] for r in rows]!=roots or any(r["differences"] for r in rows):raise ValueError("Incomplete public comparison")
out={"original_source_lines":spec["original_lines"],"revised_source_lines":spec["shortened_lines"],
     "closed_project_modules":len(spec["project_modules"]),"revised_proof_files":len(roots),"native_replays":len(rows),
     "identical_public_kernel_records":sum(r["identicalPublicRecords"] for r in rows),
     "revised_proofs_with_identical_public_types":sum(r["newProofsWithOriginalType"] for r in rows)}
(work/"verdict.json").write_text(json.dumps(out,indent=2)+"\n")
print(json.dumps(out,indent=2),flush=True)
