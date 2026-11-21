"""Rebuild the longest source in isolation and compare every compiled declaration."""
import hashlib
import json
import os
import subprocess
import sys
from pathlib import Path
from shorten import NAME, simplify

HERE=Path(__file__).resolve().parent
REV="40e56bab026552e089d7afcfeff08d2defb9c005"
FLAGS=["-j1","--tstack=400000","-DautoImplicit=false","-DrelaxedAutoImplicit=false",
       "-DmaxSynthPendingDepth=3","-DmaxHeartbeats=4000000","-Dpp.unicode.fun=true"]

def path_of(module):
    return Path(*module.split(".")).with_suffix(".lean")

def main():
    repo,out=map(lambda x:Path(x).resolve(),sys.argv[1:])
    if subprocess.check_output(["git","-C",str(repo),"rev-parse","HEAD"],text=True).strip()!=REV:
        raise ValueError("Unexpected original commit")
    out.mkdir(parents=True,exist_ok=True)
    root=repo/"src"
    old=root/path_of(NAME)
    original=old.read_bytes()
    if hashlib.sha256(original).hexdigest()!="1a3aa6ea239c03a0d40fe7e025a340fb941e368e07d0fb1db184eb4a5cc99e92":
        raise ValueError("Unexpected original source bytes")
    view=out/"native"
    src=out/"src"
    new=src/path_of(NAME)
    new.parent.mkdir(parents=True,exist_ok=True)
    new.write_bytes(simplify(original))
    if hashlib.sha256(new.read_bytes()).hexdigest()!="ae6c20cdfefcb91c08cfc129f39ba68b7059b539cc2bf197cbe5ba396949b76b":
        raise ValueError("Rewritten source differs from the measured output")
    objects=repo/".lake/build/lib/lean"
    seen=set()
    pending=[NAME]
    while pending:
        name=pending.pop()
        if name in seen:continue
        source=root/path_of(name)
        if not source.is_file():continue
        seen.add(name)
        for line in source.read_text().splitlines():
            if line.startswith("import "):pending.extend(line.split()[1:])
    if len(seen)!=148:raise ValueError("Unexpected original module closure")
    for dep in sorted(seen-{NAME}):
        rel=path_of(dep).with_suffix(".olean")
        original_dep=objects/rel
        if not original_dep.is_file():raise FileNotFoundError(original_dep)
        dest=view/rel
        dest.parent.mkdir(parents=True,exist_ok=True)
        dest.symlink_to(original_dep)
    external=[Path(d).resolve() for d in os.environ["LEAN_PATH"].split(os.pathsep) if ".lake/packages/" in d]
    if not any((d/"Mathlib.olean").exists() for d in external) or any((d/"Formalism").exists() for d in external):
        raise RuntimeError("Expected external dependencies only")
    env=os.environ|{"LEAN_PATH":os.pathsep.join(map(str,[view,*external]))}
    rel=path_of(NAME).with_suffix(".olean")
    new_object=view/rel
    new_object.parent.mkdir(parents=True,exist_ok=True)
    if new_object.exists():raise RuntimeError("Original longest module is visible")
    subprocess.run(["lean",*FLAGS,"-R",str(src),"-o",str(new_object),str(new)],cwd=src,env=env,check=True)
    subprocess.run(["leanchecker","-v",NAME],cwd=src,env=env,check=True)
    cmp=subprocess.run(["lean","--run",str(HERE/"Compare.lean"),str(objects/rel),str(new_object)],check=True,stdout=subprocess.PIPE,text=True)
    result=json.loads(cmp.stdout.strip().splitlines()[-1])
    report={"module":NAME,"original_lines":original.count(b"\n"),"revised_lines":new.read_bytes().count(b"\n"),"original_project_prerequisites":len(seen)-1,
            "revised_source_sha256":hashlib.sha256(new.read_bytes()).hexdigest(),"kernel_replayed":True,"native_comparison":result}
    (out/"result.json").write_text(json.dumps(report,indent=2)+"\n")
    print(json.dumps(report,indent=2),flush=True)

if __name__=="__main__":
    main()
