"""Remove repeated section setup from the longest original Lean source while preserving theorem bodies."""
import argparse
import hashlib
import re
from pathlib import Path

NAME = "Formalism.HermitianCurvature.HermitianCurvatureProofs.IsAdmissibleSplittingCharPairMulTwist"
OPEN = re.compile(r"^(?:(?:noncomputable )?section(?:\s|$)|namespace\s)")
END = re.compile(r"^end(?:\s|$)")
LOCAL = re.compile(r"^(?:variable|include|omit|open|attribute|local|notation|set_option|universe|export|macro|syntax|elab)\b")
LINT = {"set_option linter.unusedVariables false", "set_option linter.unusedSimpArgs false"}

def pairs(lines):
    stack, scopes = [], []
    for i, line in enumerate(lines):
        if OPEN.match(line):
            node = {"start":i, "head":line, "end":None, "parent":stack[-1] if stack else None, "commands":[]}
            scopes.append(node)
            stack.append(node)
        elif END.match(line):
            stack.pop()["end"] = i
        elif stack and line and not line[0].isspace():
            stack[-1]["commands"].append(line)
    if stack:
        raise ValueError("Unclosed upstream scope")
    return scopes

def simplify(data):
    lines = data.decode().splitlines()
    drops = {i for i,l in enumerate(lines) if l in LINT}
    edits = {}
    for node in pairs(lines):
        head = node["head"]
        start,end = node["start"],node["end"]
        settings = [s for s in node["commands"] if LOCAL.match(s) and s not in LINT]
        if head.startswith("section S_") and not settings:
            drops.update((start,end))
        elif head == "noncomputable section":
            parent = node["parent"]
            last = parent is not None and all(not t.strip() for t in lines[end+1:parent["end"]])
            if last or not settings:
                drops.update((start,end))
            else:
                edits[start]="section"
    boundary=next(i for i,l in enumerate(lines) if not l.startswith('import '))
    result=lines[:boundary]+["","noncomputable section",*sorted(LINT)]
    blanks=[]
    removed_in_gap=False
    for i in range(boundary,len(lines)):
        if i in drops:
            removed_in_gap=True
            continue
        line=edits.get(i,lines[i])
        if not line:
            blanks.append(line)
            continue
        result.extend([""] if removed_in_gap and blanks else blanks)
        result.append(line)
        blanks=[]
        removed_in_gap=False
    result.extend(["","end"])
    return ("\n".join(result)+"\n").encode()

if __name__=="__main__":
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("original",type=Path)
    p.add_argument("output",type=Path)
    a=p.parse_args()
    data=a.original.read_bytes()
    if hashlib.sha256(data).hexdigest()!='1a3aa6ea239c03a0d40fe7e025a340fb941e368e07d0fb1db184eb4a5cc99e92':
        raise ValueError("Expected the pinned 17,981-line source file")
    new=simplify(data)
    a.output.parent.mkdir(parents=True,exist_ok=True)
    a.output.write_bytes(new)
    print(len(new.splitlines()),hashlib.sha256(new).hexdigest())
