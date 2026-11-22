"""Count the original project files that supply constants to the five published proof terms."""
import csv
import gzip
import hashlib
import json
from pathlib import Path
import sys

sys.path.insert(0,str(Path(__file__).resolve().parents[1]/"reflection-imports"))
from trim import CONSTANTS, SOURCE, read_graph

def count(original, catalog):
    graph,sizes=read_graph(original)
    with catalog.open("rb") as f:
        if hashlib.file_digest(f,"sha256").hexdigest()!=CONSTANTS:
            raise ValueError("Unexpected complete constant inventory")
    owners=set()
    referenced=total=0
    with gzip.open(catalog,"rt",newline="") as f:
        for row in csv.DictReader(f):
            total+=1
            if row["origin"]!="project" or row["in_cone"]!="true":
                continue
            if row["in_export"]!="true" or row["module"] not in graph:
                raise ValueError("A referenced project constant lacks its original source")
            owners.add(row["module"])
            referenced+=1
    original_lines=sum(sizes.values())
    retained=sum(sizes[n] for n in owners)
    if total!=1484733 or (len(graph),original_lines,referenced,len(owners),retained)!=(175187,17374215,1270184,146440,15027884):
        raise ValueError("Source or proof inventory totals differ")
    return {"upstream_commit":SOURCE,"catalog_sha256":CONSTANTS,"original_lean_files":len(graph),
            "original_lean_lines":original_lines,"catalog_rows":total,"referenced_project_constants":referenced,
            "files_supplying_a_referenced_constant":len(owners),"lines_in_those_original_files":retained,
            "other_original_files":len(graph)-len(owners),"lines_in_other_original_files":original_lines-retained}

if __name__=="__main__":
    print(json.dumps(count(*map(Path,sys.argv[1:])),indent=2))
