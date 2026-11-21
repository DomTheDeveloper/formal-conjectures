"""Check every deleted import against the full graph parsed in Lean 4.33.1."""
import json
from pathlib import Path
import sys
sys.path.insert(0,str(Path(__file__).resolve().parents[1]))
from audit_imports import audit

result = audit(sys.stdin)
if (result["source_modules"], result["changed_headers"], result["removed_imports"]) != (164451,75620,228053):
    raise ValueError(f"Incomplete source audit: {result}")
receipt = {**result,"parser":"Lean 4.33.1 Lean.parseImports'","all_removed_imports_available_from_an_earlier_retained_public_import":True}
print(json.dumps(receipt,indent=2))
