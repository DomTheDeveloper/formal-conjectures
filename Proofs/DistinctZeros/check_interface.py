"""Check the corollary with its published quantitative input as a theorem parameter."""

import argparse
import hashlib
import json
import re
import urllib.request
from pathlib import Path

HERE = Path(__file__).resolve().parent
RAW = "https://raw.githubusercontent.com"
FC = f"{RAW}/google-deepmind/formal-conjectures/f606af160664c5a10952e9a957b100a1cd45bbeb"
SCORER = f"{RAW}/anthropics/formal-math/3635e74826a4c1fcece7d1cd2b6fa75e43a00510"
RECORD = f"{RAW}/josusanmartin/riemann/d4d280813d0b4f2a8fbb89229755b24f1dfee63e"
THEOREM = "riemannZeta.distinct_prop_lt"


def fetch(url, sha256):
    with urllib.request.urlopen(url, timeout=90) as response:
        source = response.read()
    if hashlib.sha256(source).hexdigest() != sha256:
        raise ValueError(f"Unexpected source digest for {url}")
    return source.decode()


def definition(source, name):
    match = re.search(rf"^(?:noncomputable )?def {name}\b.*?(?=\n\s*\n)", source, re.M | re.S)
    if not match:
        raise ValueError(f"Missing definition {name}")
    return match.group() + "\n"


def reference():
    counting = fetch(
        f"{FC}/FormalConjecturesForMathlib/NumberTheory/RiemannZetaZeros.lean",
        "2b7095f7bde68c18e8a8977594b4ceaa8aefd977545ac3a7304c934e566b02a0",
    )
    paper = fetch(
        f"{FC}/FormalConjectures/Paper/RiemannZetaZeros.lean",
        "6d51ff134cee051268522b86885f8bafeaca3ef6a964525fce7010f3f98900b1",
    )
    target = paper.split("theorem distinct_prop_lt :", 1)[1].split(" := by", 1)[0]
    names = ("nontrivialZeros", "N", "Nd", "montgomeryTaylorConst")
    return (
        "import Mathlib\n\nnamespace Complex\n" + definition(counting, "zeroCountOn")
        + "end Complex\nnamespace ZetaZeros\n" + "".join(definition(paper, n) for n in names)
        + f"end ZetaZeros\nopen Filter ZetaZeros\ntheorem {THEOREM} :" + target + " := by sorry\n"
    )


def with_score_parameter(source, score):
    prefix = f"theorem {THEOREM} :"
    if source.count(prefix) != 1:
        raise ValueError("Expected one target declaration")
    return source.replace(prefix, f"theorem {THEOREM} (candidate_critical_line_bound : {score}) :")


def interface_pair(ref):
    counts = fetch(
        f"{SCORER}/comparator/ChallengeDeps.lean",
        "f05666d0745edbf2dac6ce2a4de675abd1bba3c336fe24aebb80f27d1365ebbd",
    )
    src = fetch(
        f"{RECORD}/submissions/knausgard-rh-reflected-kernel-8542/proof/Solution.lean",
        "57ee6e4def6c05145ce8196f49ce6302b211a24fa4feb091afbd732db93a12f3",
    )
    score = src.split("theorem candidate_critical_line_bound :", 1)[1].split(" := by", 1)[0].strip()
    # Preserve the scope of namespace openings when combining the independent modules.
    header = counts.replace("import Mathlib", "import Mathlib\nsection", 1) + "\nend\n"
    header += "noncomputable def candidateKappa : ℝ := (854225 : ℝ) / 1000000\n"
    bridge = (HERE / "Bridge.lean").read_text().split("import Mathlib\n", 1)[1]
    result = (HERE / "Result.lean").read_text().split("import Solution.Candidate\n", 1)[1]
    proof = header + bridge + with_score_parameter(result, score)
    expected = header + with_score_parameter(ref.removeprefix("import Mathlib\n"), score)
    return proof, expected


def check(proof, expected, version, *, negative=False):
    payload = {"content": proof, "formal_statement": expected, "environment": version,
               "use_def_eq": True, "ignore_imports": False, "timeout_seconds": 160}
    request = urllib.request.Request("https://axle.axiommath.ai/api/v1/verify_proof",
                                     data=json.dumps(payload).encode(),
                                     headers={"Content-Type": "application/json"})
    with urllib.request.urlopen(request, timeout=210) as response:
        verdict = json.load(response)
    failed = verdict["failed_declarations"]
    messages = verdict["lean_messages"]
    if negative:
        passed = not verdict["okay"] and failed == [THEOREM] and not messages["errors"]
    else:
        axiom_report = re.search(r"depends on axioms: \[([^\]]*)\]", "\n".join(messages["infos"]))
        passed = (verdict["okay"] and not failed and not messages["errors"] and not messages["warnings"]
                  and axiom_report and set(axiom_report[1].split(", ")) ==
                  {"propext", "Classical.choice", "Quot.sound"})
    if not passed:
        raise RuntimeError(json.dumps(verdict, ensure_ascii=False))
    print(version, "negative control rejected" if negative else "passed", verdict["info"]["request_id"])


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--print-reference", action="store_true",
                        help="emit the unconditional DeepMind target for kernel-export comparison")
    args = parser.parse_args()
    ref = reference()
    if args.print_reference:
        print(ref, end="")
    else:
        proof, expected = interface_pair(ref)
        for version in ("lean-4.33.1", "lean-4.35.0"):
            check(proof, expected, version)
        altered = expected.replace("∀ T > 0, (c - o T)", "∀ T ≥ 0, (c - o T)")
        if altered == expected:
            raise ValueError("Negative control did not change the target")
        check(proof, altered, "lean-4.35.0", negative=True)
