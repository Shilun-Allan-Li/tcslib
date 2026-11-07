"""Summarize existing phase-0 execution evidence; do not run Lean or dispatch jobs.

Run from the repository root with python3 -I. The raw logs remain the authority for
execution claims; this script validates their internal accounting and records hashes.
"""

from collections import Counter
import hashlib
import json
from pathlib import Path
import re
import subprocess


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
EVIDENCE = HERE / "evidence"
SOURCE_PIN = "4364d0e0fe9accd649b6acb4751e8684aa93ad1e"
BASELINE = "869c0d55bb1c4132ba8ccf4d636ea2184ef8bd49"


def read_json(name):
    return json.loads((EVIDENCE / name).read_text())


def write_json(name, value):
    (EVIDENCE / name).write_text(json.dumps(value, indent=2) + "\n")


def git(*args):
    return subprocess.check_output(["git", *args], cwd=ROOT)


def main():
    source = read_json("source-declarations.json")
    log = (EVIDENCE / "axioms-and-constants.log").read_text()
    result = read_json("axiom-check-result.json")
    assert result["exit_code"] == result["error_lines"] == 0
    assert "error:" not in log
    axioms = {}
    pattern = (r"'([^']+)' depends on axioms:\s*\[(.*?)\]|"
               r"'([^']+)' does not depend on any axioms")
    for match in re.finditer(pattern, log, re.S):
        axioms[match[1] or match[3]] = (
            [] if match[3] else [x.strip() for x in match[2].split(",") if x.strip()])
    assert len(source) == len(axioms) == 61
    assert {row["name"] for row in source} == set(axioms)
    assert all(set(xs) <= {"propext", "Classical.choice", "Quot.sound", "sorryAx"}
               for xs in axioms.values())
    for row in source:
        row["axioms"] = axioms[row["name"]]
        row["admitted"] = "sorryAx" in row["axioms"]
    admitted = [row for row in source if row["admitted"]]
    assert len(admitted) == 14
    for name in ["TCSlib.Cryptography.LWE.DLWEAssumption",
                 "TCSlib.Cryptography.LWE.dlweAssumption_iff",
                 "TCSlib.Cryptography.SIS.SISAssumption",
                 "TCSlib.Cryptography.SIS.sisAssumption_iff"]:
        assert "sorryAx" not in axioms[name]
    write_json("declarations-and-axioms.json", source)
    write_json("admissions.json", admitted)

    structures = [row["name"] for row in source if row["kind"] == "structure"]
    constants = []
    for line in log.splitlines():
        if not line.startswith("PHASE0_CONSTANT|"):
            continue
        _, module, name, kind, private = line.split("|")
        category = "source declaration"
        if name not in axioms:
            category = ("compiler auxiliary" if "._proof_" in name or ".match_" in name
                        else "structure-generated" if any(name.startswith(n + ".")
                        for n in structures) else "unexpected")
        constants.append(dict(module=module, name=name, kind=kind,
                              private=private == "true", category=category))
    assert len(constants) == 164
    assert not any(row["private"] for row in constants)
    assert not any(row["category"] == "unexpected" for row in constants)
    auxiliary = {row["name"] for row in constants
                 if row["category"] == "compiler auxiliary"}
    assert auxiliary == {
        "TCSlib.Cryptography.LWE.Family.advantageAt._proof_1",
        "TCSlib.Cryptography.SIS.Family.successAt._proof_1",
        "TCSlib.Cryptography.SIS.successProbability.match_1"}
    write_json("elaborated-constants.json", sorted(constants, key=lambda row: row["name"]))

    sweep = read_json("initial-dependency-sweep.json")
    owned = {row["module"] for row in source}
    warnings = Counter()
    for row in sweep:
        assert row["exit_code"] == 0
        text = (EVIDENCE / "initial-dependency-sweep" / Path(row["log"]).name).read_text()
        assert "error:" not in text
        warnings["new" if row["module"] in owned else "inherited"] += (
            text.count("declaration uses 'sorry'"))
    assert len(sweep) == 55 and dict(warnings) == {"inherited": 17, "new": 14}
    assert all(row["exit_code"] == 0 for row in read_json("renamed-assumption-checks.json"))
    style = []
    for path in sorted(EVIDENCE.glob("style-*.log")):
        match = re.search(r"style_lint: (\d+) FAIL, (\d+) WARN over (\d+) files", path.read_text())
        assert match, path
        style.append(tuple(map(int, match.groups())))
    assert len(style) == 3 and tuple(map(sum, zip(*style))) == (0, 2, 10)

    paths = [row["module"] + ".lean" for row in sweep]
    paths += ["TCSlib.lean", "lean-toolchain", "lake-manifest.json",
              "scripts/lean_check_tree.sh", "scripts/campaign_style_lint.py",
              "AGENTS.md", "policy.md", "workflow.md"]
    freeze = []
    for path in sorted(set(paths)):
        data = git("show", SOURCE_PIN + ":" + path)
        assert data == (ROOT / path).read_bytes(), path
        freeze.append(dict(path=path, bytes=len(data), sha256=hashlib.sha256(data).hexdigest()))
    write_json("source-freeze.json", dict(source_pin=SOURCE_PIN, baseline=BASELINE, files=freeze))
    summary = dict(source_pin=SOURCE_PIN, baseline=BASELINE,
                   source_declarations=len(source), source_kinds=dict(Counter(r["kind"] for r in source)),
                   admitted_statements=len(admitted), elaborated_constants=len(constants),
                   constant_categories=dict(Counter(r["category"] for r in constants)),
                   fresh_dependency_sweep_modules=55, post_rename_rechecks=4,
                   admission_warnings=dict(warnings), whole_library_root_checked=False,
                   style_failures=sum(row[0] for row in style), style_warnings=sum(row[1] for row in style),
                   style_warning_reason="Acronym predicate readers follow RSA/DDH naming; lint lowercases only the first letter.",
                   external_gate_closed=False, source_pdfs_byte_archived=False,
                   published_branch_or_pr=False)
    write_json("summary.json", summary)
    print(json.dumps(summary, indent=2))


if __name__ == "__main__":
    main()
