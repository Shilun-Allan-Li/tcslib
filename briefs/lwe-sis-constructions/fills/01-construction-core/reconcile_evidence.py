"""Reconcile the final construction-core fill evidence; do not run native checks.

The public-constant walk is the unchanged statement-gate probe, run against the
fresh proof-fill objects. Historical gate evidence is read only.
"""

from collections import Counter
import hashlib
import json
from pathlib import Path
import re
import runpy
import subprocess
import sys


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
E = HERE / "evidence"
G = ROOT / "briefs/lwe-sis-constructions/gates/02-construction-core/evidence"
INSPECT = runpy.run_path(str(HERE / "verify_freeze.py"))["INSPECT"]


def write(name, value):
    (E / name).write_text(json.dumps(value, indent=2) + "\n")


def main():
    subprocess.run([sys.executable, "-I", str(HERE / "verify_freeze.py")], cwd=ROOT, check=True)
    source_pin = (E / "source-pin.txt").read_text().strip()
    source = []
    modules = sorted({r["module"] for r in json.loads((G / "declarations-and-axioms.json").read_text())})
    for module in modules:
        _, declarations, proofs = INSPECT((ROOT / (module + ".lean")).read_text())
        source += [dict(module=module, kind=k, name=n,
                        directly_admitted=bool(re.search(r"\b(sorry|admit)\b", proofs.get(n, ""))))
                   for k, n in declarations]
    assert len(source) == 62 and not any(r["directly_admitted"] for r in source)
    probe = json.loads((E / "axiom-probe/checks.json").read_text())
    assert len(probe) == 1 and probe[0]["exit_code"] == probe[0]["error_lines"] == 0
    raw = (ROOT / probe[0]["log"]).read_text()
    printed = {}
    for m in re.finditer(r"'([^']+)' depends on axioms:\s*\[(.*?)\]|'([^']+)' does not depend on any axioms", raw, re.S):
        printed[m[1] or m[3]] = [] if m[3] else sorted(x.strip() for x in m[2].split(",") if x.strip())
    assert set(printed) == {r["name"] for r in source}
    constants, axioms = [], {}
    for line in raw.splitlines():
        if line.startswith("CONSTRUCTION_CONSTANT|"):
            _, module, name, kind, private = line.split("|")
            constants.append(dict(module=module, name=name, kind=kind, private=private == "true"))
        if line.startswith("CONSTRUCTION_AXIOMS|"):
            _, name, labels = line.split("|")
            axioms[name] = sorted(filter(None, labels.split(",")))
    baseline = {r["name"]: r for r in json.loads((G / "elaborated-constants.json").read_text())}
    assert len(baseline) == 256
    names = {r["name"] for r in constants}
    assert len(names) == len(constants) and set(baseline) <= names
    new = []
    for row in constants:
        n = row["name"]
        row["axioms"] = axioms[n]
        assert not row["private"] and row["kind"] != "axiom", row
        assert set(axioms[n]) <= {"propext", "Classical.choice", "Quot.sound"}, row
        if n in baseline:
            old = baseline[n]
            assert all(row[k] == old[k] for k in ["kind", "private", "module"]), row
            row["category"] = old["category"]
            if old["category"] == "unchanged foundation":
                assert row["axioms"] == old["axioms"], row
        else:
            assert ".congr_simp" in n or "._proof_" in n, row
            row["category"] = "fill compiler auxiliary"
            new.append(row)
    for row in source:
        row["axioms"] = printed[row["name"]]
        assert row["axioms"] == axioms[row["name"]]
    write("declarations-and-axioms.json", source)
    write("admissions.json", [])
    write("elaborated-constants.json", sorted(constants, key=lambda r: r["name"]))
    write("new-compiler-constants.json", sorted(new, key=lambda r: r["name"]))
    sweep = json.loads((E / "fresh-sweep/checks.json").read_text())
    assert len(sweep) == 68
    assert [r["module"] for r in sweep] == (E / "module-order.txt").read_text().splitlines()
    warnings = Counter()
    for row in sweep:
        assert row["exit_code"] == row["error_lines"] == 0 and row["fresh_olean"]
        data = (ROOT / (row["module"] + ".lean")).read_bytes()
        assert hashlib.sha256(data).hexdigest() == row["source_sha256"]
        assert data == subprocess.check_output(["git", "show", source_pin + ":" + row["module"] + ".lean"], cwd=ROOT)
        warnings["owned" if row["module"] in modules else "inherited"] += row["admission_warnings"]
    assert warnings["owned"] == 0 and warnings["inherited"] == 17
    frozen = []
    for row in json.loads((G / "source-freeze.json").read_text())["files"]:
        path = row["path"]
        data = (ROOT / path).read_bytes()
        assert data == subprocess.check_output(["git", "show", source_pin + ":" + path], cwd=ROOT)
        frozen.append(dict(path=path, bytes=len(data), sha256=hashlib.sha256(data).hexdigest()))
    write("source-freeze.json", dict(source_pin=source_pin,
        statement_baseline="a1f1b2e0d9315dff2a8dc36e2a6f8339c0a5abdf", files=frozen))
    style = []
    for label, subtree in [("encoding", "Encoding"), ("lwe", "LWE"), ("sis", "SIS"),
                           ("regev", "Encryption/Symmetric/Regev"), ("sis-hash", "Hashing/SIS")]:
        result = subprocess.run([sys.executable, "-I", "scripts/campaign_style_lint.py",
                                 "TCSlib/Cryptography/" + subtree], cwd=ROOT, capture_output=True, text=True)
        (E / ("style-" + label + ".log")).write_text(result.stdout + result.stderr)
        m = re.search(r"style_lint: (\d+) FAIL, (\d+) WARN over (\d+) files", result.stdout)
        assert result.returncode == 0 and m
        style.append(tuple(map(int, m.groups())))
    assert tuple(map(sum, zip(*style))) == (0, 2, 18)
    summary = dict(source_pin=source_pin, statement_baseline="a1f1b2e0d9315dff2a8dc36e2a6f8339c0a5abdf",
        central_branch="cryptography/lwe-sis-constructions", pr=237, dependency_pr=236,
        source_declarations=62, proved_targets=31, direct_admissions=0,
        previous_constants=256, fill_compiler_constants=len(new), total_owned_constants=len(constants),
        constants_with_sorryAx=0, fresh_modules=68,
        fresh_seconds=round(sum(r["seconds"] for r in sweep), 3),
        admission_warnings=dict(warnings), style_failures=0, style_warnings=2, style_files=18,
        whole_library_root_checked=False, external_proof_gate_closed=False,
        source_ingestion_complete=False, new_machine_hosts=0, copied_existing_proved_infrastructure=0)
    write("summary.json", summary)
    print(json.dumps(summary, indent=2))


if __name__ == "__main__":
    main()
