"""Reconcile the adapter proof fill's fresh execution and complete axiom inventory.

This follows the audited statement gate's accounting, with zero owned admissions
and only the twelve frozen theorem bodies changed. It runs no native job.
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
G = ROOT / "briefs/lwe-sis-constructions/gates/06-dyadic-arithmetic/evidence"
BASE = "dbacd91218c19f0df106d316ce4ff0e22b869e66"
MODULE = "TCSlib/Cryptography/Encoding/DyadicArithmetic"
INSPECT = runpy.run_path(str(ROOT /
    "briefs/lwe-sis-constructions/fills/00-encodings/verify_freeze.py"))["inspect"]


def write(name, value):
    (E / name).write_text(json.dumps(value, indent=2) + "\n")


def main():
    pin = None if "--precommit" in sys.argv else (E / "source-pin.txt").read_text().strip()
    _, declarations, proofs = INSPECT((ROOT / (MODULE + ".lean")).read_text())
    assert len(declarations) == 18
    assert Counter(k for k, _ in declarations) == {"def": 3, "theorem": 15}
    assert all(not re.search(r"\b(sorry|admit)\b", proof) for proof in proofs.values())
    source = [dict(module=MODULE, kind=k, name=n, directly_admitted=False)
              for k, n in declarations]
    freeze = json.loads((E / "freeze-attestation.json").read_text())
    assert len(freeze["changed_proof_bodies"]) == 12
    assert freeze["filled_source_sha256"] == hashlib.sha256(
        (ROOT / (MODULE + ".lean")).read_bytes()).hexdigest()

    probe = json.loads((E / "axiom-probe/checks.json").read_text())
    assert len(probe) == 1
    assert probe[0]["exit_code"] == probe[0]["error_lines"] == 0 and probe[0]["fresh_olean"]
    raw = (ROOT / probe[0]["log"]).read_text()
    printed = {}
    for match in re.finditer(
        r"'([^']+)' depends on axioms:\s*\[(.*?)\]|'([^']+)' does not depend on any axioms",
        raw, re.S,
    ):
        printed[match[1] or match[3]] = [] if match[3] else sorted(
            x.strip() for x in match[2].split(",") if x.strip())
    backing = json.loads((E / "backing-contracts.json").read_text())
    assert set(printed) == {r["name"] for r in source} | set(backing)
    standard = {"propext", "Classical.choice", "Quot.sound"}
    assert all(set(axioms) <= standard for axioms in printed.values())
    write("backing-contract-axioms.json", [dict(name=n, axioms=printed[n]) for n in backing])

    constants, axioms = [], {}
    for line in raw.splitlines():
        if line.startswith("DYADIC_CONSTANT|"):
            _, module, name, kind, private = line.split("|")
            constants.append(dict(module=module, name=name, kind=kind, private=private == "true"))
        if line.startswith("DYADIC_AXIOMS|"):
            _, name, labels = line.split("|")
            axioms[name] = sorted(filter(None, labels.split(",")))
    assert len(constants) == len({r["name"] for r in constants}) == len(axioms)
    statement = {r["name"]: r for r in json.loads((G / "elaborated-constants.json").read_text())}
    foundation = {r["name"]: r for r in json.loads((ROOT /
        "briefs/lwe-sis-constructions/fills/02-encoding-adapters/evidence/elaborated-constants.json").read_text())}
    assert len(statement) == 302 and len(foundation) == 284
    assert set(statement) <= set(axioms)
    source_names = {r["name"] for r in source}
    auxiliaries = []
    for row in constants:
        name = row["name"]
        row["axioms"] = axioms[name]
        assert not row["private"] and row["kind"] != "axiom", row
        assert set(row["axioms"]) <= standard, row
        if name in statement:
            assert all(row[k] == statement[name][k] for k in ["module", "kind", "private"]), row
        if name in foundation:
            assert row["axioms"] == foundation[name]["axioms"], row
            row["category"] = "unchanged audited constant"
        elif name in source_names:
            row["category"] = "source declaration"
            if name not in freeze["changed_proof_bodies"]:
                assert row["axioms"] == statement[name]["axioms"], row
        else:
            assert ".congr_simp" in name or "._proof_" in name, row
            row["category"] = "new compiler auxiliary"
            auxiliaries.append(row)
    for row in source:
        row["axioms"] = printed[row["name"]]
        assert row["axioms"] == axioms[row["name"]]
    write("source-declarations.json", source)
    write("admissions.json", [])
    write("elaborated-constants.json", sorted(constants, key=lambda row: row["name"]))
    write("new-compiler-constants.json", sorted(auxiliaries, key=lambda row: row["name"]))

    order = (E / "module-order.txt").read_text().splitlines()
    sweep = json.loads((E / "fresh-sweep/checks.json").read_text())
    assert len(sweep) == len(order) == 94
    assert [row["module"] for row in sweep] == order
    warnings = Counter()
    for row in sweep:
        assert row["exit_code"] == row["error_lines"] == 0 and row["fresh_olean"]
        data = (ROOT / (row["module"] + ".lean")).read_bytes()
        assert hashlib.sha256(data).hexdigest() == row["source_sha256"]
        log = (ROOT / row["log"]).read_text()
        assert not re.search(r"\berror(?:\([^)]*\))?:", log)
        assert row["admission_warnings"] == log.count("declaration uses 'sorry'")
        warnings["owned" if row["module"] == MODULE else "inherited"] += row["admission_warnings"]
    assert warnings == {"owned": 0, "inherited": 17}, warnings
    files = []
    for old in json.loads((G / "source-freeze.json").read_text())["files"]:
        path = old["path"]
        data = (ROOT / path).read_bytes()
        if pin:
            assert data == subprocess.check_output(["git", "show", pin + ":" + path], cwd=ROOT), path
        if path != MODULE + ".lean":
            assert hashlib.sha256(data).hexdigest() == old["sha256"], path
        files.append(dict(path=path, bytes=len(data), sha256=hashlib.sha256(data).hexdigest()))
    assert len(files) == 102
    write("source-freeze.json", dict(source_pin=pin, statement_freeze=BASE, files=files))

    styles = []
    for label, subtree in [("encoding", "Encoding"), ("lwe", "LWE"), ("sis", "SIS"),
                           ("regev", "Encryption/Symmetric/Regev"), ("sis-hash", "Hashing/SIS")]:
        result = subprocess.run([sys.executable, "-I", "scripts/campaign_style_lint.py",
            "TCSlib/Cryptography/" + subtree], cwd=ROOT, capture_output=True, text=True)
        (E / ("style-" + label + ".log")).write_text(result.stdout + result.stderr)
        match = re.search(r"style_lint: (\d+) FAIL, (\d+) WARN over (\d+) files", result.stdout)
        assert result.returncode == 0 and match
        styles.append(tuple(map(int, match.groups())))
    assert tuple(map(sum, zip(*styles))) == (0, 2, 20)
    development = [json.loads(p.read_text())[0]
                   for p in sorted((E / "development").glob("*/checks.json"))]
    summary = dict(source_pin=pin, statement_freeze=BASE,
        central_target="cryptography/lwe-sis-constructions", pr=239,
        source_declarations=18, definitions=3, theorems=15,
        formerly_admitted_proofs_filled=12, direct_admissions=0,
        unchanged_audited_constants=284, statement_constants_preserving_identity=302,
        total_owned_constants=len(constants), new_compiler_constants=len(auxiliaries),
        owned_constants_with_sorryAx=0, backing_machine_contracts_without_sorryAx=len(backing),
        fresh_modules=94, fresh_seconds=round(sum(row["seconds"] for row in sweep), 3),
        admission_warnings=dict(warnings), style_failures=0, style_warnings=2, style_files=20,
        development_runs=len(development), failed_development_runs=sum(row["exit_code"] != 0 for row in development),
        whole_library_root_checked=False, external_statement_gate_closed=True,
        external_proof_gate_closed=False, source_policy_closed=False,
        shared_owner_api_or_export_or_pin_changed=False, new_hosts=0,
        copied_existing_proved_infrastructure=0)
    write("summary.json", summary)
    print(json.dumps(summary, indent=2))


if __name__ == "__main__":
    main()
