"""Prepare/reconcile this statement gate's source, native, constant and style records.

This deterministic script neither runs Lean nor dispatches workers. Use --prepare-probe
before checking evidence/Checks through check_modules.py; run without it afterwards.
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
BASE = "0769cba3e44c56700349f954190fc99d9e622270"
SOURCE = (E / "source-pin.txt").read_text().strip()
INSPECT = runpy.run_path(str(ROOT / "briefs/lwe-sis-constructions/fills/00-encodings/verify_freeze.py"))["inspect"]
MODULES = ["TCSlib/Cryptography/" + suffix for suffix in [
    "Encoding/ModularDecode", "LWE/SampleSchedules", "LWE/BitEncoding",
    "Encryption/Symmetric/Regev/Basic", "Encryption/Symmetric/Regev/Experiments",
    "Hashing/SIS/Basic", "Hashing/SIS/Experiments", "Hashing/SIS/Profiles"]]


def write(name, data):
    (E / name).write_text(json.dumps(data, indent=2) + "\n")


def git(*args):
    return subprocess.check_output(["git", *args], cwd=ROOT)


def source_inventory():
    source = []
    for module in MODULES:
        _, declarations, proofs = INSPECT((ROOT / (module + ".lean")).read_text())
        for kind, name in declarations:
            source.append(dict(module=module, kind=kind, name=name,
                               directly_admitted=bool(re.search(r"\bsorry\b", proofs.get(name, "")))))
    assert len(source) == 62 and len({r["name"] for r in source}) == 62
    assert Counter(r["kind"] for r in source) == {"def": 17, "theorem": 45}
    assert sum(r["directly_admitted"] for r in source) == 31
    return source


def prepare_probe(source):
    text = (E / "Checks.lean").read_text()
    before = text[:text.index("#print axioms")]
    after = text[text.index("open Lean in"):]
    (E / "Checks.lean").write_text(before + "\n".join("#print axioms " + r["name"] for r in source)
                                  + "\n" + after)
    write("new-source-declarations.json", source)


def main():
    source = source_inventory()
    if "--prepare-probe" in sys.argv:
        prepare_probe(source)
        print("Prepared exact namespace-aware 62-declaration probe.")
        return
    probe = E / "axiom-probe-final"
    checks = json.loads((probe / "checks.json").read_text())
    assert len(checks) == 1 and checks[0]["exit_code"] == checks[0]["error_lines"] == 0
    raw = (ROOT / checks[0]["log"]).read_text()
    assert not re.search(r"\berror(?:\([^)]*\))?:", raw)
    printed = {}
    for match in re.finditer(r"'([^']+)' depends on axioms:\s*\[(.*?)\]|'([^']+)' does not depend on any axioms", raw, re.S):
        printed[match[1] or match[3]] = ([] if match[3] else sorted(x.strip() for x in match[2].split(",") if x.strip()))
    assert set(printed) == {r["name"] for r in source}
    constants, axioms = [], {}
    for line in raw.splitlines():
        if line.startswith("CONSTRUCTION_CONSTANT|"):
            _, module, name, kind, private = line.split("|")
            constants.append(dict(module=module, name=name, kind=kind, private=private == "true"))
        if line.startswith("CONSTRUCTION_AXIOMS|"):
            _, name, labels = line.split("|")
            axioms[name] = sorted(filter(None, labels.split(",")))
    old = ROOT / "briefs/lwe-sis-constructions/fills/00-encodings/evidence"
    old_constants = json.loads((old / "elaborated-constants.json").read_text())
    old_names = {r["name"] for r in old_constants}
    old_axioms = {}
    for line in (old / "axioms-and-constants.log").read_text().splitlines():
        if line.startswith("FILL_CONSTANT_AXIOMS|"):
            _, name, labels = line.split("|")
            old_axioms[name] = sorted(filter(None, labels.split(",")))
    assert len(old_names) == len(old_axioms) == 166
    assert all(axioms[name] == old_axioms[name] for name in old_names)
    source_names = {r["name"] for r in source}
    readers = set()
    for owner, fields in {
        "LWE.Parameters.withSamples": ["dimension", "samples", "modulus"],
        "LWE.Family.withSamples": ["parameters", "noise", "dimensionBound", "samplesBound", "residueBits"],
        "Encryption.Symmetric.Regev.shift": ["fst", "snd"],
        "Encryption.Symmetric.Regev.encrypt": ["fst", "snd"],
        "Encryption.Symmetric.Regev.encryptDist": ["fst", "snd"],
        "Hashing.SIS.dyadicParameters": ["dimension", "columns", "modulus", "sqNormBound"],
        "Hashing.SIS.dyadicFamily": ["parameters", "dimensionBound", "columnsBound", "residueBits", "magnitudeBits"],
    }.items():
        readers.update("TCSlib.Cryptography." + owner + "_" + field for field in fields)
    assert len(readers) == 23
    for row in constants:
        name = row["name"]
        row["axioms"] = axioms[name]
        assert not row["private"] and row["kind"] != "axiom"
        assert set(row["axioms"]) <= {"propext", "Classical.choice", "Quot.sound", "sorryAx"}
        row["category"] = ("unchanged foundation" if name in old_names else
                           "source declaration" if name in source_names else
                           "generated non-simp reader" if name in readers else
                           "compiler auxiliary" if "._proof_" in name else "unexpected")
        assert row["category"] != "unexpected", row
    new = [r for r in constants if r["name"] not in old_names]
    assert len(constants) == 256 and len(new) == 90
    assert Counter(r["category"] for r in new) == {
        "source declaration": 62, "generated non-simp reader": 23, "compiler auxiliary": 5}
    for row in source:
        row["axioms"] = printed[row["name"]]
        assert row["axioms"] == axioms[row["name"]]
    write("declarations-and-axioms.json", source)
    write("admissions.json", [r for r in source if r["directly_admitted"]])
    write("elaborated-constants.json", sorted(constants, key=lambda r: r["name"]))
    write("new-transitive-admissions.json", [r for r in new if "sorryAx" in r["axioms"]])
    sweep = json.loads((E / "fresh-sweep/checks.json").read_text())
    order = (E / "module-order.txt").read_text().splitlines()
    assert len(sweep) == 68 and [r["module"] for r in sweep] == order
    warnings = Counter()
    for row in sweep:
        assert row["exit_code"] == row["error_lines"] == 0 and row["fresh_olean"]
        data = (ROOT / (row["module"] + ".lean")).read_bytes()
        assert hashlib.sha256(data).hexdigest() == row["source_sha256"]
        assert data == git("show", SOURCE + ":" + row["module"] + ".lean")
        warnings["new" if row["module"] in MODULES else "inherited"] += row["admission_warnings"]
    assert dict(warnings) == {"inherited": 17, "new": 31}
    paths = [r["module"] + ".lean" for r in sweep] + [
        "TCSlib.lean", "lean-toolchain", "lake-manifest.json", "AGENTS.md", "policy.md",
        "workflow.md", "scripts/lean_check_tree.sh", "scripts/campaign_style_lint.py"]
    frozen = []
    for path in sorted(set(paths)):
        data = (ROOT / path).read_bytes()
        assert data == git("show", SOURCE + ":" + path)
        frozen.append(dict(path=path, bytes=len(data), sha256=hashlib.sha256(data).hexdigest()))
    write("source-freeze.json", dict(source_pin=SOURCE, construction_baseline=BASE, files=frozen))
    previous = json.loads((old / "source-freeze.json").read_text())
    changed = [r["path"] for r in previous["files"]
               if hashlib.sha256((ROOT / r["path"]).read_bytes()).hexdigest() != r["sha256"]]
    assert set(changed) == {"TCSlib.lean", "TCSlib/Cryptography/Encoding.lean", "TCSlib/Cryptography/LWE.lean"}
    write("foundation-invariance.json", dict(baseline=BASE, source_pin=SOURCE,
          unchanged_previous_frozen_files=len(previous["files"]) - len(changed),
          changed_export_files=changed, baseline_constants_unchanged=166,
          baseline_axiom_sets_unchanged=True, duplication_count=0, new_machine_hosts=0))
    style = []
    for label, subtree in [
        ("encoding", "Encoding"), ("lwe", "LWE"), ("sis", "SIS"),
        ("regev", "Encryption/Symmetric/Regev"), ("sis-hash", "Hashing/SIS")]:
        result = subprocess.run([sys.executable, "-I", "scripts/campaign_style_lint.py",
                                 "TCSlib/Cryptography/" + subtree], cwd=ROOT,
                                capture_output=True, text=True)
        (E / ("style-" + label + ".log")).write_text(result.stdout + result.stderr)
        match = re.search(r"style_lint: (\d+) FAIL, (\d+) WARN over (\d+) files", result.stdout)
        assert result.returncode == 0 and match
        style.append(tuple(map(int, match.groups())))
    assert tuple(map(sum, zip(*style))) == (0, 2, 18)
    summary = dict(source_pin=SOURCE, construction_baseline=BASE,
        central_branch="cryptography/lwe-sis-constructions", dependency_pr=236,
        source_declarations=62, source_kinds={"definitions": 17, "theorems": 45},
        direct_admissions=31, new_elaborated_constants=90,
        new_constant_categories={"source": 62, "generated_readers": 23, "compiler_auxiliaries": 5},
        new_constants_with_sorryAx=sum("sorryAx" in r["axioms"] for r in new),
        unchanged_foundation_constants=166, total_owned_constants=256,
        fresh_modules=68, fresh_seconds=round(sum(r["seconds"] for r in sweep), 3),
        admission_warnings=dict(warnings), style_failures=0, style_warnings=2,
        style_files=18, whole_library_root_checked=False, external_gate_closed=False,
        source_pdfs_byte_archived=True, source_ingestion_complete=False)
    write("summary.json", summary)
    print(json.dumps(summary, indent=2))


if __name__ == "__main__":
    main()
