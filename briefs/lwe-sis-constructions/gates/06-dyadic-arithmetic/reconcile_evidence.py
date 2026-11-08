"""Reconcile the dyadic arithmetic statement gate without native execution or dispatch.

Before code commits, use --precommit. Afterwards source-pin.txt identifies the
exact checked Lean/root; all frozen bytes must then match that Git revision.
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
BASE = "8627edde9892607a699cf997c8dd5a8a2a700e26"
MODULE = "TCSlib/Cryptography/Encoding/DyadicArithmetic"
INSPECT = runpy.run_path(str(ROOT / "briefs/lwe-sis-constructions/fills/00-encodings/verify_freeze.py"))["inspect"]


def write(name, value):
    (E / name).write_text(json.dumps(value, indent=2) + "\n")


def git(*args):
    return subprocess.check_output(["git", *args], cwd=ROOT)


def main():
    precommit = "--precommit" in sys.argv
    pin = None if precommit else (E / "source-pin.txt").read_text().strip()
    _, declarations, proofs = INSPECT((ROOT / (MODULE + ".lean")).read_text())
    assert len(declarations) == 18 and Counter(k for k, _ in declarations) == {"def": 3, "theorem": 15}
    source = [dict(module=MODULE, kind=k, name=n,
                   directly_admitted=bool(re.search(r"\bsorry\b", proofs.get(n, ""))))
              for k, n in declarations]
    assert sum(r["directly_admitted"] for r in source) == 12
    closed = {n for _, n in declarations if n in proofs and not re.search(r"\bsorry\b", proofs[n])}
    assert closed == {"TCSlib.Cryptography.Encoding.DyadicArithmetic." + n for n in
                      ["addPoly_eq", "mulPoly_eq", "subPoly_eq"]}
    assert all(proofs[n] == "rfl" for n in closed)
    probe = json.loads((E / "axiom-probe/checks.json").read_text())
    assert len(probe) == 1 and probe[0]["exit_code"] == probe[0]["error_lines"] == 0
    raw = (ROOT / probe[0]["log"]).read_text()
    printed = {}
    for m in re.finditer(r"'([^']+)' depends on axioms:\s*\[(.*?)\]|'([^']+)' does not depend on any axioms", raw, re.S):
        printed[m[1] or m[3]] = [] if m[3] else sorted(x.strip() for x in m[2].split(",") if x.strip())
    backing = json.loads((E / "backing-contracts.json").read_text())
    assert set(printed) == {r["name"] for r in source} | set(backing)
    standard = {"propext", "Classical.choice", "Quot.sound"}
    for n in backing:
        assert set(printed[n]) <= standard, (n, printed[n])
    write("backing-contract-axioms.json", [dict(name=n, axioms=printed[n]) for n in backing])
    constants, axioms = [], {}
    for line in raw.splitlines():
        if line.startswith("DYADIC_CONSTANT|"):
            _, module, name, kind, private = line.split("|")
            constants.append(dict(module=module, name=name, kind=kind, private=private == "true"))
        if line.startswith("DYADIC_AXIOMS|"):
            _, name, labels = line.split("|")
            axioms[name] = sorted(filter(None, labels.split(",")))
    baseline = {r["name"]: r for r in json.loads((ROOT /
        "briefs/lwe-sis-constructions/fills/02-encoding-adapters/evidence/elaborated-constants.json").read_text())}
    assert len(baseline) == 284
    assert set(baseline) <= {r["name"] for r in constants}
    source_names = {r["name"] for r in source}
    new = []
    for row in constants:
        n = row["name"]
        row["axioms"] = axioms[n]
        assert not row["private"] and row["kind"] != "axiom", row
        assert set(row["axioms"]) <= standard | {"sorryAx"}, row
        if n in baseline:
            old = baseline[n]
            assert all(row[k] == old[k] for k in ["module", "kind", "private", "axioms"]), row
            row["category"] = "unchanged audited constant"
        else:
            row["category"] = "source declaration" if n in source_names else "compiler auxiliary"
            assert n in source_names or ".congr_simp" in n or "._proof_" in n, row
            new.append(row)
    for row in source:
        row["axioms"] = printed[row["name"]]
        assert row["axioms"] == axioms[row["name"]]
        assert ("sorryAx" in row["axioms"]) == row["directly_admitted"]
    write("source-declarations.json", source)
    write("admissions.json", [r for r in source if r["directly_admitted"]])
    write("elaborated-constants.json", sorted(constants, key=lambda r: r["name"]))
    write("new-compiler-constants.json", [r for r in new if r["category"] != "source declaration"])
    order = (E / "module-order.txt").read_text().splitlines()
    sweep = json.loads((E / "fresh-sweep/checks.json").read_text())
    assert len(sweep) == len(order) == 94 and [r["module"] for r in sweep] == order
    warnings = Counter()
    for row in sweep:
        assert row["exit_code"] == row["error_lines"] == 0 and row["fresh_olean"]
        data = (ROOT / (row["module"] + ".lean")).read_bytes()
        assert hashlib.sha256(data).hexdigest() == row["source_sha256"]
        warnings["new" if row["module"] == MODULE else "inherited"] += row["admission_warnings"]
    assert warnings == {"new": 12, "inherited": 17}, warnings
    paths = [m + ".lean" for m in order] + ["TCSlib.lean", "lean-toolchain", "lake-manifest.json",
        "AGENTS.md", "policy.md", "workflow.md", "scripts/lean_check_tree.sh", "scripts/campaign_style_lint.py"]
    files, unchanged = [], []
    for path in sorted(set(paths)):
        data = (ROOT / path).read_bytes()
        if pin:
            assert data == git("show", pin + ":" + path), path
        if path not in {MODULE + ".lean", "TCSlib/Cryptography/Encoding.lean"}:
            assert data == git("show", BASE + ":" + path), path
            unchanged.append(path)
        files.append(dict(path=path, bytes=len(data), sha256=hashlib.sha256(data).hexdigest()))
    assert len(files) == 102
    write("source-freeze.json", dict(source_pin=pin, baseline=BASE, files=files))
    write("invariance.json", dict(baseline=BASE, unchanged_frozen_files=unchanged,
        new_math_file=MODULE + ".lean", existing_file_overlap="TCSlib/Cryptography/Encoding.lean",
        shared_owner_definitions_changed=False, policy_toolchain_manifest_unchanged=True,
        source_invariant="Existing source bytes compared with audited dependency; no existing theorem body or signature changes."))
    styles = []
    for label, subtree in [("encoding", "Encoding"), ("lwe", "LWE"), ("sis", "SIS"),
                           ("regev", "Encryption/Symmetric/Regev"), ("sis-hash", "Hashing/SIS")]:
        result = subprocess.run([sys.executable, "-I", "scripts/campaign_style_lint.py",
            "TCSlib/Cryptography/" + subtree], cwd=ROOT, capture_output=True, text=True)
        (E / ("style-" + label + ".log")).write_text(result.stdout + result.stderr)
        m = re.search(r"style_lint: (\d+) FAIL, (\d+) WARN over (\d+) files", result.stdout)
        assert result.returncode == 0 and m
        styles.append(tuple(map(int, m.groups())))
    assert tuple(map(sum, zip(*styles))) == (0, 2, 20)
    summary = dict(source_pin=pin, baseline=BASE, central_target="cryptography/lwe-sis-constructions",
        dependency_prs=[236, 237, 238], source_declarations=18, definitions=3, theorems=15,
        defining_equations_proved=3, direct_admissions=12,
        unchanged_audited_constants=284, new_constants=len(new), total_owned_constants=len(constants),
        new_compiler_constants=len([r for r in new if r["category"] != "source declaration"]),
        new_constants_with_sorryAx=sum("sorryAx" in r["axioms"] for r in new),
        backing_machine_contracts_without_sorryAx=len(backing), fresh_modules=94,
        fresh_seconds=round(sum(r["seconds"] for r in sweep), 3), admission_warnings=dict(warnings),
        style_failures=0, style_warnings=2, style_files=20, whole_library_root_checked=False,
        external_statement_gate_closed=False, source_policy_closed=False, new_hosts=0,
        copied_existing_proved_infrastructure=0)
    write("summary.json", summary)
    print(json.dumps(summary, indent=2))


if __name__ == "__main__":
    main()
