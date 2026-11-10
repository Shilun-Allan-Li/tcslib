"""Check the construction-core proof fill against its audited statement freeze.

Reuse the earlier fill's comment-aware declaration inspector. Only theorem bodies,
comments, and the three enumerated precise imports may change.
"""

from collections import Counter
import hashlib
import json
from pathlib import Path
import re
import runpy
import subprocess


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
BASE = "a1f1b2e0d9315dff2a8dc36e2a6f8339c0a5abdf"
GATE = ROOT / "briefs/lwe-sis-constructions/gates/02-construction-core/evidence"
INSPECT = runpy.run_path(str(ROOT / "briefs/lwe-sis-constructions/fills/00-encodings/verify_freeze.py"))["inspect"]
STRIP = runpy.run_path(str(ROOT / "scripts/campaign_style_lint.py"))["strip_comments"]
ADDED_IMPORTS = {
    "TCSlib/Cryptography/Encoding/ModularDecode.lean": [
        "import Mathlib.Algebra.BigOperators.Group.List.Lemmas\n"],
    "TCSlib/Cryptography/Hashing/SIS/Profiles.lean": [
        "import Mathlib.Tactic.Linarith\n", "import Mathlib.Tactic.Ring\n"],
}


def main():
    source = json.loads((GATE / "declarations-and-axioms.json").read_text())
    targets = {r["name"] for r in json.loads((GATE / "admissions.json").read_text())}
    files = {r["module"] + ".lean" for r in source}
    before_decls, after_decls, changed, records = [], [], set(), []
    for path in sorted(files):
        before = subprocess.check_output(["git", "show", BASE + ":" + path], cwd=ROOT).decode()
        after = (ROOT / path).read_text()
        compared = after
        for added in ADDED_IMPORTS.get(path, []):
            assert added not in before and compared.count(added) == 1, (path, added)
            compared = compared.replace(added, "", 1)
        a, da, pa = INSPECT(before)
        b, db, pb = INSPECT(compared)
        assert a == b, "Signature/definition/attribute/namespace drift: " + path
        assert da == db, "Ordered declaration drift: " + path
        assert not re.search(r"\b(sorry|admit|axiom|unsafe)\b", STRIP(after)), path
        before_decls += da
        after_decls += db
        changed.update(n for n in pa if pa[n] != pb[n])
        records.append(dict(path=path, source_sha256=hashlib.sha256(after.encode()).hexdigest(),
                            invariant_surface_sha256=hashlib.sha256(b.encode()).hexdigest()))
    assert before_decls == after_decls and len(after_decls) == 62
    assert Counter(before_decls) == Counter(after_decls)
    assert Counter(k for k, _ in after_decls) == {"def": 17, "theorem": 45}
    assert changed == targets and len(changed) == 31, changed ^ targets
    unchanged = []
    for row in json.loads((GATE / "source-freeze.json").read_text())["files"]:
        if row["path"] not in files:
            assert hashlib.sha256((ROOT / row["path"]).read_bytes()).hexdigest() == row["sha256"], row["path"]
            unchanged.append(row["path"])
    result = dict(statement_baseline=BASE, source_declarations_before=62,
                  source_declarations_after=62, source_kinds={"definitions": 17, "theorems": 45},
                  ordered_declarations_unchanged=True, declaration_multiset_unchanged=True,
                  signatures_definitions_attributes_namespaces_unchanged=True,
                  changed_proof_bodies=sorted(changed), new_helpers=0,
                  added_imports=ADDED_IMPORTS, unchanged_other_frozen_files=unchanged,
                  source_files=records,
                  scope="Comment-stripped source invariant, not an elaborated type-hash comparison.")
    evidence = HERE / "evidence"
    evidence.mkdir(exist_ok=True)
    (evidence / "freeze-attestation.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(dict(declarations=62, proved_targets=31,
                         unchanged_other_frozen_files=len(unchanged), signature_definition_drift=False)))


if __name__ == "__main__":
    main()
