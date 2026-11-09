"""Verify the twelve-body adapter fill against its audited statement freeze.

Reuse the existing nesting-aware campaign source inspector. This is a source
comparison, not an elaborated type-hash comparison. No native check is run.
"""

import hashlib
import json
from pathlib import Path
import runpy
import subprocess


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
GATE = ROOT / "briefs/lwe-sis-constructions/gates/06-dyadic-arithmetic/evidence"
INSPECT = runpy.run_path(str(ROOT /
    "briefs/lwe-sis-constructions/fills/00-encodings/verify_freeze.py"))["inspect"]
SOURCE = "dbacd91218c19f0df106d316ce4ff0e22b869e66"
PATH = "TCSlib/Cryptography/Encoding/DyadicArithmetic.lean"


def main():
    before = subprocess.check_output(["git", "show", SOURCE + ":" + PATH],
                                     cwd=ROOT).decode()
    after = (ROOT / PATH).read_text()
    old_surface, old_decls, old_proofs = INSPECT(before)
    new_surface, new_decls, new_proofs = INSPECT(after)
    assert old_surface == new_surface, "Definition/signature/import/attribute drift"
    assert old_decls == new_decls and len(new_decls) == 18
    targets = {row["name"] for row in json.loads((GATE / "admissions.json").read_text())}
    changed = {name for name in old_proofs if old_proofs[name] != new_proofs[name]}
    assert changed == targets and len(targets) == 12, changed ^ targets
    assert not any("sorry" in proof.split() for proof in new_proofs.values())
    freeze = json.loads((GATE / "source-freeze.json").read_text())
    unchanged = []
    for row in freeze["files"]:
        if row["path"] == PATH:
            continue
        data = (ROOT / row["path"]).read_bytes()
        assert hashlib.sha256(data).hexdigest() == row["sha256"], row["path"]
        unchanged.append(row["path"])
    assert len(unchanged) == 101
    result = {
        "statement_freeze": SOURCE,
        "comparison": "Comment-stripped source surface, not elaborated type hashes",
        "source_declarations": 18,
        "ordered_declarations_unchanged": True,
        "definitions_signatures_imports_attributes_namespaces_unchanged": True,
        "changed_proof_bodies": sorted(changed),
        "new_source_helpers": 0,
        "unchanged_frozen_paths": unchanged,
        "filled_module": PATH,
        "filled_source_sha256": hashlib.sha256(after.encode()).hexdigest(),
        "invariant_surface_sha256": hashlib.sha256(new_surface.encode()).hexdigest(),
    }
    (HERE / "evidence/freeze-attestation.json").write_text(
        json.dumps(result, indent=2) + "\n")
    print(json.dumps({"source_declarations": 18, "filled_proofs": len(changed),
                      "unchanged_frozen_paths": len(unchanged), "surface_drift": False}))


if __name__ == "__main__":
    main()
