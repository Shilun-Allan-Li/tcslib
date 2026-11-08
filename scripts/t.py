python3 - <<'PY'
import json
from pathlib import Path
from proofmatch.dataset_io import open_dataset

marker = ("Statement pending regeneration", "dataset-pipeline: stub")
def is_stub(text):
    return any(m in text for m in marker)

ids = set()
with open_dataset(Path("dataset/tcslib_theorems.jsonl")) as f:
    for line in f:
        r = json.loads(line)
        s = r.get("informal_statement", "")
        stub_deps = [
            d["id"] for d in r.get("definitions", [])
            if is_stub(d.get("informal", ""))
        ]
        ids.update(stub_deps)

        # Include a theorem itself when its claim still has placeholder prose.
        claim = s.split("\n\nStatement:", 1)[-1]
        if is_stub(claim) or (is_stub(s) and not stub_deps):
            ids.add(r["id"])

ids.discard("Complexity.tautControlDecidableEq")
path = Path("dataset/.pipeline/stub-retry-ids.txt")
path.write_text("".join(name + "\n" for name in sorted(ids)))
print(f"Wrote {len(ids)} generator-supported IDs to {path}")
print("Handle Complexity.tautControlDecidableEq manually in its blueprint entry.")
PY
