"""Freeze only this evidence folder after successful native and parser checks."""
from pathlib import Path
import datetime
import hashlib
import json

OUT = Path(__file__).resolve().parent
assert not (OUT / "MANIFEST.json").exists()
for name in ["SAT-compile", "Hardness-compile", "Metadata-roots-census-v1", "Metadata-whole9-axioms-v1"]:
    receipt = json.loads((OUT / (name + "-run.json")).read_text())
    assert receipt["exit"] == 0 and receipt["errors"] == 0
summary = json.loads((OUT / "metadata-summary.json").read_text())
assert summary["repaired_roots"] == 16 and summary["generated_descendants"] == 7
assert summary["selected_standard_axioms"] and not summary["selected_sorryAx"]
assert summary["ALLAX_exact_census_coverage"] and summary["PUBLICAX_exact_nonprivate_coverage"]
assert not summary["different_home_private_citations"]
artifacts = json.loads((OUT / "final-artifact-verification.json").read_text())
assert artifacts["shared_snapshot_unchanged"] and artifacts["complete_population_preserved"]
files = []
for p in sorted(OUT.rglob("*")):
    assert not p.is_symlink()
    if not p.is_file():
        continue
    assert p.suffix != ".lean", "Lean source in records must be inert"
    data = p.read_bytes()
    files.append(dict(path=p.relative_to(OUT).as_posix(), bytes=len(data), sha256=hashlib.sha256(data).hexdigest()))
manifest = dict(
    status="Frozen combined final16 SG1 native/compiled-metadata evidence; MSG4 pre-#230 dependencies; no merged replay or gate clearance",
    at_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
    source_pins=json.loads((OUT / "context.json").read_text())["source_pins"],
    files=files,
)
data=(json.dumps(manifest, indent=2)+"\n").encode()
(OUT / "MANIFEST.json").write_bytes(data)
print(json.dumps(dict(files=len(files), bytes=sum(x["bytes"] for x in files), manifest_sha256=hashlib.sha256(data).hexdigest()),indent=2))
