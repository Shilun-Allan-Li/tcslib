#!/usr/bin/env python3
"""Rebind the manually reviewed row draft to the identical final2 inventory."""
from pathlib import Path
import hashlib
import json

ROOT = Path(__file__).resolve().parents[2]
FIRST = ROOT / "evidence/probes/Rule10/final1/final-scan-plan.json"
SECOND = ROOT / "evidence/probes/Rule10/final2/final-scan-plan.json"
first = json.loads(FIRST.read_text())
second = json.loads(SECOND.read_text())
assert first["items"] == second["items"], "row-by-row source inventory changed"
assert len(second["items"]) == 595
source = (ROOT / "evidence/tools/manual_explicit_review_draft.py").read_text()
assert source.count("evidence/probes/Rule10/final1/final-scan-plan.json") == 1
source = source.replace("evidence/probes/Rule10/final1/final-scan-plan.json",
                        "evidence/probes/Rule10/final2/final-scan-plan.json")
exec(compile(source, str(ROOT / "evidence/tools/manual_explicit_review_draft.py")
             + "::<final2 identical-row rebinding>", "exec"),
     {"__file__": str(ROOT / "evidence/tools/manual_explicit_review_draft.py")})
