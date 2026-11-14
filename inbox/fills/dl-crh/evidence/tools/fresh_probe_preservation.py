#!/usr/bin/env python3
"""Verify all final3 probe sources by insertion removal, without invoking Lean."""
from __future__ import annotations
import hashlib
import importlib.util
import json
from pathlib import Path
import sys

ROOT=Path(__file__).resolve().parents[2]
OUT=ROOT/"evidence/probes/Rule10/final3"
sys.dont_write_bytecode=True


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    spec=importlib.util.spec_from_file_location("dl_crh_fresh_source_preservation",ROOT/"evidence/tools/seal_provenance.py")
    helper=importlib.util.module_from_spec(spec)
    spec.loader.exec_module(helper)
    state_path=OUT/"snapshot.json"
    state=json.loads(state_path.read_text())
    helper.R.verify_source_snapshot(state,ROOT)
    manifest_path=OUT/"final-seal-manifest.json"
    manifest=json.loads(manifest_path.read_text())
    records={}
    for entry in manifest["probes"]:
        record_path=ROOT/entry["record"]
        record=json.loads(record_path.read_text())
        key=("final",record["owner"],record["variant"])
        helper.need(key not in records and record["side"]=="final","duplicate/wrong final source identity")
        helper.need(record["probe_sha256"]==entry["probe_sha256"],"final manifest binding differs")
        helper.need(record["harness_revision"]==helper.REVISION and record["chunk_size"]==2048,
                    "fresh instrumentation revision differs from historical pilot")
        helper.need(record["chunks"]==helper.P.seal_chunks(record["label"],record["rows"]),"fresh chunk metadata differs")
        records[key]=(record,record_path)
    expected={("final",owner,variant) for owner in state["owners"] for variant in ("A","B")}
    helper.need(len(records)==16 and set(records)==expected,"fresh final probe scope differs")
    rows=helper.verify_probe_sources("final3",records)
    result=dict(status="VERIFIED_SOURCE_PRESERVATION_ONLY",edition="final3",probe_count=16,
        original_source_bytes_preserved=True,delivered_and_executed_probe_bytes_identical=True,
        all_fresh_source_bindings_match_snapshot=True,native_checks_asserted=False,
        harness_revision=helper.REVISION,chunk_size=2048,
        snapshot=dict(path=state_path.relative_to(ROOT).as_posix(),sha256=sha(state_path)),
        manifest=dict(path=manifest_path.relative_to(ROOT).as_posix(),sha256=sha(manifest_path)),
        historical_harness_provenance=dict(path="evidence/probes/Rule10/final2/seal-provenance.json",
            sha256=sha(ROOT/"evidence/probes/Rule10/final2/seal-provenance.json"),edition="final2"),
        probes=rows,limitations=["This read-only byte/manifest check asserts no native probe result.",
            "Historical final2 optimization pilots remain historical; final3 native seals/controls and summary are independently required."])
    destination=OUT/"probe-source-preservation.json"
    destination.write_text(json.dumps(result,indent=2,ensure_ascii=False)+"\n")
    print(json.dumps(dict(status=result["status"],probes=16,path=destination.relative_to(ROOT).as_posix())))


if __name__=="__main__":
    main()
