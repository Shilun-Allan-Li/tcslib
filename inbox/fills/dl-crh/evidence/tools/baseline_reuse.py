#!/usr/bin/env python3
"""Verify reuse of original final2 baseline evidence by fresh final3 audits.

Run with python3 -I. This tool runs no Lean/Lake checks and never copies or
relabels native records. Git reads verify the exact issued baseline sources.
"""
from __future__ import annotations
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
PROBES = ROOT / "evidence/probes/Rule10"
BASE = "eff2dcd0a63f0c371118a17c67b9a5dfc046f4e9"
sys.dont_write_bytecode = True


def need(ok, why):
    if not ok:
        raise RuntimeError(why)


def read(path):
    return json.loads(path.read_text())


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def load(name):
    path = Path(__file__).with_name(name + ".py")
    spec = importlib.util.spec_from_file_location("dl_crh_baseline_reuse_" + name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--edition", default="final3")
    parser.add_argument("--base-edition", default="final2")
    args = parser.parse_args()
    need(args.edition == "final3" and args.base_edition == "final2", "this reuse audit is pinned to final3/final2")
    P, R, S, H = (load(name) for name in ("rule10_prepare", "rule10_run", "rule10_summary", "seal_provenance"))
    evidence = {}
    def capture(path, role):
        path = path.resolve()
        relative = path.relative_to(ROOT).as_posix()
        if relative in evidence:
            need(sha(path) == evidence[relative]["sha256"], "evidence changed during reuse verification")
            evidence[relative]["roles"] = sorted(set(evidence[relative]["roles"] + [role]))
        else:
            evidence[relative] = dict(path=relative,sha256=sha(path),roles=[role])
        return dict(path=relative,sha256=evidence[relative]["sha256"])
    state_path = PROBES / "base-state.json"
    state = read(state_path)
    need(state["base"] == P.BASE == BASE and len(state["source_hashes"]) == 98, "issued base pin/closure differs")
    base_snapshot = ROOT / state["snapshot_root"]
    base_runtime = ROOT / state["root"]
    R.verify_source_snapshot(state, base_snapshot)
    R.verify_source_snapshot(state, base_runtime)
    source_bindings = []
    for source, digest in sorted(state["source_hashes"].items()):
        need(hashlib.sha256(P.git(source)).hexdigest() == digest, "source snapshot is not the exact Git issue base")
        source_bindings.append(dict(module=source.removesuffix(".lean").replace("/","."),source=source,
            sha256=digest,snapshot=capture(base_snapshot/source,"exact Git-base source"),runtime_source_unchanged=True))
    pin_sources = {}
    for source in ("lean-toolchain", "lake-manifest.json"):
        expected = hashlib.sha256(P.git(source)).hexdigest()
        need(sha(base_snapshot/source) == sha(base_runtime/source) == sha(ROOT/source) == expected,
             "baseline/current compiler or package pin differs")
        pin_sources[source] = capture(base_snapshot/source,"exact issued compiler/package pin")
    need((base_snapshot/"lean-toolchain").read_text().strip() == "leanprover/lean4:v4.25.0", "wrong Lean version")
    R.verify_base_products(state)
    bootstrap = {}
    for path in (ROOT/"evidence/logs/rule10").rglob("results.jsonl"):
        for line in path.read_text().splitlines():
            if not line.strip(): continue
            row=json.loads(line)
            if row.get("side")=="base" and row.get("phase")=="base-bootstrap" and row.get("end","")>=bootstrap.get(row["module"],{}).get("end",""):
                bootstrap[row["module"]] = row
                capture(path,"original exact-base bootstrap results")
    objects = []
    order_path = PROBES/"base-order.txt"
    order = order_path.read_text().splitlines()
    need(len(order)==98 and set(order)=={p.removesuffix(".lean") for p in state["source_hashes"]}, "base module order differs")
    for module in order:
        row=bootstrap[module]
        obj=ROOT/state["olean_tree"]/(module+".olean")
        need(row["source_unchanged"] is True and row["source_sha256"]==row["source_after_sha256"]==state["source_hashes"][module+".lean"] and
             row["exit_code"]==0 and sha(obj)==row["olean_sha256"], "baseline source/object changed")
        log=ROOT/row["log"]
        need(sha(log)==row["log_sha256"], "baseline bootstrap raw log changed")
        capture(log,"original exact-base bootstrap log")
        objects.append(dict(module=module,runtime_olean_path=obj.relative_to(ROOT).as_posix(),sha256=sha(obj),
                            matches_original_bootstrap=True))
    old_snapshot=read(PROBES/args.base_edition/"snapshot.json")
    fresh_snapshot_path=PROBES/args.edition/"snapshot.json"
    fresh_snapshot=read(fresh_snapshot_path)
    need(old_snapshot["base"]==fresh_snapshot["base"]==BASE and old_snapshot["owners"]==fresh_snapshot["owners"], "fresh final owner scope/base differs")
    changed=[path for path,digest in fresh_snapshot["source_hashes"].items() if old_snapshot["source_hashes"].get(path)!=digest]
    need(set(changed)=={"TCSlib/Cryptography/Hashing/FromDiscreteLog.lean","TCSlib/Cryptography/Hashing/FromDiscreteLog/Reduction.lean"},
         "fresh source changes exceed the declared proof-body repair scope")
    _,adapter=P.builders()
    seal_manifest_path=PROBES/args.base_edition/"base-seal-manifest.json"
    seal_manifest=read(seal_manifest_path)
    need(len(seal_manifest["probes"])==4, "baseline seal scope differs")
    base_records={}
    seal_rows=[]
    for entry in seal_manifest["probes"]:
        record_path=ROOT/entry["record"]
        record=read(record_path)
        need(record["side"]=="base" and record["source_sha256"]==state["source_hashes"][record["source"]], "baseline request source differs")
        key=("base",record["owner"],record["variant"])
        need(key not in base_records, "duplicate original baseline seal")
        base_records[key]=(record,record_path)
        native,failures,raw,_=H.verify_seal(args.base_edition,record,adapter)
        need(not failures, "unexpected original baseline source failures")
        capture(ROOT/raw["path"],"original baseline whole-file seal raw log")
        capture(record_path,"original baseline seal request record")
        capture(ROOT/record["delivered_probe_source"],"original baseline executed seal source copy")
        capture(ROOT/record["collector_log"],"original exact-base native closure collector")
        seal_rows.append(dict(owner=record["owner"],variant=record["variant"],raw_log=raw,
                              source_sha256=record["source_sha256"],probe_sha256=record["probe_sha256"],
                              requested=record["requested"],valid=True,failing_declarations=[]))
    H.verify_probe_sources(args.base_edition,base_records)
    controls,control_support=H.verify_controls(args.base_edition,adapter)
    for item in controls["raw_logs"]+control_support:
        capture(ROOT/item["path"],"original baseline paired controls evidence")
    control_plan=read(PROBES/args.base_edition/"base-controls-plan.json")
    for plan in control_plan["probes"]:
        capture(ROOT/plan["delivered_source"],"original baseline paired control source copy")
    scan_path=PROBES/args.base_edition/"base-explicit-scan.json"
    review_path=PROBES/args.base_edition/"base-explicit-manual-review.json"
    scan,review=read(scan_path),read(review_path)
    need(review["status"]=="COMPLETE" and review["reviewed_all_rows"] is True and review["pending_rows"]==0 and
         review["new_foreign_definition_hits"]==0 and review["side"]=="base" and review["edition"]==args.base_edition and
         review["row_count"]==len(review["rows"])==len(scan["items"])==208, "original base manual scan review is incomplete")
    need(sha(scan_path)==review["native_scan_sha256"] and sha(ROOT/scan["native_log"])==scan["native_log_sha256"] and
         sha(ROOT/review["plan"])==review["plan_sha256"], "original base scan/review provenance differs")
    for item,reviewed in zip(scan["items"],review["rows"]):
        need(item["path"]==reviewed["path"] and item["line"]==reviewed["line"] and item["item"]==reviewed["item"] and
             reviewed["status"]=="REVIEWED", "original manual review/source row differs")
    for path,role in ((scan_path,"original baseline native explicit scan"),(review_path,"original complete base manual review"),
                      (review_path.with_suffix(".md"),"original complete base manual review text"),
                      (ROOT/review["plan"],"original baseline scan plan"),(ROOT/scan["native_log"],"original baseline native scan raw log"),
                      (ROOT/"evidence/logs/rule10"/args.base_edition/"scan-base/results.jsonl","original baseline native scan results"),
                      (ROOT/read(ROOT/review["plan"])["delivered_source"],"original baseline native scan source copy")):
        capture(path,role)
    census_path=ROOT/"evidence/logs/rule10/checkpoint1/base-collect/evidence_probes_Rule10_CensusBase.001.log"
    census=S.parse_census(census_path)
    need(len(census)==172 and {row["module"] for row in census.values()}==set(state["owners"]), "base all-stored census scope differs")
    collect_results=ROOT/"evidence/logs/rule10/checkpoint1/base-collect/results.jsonl"
    collect_rows=[json.loads(line) for line in collect_results.read_text().splitlines() if line.strip()]
    for module in ("evidence/probes/Rule10/CollectBase","evidence/probes/Rule10/CensusBase"):
        selected=[r for r in collect_rows if r["module"]==module]
        need(len(selected)==1, "base collector/census result identity differs")
        row=selected[0]
        need(row["exit_code"]==0 and row["source_unchanged"] is True and
             sha(ROOT/row["log"])==row["log_sha256"] and sha(base_runtime/(module+".lean"))==
             sha(base_snapshot/(module+".lean"))==row["source_sha256"]==row["source_after_sha256"], "base collector/census changed")
        capture(base_snapshot/(module+".lean"),"original exact-base collector/census source")
        capture(ROOT/row["log"],"original exact-base collector/census raw log")
    historical_path=PROBES/args.base_edition/"seal-provenance.json"
    historical=read(historical_path)
    need(historical["status"]=="COMPLETE" and historical["edition"]==args.base_edition and
         historical["harness_revision"]==P.HARNESS_REVISION and historical["chunk_size"]==P.CHUNK_SIZE==2048,
         "historical harness pilot is not complete/same revision")
    for source,digest in historical["retained_tool_sha256"].items():
        need(sha(ROOT/source)==digest, "historical/current generator tool differs")
        capture(ROOT/source,"unchanged historical/current generator bytes")
    for source,digest in historical["api_source_hashes"].items():
        need(sha(ROOT/source)==digest, "historical pinned API source differs")
        capture(ROOT/source,"retained ordinary attribute API source")
    for item in historical["raw_logs"]+historical["supporting_files"]+[historical["static_assembly"]]:
        need(sha(ROOT/item["path"])==item["sha256"], "historical pilot evidence differs")
        capture(ROOT/item["path"],"original historical harness pilot evidence")
    capture(historical_path,"completed historical final2 optimization pilot")
    capture(seal_manifest_path,"original baseline whole-file seal manifest")
    capture(ROOT/"evidence/logs/rule10"/args.base_edition/"seals-base/results.jsonl","original four baseline seal results")
    capture(collect_results,"original exact-base collector/census results")
    capture(order_path,"original 98-module baseline order")
    state_reference=capture(state_path,"original unchanged exact-base state")
    # Freeze every input binding only after all read-only checks have passed.
    for item in evidence.values():
        need(sha(ROOT/item["path"])==item["sha256"], "original evidence changed before reuse record")
    result=dict(status="COMPLETE",edition=args.edition,base_edition=args.base_edition,base=BASE,
        baseline_unchanged=True,raw_records_reused_without_relabeling=True,
        fresh_final_evidence_edition=args.edition,base_state=state_reference,
        source_hashes=state["source_hashes"],source_bindings=source_bindings,
        exact_module_pins=dict(base=BASE,compiler="leanprover/lean4:v4.25.0",source_module_count=98,
                              owner_modules=state["owners"],pin_sources=pin_sources),
        runtime_object_verifications=objects,base_seals=seal_rows,base_controls=dict(probe_count=8,all_pass=True),
        base_scan=dict(path=scan_path.relative_to(ROOT).as_posix(),sha256=sha(scan_path),items=208),
        base_manual_review=dict(path=review_path.relative_to(ROOT).as_posix(),sha256=sha(review_path),rows=208),
        base_census=dict(path=census_path.relative_to(ROOT).as_posix(),sha256=sha(census_path),stored_constants=172),
        historical_harness_provenance=dict(path=historical_path.relative_to(ROOT).as_posix(),sha256=sha(historical_path),
            edition=args.base_edition,harness_revision=P.HARNESS_REVISION,chunk_size=P.CHUNK_SIZE,same_generator_tools=True),
        fresh_final_snapshot=dict(path=fresh_snapshot_path.relative_to(ROOT).as_posix(),sha256=sha(fresh_snapshot_path),
                                 changed_since_final2=sorted(changed)),
        original_evidence=[evidence[path] for path in sorted(evidence)],
        limits=["Original final2 base runs are reused under their original paths and identities; no new base run is claimed.",
                "Historical final2 optimization pilots validate the unchanged harness, not the repaired final3 proof bodies.",
                "Fresh final3 collectors, final seals, final controls, final scan/review and sweep remain independently required.",
                "Runtime baseline oleans are checked in place and are intentionally not included in delivery caches."])
    destination=PROBES/args.edition/"baseline-reuse.json"
    destination.write_text(json.dumps(result,indent=2,ensure_ascii=False)+"\n")
    print(json.dumps(dict(status="COMPLETE",path=destination.relative_to(ROOT).as_posix(),original_files=len(evidence),
                         source_modules=98,base_seals=4,base_controls=8,base_scan=208,base_census=172),indent=2))


if __name__=="__main__":
    main()
