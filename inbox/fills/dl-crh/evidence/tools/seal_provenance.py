#!/usr/bin/env python3
"""Verify completed optimized-harness pilots and write bound provenance.

Run with python3 -I. This tool never invokes Lean, Lake, subprocesses or Git.
It writes seal-provenance.json only after every required assertion passes.
"""
from __future__ import annotations
import argparse
import datetime
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[2]
PROBES = ROOT / "evidence/probes/Rule10"
OWNER = "TCSlib.Cryptography.Candidates.DiscreteLog"
REVISION = "batch2048-ordinary-local-attribute-api-v2"
sys.dont_write_bytecode = True


def need(ok, reason):
    if not ok:
        raise RuntimeError(reason)


def read(path):
    return json.loads(path.read_text())


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def rel(path):
    return path.resolve().relative_to(ROOT).as_posix()


def reference(path):
    return dict(path=rel(path), sha256=sha(path))


def load_tool(name):
    path = Path(__file__).with_name(name + ".py")
    spec = importlib.util.spec_from_file_location("dl_crh_provenance_" + name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


P = load_tool("rule10_prepare")
R = load_tool("rule10_run")
S = load_tool("rule10_summary")


def jsonl(path):
    need(path.is_file(), "required completed results absent: " + rel(path))
    return [json.loads(line) for line in path.read_text().splitlines() if line.strip()]


def latest(rows, key):
    result = {}
    for row in rows:
        identity = row[key]
        if row.get("end", "") >= result.get(identity, {}).get("end", ""):
            result[identity] = row
    return result


def duration(row):
    start = datetime.datetime.fromisoformat(row["start"])
    end = datetime.datetime.fromisoformat(row["end"])
    need(start.utcoffset() == datetime.timedelta(0) and end.utcoffset() == datetime.timedelta(0),
         "pilot timestamps are not UTC")
    elapsed = (end - start).total_seconds()
    need(elapsed > 0, "pilot duration is not positive")
    return elapsed


def source_tree(side):
    return ROOT / read(PROBES / "base-state.json")["root"] if side == "base" else ROOT


def restore_source(probe, insertions):
    previous_end = 0
    for item in sorted(insertions, key=lambda row: row["probe_byte_offset"]):
        begin = item["probe_byte_offset"]
        end = begin + item["byte_count"]
        need(begin >= previous_end and end <= len(probe), "overlapping/out-of-range insertion")
        need(hashlib.sha256(probe[begin:end]).hexdigest() == item["sha256"], "insertion bytes differ")
        previous_end = end
    original = probe
    for item in sorted(insertions, key=lambda row: row["probe_byte_offset"], reverse=True):
        begin = item["probe_byte_offset"]
        original = original[:begin] + original[begin + item["byte_count"]:]
    return original


def manifests(edition):
    result = {}
    for side in ("base", "final"):
        path = PROBES / edition / (side + "-seal-manifest.json")
        manifest = read(path)
        for entry in manifest["probes"]:
            record_path = ROOT / entry["record"]
            record = read(record_path)
            key = (side, record["owner"], record["variant"])
            need(key not in result, "duplicate seal identity")
            need(record["probe_sha256"] == entry["probe_sha256"], "manifest probe binding differs")
            result[key] = (record, record_path)
    need(len(result) == 20, "expected exactly 20 base/final seal records")
    return result


def verify_probe_sources(edition, records):
    rows = []
    base_state = read(PROBES / "base-state.json")
    final_state = read(PROBES / edition / "snapshot.json")
    for (side, owner, variant), (record, record_path) in sorted(records.items()):
        state = base_state if side == "base" else final_state
        snapshot = ROOT / state["snapshot_root"] if side == "base" else PROBES / edition / "snapshot"
        original_path = snapshot / record["source"]
        original = original_path.read_bytes()
        need(sha(original_path) == state["source_hashes"][record["source"]] == record["source_sha256"],
             "snapshot/source binding differs")
        executed = source_tree(side) / (record["probe_module"] + ".lean")
        delivered = ROOT / record["delivered_probe_source"]
        need(sha(executed) == sha(delivered) == record["probe_sha256"], "executed/delivered probe differs")
        need(restore_source(delivered.read_bytes(), record["insertions"]) == original,
             "insertion removal does not reconstruct exact snapshot: " + record["label"])
        rows.append(dict(side=side, owner=owner, variant=variant, requested=len(record["rows"]),
                         record=reference(record_path), delivered_probe=reference(delivered),
                         source_sha256=record["source_sha256"], original_bytes_reconstructed=True))
    return rows


def filter_chunk(text, label):
    return "\n".join(line for line in text.splitlines()
        if not ("G06-COMPONENT label=" in line or "G06-MASK label=" in line)
        or "label=" + label + " " in line)


def verify_masks(adapter, text, plan):
    for chunk in plan["chunks"]:
        rows = plan["rows"][chunk["start"]:chunk["start"] + chunk["count"]]
        filtered = filter_chunk(text, chunk["label"])
        adapter.verify_component_log(filtered, chunk["label"], rows, ("install", "eof"))
        adapter.verify_mask_log(filtered, chunk["label"], rows, ("install", "eof"))


def verify_seal(edition, record, adapter):
    result_path = ROOT / "evidence/logs/rule10" / edition / "seals-base/results.jsonl"
    done = latest(jsonl(result_path), "label")
    need(record["label"] in done, "full base-A native pilot not completed: " + edition)
    row = done[record["label"]]
    log = ROOT / row["log"]
    need(sha(log) == row["log_sha256"], "pilot raw log changed")
    need(row["source_sha256"] == row["source_after_sha256"] == record["probe_sha256"] and
         row["source_unchanged"] is True, "pilot source hash mismatch")
    need(row["exit_code"] == 0 and row["mask_verified"] is True and
         row["actual_name_components_verified"] is True and row["harness_error"] is None,
         "full base-A pilot is not a native zero-exit valid harness")
    text = log.read_text(errors="replace")
    verify_masks(adapter, text, record)
    diagnostics = R.errors(text)
    need(diagnostics == row["errors"] and not diagnostics, "zero-exit pilot contains diagnostics")
    need(not re.search(r"^FAIL\(", text, re.M), "native checker reports a failure")
    failures = R.failing_sources(record, diagnostics, source_tree("base"), P)
    need(failures == row["failing_declarations"], "pilot failing-declaration inventory differs")
    # The final2 seals JSONL continues growing after the first pilot. Bind the
    # selected row itself; main retains it in a separate immutable snapshot.
    selected = dict(path=rel(result_path), label=row["label"],
                    selected_record_sha256=hashlib.sha256(
                        json.dumps(row, sort_keys=True, separators=(",", ":")).encode()).hexdigest())
    return row, failures, reference(log), selected


def verify_controls(edition, adapter):
    plan_path = PROBES / edition / "base-controls-plan.json"
    plans = read(plan_path)["probes"]
    need(len(plans) == 8, "expected all eight base control probes")
    expected = {(owner, variant, sealed) for owner in read(PROBES / "base-state.json")["owners"]
                for variant in ("A", "B") for sealed in (False, True)}
    need({(p["owner"], p["variant"], p["sealed"]) for p in plans} == expected, "base control scope differs")
    directory = ROOT / "evidence/logs/rule10" / edition / "controls-base"
    validation_path = directory / "control-validation.jsonl"
    result_path = directory / "results.jsonl"
    validations = latest(jsonl(validation_path), "label")
    native = latest(jsonl(result_path), "log")
    findings = []
    raw_logs = []
    for plan in plans:
        need(plan["label"] in validations, "base control validation incomplete: " + plan["label"])
        validation = validations[plan["label"]]
        need(validation["passed"] is True and not validation["unexpected_errors"], "base control validation failed")
        need(validation["raw_log"] in native, "native control result absent")
        row = native[validation["raw_log"]]
        log = ROOT / row["log"]
        need(sha(log) == row["log_sha256"] == validation["raw_log_sha256"], "control raw log differs")
        source = source_tree("base") / (plan["module"] + ".lean")
        delivered = ROOT / plan["delivered_source"]
        need(sha(source) == sha(delivered) == plan["source_sha256"] == row["source_sha256"] ==
             row["source_after_sha256"] and row["source_unchanged"] is True, "control source binding differs")
        text = log.read_text(errors="replace")
        if plan["sealed"]:
            verify_masks(adapter, text, plan)
        else:
            adapter.verify_component_log(text, plan["label"], plan["rows"], ("catalog-unsealed", "catalog-eof"))
        unmatched = R.errors(text)
        need(unmatched == row["errors"], "recorded control diagnostics differ")
        checks = []
        for control in plan["controls"]:
            hits = [error for error in unmatched if control["start_line"] <= error["line"] <= control["end_line"]]
            expected_errors = 1 if plan["sealed"] and control["negative"] else 0
            need(len(hits) == expected_errors, "control does not have exact expected diagnostics")
            checks.append(dict(control=control["name"], expected_errors=expected_errors, actual_errors=len(hits)))
            unmatched = [error for error in unmatched if error not in hits]
        need(not unmatched, "unexpected control diagnostics outside proof ranges")
        expected_errors = sum(check["expected_errors"] for check in checks)
        need(row["exit_code"] == (1 if expected_errors else 0), "control native exit differs")
        statuses = [int(value) for value in re.findall(r"^FAIL\([^\n]*\): lean exited with status (\d+)$", text, re.M)]
        need(all(status == 1 for status in statuses), "control has abnormal native exit")
        findings.append(dict(label=plan["label"], sealed=plan["sealed"], owner=plan["owner"],
                             variant=plan["variant"], checks=checks, passed=True,
                             raw_log=reference(log), source=reference(delivered)))
        raw_logs.append(reference(log))
    return dict(unsealed_pass=True, sealed_expected_failures_exactly_once=True, reader_positives_pass=True,
                probe_count=len(plans), probes=findings, raw_logs=raw_logs), [reference(plan_path), reference(validation_path), reference(result_path)]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--edition", default="final2")
    parser.add_argument("--prior-edition", default="final1")
    args = parser.parse_args()
    need(args.edition == "final2" and args.prior_edition == "final1", "this comparison is pinned to final1/final2")
    template_path = PROBES / "harness-v2-provenance-template.json"
    result = read(template_path)
    need(result["status"] == "PENDING_NATIVE_PILOT", "unexpected provenance template status")
    assembly_path = ROOT / result["static_assembly"]["path"]
    need(sha(assembly_path) == result["static_assembly"]["sha256"], "static assembly evidence changed")
    assembly = read(assembly_path)
    need(P.HARNESS_REVISION == result["harness_revision"] == assembly["harness_revision"] == REVISION and
         P.CHUNK_SIZE == result["chunk_size"] == assembly["chunk_size"] == 2048, "harness revision differs")
    for source, digest in result["api_source_hashes"].items():
        need(sha(ROOT / source) == digest, "retained pinned API source differs")
    tool_hashes = {}
    for source, digest in assembly["tool_sha256"].items():
        path = ROOT / "evidence/tools" / Path(source).name
        need(sha(path) == digest, "retained/original harness tool bytes changed: " + path.name)
        tool_hashes[rel(path)] = digest
    for phase in ("install", "eof"):
        counters = assembly["phases"][phase]
        need(counters["command_elaboration_calls"] == 0 and counters["direct_status_setter"] is False and
             counters["unsafe_reducibility"] is False, "unsafe/unreviewed static assembly")
    need(assembly["phases"]["install"]["ordinary_local_attribute_api_calls"] == 1, "ordinary attribute API absent")
    old_records = manifests(args.prior_edition)
    new_records = manifests(args.edition)
    need(old_records.keys() == new_records.keys(), "old/new seal owner scopes differ")
    comparisons = []
    for key in sorted(new_records):
        old, old_path = old_records[key]
        new, new_path = new_records[key]
        need(old["rows"] == new["rows"] and old["source_sha256"] == new["source_sha256"],
             "old/new source or full request rows differ")
        need(new["chunks"] == P.seal_chunks(new["label"], new["rows"]) and
             new["harness_revision"] == REVISION and new["chunk_size"] == 2048, "new chunk metadata differs")
        comparisons.append(dict(side=key[0], owner=key[1], variant=key[2], requested=len(new["rows"]),
                                request_rows_identical=True, source_sha256=new["source_sha256"],
                                old_record=reference(old_path), new_record=reference(new_path)))
    old_sources = verify_probe_sources(args.prior_edition, old_records)
    new_sources = verify_probe_sources(args.edition, new_records)
    pilot_key = ("base", OWNER, "A")
    old_record = old_records[pilot_key][0]
    new_record = new_records[pilot_key][0]
    active = assembly["active_final1_probe_binding"]
    active_path = source_tree("base") / (old_record["probe_module"] + ".lean")
    need(sha(active_path) == active["sha256"] == old_record["probe_sha256"] and active["matches_original_record"] is True,
         "original final1 active probe source was changed")
    _, adapter = P.builders()
    controls, support = verify_controls(args.edition, adapter)
    old_run, old_failures, old_log, old_results = verify_seal(args.prior_edition, old_record, adapter)
    new_run, new_failures, new_log, new_results = verify_seal(args.edition, new_record, adapter)
    old_set = sorted({S.source_key(error) for error in old_failures if error["classification"] == "SOURCE"})
    new_set = sorted({S.source_key(error) for error in new_failures if error["classification"] == "SOURCE"})
    need(old_set == new_set, "old/new full base-A source failure sets differ")
    old_seconds, new_seconds = duration(old_run), duration(new_run)
    native_snapshot = PROBES / args.edition / "seal-provenance-native-records.json"
    native_snapshot.write_text(json.dumps(dict(old=old_run, new=new_run), indent=2, ensure_ascii=False)+"\n")
    native_reference = reference(native_snapshot)
    old_results["retained_records"] = native_reference
    new_results["retained_records"] = native_reference
    result.update(status="COMPLETE", edition=args.edition, prior_edition=args.prior_edition,
        ordinary_registered_local_attribute_api=True, prior_final1_artifacts_preserved=True,
        request_rows_unchanged=True, original_source_bytes_preserved=True,
        retained_tool_sha256=tool_hashes, request_comparisons=comparisons,
        old_probe_source_verifications=old_sources, probe_source_verifications=new_sources,
        control_pilots=controls,
        full_seal_pilot=dict(side="base", owner=OWNER, variant="A", harness_valid=True,
            mask_components_install_eof_verified=True, raw_logs=[new_log], native_results=new_results),
        comparison=dict(baseA_failing_declarations_equal=True, old_failing_declarations=old_set,
            new_failing_declarations=new_set, raw_logs=[old_log, new_log]),
        benchmark=dict(old_duration_seconds=old_seconds, new_duration_seconds=new_seconds,
            old_seconds=old_seconds, new_seconds=new_seconds, old_start=old_run["start"],
            old_end=old_run["end"], new_start=new_run["start"], new_end=new_run["end"]),
        raw_logs=controls["raw_logs"]+[old_log,new_log], supporting_files=support+[native_reference],
        selected_native_records=[old_results,new_results],
        limits=["Completion certifies this optimization's base-control and full base-A pilots, source reconstruction and request equivalence.",
                "Final all-owner seals, final controls, scans and the full issued sweep remain independently required."])
    destination = PROBES / args.edition / "seal-provenance.json"
    destination.write_text(json.dumps(result, indent=2, ensure_ascii=False)+"\n")
    print(json.dumps(dict(status="COMPLETE", path=rel(destination), probe_pairs=len(comparisons),
                         base_controls=controls["probe_count"], benchmark=result["benchmark"]), indent=2))


if __name__ == "__main__":
    main()
