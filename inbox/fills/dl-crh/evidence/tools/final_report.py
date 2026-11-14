#!/usr/bin/env python3
"""Generate FINAL-REPORT.md only after the actual final evidence has cleared.

Use python3 -I. This never starts Lean/Lake, builds a payload, pushes, or marks a
goal complete. Missing/pending/failed evidence aborts before any report is written.
Base/final manual-review paths are arguments so finalized review artifacts can be
supplied without weakening the completion checks.
"""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import re
import subprocess
from zipfile import ZipFile

BASE = "eff2dcd0a63f0c371118a17c67b9a5dfc046f4e9"
HEAD = "fa33b9b8fa3a9b801a7db8857d7a2739c61c1e16"
PRE_REPAIR_HEAD = "5a24269932a72f672104b18280609879dd992c82"
EXPECTED_PATCH_COUNT = 4
FINAL_SCAN_ROWS = {"final1": 595, "final2": 595, "final3": 595}
ISSUE = "b436d19a0310265b214447ea6710deba32df6dd8"
STANDARD = {"propext", "Classical.choice", "Quot.sound"}
TARGET = "TCSlib.Cryptography.Authentication.dlHash_crh"
MAIN = "TCSlib/Cryptography/Hashing/FromDiscreteLog.lean"
PROVIDER = "TCSlib/Cryptography/Candidates/DiscreteLog.lean"
HELPERS = ("Algebra", "Coins", "Encoding", "Probability", "Reduction", "Sampling")
CHANGED = {MAIN, PROVIDER} | {MAIN.removesuffix(".lean") + "/" + name + ".lean" for name in HELPERS}
CHECKPOINTS = [
    ("checkpoint 1: reader escalation", "396c734fac3ba4a0e8d06320517f56017962f734"),
    ("initial escalation final record (proof remained admitted)", "dc9846a2d46aca5be8fe6d48f2c9064090a48014"),
    ("checkpoint 2: compression and collision shape", "cb64931761fae93c916535fc454f8c5a5a4bcab0"),
    ("checkpoint 3: concrete reduction and collision-to-DL success", "88cca5e5dd801753da004f86c982f1f80f0a270a"),
]
OVERLAPS = [
    ("TCSlib/Cryptography/Candidates/DiscreteLogHardcore.lean", "dlb_expo_val",
     "Arbitrary-natural unit-power values were rederived from public val_units_pow, coe_expUnit, and expValid_iff."),
    ("TCSlib/Cryptography/Candidates/Factoring.lean", "fac_listToNat_inj",
     "Equal-width numeral injectivity was rederived through public numeral canonicity in inputWord_num_ext."),
    ("TCSlib/Cryptography/Asymptotic/UniversalPadding.lean", "ofFn_splitCoins_symm_cast",
     "Coin-cast concatenation was rederived using public ofFn_arrowCongr_finCongr and ofFn_splitCoins_symm."),
    ("TCSlib/Cryptography/Candidates/DiscreteLog.lean", "dla_statClose_expDec",
     "Overlapping residue relabel/statistical-switch submaterial uses public sampler closeness and Mathlib ZMod.finEquiv; the private implementation was not copied."),
]
PROMOTIONS = [
    "Encoding: ofFn_splitBits_fst, ofFn_splitBits_snd, inputWord_split, inputWord_take, inputWord_drop, inputWord_ext, inputWord_num_ext, boundedInputEquiv, boundedInputEquiv_apply, boundedInputEquiv_symm_apply, card_boundedInput, and card_boundedRange → shared authentication/bit-vector encoding.",
    "Algebra: private residue_difference → shared natural modular arithmetic; expUnit_pow_val → the candidate unit-power interface.",
    "Coins: sumCoinsEquiv, sumCoinsEquiv_eq, and sumCoinsEquiv_symm_ofFn → the shared randomized/collection coin interface.",
    "Reduction: modularDifference, modularDifference_eq, modularDifference_value, and polyTimeComputable_modularDifference → the shared arithmetic string layer. The local padding-idempotence argument in collisionPost_split is a candidate shared padStr lemma.",
    "Probability: expect_sample_eq_uexp → the shared games bridge/probability layer; collision_accept_eq → Hashing/CollisionResistant.",
    "Sampling: residueFinEquiv, residueFinEquiv_eq, and residueFinEquiv_val → finite-residue encoding; sampleBelowL_uprob_le → the candidate sampler interface; expEval_natToList_val → canonical candidate-evaluator readers.",
]


def need(condition, message):
    if not condition:
        raise RuntimeError(message)


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def read(path):
    return json.loads(Path(path).read_text())


def git(*args):
    return subprocess.check_output(["git", *args])


def rows(path):
    return [json.loads(line) for line in Path(path).read_text().splitlines() if line.strip()]


def verify_manual(path, side, edition):
    review = read(path)
    need(review.get("status") == "COMPLETE", f"{side} manual scan review is not COMPLETE")
    need(review.get("reviewed_all_rows") is True, f"{side} review did not review all rows")
    need(review.get("pending_rows") == 0, f"{side} review retains pending rows")
    need(review.get("new_foreign_definition_hits") == 0,
         f"{side} review has a new foreign-definition BODY-reading violation")
    need(review.get("side", side) == side and review.get("edition", edition) == edition,
         f"{side} review provenance differs")
    plan_path = Path(review["plan"])
    need(sha(plan_path) == review["plan_sha256"], f"{side} scan plan hash differs")
    plan = read(plan_path)
    need(len(review["rows"]) == len(plan["items"]), f"{side} review is not row complete")
    need(review.get("row_count", len(review["rows"])) == len(review["rows"]), f"{side} review row count differs")
    for row in review["rows"]:
        for key in ("status", "final_native_disposition", "draft_disposition"):
            if key in row and key != "draft_disposition":
                value = str(row[key]).upper()
                need(not any(word in value for word in ("PENDING", "NOT_YET", "UNRESOLVED")),
                     f"{side} row has an unfinished {key}: {row}")
    native = review.get("native_scan")
    need(native and review.get("native_scan_sha256"), f"{side} review lacks native scan provenance")
    need(sha(native) == review["native_scan_sha256"], f"{side} native scan hash differs")
    for field in ("native_log", "source_snapshot"):
        if field in review:
            need(sha(review[field]) == review[field + "_sha256"], f"{side} {field} hash differs")
    if side == "final":
        owner_hashes = review.get("reviewed_owner_source_hashes")
        need(owner_hashes and set(owner_hashes) == CHANGED, "final review does not bind all eight owned source files")
        need(all(sha(source) == digest for source, digest in owner_hashes.items()),
             "final review source bytes differ from the repaired proof")
        snapshot = read(review["source_snapshot"])
        need(snapshot["edition"] == edition and snapshot["base"] == BASE,
             "final review snapshot provenance differs")
        need(all(sha(source) == digest for source, digest in snapshot["source_hashes"].items()),
             "final review import-closure source bytes changed")
    return review


def verify_explicit_scan_schema(reviews, summary=None):
    """Verify completed review/native schema; optionally bind the final summary."""
    final_edition = reviews["final"]["edition"]
    need(final_edition in FINAL_SCAN_ROWS, "fresh final scan row count must be pinned after the repaired commit")
    need(len(reviews["base"]["rows"]) == 208 and
         len(reviews["final"]["rows"]) == FINAL_SCAN_ROWS[final_edition],
         "manual scan inventories differ from the unchanged proof-source plans")
    raw_scans = {side: read(reviews[side]["native_scan"]) for side in ("base", "final")}
    for side, candidates, unresolved in (("base", 0, 10), ("final", 4, 15)):
        need(len(raw_scans[side]["foreign_definition_items"]) == candidates and
             len(raw_scans[side]["unresolved_items"]) == unresolved,
             "raw scan candidate/unresolved counts differ from reviewed inventories")
        if summary is not None:
            raw_summary = summary["explicit_scan"][side]
            need(raw_summary["foreign_definition_items"] == candidates and
                 raw_summary["unresolved_items"] == unresolved,
                 "summary scan candidate/unresolved counts differ from reviewed native inventories")
    need(all(row["item"] == "↓reduceIte" and row["head"] == "reduceIte" and
             all(candidate["home"] == "Lean.Meta.Tactic.Simp.BuiltinSimprocs.Core" and
                 candidate["name"] == "reduceIte" for candidate in row["foreign_definitions"])
             for row in raw_scans["final"]["foreign_definition_items"]),
         "raw final foreign-definition candidates differ from the four reviewed simproc invocations")
    support_path = reviews["final"].get("supporting_simproc_source_evidence")
    need(support_path and Path(support_path).is_file(), "final simproc source-review evidence absent")
    support = read(support_path)
    need(support["lean_pin"] == "4.25.0", "simproc source evidence has the wrong Lean pin")
    excerpts = "\n".join(excerpt["source"] for source in support["sources"] for excerpt in source["excerpts"])
    for token in ("builtin_simproc", "reduceIte", "simproc", "addSimproc", "ite_cond_eq_true", "ite_cond_eq_false"):
        need(token in excerpts, "simproc source evidence omits " + token)
    return raw_scans


def verify_sweep(admission, result_path):
    need(admission["status"] == "PASS", "admission delta did not pass")
    need(admission["module_count"] == 176 and admission["baseline_total"] == 22 and admission["final_total"] == 21,
         "wrong sweep/admission counts")
    need(not admission["added"], "new admission")
    need(admission["removed"] == [dict(module=MAIN.removesuffix(".lean"), declaration="dlHash_crh", count=1)],
         "admission removal differs from the target only")
    result_path, order_path = Path(result_path), Path("evidence/final-order.txt")
    need(sha(result_path) == admission["results_sha256"] and sha(order_path) == admission["order_sha256"],
         "sweep changed since admission analysis")
    order = [s.strip() for s in order_path.read_text().splitlines() if s.strip()]
    latest = {row["module"]: row for row in rows(result_path)}
    need(len(order) == 176 and set(order) == set(latest), "incomplete final sweep")
    for module in order:
        row = latest[module]
        need(row["exit_code"] == 0 and row["source_unchanged"], "failed/changed sweep source: " + module)
        need(sha(row["log"]) == row["log_sha256"], "changed sweep log: " + module)
        need(sha(module + ".lean") == row["source_sha256"] == row["source_after_sha256"],
             "source changed after sweep: " + module)


def verify_style(style):
    need(style["base_counts"] == {"FAIL": 216, "WARN": 102} and
         style["final_counts"] == {"FAIL": 222, "WARN": 102}, "unexpected lint totals")
    need(sha(style["base_log"]) == style["base_sha256"] and sha(style["final_log"]) == style["final_sha256"],
         "lint log hash differs")
    added_fails = [item for item in style["added"] if item["status"] == "FAIL"]
    expected = {"facade does not import child module `TCSlib.Cryptography.Hashing.FromDiscreteLog." + h + "`"
                for h in HELPERS}
    need(len(added_fails) == 6 and {i["message"] for i in added_fails} == expected and
         all(i["path"] == "TCSlib/Cryptography/Hashing.lean" and i["count"] == 1 for i in added_fails),
         "new lint failures exceed the exact six-diagnostic exception")
    need(not any(i["status"] == "FAIL" for i in style["removed"]), "unexpected removed baseline FAIL")
    need("Acknowledge exactly six lint false positives" in Path("evidence/authorization.md").read_text(),
         "exact user lint exception is not recorded")


def target_header(text):
    start = text.index("theorem dlHash_crh ")
    return text[start:text.index(":= by", start)]


def historical_seal_findings(result_path):
    """Bind every superseded final2 source failure and its unchanged theorem type."""
    expected = {
        ("TCSlib.Cryptography.Hashing.FromDiscreteLog.Reduction", "A",
         "TCSlib.Cryptography.Authentication.FromDiscreteLog.collisionPost_split"): 1,
        ("TCSlib.Cryptography.Hashing.FromDiscreteLog.Reduction", "B",
         "TCSlib.Cryptography.Authentication.FromDiscreteLog.collisionPost_split"): 1,
        ("TCSlib.Cryptography.Hashing.FromDiscreteLog", "B",
         "TCSlib.Cryptography.Authentication.dlHash_compresses"): 3,
        ("TCSlib.Cryptography.Hashing.FromDiscreteLog", "B",
         "TCSlib.Cryptography.Authentication.dlHash_collision_accept_eq"): 1,
    }
    actual, findings = Counter(), []
    for record in rows(result_path):
        errors = record.get("failing_declarations", [])
        if not errors:
            continue
        need(all(error["classification"] == "SOURCE" for error in errors),
             "superseded run contains an unmapped/harness error")
        need(record["exit_code"] == 1 and record.get("harness_error") is None and
             record.get("actual_name_components_verified") and record.get("mask_verified") and
             record["source_unchanged"], "superseded source findings are not valid native seal evidence")
        need(sha(record["log"]) == record["log_sha256"], "superseded seal raw log hash differs")
        text = Path(record["log"]).read_text()
        native_errors = re.findall(r"^.*\.lean:\d+:\d+: error:", text, re.M)
        need(len(native_errors) == len(errors), "superseded raw diagnostic count differs from mapped findings")
        for declaration in sorted({error["declaration"] for error in errors}):
            selected = [error for error in errors if error["declaration"] == declaration]
            key = (record["owner"], record["variant"], declaration)
            actual[key] += len(selected)
            findings.append(dict(owner=record["owner"], variant=record["variant"], declaration=declaration,
                                 diagnostics=len(selected), source_lines=[error["source_line"] for error in selected],
                                 probe_lines=[error["line"] for error in selected],
                                 log=record["log"], log_sha256=record["log_sha256"]))
    need(actual == Counter(expected), "superseded failing declaration/variant inventory differs")
    for file, declaration in ((MAIN, "dlHash_compresses"), (MAIN, "dlHash_collision_accept_eq"),
                              (MAIN.removesuffix(".lean") + "/Reduction.lean", "collisionPost_split")):
        def header(text):
            match = re.search(r"(?m)^theorem " + re.escape(declaration) + r"\b", text)
            need(match is not None, "missing repaired declaration " + declaration)
            return text[match.start():text.index(":= by", match.start())]
        need(header(git("show", PRE_REPAIR_HEAD + ":" + file).decode()) == header(Path(file).read_text()),
             "repair changed a declaration type: " + declaration)
    return sorted(findings, key=lambda row: (row["owner"], row["variant"], row["declaration"]))


def verify_seal_provenance(path, edition):
    provenance = read(path)
    need(provenance.get("status") == "COMPLETE", "optimized harness provenance/pilots remain pending")
    need(provenance.get("edition", edition) == edition, "optimized harness edition differs")
    need(provenance.get("harness_revision") == "batch2048-ordinary-local-attribute-api-v2" and
         provenance.get("chunk_size") == 2048, "unreviewed optimized harness revision")
    for field in ("ordinary_registered_local_attribute_api", "prior_final1_artifacts_preserved",
                  "request_rows_unchanged", "original_source_bytes_preserved"):
        need(provenance.get(field) is True, "optimized harness property not certified: " + field)
    static = provenance["static_assembly"]
    need(sha(static["path"]) == static["sha256"], "static assembly evidence changed")
    assembly = read(static["path"])
    need(assembly["harness_revision"] == provenance["harness_revision"] and assembly["chunk_size"] == 2048,
         "static assembly revision differs")
    need(assembly["phases"]["install"]["ordinary_local_attribute_api_calls"] == 1,
         "install does not use the ordinary registered local attribute API")
    for phase in ("install", "eof"):
        need(assembly["phases"][phase]["command_elaboration_calls"] == 0 and
             assembly["phases"][phase]["direct_status_setter"] is False and
             assembly["phases"][phase]["unsafe_reducibility"] is False,
             "optimized phase bypasses ordinary attribute handling")
    need(provenance["api_source_hashes"], "ordinary attribute API source provenance absent")
    for source, digest in provenance["api_source_hashes"].items():
        need(sha(source) == digest, "ordinary attribute API source changed: " + source)
    pilots = provenance["control_pilots"]
    for field in ("unsealed_pass", "sealed_expected_failures_exactly_once", "reader_positives_pass"):
        need(pilots.get(field) is True, "native optimized pilot did not pass: " + field)
    full = provenance["full_seal_pilot"]
    need(full["side"] == "base" and full["variant"] == "A" and
         full["owner"] in ("Candidates.DiscreteLog", "TCSlib.Cryptography.Candidates.DiscreteLog") and
         full.get("harness_valid") is True and full.get("mask_components_install_eof_verified") is True,
         "full optimized base-A pilot is incomplete/invalid")
    comparison = provenance["comparison"]
    need(comparison.get("baseA_failing_declarations_equal") is True,
         "optimized base-A failures differ from the completed original run")
    if "old_failing_declarations" in comparison or "new_failing_declarations" in comparison:
        need(set(comparison["old_failing_declarations"]) == set(comparison["new_failing_declarations"]),
             "pilot comparison lists disagree")
    benchmark = provenance["benchmark"]
    for short, long in (("old_seconds", "old_duration_seconds"), ("new_seconds", "new_duration_seconds")):
        if short not in benchmark:
            benchmark[short] = benchmark.get(long)
    need(all(isinstance(benchmark.get(key), (int, float)) and benchmark[key] > 0
             for key in ("old_seconds", "new_seconds")), "actual pilot durations are missing")
    need(provenance["raw_logs"], "native pilot raw evidence absent")
    for raw in provenance["raw_logs"]:
        need(sha(raw["path"]) == raw["sha256"], "native pilot raw evidence changed")
    need(Path("evidence/tools/rule10_prepare-v1.py").is_file() and
         Path("evidence/tools/rule10_controls-v1.py").is_file(), "original harness tools not retained")
    return provenance


def verify_baseline_reuse(path, edition, base_edition, harness_edition, harness_path):
    reuse = read(path)
    need(reuse["status"] == "COMPLETE" and reuse["edition"] == edition and
         reuse["base_edition"] == base_edition and reuse["base"] == BASE,
         "baseline reuse provenance is incomplete or belongs to another base/edition")
    need(reuse["baseline_unchanged"] is True and reuse["raw_records_reused_without_relabeling"] is True and
         reuse["fresh_final_evidence_edition"] == edition, "baseline reuse relabels or changes original evidence")
    state = reuse["base_state"]
    need(sha(state["path"]) == state["sha256"], "original base-state metadata changed")
    need(len(reuse["source_hashes"]) == 98, "baseline reuse does not bind the complete 98-source closure")
    verifications = reuse["runtime_object_verifications"]
    need((len(verifications) if isinstance(verifications, (list, dict)) else verifications) == 98,
         "baseline reuse lacks 98 runtime-object verifications")
    need(reuse["original_evidence"], "original baseline raw evidence bindings absent")
    for item in reuse["original_evidence"]:
        need(sha(item["path"]) == item["sha256"], "original baseline evidence changed: " + item["path"])
    historical = reuse["historical_harness_provenance"]
    need(historical["edition"] == harness_edition and historical["same_generator_tools"] is True and
         historical["harness_revision"] == "batch2048-ordinary-local-attribute-api-v2" and
         historical["chunk_size"] == 2048 and historical["path"] == str(harness_path) and
         sha(historical["path"]) == historical["sha256"],
         "historical harness pilot is not explicitly and correctly bound")
    return reuse


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--edition", default="final1")
    parser.add_argument("--base-edition", help="Edition containing unchanged original baseline raw evidence")
    parser.add_argument("--harness-edition", help="Historical edition containing equivalent harness pilots")
    parser.add_argument("--baseline-reuse", type=Path)
    parser.add_argument("--summary", type=Path)
    parser.add_argument("--base-review", type=Path)
    parser.add_argument("--final-review", type=Path)
    parser.add_argument("--seal-provenance", type=Path,
                        help="Completed optimization/pilot evidence; required for editions after final1")
    parser.add_argument("--admissions", type=Path)
    parser.add_argument("--sweep-results", type=Path,
                        help="Canonical successful 176-module results; final3 defaults to final-sweep-repaired")
    parser.add_argument("--style", type=Path)
    parser.add_argument("--declarations", type=Path)
    parser.add_argument("--proof-route", type=Path)
    parser.add_argument("--source-preservation", type=Path)
    parser.add_argument("--historical-seal-results", type=Path,
                        default=Path("evidence/logs/rule10/final2/seals-final/results.jsonl"))
    parser.add_argument("--patch-reproduction", type=Path)
    parser.add_argument("--output", type=Path, default=Path("evidence/FINAL-REPORT.md"))
    args = parser.parse_args()
    args.base_edition = args.base_edition or args.edition
    args.harness_edition = args.harness_edition or args.edition
    edition_root = Path("evidence/probes/Rule10") / args.edition
    base_root = Path("evidence/probes/Rule10") / args.base_edition
    harness_root = Path("evidence/probes/Rule10") / args.harness_edition
    args.summary = args.summary or edition_root / "summary.json"
    args.base_review = args.base_review or base_root / "base-explicit-manual-review.json"
    args.final_review = args.final_review or edition_root / "final-explicit-manual-review.json"
    if args.harness_edition != "final1":
        args.seal_provenance = args.seal_provenance or harness_root / "seal-provenance.json"
    if args.base_edition != args.edition:
        args.baseline_reuse = args.baseline_reuse or edition_root / "baseline-reuse.json"
    args.sweep_results = args.sweep_results or Path("evidence/logs") / (
        "final-sweep-repaired" if args.edition == "final3" else "final-sweep-verified") / "results.jsonl"
    args.style = args.style or Path("evidence/style-delta-repaired.json" if args.edition == "final3"
                                    else "evidence/style-delta.json")
    args.admissions = args.admissions or Path("evidence/admission-delta-repaired.json" if args.edition == "final3"
                                              else "evidence/admission-delta.json")
    args.declarations = args.declarations or Path("evidence/new-declarations-final3.json" if args.edition == "final3"
                                                  else "evidence/new-declarations.json")
    args.proof_route = args.proof_route or Path("evidence/proof-route-final3.md" if args.edition == "final3"
                                               else "evidence/proof-route.md")
    args.source_preservation = args.source_preservation or Path(
        "evidence/logs/final-source-preservation-repaired.json" if args.edition == "final3"
        else "evidence/logs/final-source-preservation.json")
    args.patch_reproduction = args.patch_reproduction or Path(
        "evidence/patch-reproduction-repaired/result.json" if args.edition == "final3"
        else "evidence/patch-reproduction-final/result.json")
    need(git("rev-parse", "HEAD").decode().strip() == HEAD, "proof HEAD changed; refresh evidence/report tool")
    need(git("branch", "--show-current").decode().strip() == "fill/dl-crh", "wrong local proof branch")
    need(not git("for-each-ref", "--contains", HEAD, "--format=%(refname)", "refs/remotes").strip(),
         "proof commit appears in a remote-tracking branch")
    need(not subprocess.run(["git", "diff", "--quiet", "HEAD", "--", "TCSlib"]).returncode,
         "uncommitted Lean changes")
    changed = set(git("diff", "--name-only", BASE, HEAD, "--", "*.lean").decode().splitlines())
    need(changed == CHANGED, "changed Lean scope differs")
    need(target_header(git("show", BASE + ":" + MAIN).decode()) == target_header(Path(MAIN).read_text()),
         "target statement header differs")
    provider_delta = git("diff", "--numstat", BASE, HEAD, "--", PROVIDER).decode().split()
    need(provider_delta[:2] == ["17", "0"], "provider scope delta changed")
    for path in CHANGED - {PROVIDER}:
        need(len(Path(path).read_text().splitlines()) < 1000, "new/owned file reaches size limit: " + path)

    summary, admission, style, decls, reproduction = map(read, (args.summary, args.admissions, args.style,
                                                               args.declarations, args.patch_reproduction))
    need(summary["edition"] == args.edition and summary["mechanical_checks_pass"] is True,
         "Rule 10 mechanical checks did not pass")
    need(summary.get("base_edition", args.edition) == args.base_edition,
         "summary does not identify the actual reused baseline edition")
    need(summary["seals"]["all_harnesses_valid"] and summary["seals"]["new_failing_declarations"] == 0,
         "invalid seals or new failing declaration")
    need(all(not row["failing_declarations"] for row in summary["seals"]["table"] if row["side"] == "final"),
         "fresh final-source seals still have a failing declaration")
    historical = historical_seal_findings(args.historical_seal_results)
    owners = {p.removesuffix(".lean").replace("/", ".") for p in CHANGED}
    expected_seals = {(side, owner, variant) for side in ("base", "final") for owner in
                      (owners if side == "final" else {MAIN.removesuffix(".lean").replace("/", "."),
                                                       PROVIDER.removesuffix(".lean").replace("/", ".")})
                      for variant in ("A", "B")}
    need({(r["side"], r["owner"], r["variant"]) for r in summary["seals"]["table"]} == expected_seals,
         "incomplete base/final whole-file seal coverage")
    for row in summary["seals"]["table"]:
        need(row["valid"] and row["native_exit_consistent"] and not row["unexpected_errors"] and
             row["harness_error"] is None, "invalid seal row")
        need(Path(row["log"]).is_file(), "missing seal log")
    controls = summary["controls"]
    need(controls["all_pass"], "paired controls did not pass")
    for side in ("base", "final"):
        need(controls["sides"][side], "missing " + side + " paired controls")
        need(len(controls["sides"][side]) == (8 if side == "base" else 32),
             "incomplete per-owner/variant paired-control run coverage")
        for row in controls["sides"][side]:
            need(row["passed"] and not row["unexpected_errors"], "failed control pair")
            need(sha(row["raw_log"]) == row["raw_log_sha256"], "control log changed")
            for check in row["checks"]:
                need(check["passed"] and check["actual_errors"] == check["expected_errors"] and
                     check["expected_errors"] in (0, 1), "control did not have exact expected diagnostic count")
    axioms = summary["axioms"]
    need(axioms["target_standard_only"] and set(axioms["target_axioms"]) == STANDARD,
         "target does not have exactly the standard three axioms")
    need(not axioms["removed"] and not axioms["metadata_changes"] and not axioms["new_nonstandard"],
         "stored constant removal/metadata/nonstandard axiom regression")
    need(sha(axioms["base_log"]) == axioms["base_log_sha256"] and
         sha(axioms["final_log"]) == axioms["final_log_sha256"], "axiom census log changed")
    reviews = {"base": verify_manual(args.base_review, "base", args.base_edition),
               "final": verify_manual(args.final_review, "final", args.edition)}
    raw_scans = verify_explicit_scan_schema(reviews, summary)
    provenance = verify_seal_provenance(args.seal_provenance, args.harness_edition) if args.seal_provenance else None
    reuse = verify_baseline_reuse(args.baseline_reuse, args.edition, args.base_edition,
        args.harness_edition, args.seal_provenance) if args.baseline_reuse else None
    verify_sweep(admission, args.sweep_results)
    verify_style(style)
    need(decls["base"] == BASE and decls["head"] == HEAD and decls["added_count"] == 69 and
         decls["removed_count"] == 0, "source declaration inventory differs")
    preserved = read(args.source_preservation)
    body_checks = [row for row in preserved["checks"] if "base_code_exact_substring" in row]
    need(preserved["base"] == BASE and len(body_checks) == 16 and
         all(row["base_code_exact_substring"] for row in body_checks), "original declaration bodies changed")
    need(next(row for row in preserved["checks"] if row.get("declaration") == "dlHash_crh")["frozen_statement_exact"],
         "source preservation check found a changed target statement")
    doc_check = next(row for row in preserved["checks"] if "original_decl_docstrings" in row)
    need(doc_check["original_decl_docstrings"] == 17 and doc_check["all_exact_substrings"],
         "original declaration statement prose changed")
    need({row["file"] for row in preserved["snapshot"]} == CHANGED and
         all(sha(row["file"]) == row["sha256"] for row in preserved["snapshot"]),
         "source preservation snapshot is stale")
    need(reproduction["base"] == BASE and reproduction["head"] == HEAD and
         reproduction["all_reproduced"] and {r["path"] for r in reproduction["files"]} == CHANGED and
         len(reproduction["patches"]) == EXPECTED_PATCH_COUNT, "complete patch reproduction did not pass")
    for item in reproduction["files"]:
        need(sha(item["path"]) == item["head_sha256"] == item["reproduced_sha256"],
             "reproduced source bytes differ: " + item["path"])
    roots = Path("evidence/roots.txt").read_text().splitlines()
    need(len(roots) == 87 and roots == Path("evidence/logs/resume-1/mathlib-roots.txt").read_text().splitlines(),
         "narrowed roots differ")
    cache = Path("evidence/logs/resume-1/cache-get-cap3.log").read_text()
    need("No files to download" in cache and "Decompressing 2339 file(s)" in cache and "EXIT 0" in cache,
         "narrowed cache completion not verified")
    need("PASS all 11 present packages match manifest URLs and revisions" in
         Path("evidence/logs/resume-1/package-pins.log").read_text(), "package pins failed")
    need(not Path("evidence/logs/resume-1/zero-oleans.log").read_text().strip(), "empty cached olean found")
    need("EXIT 0" in Path("evidence/logs/resume-1/cache-probe.log").read_text(),
         "Mathlib-root cache probe did not pass")
    with ZipFile("evidence/initial-escalation.zip") as archive:
        need(archive.testzip() is None, "initial escalation ZIP corrupt")
        need(archive.read("dl-crh/evidence/logs/pack-verification.log").count(b": OK") == 7,
             "original pack checksum evidence incomplete")
        need(archive.read("dl-crh/evidence/logs/source-inspection.log").count(b": OK") == 170,
             "issue-source checksum evidence incomplete")
    route = args.proof_route.read_text()
    need(HEAD in route and "All six brief edge cases" in route, "route/edge-case report not current")
    promotion_ledger = Path("evidence/PROMOTION.md").read_text()
    for path, item, _ in OVERLAPS:
        need("overlap: " + path + " " + item in promotion_ledger, "missing overlap disclosure")

    lines = ["# dl-crh — final proof report", "",
             "**Status: proof complete, with the recorded user scope and lint exceptions.**",
             "`TCSlib.Cryptography.Authentication.dlHash_crh` is proved with its original statement.",
             "The proof branch `fill/dl-crh` remains local. Only the assigned exchange delivery path is used.",
             "", f"Issue pack: `{ISSUE}`. Issue base: `{BASE}`.",
             f"Final proof commit: `{HEAD}`. Lean: `leanprover/lean4:v4.25.0`.",
             "Pinned Mathlib: `029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e`.",
             "", "## Delivered mathematics and edge cases", "",
             route.split("## Actual proof", 1)[1].replace("## All six brief edge cases", "## All six brief edge cases", 1),
             "", "## Scope, declarations, and sketch", "",
             "Eight Lean files changed: the owned hashing module, six helpers, and the two expressly authorized",
             "reader equations in Candidates/DiscreteLog.lean. No target or existing declaration type changed;",
             "the separate source-preservation check retains all 16 other original bodies and all 17 original",
             "declaration docstrings byte-for-byte, together with the frozen target statement.",
             "the stored metadata comparison reports no kind/type/reducibility/abbreviation/simp/instance/protected delta.",
             "The hashing title drops statement phase, Main results records the proof, and Contents lists all six helpers.",
             "The sketch follows compression, selector inequality, the concrete reduction, and the sampler switch.",
             "", "The complete 69-entry source declaration inventory, with qualified names, kinds, visibility, files,",
             f"and source lines, is `{args.declarations.with_suffix('.md')}` and `{args.declarations}`, generated by",
             "`python3 -I evidence/tools/new_declarations.py`. Both private helper declarations are included.",
             "Generated kernel constants are included separately in the stored-constant census.",
             "", "## Promotions and resolved reader requests", "",
             "The initial missing-reader escalation was resolved by the user's scoped authorization for",
             "`expGenFun_eq` and `expSampleRaw_eq`; both are delivered with equation docstrings and no simp attribute.",
             "No outstanding foreign-reader request remains.", ""]
    lines += ["- " + item for item in PROMOTIONS]
    lines += ["", "Searches and detailed provenance are retained in `evidence/PROMOTION.md` and the delivered tools/logs.",
              "Existing public lemmas are imported. No private provider proof was copied.", "", "## All four overlap disclosures", ""]
    for path, item, reason in OVERLAPS:
        lines += [f"**overlap: {path} {item}**", "", reason, ""]
    lines += ["## Checks and admissions", "",
              "The original seven pack checksums and 170 issue-source checksums passed; original raw evidence remains",
              "verbatim in `evidence/initial-escalation.zip`. The canonical final sweep under",
              f"`{args.sweep_results.parent}/` checked all 176 modules, one module per",
              "`scripts/lean_check_tree.sh` call, with zero errors. Source/log hashes are bound in raw results.",
              "The earlier complete pass under `logs/final-sweep/` also built previously unbuilt downstream",
              "prerequisites. It remains labeled preliminary; `evidence/sweep-phases.md` records why the fully",
              "bootstrapped order was then checked again. No running Lean process was interrupted.",
              "The admission comparison is exactly 22 → 21: only `dlHash_crh` was removed, with no added admission.",
              f"`{args.admissions}` retains every warning and its source/log location.",
              "", "No project `lake build` or unfiltered cache fetch was used. Python commands use `python3 -I`.",
              "Development failures, repairs, raw logs, probe sources, manifests, request records, and tools are retained.",
              "", "## Axioms and stored metadata", "",
              "Target axioms: `propext`, `Classical.choice`, `Quot.sound`.",
              f"All-stored census: base {axioms['base_stored']}, final {axioms['final_stored']}; "
              f"{len(axioms['added'])} added stored constants and {len(axioms['removed'])} removed.",
              f"Metadata changes: {len(axioms['metadata_changes'])}. New nonstandard-axiom dependencies: {len(axioms['new_nonstandard'])}.",
              "The full raw census, including generated matchers/projections, is delivered and named in the summary.",
              "", "Every axiom delta:", ""]
    for item in axioms["axiom_changes"]:
        lines.append(f"- `{item['module']}` / `{item['name']}`: `{item['before']}` → `{item['after']}`.")
    if not axioms["axiom_changes"]:
        lines.append("None.")
    lines += ["", f"Inherited final nonstandard entries: {len(axioms['final_nonstandard'])}; none is new or worsened:", ""]
    for item in axioms["final_nonstandard"]:
        lines.append(f"- `{item['module']}` / `{item['name']}`: `{item['axioms']}`.")
    lines += ["", "## Rule 10 seals, controls, and explicit scan", "",
              "A excludes exactly `Complexity.PolyExpr.eval` as notation; B seals it. Both seal all ordinary",
              "foreign TCSlib definitions in the full import closure, including eligible generated matchers and",
              "definition instances; recorded abbreviation/status exclusions remain visible in request records.",
              "Base covers the two pre-existing changed files; all six new helpers are absent at base. Final covers",
              "all eight files. Every harness and mask check is valid, and there are zero new failing declarations.",
              "", "Current baseline/final source declaration results, by side/owner/variant:", ""]
    if reuse:
        lines += ["### Explicit reuse of the unchanged original baseline", "",
                  f"Fresh final-source evidence belongs to `{args.edition}`. The four original baseline seals,",
                  f"eight baseline control runs, baseline census, and 208-row baseline scan/review remain in",
                  f"their actual `{args.base_edition}` paths; they were not copied or relabeled as fresh runs.",
                  "The reuse record binds all original raw evidence, the unchanged 98-source baseline closure,",
                  "and 98 runtime-object verifications. Fresh final-source snapshots, seals, controls, census,",
                  "and manual scan review are separately checked against the repaired current proof bytes.",
                  f"Binding record: `{args.baseline_reuse}`.", ""]
    if provenance:
        benchmark = provenance["benchmark"]
        lines += ["### Harness revision and measured pilot equivalence", "",
                  f"This report uses final-source edition `{args.edition}` and harness revision `{provenance['harness_revision']}`.",
                  f"The optimization pilot/benchmark is historical evidence from `{args.harness_edition}`.",
                  "Its original-source/request preservation claims refer to that historical before/after harness",
                  "comparison. They do not assert that the pilot's source snapshot equals the repaired final",
                  "proof source snapshot. The fresh final-source evidence is independently bound above.",
                  "The original final1 probes, logs, and versioned tools are retained. Performance investigation",
                  "identified 24 full-environment scans and 12 mask snapshots for the original 1409-request base-A",
                  "probe. The revision",
                  "uses batches of at most 2048 requests through the same ordinary registered local attribute API,",
                  "with component/mask checks at install and EOF. It does not use a direct reducibility setter,",
                  "unsafe reducibility, or source/proof changes. Static assembly alone was explicitly insufficient;",
                  "the delivered completed provenance also contains actual native controls and a full base-A pilot.",
                  "", "The optimized unsealed/reader controls passed; each sealed negative failed exactly once.",
                  "The complete optimized base-A failure set equals the completed original base-A failure set.",
                  f"Measured original base-A duration: {benchmark['old_seconds']} seconds; optimized base-A:",
                  f"{benchmark['new_seconds']} seconds (ratio {benchmark['old_seconds']/benchmark['new_seconds']:.3f}).",
                  f"Actual logs, API source hashes, assembly data, and comparisons: `{args.seal_provenance}`.",
                  "The complete base/final seals, controls, census, and full per-row scan reviews are separately",
                  "required by this report; pilot results do not substitute for those checks.", ""]
    for row in sorted(summary["seals"]["table"], key=lambda r: (r["side"], r["owner"], r["variant"])):
        lines += [f"### {row['side']} / {row['owner']} / {row['variant']}", "",
                  f"Valid harness; exit {row['exit_code']}. Raw log: `{row['log']}`.", ""]
        lines += ["- `" + name + "`." for name in row["failing_declarations"]] or ["None."]
        lines.append("")
    lines += ["### Superseded final2 seal failures and their repairs", "",
              f"The superseded final2 runs checked source commit `{PRE_REPAIR_HEAD}`. Their source failures",
              "are disclosed below even though every fresh final3 source seal now has zero errors. The generator",
              "rehashes each original raw log and checks every diagnostic against the mapped native records;",
              "the final3 success does not erase these earlier findings.", "",
              "| Variant | Failing declaration | Diagnostics | Original source lines | Raw probe lines |",
              "|---|---|---:|---|---|"]
    for row in historical:
        lines.append(f"| {row['variant']} | `{row['declaration']}` | {row['diagnostics']} | "
                     f"{', '.join(map(str,row['source_lines']))} | {', '.join(map(str,row['probe_lines']))} |")
    lines += ["", "Original raw-log bindings (shared logs intentionally occur for both affected declarations):", ""]
    for row in historical:
        lines += [f"- {row['variant']} / `{row['declaration']}`: `{row['log']}`;",
                  f"  SHA-256 `{row['log_sha256']}`."]
    lines += ["", "The four variant/declaration rows contain six diagnostics in three raw logs:", "",
              "- `collisionPost_split` (A and B, one diagnostic each): the original `simpa` required an implicit",
              "  dependent transport of the padded-word width. The repair first proves `hwidth` with the public",
              "  polynomial-evaluation readers, then uses `congrArg (fun k : ℕ => List.ofFn (padFin k raw)) hwidth`,",
              "  reverses that equality, and composes it with the public `ofFn_padFin_eq_padStr` equation.",
              "- `dlHash_compresses` (B, three diagnostics) and `dlHash_collision_accept_eq` (B, one diagnostic):",
              "  combined simplification normalized dependent input widths before the CRH field/hash readers",
              "  could match while `PolyExpr.eval` was sealed. The repair stages simplification: first",
              "  `dlHash_inDom`, `dlHash_inRange` where needed, `CRH.hash_eq`, `dlHash_eval`, pair/guard readers;",
              "  then `dlHash_domLen`, `dlHash_rangeLen`, and the published polynomial evaluation equations.",
              "", "All three theorem headers/types are byte-identical before and after these repairs, as checked",
              "again by this generator. No statement, hardness assumption, global simp attribute, or mathematics",
              "changed. Fresh final3 seals validate the repaired bytes: all 16 final owner/variant runs have",
              "zero failing declarations, including Reduction A/B and the owned module B.", ""]
    for side in ("base", "final"):
        controls_side = controls["sides"][side]
        checks = [check for row in controls_side for check in row["checks"]]
        negative = sum(check["expected_errors"] == 1 for check in checks)
        lines += [f"{side}: {len(controls_side)} control probe runs, {len(checks)} per-case checks, "
                  f"{negative} sealed negatives; each negative fails exactly once and every expected positive/unsealed case passes.", "",
                  f"{side} explicit scan: {len(reviews[side]['rows'])} individually reviewed rows. Raw scanner "
                  f"foreign-definition candidates: {len(raw_scans[side]['foreign_definition_items'])}; "
                  f"raw unresolved rows before manual review: {len(raw_scans[side]['unresolved_items'])}. "
                  f"Final manual disposition: pending 0, new foreign-definition BODY-reading violations 0. Review: "
                  f"`{args.base_review if side == 'base' else args.final_review}`.", ""]
    lines += ["The four raw final candidates are the following registered built-in simproc invocations:", ""]
    for row in raw_scans["final"]["foreign_definition_items"]:
        lines.append(f"- `{row['path']}:{row['line']}`, `{row['declaration']}`: `{row['item']}`.")
    lines += ["", "The finalized per-row review retains the pinned `builtin_simproc` registration and the",
              "`.simproc` → `.addSimproc` elaborator path. These `↓reduceIte` items invoke the registered",
              "simproc, which produces proofs through `ite_cond_eq_true` / `ite_cond_eq_false`; they do not",
              "ask simp to unfold the metaprogram's definition body. The raw candidate counts remain 0/4",
              "and raw unresolved counts remain 10/15; manual clearance means zero newly introduced",
              "foreign-definition body readings, not zero raw candidates.", ""]
    lines += ["## Lint and explicit exceptions", "",
              "Required lint: **222 FAIL / 102 WARN**, versus baseline **216 FAIL / 102 WARN**.",
              "The exact six added FAIL entries are the frozen ancestor Hashing.lean facade's direct-import",
              "diagnostics for Algebra, Coins, Encoding, Probability, Reduction, and Sampling. All six helpers are",
              "exported through the owned FromDiscreteLog facade. The user explicitly authorized:", "",
              "> Acknowledge exactly six lint false positives", "",
              "This is an exception to literal zero-new-FAIL lint, not a claim that the lint mechanically passed.",
              "No other added FAIL is accepted. Raw baseline/final logs and every changed WARN message are in",
              f"`{args.style.with_suffix('.md')}` / `{args.style}`; the inherited provider-size warning changes 1192 → 1209 lines,",
              "and its missing-reader warning list drops expSampleRaw after its new equation reader.",
              "The scoped provider exception preserves this pre-existing over-1000-line file without unrelated",
              "splitting. Every owned/new hashing file remains below 1000 lines. No global simp attribute was added.",
              "", "## Host, cache, and bootstrap", "",
              "Resumption preflight: 12 CPUs; physical RAM 19,327,352,832 bytes; APFS free space",
              "264,007,364,608 bytes (>12 GiB). Native non-cache memory-use proxy 12,238,684,160 bytes and",
              "headroom proxy 7,088,668,672 bytes (>4 GiB). macOS lacks Linux cgroup/MemAvailable counters;",
              "the native proxy is explicitly not claimed to be Linux MemAvailable. Raw native readings and",
              "subsequent resource logs are retained under `evidence/logs/resume-1/`.",
              "The user overrode host serialization to at most three Lean processes. This worker checks one",
              "module at a time in its own olean tree and counts other host processes before launch. Exact",
              "authorizations and the authorized coordination-note provenance are in `evidence/authorization.md`.",
              "", "Only the 87 issued Mathlib roots were fetched. The narrowed cache command exited 0:",
              "2,339 files decompressed, zero files downloaded, from the pre-existing hash-addressed archive store",
              "(32,667 files; 1,595,387,830 bytes; precise originating sessions unknown). All 11 present packages",
              "match manifest URLs/revisions; doc-gen4, UnicodeBasic, BibtexQuery, and MD4Lean are absent.",
              "No empty olean was found; the Mathlib-root import probe and bootstrap passed. No dependency tree",
              "was copied or reused from another session, and no memory-backed scratch filesystem was used.",
              "Module timestamps and native maximum-memory outputs are retained. Checks standardized on Lean -j4",
              "without self-imposed timeouts; earlier wrapper versions and their logs remain delivered.",
              "", "## Patch reproduction and transport history", "",
              f"The complete {len(reproduction['patches'])}-patch series from the exact issue base reproduces all eight changed/new files",
              f"byte-for-byte. `{args.patch_reproduction}` records every reproduced/head hash:", ""]
    for item in reproduction["files"]:
        lines.append(f"- `{item['path']}`: `{item['head_sha256']}`.")
    lines += ["", "Patch files:", ""] + ["- `" + name + "`." for name in reproduction["patches"]]
    lines += ["", "Exchange records already pushed only under `inbox/fills/dl-crh/`:", ""]
    lines += [f"- {label}: `{commit}`." for label, commit in CHECKPOINTS]
    lines += ["", "The final exchange push identity belongs in the final chat, not recursively inside its own payload.",
              "The payload contains REPORT.md, the full patch series, exact src bytes, and all evidence. Packaging",
              "generates manifests after this report and verifies exact path-set/hash equality and ZIP bytes; its",
              "actual output is retained separately. The fallback ZIP has `dl-crh/` at its root.",
              "", "## Bound report inputs", ""]
    report_inputs = [args.summary, args.base_review, args.final_review, args.admissions, args.style,
                     args.declarations, args.proof_route, args.source_preservation, args.patch_reproduction,
                     args.historical_seal_results]
    if args.seal_provenance:
        report_inputs.append(args.seal_provenance)
    if args.baseline_reuse:
        report_inputs.append(args.baseline_reuse)
    for path in report_inputs:
        lines.append(f"- `{path}`: `{sha(path)}`.")
    lines.append("")
    args.output.write_text("\n".join(lines))
    print(json.dumps(dict(status="PROOF_CHECKS_COMPLETE", output=str(args.output), head=HEAD,
                          modules=176, admissions="22->21, target only", new_source_declarations=69,
                          rule10_new_failures=0, target_axioms=sorted(STANDARD))))


if __name__ == "__main__":
    main()
