"""Prepare additional whole-file Rule 10 seals for the approved Randomness facade.

No Lean is started. Run from the fill checkout as python3 -I:
  evidence/tools/prepare_facade_rule10.py init base
  evidence/tools/prepare_facade_rule10.py init final
  evidence/tools/prepare_facade_rule10.py seals base
  evidence/tools/prepare_facade_rule10.py seals final

The base facade imports an exact pinned Extraction snapshot already compiled as
evidence.rule10.«base-r2».probes.BaseExtraction. Only that direct import is
rewritten in the probe; both original and effective source bytes are retained.
Every other imported module is verified not to import Extraction and to have
the same current source bytes as the issue base. Final uses actual modules.

Shared census/insertion functions are loaded from the delivered preparation
tool, not from historical campaign scripts. Existing artifacts are not edited.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re
import runpy


COMMON_PATH = Path("evidence/tools/prepare_rule10.py")
common = runpy.run_path(str(COMMON_PATH), run_name="facade_rule10_shared")
FACADE = "TCSlib.Cryptography.Randomness"
EXTRACTION = "TCSlib.Cryptography.Randomness.Extraction"
SOURCE_PATH = Path("TCSlib/Cryptography/Randomness.lean")


def area_for(side: str) -> Path:
    return Path("evidence/rule10/facade-" + side)


def sha(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def init(side: str) -> None:
    area = area_for(side)
    raw = common["source"](FACADE, side)
    masked = common["code_mask"](raw.decode())
    assert not re.search(r"(?m)^\s*(?:(?:private|protected|noncomputable|nonrec)\s+)*(?:def|theorem|lemma|axiom|abbrev|opaque|structure|inductive|class|instance)\b", masked)
    info = common["header"](raw)
    graph, hashes = {}, {}
    original_closure = sorted(common["closure"](FACADE, side, graph, hashes))
    other_import_checks = []
    for direct in info["imports"]:
        if direct == EXTRACTION or not direct.startswith("TCSlib."):
            continue
        deps = common["closure"](direct, side, graph, hashes)
        assert EXTRACTION not in deps, (direct, "indirectly imports Extraction")
        other_import_checks.append({"direct_import": direct, "transitive_imports_exclude_Extraction": True})
    effective = raw
    rewrite = None
    owners = [FACADE]
    native_closure = original_closure
    snapshot_module = None
    unchanged = []
    if side == "base":
        base = json.loads(Path("evidence/rule10/base-r2/init.json").read_bytes())
        snapshot = base["entries"][0]
        assert snapshot["module"] == EXTRACTION
        assert sha(common["source"](EXTRACTION, "base")) == snapshot["source_sha256"]
        base_home = snapshot["loaded_home"]
        original_line = ("import " + EXTRACTION + "\n").encode()
        replacement = ("import " + base_home + "\n").encode()
        assert raw.count(original_line) == 1
        offset = raw.index(original_line)
        effective = raw[:offset] + replacement + raw[offset + len(original_line):]
        assert effective.replace(replacement, original_line, 1) == raw
        rewrite = {"kind": "base_Extraction_import_to_verified_snapshot",
                   "byte_offset": offset, "original": original_line.decode(),
                   "replacement": replacement.decode(),
                   "snapshot_source_sha256": snapshot["source_sha256"]}
        native_closure = sorted((set(original_closure) - {EXTRACTION}) | {base_home})
        snapshot_path = area / "probes/BaseFacade.lean"
        common["write_new"](snapshot_path, effective)
        snapshot_module = snapshot_path.with_suffix("").as_posix()
        facade_home = common["module_syntax"](snapshot_module.replace("/", "."))
        owners = [facade_home, base_home]
        # Other modules use ordinary current oleans, so prove their sources have
        # not drifted from the pinned base. The target is supplied by snapshot.
        for module in original_closure:
            if module == EXTRACTION:
                continue
            current = common["source"](module, "final")
            assert sha(current) == hashes[module], (module, "changed foreign source")
            unchanged.append({"module": module, "base_and_current_sha256": hashes[module]})
    else:
        facade_home = FACADE
    common["write_new"](area / "sources/Randomness.original.lean", raw)
    common["write_new"](area / "sources/Randomness.effective.lean", effective)
    text = "import Lean\nimport " + facade_home + "\n"
    body = common["CENSUS_BODY"].replace("OWNERS", "[" + ", ".join(common["lean_literal"](home) for home in owners) + "]")
    required = "".join(
        "  unless (env.getModuleIdx? `" + home + ").isSome do\n"
        "    throwError \"FACADE-CENSUS: missing expected imported module " + home + "\"\n"
        for home in owners)
    body = body.replace("  let env ← getEnv\n", "  let env ← getEnv\n" + required, 1)
    text += body
    census = area / "probes/Census.lean"
    common["write_new"](census, text.encode())
    common["save_json"](area / "init.json", {
        "base": common["BASE"], "side": side, "module": FACADE,
        "source": str(SOURCE_PATH), "source_sha256": sha(raw),
        "effective_source_sha256": sha(effective), "source_rewrite": rewrite,
        "facade_home": facade_home, "census_owners": owners,
        "census_module": census.with_suffix("").as_posix(), "census_source_sha256": sha(text.encode()),
        "snapshot_module": snapshot_module, "original_import_closure": original_closure,
        "native_import_closure": native_closure, "graph": graph, "source_hashes": hashes,
        "other_direct_import_checks": other_import_checks,
        "unchanged_foreign_sources": unchanged,
        "shared_tool_sha256": sha(COMMON_PATH.read_bytes()),
        "facade_tool_sha256": sha(Path(__file__).read_bytes()), "status": "PREPARED_NOT_RUN"})
    print("Prepared facade", side, "census", census.with_suffix("").as_posix())


def proven_controls(side: str) -> list[dict]:
    area = Path("evidence/rule10/base-r2" if side == "base" else "evidence/rule10/final")
    manifest = area / "manifest.json"
    controls = json.loads(manifest.read_bytes())["controls"]
    reused = []
    for control in controls:
        result_path = area / "logs" / (control["label"] + ".json")
        result = json.loads(result_path.read_bytes())
        assert result["valid_harness"] and result["meets_expected_error_count"]
        assert len(result["errors"]) == control["expected_errors"]
        assert result["source_unchanged"] and result["probe_sha256"] == control["probe_sha256"]
        source = Path(control["module"] + ".lean")
        assert sha(source.read_bytes()) == control["probe_sha256"]
        log = Path(result["log"])
        assert sha(log.read_bytes()) == result["log_sha256"]
        reused.append({"label": control["label"], "expected_errors": control["expected_errors"],
                       "source": str(source), "source_sha256": control["probe_sha256"],
                       "result": str(result_path), "result_sha256": sha(result_path.read_bytes()),
                       "log": str(log), "log_sha256": result["log_sha256"],
                       "manifest": str(manifest), "manifest_sha256": sha(manifest.read_bytes()),
                       "reuse_reason": "same shared instrumentation, Lean pin, ordinary definitions and notation controls"})
    assert len(reused) == 11
    return reused


def seals(side: str) -> None:
    area = area_for(side)
    config = json.loads((area / "init.json").read_bytes())
    assert config["side"] == side
    log = area / "logs/Census.log"
    result = json.loads(log.with_suffix(".json").read_bytes())
    assert result["rc"] == 0 and result["fresh_nonempty_object"] and not result["errors"]
    assert result["source_unchanged"] and result["source_sha256"] == config["census_source_sha256"]
    assert result["log_sha256"] == sha(log.read_bytes())
    constants, axioms = common["read_census"](log, config["census_owners"], allow_empty_owners=True)
    own_constants = [r for r in constants.values() if r["home"] == config["facade_home"]]
    own_axioms = [r for r in axioms.values() if r["home"] == config["facade_home"]]
    assert not own_constants and not own_axioms, "import-only facade unexpectedly owns constants"
    if side == "base":
        assert any(r["home"] == config["census_owners"][1] for r in constants.values())
    raw = (area / "sources/Randomness.effective.lean").read_bytes()
    assert sha(raw) == config["effective_source_sha256"]
    assert sha(common["source"](FACADE, side)) == config["source_sha256"]
    candidates = [r for r in constants.values() if r["home"] in config["native_import_closure"] and r["kind"] == "def"]
    exempt = [r for r in candidates if r["abbrev"] and not r["matcher"] and r["status"].rsplit(".", 1)[-1] == "reducible"]
    candidates = [r for r in candidates if r not in exempt]
    assert not any(r["status"].rsplit(".", 1)[-1] == "reducible" for r in candidates), "unsealable nonnotation definition"
    controls = proven_controls(side)
    probes = []
    for variant in ("A", "B"):
        requests = sorted((r for r in candidates if variant == "B" or r["name"] != common["EVAL"]), key=lambda r: r["name"])
        label = "FacadeSeal" + variant
        probe, edits, line_map = common["instrument"](raw, label, requests)
        path = area / "probes" / (label + ".lean")
        common["write_new"](path, probe)
        row = {"label": label, "variant": variant, "source": str(SOURCE_PATH),
               "module": path.with_suffix("").as_posix(), "requests": requests,
               "original_source_sha256": config["source_sha256"], "source_sha256": sha(raw),
               "probe_sha256": sha(probe), "insertions": edits, "line_map": line_map,
               "expected_errors": 0}
        probes.append(row)
        common["save_json"](area / "requests" / (label + ".json"), row)
    common["save_json"](area / "census-constants.json", list(constants.values()))
    common["save_json"](area / "all-stored-axioms.json", own_axioms)
    common["save_json"](area / "foreign-snapshot-axioms.json", list(axioms.values()))
    common["save_json"](area / "abbreviation-exclusions.json", exempt)
    common["save_json"](area / "manifest.json", {
        "base": common["BASE"], "side": side, "module": FACADE,
        "facade_stored_constants": 0, "facade_axiom_rows": 0,
        "init_sha256": sha((area / "init.json").read_bytes()),
        "census_log": str(log), "census_log_sha256": sha(log.read_bytes()),
        "census_result_sha256": sha(log.with_suffix(".json").read_bytes()),
        "source_rewrite": config["source_rewrite"], "controls": [],
        "verified_reused_controls": controls, "seals": probes, "status": "PREPARED_NOT_RUN"})
    print("Prepared facade", side, "A/B seals; stored constants 0; reused verified controls", len(controls))


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("action", choices=("init", "seals"))
    parser.add_argument("side", choices=("base", "final"))
    args = parser.parse_args()
    if args.action == "init":
        init(args.side)
    else:
        seals(args.side)


if __name__ == "__main__":
    main()
