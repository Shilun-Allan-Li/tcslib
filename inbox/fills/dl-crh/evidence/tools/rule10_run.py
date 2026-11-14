#!/usr/bin/env python3
"""Run prepared dl-crh evidence checks serially through lean_check_tree.sh.

Use python3 -I. Base and final own-source trees have separate TCSlib olean trees;
both read this checkout's single pinned package cache. This script never invokes
Lake and never schedules more than one module at a time. The parent's existing
wait_lean_slot.sh applies the user's shared-host launch cap.
"""
from __future__ import annotations
import argparse
import datetime
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[2]
PROBES = ROOT / "evidence/probes/Rule10"
sys.dont_write_bytecode = True


def need(test, why):
    if not test:
        raise RuntimeError(why)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def load_prepare():
    path = Path(__file__).with_name("rule10_prepare.py")
    spec = importlib.util.spec_from_file_location("dl_crh_rule10_prepare", path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def errors(text):
    return [dict(path=m[1], line=int(m[2]), column=int(m[3]), message=m[4])
            for m in re.finditer(r"^(.+\.lean):(\d+):(\d+): error: (.*)$", text, re.M)]


def verify_source_snapshot(state, tree):
    for path, digest in state["source_hashes"].items():
        need(sha(tree / path) == digest, "source changed since preparation: " + path)


def materialize_base(state):
    snapshot = ROOT / state["snapshot_root"]
    runtime = ROOT / state["root"]
    verify_source_snapshot(state,snapshot)
    for source in snapshot.rglob("*"):
        need(not source.is_symlink(),"baseline source snapshot must not contain symlinks")
        if source.is_file():
            target=runtime/source.relative_to(snapshot)
            target.parent.mkdir(parents=True,exist_ok=True)
            raw=source.read_bytes()
            if target.exists():
                need(target.read_bytes()==raw,"runtime baseline source differs: "+str(target))
            else:
                target.write_bytes(raw)
    cache=runtime/".lake/packages"
    cache.parent.mkdir(parents=True,exist_ok=True)
    own=ROOT/".lake/packages"
    if cache.is_symlink():
        need(cache.resolve()==own.resolve(),"baseline runtime cache link differs")
    else:
        need(not cache.exists(),"baseline runtime cache is not a symlink")
        cache.symlink_to(own,target_is_directory=True)
    return runtime


def verify_base_products(state):
    found={}
    for path in (ROOT/"evidence/logs/rule10").rglob("results.jsonl"):
        for line in path.read_text().splitlines():
            row=json.loads(line)
            if row.get("side")=="base" and row.get("phase")=="base-bootstrap":
                m=row["module"]
                if row.get("end","") >= found.get(m,{}).get("end",""):
                    found[m]=row
    for m in (PROBES/"base-order.txt").read_text().splitlines():
        row=found.get(m)
        need(row is not None and row["exit_code"]==0 and
             row["source_sha256"]==state["source_hashes"][m+".lean"],
             "missing successful exact-base prerequisite: "+m)
        obj=ROOT/state["olean_tree"]/(m+".olean")
        need(obj.is_file() and sha(obj)==row["olean_sha256"],"baseline prerequisite object differs: "+m)


def verify_final_products(state):
    # Compare current own-module source hashes with the latest native check
    # records; a stale/failed check cannot authorize a final collector import.
    found = {}
    for path in (ROOT / "evidence/logs").rglob("results.jsonl"):
        if "rule10" in path.parts:
            continue
        for line in path.read_text().splitlines():
            try:
                row = json.loads(line)
            except json.JSONDecodeError:
                continue
            m = row.get("module", "").replace("/", ".")
            if m in state["owners"] and row.get("end", "") >= found.get(m, {}).get("end", ""):
                found[m] = row
    for module in state["owners"]:
        path = module.replace(".", "/") + ".lean"
        row = found.get(module)
        need(row is not None and row.get("exit_code") == 0 and
             row.get("source_sha256") == state["source_hashes"][path],
             "no current successful native source check: " + module)
        obj = ROOT / ".lake/tcslib-check-oleans" / (module.replace(".", "/") + ".olean")
        need(obj.is_file() and sha(obj) == row.get("olean_sha256"), "current object differs: " + module)


def failing_sources(record, diagnostics, source_root, prepare):
    raw = (source_root / record["source"]).read_text()
    clean = prepare.builders()[0].blank_comments_strings(raw)
    lines = clean.splitlines()
    positions = []
    namespace = []
    stack = []
    # Declaration headings are retained as explicit source labels. Generated
    # constant names remain in collector/census records; a command error is not
    # silently assigned to the preceding theorem.
    for i, line in enumerate(lines, 1):
        if line.startswith("namespace "):
            stack.append(list(namespace))
            namespace += line.split()[1].split(".")
        elif re.match(r"^(?:noncomputable\s+)?section(?:\s|$)", line):
            stack.append(list(namespace))
        elif re.match(r"^end(?:\s|$)", line) and stack:
            namespace = stack.pop()
        match = re.match(r"^(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|nonrec)\s+)*(theorem|lemma|def|abbrev|instance|structure|class|inductive|opaque|axiom)\s*([^\s:({\[]*)", line)
        if match:
            name = match[2] or "<anonymous-instance>"
            qualified = name[7:] if name.startswith("_root_.") else ".".join(namespace + [name])
            positions.append((i, qualified, line.strip()))
        elif re.match(r"^(attribute|set_option|open|export|initialize|notation|syntax|macro|elab)\b", line):
            positions.append((i, "<command@" + str(i) + ">", line.strip()))
    reverse = {r["probe_line"]: r["source_line"] for r in record["source_to_probe_lines"]}
    failures = []
    for diag in diagnostics:
        original = reverse.get(diag["line"])
        if original is None:
            failures.append(dict(**diag, classification="HARNESS_OR_INSERTED_TEXT", source_line=None))
            continue
        prior = [p for p in positions if p[0] <= original]
        label = prior[-1] if prior else (1, "<header>", "")
        failures.append(dict(**diag, classification="SOURCE", source_line=original,
                             declaration=label[1], declaration_start=label[0], heading=label[2]))
    return failures


def run_one(module, side, phase, edition, record=None):
    prepare = load_prepare()
    statepath = PROBES / "base-state.json" if side == "base" else PROBES / edition / "snapshot.json"
    state = json.loads(statepath.read_text())
    tree = ROOT / state["root"] if side == "base" else ROOT
    source = tree / (module + ".lean")
    need(source.is_file(), "missing prepared module: " + str(source))
    if record:
        need(sha(source) == record["probe_sha256"], "prepared probe hash differs")
    targetdir = ROOT / "evidence/logs/rule10" / edition / phase
    targetdir.mkdir(parents=True, exist_ok=True)
    stem = module.replace("/", "_")
    attempt = len(list(targetdir.glob(stem + ".*.log"))) + 1
    log = targetdir / f"{stem}.{attempt:03d}.log"
    env = os.environ.copy()
    env["PATH"] = str(ROOT / "evidence/tools/timed-bin") + os.pathsep + env["PATH"]
    objtree = ROOT / (".lake/dl-crh-base-oleans" if side == "base" else ".lake/tcslib-check-oleans")
    env["TCSLIB_OLEANS"] = str(objtree)
    before = sha(source)
    start = datetime.datetime.now(datetime.timezone.utc).isoformat()
    print("CHECK", phase, module, start, flush=True)
    with log.open("wb") as output:
        rc = subprocess.run(["bash", str(ROOT / "evidence/tools/wait_lean_slot.sh"),
                             "bash", str(tree / "scripts/lean_check_tree.sh"), module],
                            cwd=ROOT, env=env, stdout=output, stderr=subprocess.STDOUT).returncode
    end = datetime.datetime.now(datetime.timezone.utc).isoformat()
    text = log.read_text(errors="replace")
    diagnostics = errors(text)
    obj = objtree / (module + ".olean")
    result = dict(module=module, side=side, phase=phase, start=start, end=end,
                  exit_code=rc, log=str(log.relative_to(ROOT)), log_sha256=sha(log),
                  source_sha256=before, source_after_sha256=sha(source), source_unchanged=before==sha(source),
                  olean_sha256=sha(obj) if obj.exists() else None,
                  maximum_resident_set_sizes=[int(n) for n in re.findall(r"^\s*(\d+)\s+maximum resident set size$",text,re.M)],
                  peak_memory_footprints=[int(n) for n in re.findall(r"^\s*(\d+)\s+peak memory footprint$",text,re.M)],
                  errors=diagnostics)
    if record:
        result["label"] = record["label"]
        result["owner"] = record["owner"]
        result["variant"] = record["variant"]
        mask_ok, component_ok, harness_error = True, True, None
        adapter = prepare.builders()[1]
        try:
            for chunk in record["chunks"]:
                rows = record["rows"][chunk["start"]:chunk["start"]+chunk["count"]]
                filtered="\n".join(line for line in text.splitlines()
                    if not ("G06-COMPONENT label=" in line or "G06-MASK label=" in line)
                    or "label="+chunk["label"]+" " in line)
                adapter.verify_component_log(filtered,chunk["label"],rows,("install","eof"))
                adapter.verify_mask_log(filtered,chunk["label"],rows,("install","eof"))
        except Exception as exc:
            mask_ok = component_ok = False
            harness_error = str(exc)
        result.update(mask_verified=mask_ok, actual_name_components_verified=component_ok,
                      harness_error=harness_error)
        result["failing_declarations"] = failing_sources(record, diagnostics, tree, prepare)
    with (targetdir / "results.jsonl").open("a") as records:
        records.write(json.dumps(result,ensure_ascii=False) + "\n")
    print("RESULT",phase,module,rc,"errors",len(diagnostics),end,flush=True)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("phase", choices=("base-bootstrap","base-collect","final-collect","seals","controls"))
    parser.add_argument("--edition",default="checkpoint1")
    parser.add_argument("--side",choices=("base","final"),default="final")
    args = parser.parse_args()
    base_state = json.loads((PROBES / "base-state.json").read_text())
    if args.phase.startswith("base-"):
        runtime=materialize_base(base_state)
        verify_source_snapshot(base_state,runtime)
        if args.phase=="base-collect": verify_base_products(base_state)
        modules = ((PROBES / "base-order.txt").read_text().splitlines() if args.phase=="base-bootstrap"
                   else ["evidence/probes/Rule10/CollectBase","evidence/probes/Rule10/CensusBase"])
        for module in modules:
            result=run_one(module,"base",args.phase,args.edition)
            need(result["exit_code"]==0 and result["source_unchanged"],"baseline check stopped; skip dependent checks")
    elif args.phase=="final-collect":
        state=json.loads((PROBES/args.edition/"snapshot.json").read_text())
        verify_source_snapshot(state,ROOT)
        verify_final_products(state)
        for module in [f"evidence/probes/Rule10/{args.edition}/CollectFinal","evidence/probes/CensusFinal"]:
            result=run_one(module,"final",args.phase,args.edition)
            need(result["exit_code"]==0 and result["source_unchanged"],"final collector check stopped")
    elif args.phase=="seals":
        state=json.loads((PROBES/"base-state.json" if args.side=="base" else PROBES/args.edition/"snapshot.json").read_text())
        verify_source_snapshot(state,ROOT/state["root"] if args.side=="base" else ROOT)
        manifest=json.loads((PROBES/args.edition/(args.side+"-seal-manifest.json")).read_text())
        for entry in manifest["probes"]:
            record=json.loads((ROOT/entry["record"]).read_text())
            result=run_one(record["probe_module"],args.side,"seals-"+args.side,args.edition,record)
            need(result["source_unchanged"],"seal probe changed during check")
            # Source failures are retained for base/final comparison. Harness
            # failures invalidate the run and must not be reported as findings.
            need(result["harness_error"] is None,"seal harness failed: "+str(result["harness_error"]))
    else:
        raise RuntimeError("Controls runner is prepared by rule10_controls.py; use that tool's documented CLI")


if __name__=="__main__": main()
