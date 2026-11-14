#!/usr/bin/env python3
"""Prepare dl-crh evidence sources/manifests; NEVER invoke Lean or Lake.

Run with python3 -I. The baseline is an exact own-source snapshot with a separate
TCSlib olean tree; it reads this checkout's one package cache through a symlink.
The seal instrumenter and scoped instance-unfolding mask are adapted from the
verified dl-folds evidence tools retained beside this file.
"""
from __future__ import annotations
import argparse
import datetime
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[2]
PROBES = ROOT / "evidence/probes/Rule10"
BASE = "eff2dcd0a63f0c371118a17c67b9a5dfc046f4e9"
BASE_OWNERS = ["TCSlib.Cryptography.Candidates.DiscreteLog",
               "TCSlib.Cryptography.Hashing.FromDiscreteLog"]
ARCH = ROOT / "evidence/tools/archived-dl-folds"
sys.dont_write_bytecode = True


def need(test, why):
    if not test:
        raise RuntimeError(why)


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def save(path, obj):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(obj, indent=2, ensure_ascii=False) + "\n")


def git(path):
    return subprocess.check_output(["git", "--no-optional-locks", "-C", str(ROOT),
                                    "show", BASE + ":" + path])


def modpath(module):
    return module.replace(".", "/") + ".lean"


def imports(raw):
    # Source headers in this closure use one ordinary import per line. The
    # independent compiled-environment closure is compared against this graph.
    return re.findall(r"^import\s+(TCSlib(?:\.[A-Za-z_][A-Za-z0-9_']*)+)\s*$",
                      raw.decode(), re.M)


def current_owners():
    helper = ROOT / "TCSlib/Cryptography/Hashing/FromDiscreteLog"
    return [BASE_OWNERS[0]] + [p.relative_to(ROOT).with_suffix("").as_posix().replace("/", ".")
                              for p in sorted(helper.rglob("*.lean"))] + [BASE_OWNERS[1]]


def closure(owner, sources):
    seen = set()
    def visit(module):
        for dep in imports(sources[modpath(module)]):
            if dep in seen:
                continue
            seen.add(dep)
            visit(dep)
    visit(owner)
    return sorted(seen)


def source_closure(owners, read):
    sources = {}
    def visit(module):
        path = modpath(module)
        if path in sources:
            return
        sources[path] = read(path)
        for dep in imports(sources[path]):
            visit(dep)
    for owner in owners:
        visit(owner)
    return sources


def collector(owners, title):
    raw = (ARCH / "NmCollect.template.lean").read_text()
    a = raw.index("def owners : List Name := [")
    b = raw.index("]", a)
    raw = raw[:a] + "def owners : List Name := [\n  " + ",\n  ".join("`" + m for m in owners) + raw[b:]
    raw = re.sub(r"^import TCSlib\S*\n", "", raw, flags=re.M)
    raw = raw.replace("import Lean\n", "import Lean\n" + "".join("import " + m + "\n" for m in owners), 1)
    raw = re.sub(r"/-! nm-cca2 review collector.*?-/", "/-! " + title + " -/", raw, flags=re.S)
    # The original catalogue already records every imported TCSlib definition,
    # every owner's stored constants, and actual Name components. Keep it intact.
    return raw


def census(owners, side):
    archived = (ARCH / "mkcensus.py").read_text()
    loop = archived.split("L.append(r'''", 1)[1].split("''')", 1)[0]
    head = "import Lean\n" + "".join("import " + m + "\n" for m in owners)
    head += "\nset_option maxHeartbeats 0\nset_option maxRecDepth 65536\nopen Lean Elab Command\n"
    head += "#print axioms TCSlib.Cryptography.Authentication.dlHash_crh\n"
    head += "def owners : List Name := [" + ", ".join("`" + m for m in owners) + "]\n"
    head += "def nameMap : Std.HashMap String String := {}\n"
    return head + "/- dl-crh all-stored census, " + side + ". -/\n" + loop


def init(edition):
    base_root = PROBES / "BaseTree"
    base_sources = source_closure(BASE_OWNERS, git)
    # All TCSlib source bytes, module identities and script/toolchain bytes are
    # independent of the working proof tree. No package or build tree is copied.
    for path, raw in base_sources.items():
        target = base_root / path
        target.parent.mkdir(parents=True, exist_ok=True)
        if target.exists():
            need(target.read_bytes() == raw, "baseline source changed: " + path)
        else:
            target.write_bytes(raw)
    for path in ("scripts/lean_check_tree.sh", "lean-toolchain", "lake-manifest.json"):
        target = base_root / path
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(git(path))
    # Keep the delivered source snapshot free of cache links: copytree callers
    # must never accidentally traverse a package tree while staging evidence.
    cache = base_root / ".lake/packages"
    actual_cache = ROOT / ".lake/packages"
    if cache.is_symlink():
        need(cache.resolve() == actual_cache.resolve(), "baseline cache link changed")
        cache.unlink()
    need(not cache.exists(), "delivered baseline snapshot contains a cache tree")
    issued = (ROOT / "evidence/order.txt").read_text().splitlines()
    wanted = {p[:-5] for p in base_sources}
    order = [m for m in issued if m in wanted]
    need(set(order) == wanted, "baseline closure is outside issued order")
    seen = set()
    for module in order:
        need(set(imports(base_sources[module + ".lean"])) <= seen, "baseline order is not topological: " + module)
        seen.add(module.replace("/", "."))
    (PROBES / "base-order.txt").write_text("\n".join(order) + "\n")
    base_probe = base_root / "evidence/probes/Rule10"
    base_probe.mkdir(parents=True, exist_ok=True)
    (base_probe / "CollectBase.lean").write_text(collector(BASE_OWNERS, "dl-crh exact-base closure collector"))
    (base_probe / "CensusBase.lean").write_text(census(BASE_OWNERS, "base"))
    base_state = dict(base=BASE, root=".lake/dl-crh-base-work",
                      snapshot_root=str(base_root.relative_to(ROOT)), owners=BASE_OWNERS,
                      source_hashes={p: sha(r) for p, r in sorted(base_sources.items())},
                      package_cache_link=str(actual_cache), olean_tree=".lake/dl-crh-base-oleans",
                      method="Exact git-base own-source snapshot, original TCSlib module identities; own package cache symlink; independent own TCSlib oleans.")
    save(PROBES / "base-state.json", base_state)
    owners = current_owners()
    final_sources = source_closure(owners, lambda p: (ROOT / p).read_bytes())
    out = PROBES / edition
    need(not (out / "snapshot.json").exists(), "edition already initialized; use a fresh edition name")
    out.mkdir(parents=True, exist_ok=True)
    for path, raw in final_sources.items():
        snap = out / "snapshot" / path
        snap.parent.mkdir(parents=True, exist_ok=True)
        snap.write_bytes(raw)
    (out / "CollectFinal.lean").write_text(collector(owners, "dl-crh final full-closure collector"))
    (ROOT / "evidence/probes/CensusFinal.lean").write_text(census(owners, "final"))
    save(out / "snapshot.json", dict(edition=edition, base=BASE, owners=owners,
         source_hashes={p: sha(r) for p, r in sorted(final_sources.items())},
         base_absent=[m for m in owners if m not in BASE_OWNERS],
         generated_at=datetime.datetime.now(datetime.timezone.utc).isoformat()))
    print("Prepared exact baseline:", len(order), "modules; final owners:", len(owners))
    print("Delivered baseline is source-only; runner materializes an isolated runtime with this checkout's own cache symlink outside evidence/.")


def load_tool(path, name):
    spec = importlib.util.spec_from_file_location(name, path)
    need(spec is not None and spec.loader is not None, "cannot import reviewed tool")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def builders():
    old = ARCH / "archived-gate10-tools"
    bs = load_tool(old / "build_seals.py", "dl_crh_archived_bs")
    ctl = load_tool(old / "build_controls.py", "dl_crh_archived_ctl")
    adapter = load_tool(old / "request_payload_adapter.py", "dl_crh_archived_adapter")
    adapter.configure_builders(bs, ctl)
    original = bs.seal_command
    def chunked(label, rows, *, end):
        chunks = [rows[i:i+128] for i in range(0, len(rows), 128)] or [[]]
        return b"".join(original(label + "_part" + str(i+1), part, end=end)
                        for i, part in enumerate(chunks))
    bs.seal_command = chunked
    return bs, adapter


def parse_catalog(path):
    cat, closures, roots, counts = {}, {}, {}, {}
    for line in path.read_text().splitlines():
        if line.startswith("CAT "):
            row = json.loads(line[4:])
            name = row["name"]["display"]
            need(name not in cat, "duplicate catalog Name")
            cat[name] = row
        elif line.startswith("CLOSURE "):
            row = json.loads(line[8:])
            need(row["module"] not in closures, "duplicate closure")
            closures[row["module"]] = row["closure"]
        elif line.startswith("ROOT "):
            row = json.loads(line[5:])
            roots.setdefault(row["module"], []).append(row)
        elif line.startswith("MODULE "):
            name, count = line[7:].split(": stored ")
            counts[name] = int(count)
    need(cat and closures and counts, "incomplete collector log")
    for owner, count in counts.items():
        need(len(roots.get(owner, [])) == count, "stored-root census mismatch: " + owner)
    return cat, closures, roots, counts


def seals(edition, side, log):
    out = PROBES / edition
    state = json.loads((PROBES / "base-state.json" if side == "base" else out / "snapshot.json").read_text())
    source_root = ROOT / state["root"] if side == "base" else ROOT
    owners = state["owners"]
    for path, digest in state["source_hashes"].items():
        need(sha((source_root / path).read_bytes()) == digest, "source changed since preparation: " + path)
    sources = {p: (source_root / p).read_bytes() for p in state["source_hashes"]}
    cat, closures, roots, counts = parse_catalog(log)
    need(set(closures) == set(owners), "collector owner scope differs")
    bs, _ = builders()
    records = []
    for owner in owners:
        expected_closure = closure(owner, sources)
        need(closures[owner] == expected_closure, "compiled/source closure mismatch: " + owner)
        for letter, excluded in (("A", {"Complexity.PolyExpr.eval"}), ("B", set())):
            eligible = [r for r in cat.values() if r["home"]["display"] in expected_closure
                        and r["kind"] == "def" and (r["matcher"] or r["status"] != "reducible")
                        and r["name"]["display"] not in excluded]
            rows = [dict(spelling=r["name"]["display"], home=r["home"]["display"],
                         name_components=r["name"]["components"], home_components=r["home"]["components"],
                         instance=r["instance"], matcher=r["matcher"], abbrev=r["abbrev"],
                         collector_reducibility=r["status"]) for r in sorted(eligible, key=lambda r:r["name"]["display"])]
            label = "DlCrh_" + side + "_" + letter + "_" + owner.replace(".", "_")
            raw = sources[modpath(owner)]
            probe, insertions, line_map = bs.instrument(raw, bs.header(raw), label, rows)
            relative = Path("evidence/probes/Rule10") / edition / "seals" / side / letter / (label + ".lean")
            target = source_root / relative
            target.parent.mkdir(parents=True, exist_ok=True)
            need(not target.exists(), "seal source already exists")
            target.write_bytes(probe)
            copy = out / "probe-sources" / side / letter / (label + ".lean.txt")
            copy.parent.mkdir(parents=True, exist_ok=True)
            copy.write_bytes(probe)
            own_terms = {ref["display"] for root in roots[owner]
                         for ref in root["type_refs"] + root["value_refs"]}
            selected = {r["spelling"] for r in rows}
            excluded_terms = {}
            for name in sorted(own_terms - selected):
                r = cat[name]
                need(r["home"]["display"] in expected_closure, "foreign term outside closure")
                reason = "notation" if name in excluded else "abbrev" if r["abbrev"] else "reducible" if r["status"] == "reducible" else None
                need(reason is not None, "ordinary foreign term omitted from full closure: " + name)
                excluded_terms[name] = reason
            record = dict(label=label, side=side, variant=letter, owner=owner,
                          probe_module=relative.with_suffix("").as_posix(),
                          source=modpath(owner), source_sha256=sha(raw), probe_sha256=sha(probe),
                          delivered_probe_source=str(copy.relative_to(ROOT)),
                          requested=len(rows), rows=rows, closure=expected_closure,
                          excluded_notation=sorted(excluded), term_exclusions=excluded_terms,
                          stored_constants=counts[owner], collector_log=str(log.relative_to(ROOT)),
                          collector_log_sha256=sha(log.read_bytes()), insertions=insertions,
                          source_to_probe_lines=line_map,
                          chunks=[dict(label=label+"_part"+str(i//128+1), start=i,
                                       count=len(rows[i:i+128])) for i in range(0,len(rows),128)] or
                                 [dict(label=label+"_part1",start=0,count=0)],
                          unsealable_reducible=[r for r in cat.values()
                              if r["home"]["display"] in expected_closure and r["kind"] == "def"
                              and r["status"] == "reducible" and not r["matcher"]])
            recpath = out / "records" / side / letter / (label + ".json")
            save(recpath, record)
            records.append(dict(record=str(recpath.relative_to(ROOT)), **{k:record[k] for k in
                ("label","side","variant","owner","probe_module","probe_sha256","requested")}))
    save(out / (side + "-seal-manifest.json"), dict(side=side, base=BASE, edition=edition,
         variants={"A":"PolyExpr.eval excluded as exact notation", "B":"PolyExpr.eval sealed"},
         probes=records, status="PREPARED_NOT_RUN",
         base_absent=json.loads((out / "snapshot.json").read_text())["base_absent"] if side=="base" else []))
    print("Prepared", len(records), side, "whole-file seal probes; no Lean was invoked")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="command", required=True)
    p = sub.add_parser("init"); p.add_argument("--edition", required=True)
    p = sub.add_parser("seals"); p.add_argument("--edition", required=True)
    p.add_argument("--side", choices=("base","final"), required=True)
    p.add_argument("--collector-log", type=Path, required=True)
    args = parser.parse_args()
    PROBES.mkdir(parents=True, exist_ok=True)
    need(re.fullmatch(r"[A-Za-z0-9_-]+", args.edition), "unsafe edition name")
    if args.command == "init": init(args.edition)
    else: seals(args.edition, args.side, args.collector_log.resolve())


if __name__ == "__main__": main()
