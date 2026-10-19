r"""Reference texts in one place: which are attached, which theorems they cover, and
which texts (and which Lean files) are still waiting for one.

    python3 scripts/sources.py                       # status (the default)
    python3 scripts/sources.py status --modules LearningTheory --all
    python3 scripts/sources.py add CBL06=~/texts/cesa-bianchi-lugosi-ch07.pdf   # attach + match
    python3 scripts/sources.py add Ver18=~/texts/vershynin.md --no-match          # attach only
    python3 scripts/sources.py match vershynin-hdp-book                          # match an ingested text
    python3 scripts/sources.py register Ver18=vershynin-hdp-book                 # tag -> document

The contract (dataset/README.md, policy.md §2): whoever formalizes a result attaches the
text it came from, under the [TAG] its docstring cites.  `status` is the view of that
contract from three sides:

  texts     every document ingested under blueprint/src/references/: the tags it is
            registered for, and how many theorems the blueprint cites it for (a text
            that was ingested but never matched shows `not matched`);
  tags      every [TAG] the theorems' docstrings cite: how many theorems, how many of
            them are cited, and whether a text is attached (`attached`), attached but
            never matched (`unmatched`) or `MISSING`;
  files     every Lean module of the dataset that is not fully cited, with what it is
            waiting for: a text to attach, a match to run, or docstring tags.

`add TAG=PATH` ingests the text (a PDF is OCR'd and cleaned by the model; a validated
.md is copied), registers the tag and matches the text against the dataset -- the
`references` and `citations` stages of scripts/dataset_pipeline.py.  The citations land
in the blueprint; `python3 scripts/dataset_pipeline.py --stages dataset,verify` then
carries them into dataset/tcslib_theorems.jsonl.gz.
"""

from __future__ import annotations

import argparse
import collections
import importlib.util
import json
import subprocess
import sys
from pathlib import Path

BASE = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(BASE))

from proofmatch.dataset_io import open_dataset, resolve_dataset  # noqa: E402

SCRIPTS = BASE / "scripts"


def _load_sibling(name: str):
    spec = importlib.util.spec_from_file_location(name, SCRIPTS / f"{name}.py")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


rc = _load_sibling("reference_coverage")
bd = rc.bd
bpn = rc.bpn

REFERENCES = rc.REFERENCES
DATASET = BASE / "dataset" / "tcslib_theorems.jsonl"
PASS1 = BASE / "dataset" / ".pipeline" / "pass1.jsonl"


# --------------------------------------------------------------------------- #
# Gathering
# --------------------------------------------------------------------------- #
def load_records(path: Path) -> list[dict]:
    if not resolve_dataset(path).exists():
        return []
    with open_dataset(path) as handle:
        return [json.loads(l) for l in handle if l.strip()]


def status_data(records: list[dict], wanted_modules: list[str] | None) -> dict:
    """Everything `print_status` shows, as plain data (also written with --json)."""
    graph = json.load(open(bd.DEP_GRAPH))["modules"] if bd.DEP_GRAPH.exists() else {}
    index = bd.build_index(graph) if graph else {}
    sources = rc.Sources(index)
    registry = rc.load_registry()
    citations = bpn.blueprint_citations()
    ingested = rc.ingested_documents()
    raw_only = sorted({p.name[:-7] for p in REFERENCES.glob("*.raw.md")} - ingested)

    # Documents: registered tags, and how many declarations the blueprint cites them for.
    doc_tags: dict[str, list[str]] = collections.defaultdict(list)
    for tag, row in registry["tags"].items():
        for doc in row["documents"]:
            doc_tags[doc].append(tag)
    doc_cites: dict[str, collections.Counter] = collections.defaultdict(collections.Counter)
    for name, cite in citations.items():
        for group in ("proof_sources", "statement_sources"):
            for row in cite.get(group, []):
                doc_cites[row["document"]][group] += 1
    texts = []
    for doc in sorted(ingested):
        proofs = doc_cites[doc]["proof_sources"]
        statements = doc_cites[doc]["statement_sources"]
        texts.append({
            "document": doc,
            "tags": sorted(doc_tags.get(doc, [])),
            "proof_citations": proofs,
            "statement_citations": statements,
            "status": "matched" if proofs or statements else "not matched",
        })
    doc_matched = {t["document"] for t in texts if t["status"] == "matched"}

    # Theorems: per tag and per module.
    theorems = [r for r in records if r.get("kind") in bd.PROOF_KINDS]
    if wanted_modules:
        theorems = [r for r in theorems if bd.module_matches(r.get("source_module", ""), wanted_modules)]
    per_tag: dict[str, dict] = {}
    per_module: dict[str, dict] = {}
    titles: dict[str, str] = {}
    for record in theorems:
        rid = record["id"]
        module = record.get("source_module", "")
        cite = citations.get(rid) or {}
        cited = bool(cite.get("proof_sources") or cite.get("statement_sources"))
        tags = sorted({t for t, _ in sources.tags(rid, module)})
        row = per_module.setdefault(module, {"module": module, "theorems": 0, "cited": 0,
                                             "tags": collections.Counter(), "untagged": 0})
        row["theorems"] += 1
        row["cited"] += cited
        if not tags:
            row["untagged"] += 1
            row["untagged_uncited"] = row.get("untagged_uncited", 0) + (not cited)
        for tag in tags:
            row["tags"][tag] += 1
            t = per_tag.setdefault(tag, {"tag": tag, "theorems": 0, "cited": 0,
                                         "modules": collections.Counter(), "locations": collections.Counter()})
            t["theorems"] += 1
            t["cited"] += cited
            t["modules"][module] += 1
            for tag2, loc in sources.tags(rid, module):
                if tag2 == tag and loc:
                    t["locations"][loc.split(",")[0].strip()] += 1
            if tag not in titles:
                titles[tag] = sources.titles(module).get(tag, "") or registry["tags"].get(tag, {}).get("title", "")

    def tag_status(tag: str, uncited: int) -> tuple[str, list[str]]:
        docs = [d for d in registry["tags"].get(tag, {}).get("documents", []) if d in ingested]
        if not docs:
            # Every theorem citing the tag is cited through some other text: nothing to attach.
            return ("covered" if uncited == 0 else "MISSING"), []
        if any(d in doc_matched for d in docs):
            return "attached", docs
        return "unmatched", docs

    tags = []
    for tag, t in sorted(per_tag.items(), key=lambda kv: (-(kv[1]["theorems"] - kv[1]["cited"]), kv[0])):
        status, docs = tag_status(tag, t["theorems"] - t["cited"])
        tags.append({
            "tag": tag, "title": titles.get(tag, ""),
            "theorems": t["theorems"], "cited": t["cited"], "uncited": t["theorems"] - t["cited"],
            "status": status, "documents": docs,
            "modules": [m for m, _ in t["modules"].most_common(6)],
            "locations": [f"{loc} ({n})" for loc, n in t["locations"].most_common(5)],
        })
    tag_state = {t["tag"]: t["status"] for t in tags}

    files = []
    for module, row in sorted(per_module.items()):
        uncited = row["theorems"] - row["cited"]
        missing = sorted(t for t in row["tags"] if tag_state.get(t) == "MISSING")
        unmatched = sorted(t for t in row["tags"] if tag_state.get(t) == "unmatched")
        if uncited == 0:
            state, need = "cited", ""
        elif missing:
            state = "needs text"
            need = "attach " + ", ".join(missing)
        elif unmatched:
            state = "needs match"
            need = "match " + ", ".join(
                d for t in unmatched for d in registry["tags"].get(t, {}).get("documents", []) if d in ingested)
        elif row["untagged"] == row["theorems"]:
            state, need = "untagged", "add [TAG, location] docstring citations (policy.md §2), then attach the text"
        elif row["untagged"]:
            state, need = "partly tagged", f"{row['untagged']} theorem(s) without a docstring tag"
        else:
            state, need = "partly cited", "text attached and matched; the rest were not found in it"
        files.append({
            "module": module, "theorems": row["theorems"], "cited": row["cited"], "uncited": uncited,
            "tags": sorted(row["tags"]), "untagged": row["untagged"],
            "untagged_uncited": row.get("untagged_uncited", 0), "state": state, "need": need,
        })

    return {
        "theorems": len(theorems),
        "cited": sum(f["cited"] for f in files),
        "texts": texts,
        "raw_only": raw_only,
        "tags": tags,
        "untagged_theorems": sum(f["untagged_uncited"] for f in files),
        "files": files,
    }


# --------------------------------------------------------------------------- #
# Printing
# --------------------------------------------------------------------------- #
def _area(module: str) -> str:
    parts = module.split(".")
    return parts[1] if len(parts) > 1 else module


def print_status(data: dict, *, show_all: bool, selection: bool) -> None:
    texts, tags, files = data["texts"], data["tags"], data["files"]
    cited, total = data["cited"], data["theorems"]
    print(f"{total} theorems in the dataset{' (selection)' if selection else ''}: "
          f"{cited} cited from a reference text, {total - cited} not "
          f"({data['untagged_theorems']} of those carry no docstring tag)")

    # Texts
    matched = [t for t in texts if t["status"] == "matched"]
    unmatched = [t for t in texts if t["status"] != "matched"]
    print(f"\nReference texts under blueprint/src/references/: {len(texts)} ingested, "
          f"{len(matched)} matched, {len(unmatched)} never matched")
    print(f"  {'document':46s} {'tags':14s} {'proofs':>6s} {'stmts':>6s}  status")
    for t in texts:
        print(f"  {t['document'][:46]:46s} {(', '.join(t['tags']) or '-')[:14]:14s} "
              f"{t['proof_citations']:6d} {t['statement_citations']:6d}  {t['status']}")
    if unmatched:
        print("  never matched against the dataset; to look for citations in them:")
        for t in unmatched[:6]:
            print(f"      python3 scripts/sources.py match {t['document']}")
        if len(unmatched) > 6:
            print(f"      ... ({len(unmatched) - 6} more; `match` accepts several documents)")
    if data["raw_only"]:
        print(f"  {len(data['raw_only'])} raw extraction(s) with no validated .md "
              f"(an interrupted ingestion; re-run `add`): {', '.join(data['raw_only'])}")

    # Tags
    print(f"\nDocstring tags cited by the theorems ([TAG, location], policy.md §2): {len(tags)}")
    print(f"  {'tag':9s} {'theorems':>8s} {'cited':>6s} {'uncited':>7s}  text")
    for t in tags:
        where = (", ".join(t["documents"]) if t["documents"] else "" if t["status"] == "covered"
                 else f"python3 scripts/sources.py add {t['tag']}=<path>")
        label = {"attached": "attached: ", "unmatched": "attached, never matched: ",
                 "MISSING": "MISSING -> ", "covered": "cited through other texts; nothing to attach"}[t["status"]]
        print(f"  {t['tag']:9s} {t['theorems']:8d} {t['cited']:6d} {t['uncited']:7d}  {label}{where}")
        if t["title"]:
            print(f"            {t['title'][:96]}")
        if t["status"] == "MISSING" and t["locations"]:
            print(f"            cited at: {', '.join(t['locations'])}")
    missing = [t for t in tags if t["status"] == "MISSING"]
    if missing:
        print("\n  To attach the missing texts (then their theorems get citations instead of "
              "informalized proof notes):")
        for t in missing:
            hint = t["locations"][0].split(" (")[0] if t["locations"] else "the cited part"
            print(f"      python3 scripts/sources.py add {t['tag']}=<{t['tag']} text, {hint} ...>")

    # Files
    todo = [f for f in files if f["state"] != "cited"]
    by_area: dict[str, collections.Counter] = collections.defaultdict(collections.Counter)
    for f in files:
        by_area[_area(f["module"])][f["state"]] += 1
    print(f"\nLean files: {len(files)} modules in the dataset, {len(files) - len(todo)} fully cited, "
          f"{len(todo)} waiting for something")
    print(f"  {'area':26s} {'modules':>7s}  states")
    for area, states in sorted(by_area.items()):
        print(f"  {area:26s} {sum(states.values()):7d}  "
              + ", ".join(f"{n} {s}" for s, n in states.most_common()))
    order = {"needs text": 0, "needs match": 1, "partly tagged": 2, "partly cited": 3, "untagged": 4}
    todo.sort(key=lambda f: (order.get(f["state"], 9), -f["uncited"], f["module"]))
    shown = todo if show_all else [f for f in todo if f["state"] != "untagged"][:40]
    if shown:
        print(f"\n  {'module':62s} {'thms':>4s} {'cited':>5s}  state          what it needs")
        for f in shown:
            print(f"  {f['module'][:62]:62s} {f['theorems']:4d} {f['cited']:5d}  {f['state']:14s} {f['need']}")
    hidden = len(todo) - len(shown)
    if hidden:
        untagged = sum(1 for f in todo if f["state"] == "untagged")
        print(f"  ... {hidden} more module(s) not shown"
              + (f", {untagged} of them untagged (no [TAG] in any docstring; older areas)" if untagged else "")
              + "; --all lists every one, --modules AREA narrows")


# --------------------------------------------------------------------------- #
# Actions
# --------------------------------------------------------------------------- #
def pipeline(argv: list[str]) -> int:
    cmd = [sys.executable, str(SCRIPTS / "dataset_pipeline.py"), *argv]
    print("$ " + " ".join(cmd[1:]))
    return subprocess.call(cmd, cwd=BASE)


def cmd_add(args) -> int:
    for item in args.source:
        if "=" not in item:
            print(f"ERROR: `add` wants TAG=PATH (the [TAG] the docstrings cite), got {item!r}")
            return 2
        tag, path = item.split("=", 1)
        if not rc.TAG_RE.match(f"[{tag.strip()}]"):
            print(f"ERROR: {tag!r} does not look like a docstring tag such as AB09 or HILL99")
            return 2
        if not Path(path).expanduser().exists():
            print(f"ERROR: {path} does not exist")
            return 2
    stages = "references" if args.no_match else "references,citations"
    argv = ["--stages", stages, *[a for s in args.source for a in ("--source", s)]]
    argv += _passthrough(args)
    rc_ = pipeline(argv)
    if rc_ != 0:
        return rc_
    print()
    return cmd_status(args)


def cmd_match(args) -> int:
    registry = rc.load_registry()
    by_doc = {d: t for t, row in registry["tags"].items() for d in row["documents"]}
    sources = []
    for doc in args.document:
        stem = Path(doc).name
        for suffix in (".raw.md", ".md", ".pdf"):
            if stem.endswith(suffix):
                stem = stem[: -len(suffix)]
        md = REFERENCES / f"{stem}.md"
        if not md.exists():
            print(f"ERROR: no validated {md.relative_to(BASE)}; attach it first with "
                  f"`python3 scripts/sources.py add TAG={doc}`")
            return 2
        tag = by_doc.get(stem)
        if not tag:
            print(f"WARNING: {stem} is registered under no tag; register it so the status "
                  f"can tie docstrings to it: python3 scripts/sources.py register TAG={stem}")
        sources.append(f"{tag}={md}" if tag else str(md))
    argv = ["--stages", "citations", *[a for s in sources for a in ("--source", s)]]
    if args.rematch:
        argv.append("--rematch")
    argv += _passthrough(args)
    rc_ = pipeline(argv)
    if rc_ != 0:
        return rc_
    print()
    return cmd_status(args)


def cmd_register(args) -> int:
    cmd = [sys.executable, str(SCRIPTS / "reference_coverage.py"),
           *[a for item in args.pair for a in ("--register", item)]]
    out = subprocess.run(cmd, cwd=BASE, capture_output=True, text=True)
    for line in out.stdout.splitlines():
        if line.startswith(("registry", "WARNING", "ERROR")):
            print(line)
    return out.returncode if out.returncode else cmd_status(args)


def cmd_status(args) -> int:
    dataset = Path(args.dataset) if args.dataset else DATASET
    records = load_records(dataset)
    if not records:
        print(f"ERROR: no records in {dataset}")
        return 1
    if not bd.DEP_GRAPH.exists():
        print(f"WARNING: {bd.DEP_GRAPH.name} missing; docstring tags are read from the source "
              "files by name")
    data = status_data(records, args.modules)
    print_status(data, show_all=args.all, selection=bool(args.modules))
    if args.json:
        args.json.parent.mkdir(parents=True, exist_ok=True)
        args.json.write_text(json.dumps(data, indent=2, ensure_ascii=False), encoding="utf-8")
        print(f"\njson -> {args.json}")
    return 0


def _passthrough(args) -> list[str]:
    argv = []
    if args.yes:
        argv.append("--yes")
    if args.model:
        argv += ["--model", args.model]
    if args.backend:
        argv += ["--backend", args.backend]
    if args.max_cost:
        argv += ["--max-cost", args.max_cost]
    return argv


def _common(p: argparse.ArgumentParser) -> None:
    p.add_argument("--dataset", help=f"dataset to report on (default {DATASET.relative_to(BASE)})")
    p.add_argument("--modules", nargs="+", metavar="MODULE",
                   help="restrict to these modules (full name, dotted suffix or area)")
    p.add_argument("--all", action="store_true", help="list every module, untagged ones included")
    p.add_argument("--json", type=Path, help="also write the status as JSON here")


def _spend(p: argparse.ArgumentParser) -> None:
    p.add_argument("--yes", action="store_true", help="do not ask before the model runs")
    p.add_argument("--model", help="model for the OCR cleanup / matching")
    p.add_argument("--backend", choices=("auto", "claude", "codex"),
                   help="CLI that runs the model (default: inferred from the model id)")
    p.add_argument("--max-cost", help="cap in USD for the model runs")


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest="command")

    st = sub.add_parser("status", help="what is attached, cited and missing (the default)")
    _common(st)
    st.set_defaults(func=cmd_status)

    add = sub.add_parser("add", help="attach a text: ingest, register its tag, match it")
    add.add_argument("source", nargs="+", metavar="TAG=PATH", help="PDF or validated .md")
    add.add_argument("--no-match", action="store_true", help="ingest and register only")
    _common(add)
    _spend(add)
    add.set_defaults(func=cmd_add)

    mt = sub.add_parser("match", help="match ingested document(s) against the dataset")
    mt.add_argument("document", nargs="+", help="document stem(s) under blueprint/src/references/")
    mt.add_argument("--rematch", action="store_true", help="redo a document already matched")
    _common(mt)
    _spend(mt)
    mt.set_defaults(func=cmd_match)

    rg = sub.add_parser("register", help="record that a document covers a docstring tag")
    rg.add_argument("pair", nargs="+", metavar="TAG=DOCUMENT")
    _common(rg)
    rg.set_defaults(func=cmd_register)

    argv = list(sys.argv[1:] if argv is None else argv)
    if not argv or argv[0] not in ("status", "add", "match", "register", "-h", "--help"):
        argv = ["status", *argv]
    args = ap.parse_args(argv)
    return args.func(args)


if __name__ == "__main__":
    raise SystemExit(main())
