r"""Which theorems have no reference text behind them, and which text is missing.

The dataset builder never goes looking for sources.  A theorem gets a citation only
when the text it was formalized from has been ingested under
`blueprint/src/references/<name>.md` and matched (`proofmatch match`, the `citations`
stage of scripts/dataset_pipeline.py).  Everything else falls through to the
`informalize` stage, which writes a prose account of the Lean proof instead of a
citation.  The policy (policy.md §2 and dataset/README.md) is therefore:

    whoever submits a formalization attaches the text it came from
    (`dataset_pipeline.py --source TAG=path.pdf`), in the same change.

This script tells both sides what is outstanding.  Every declaration's docstring carries
a `[TAG, location]` citation (policy.md §2); the registry `references/sources.json` maps
a TAG to the ingested documents that cover it.  For every theorem in scope that has no
blueprint citation the script reports its docstring tag, whether a document is
registered for that tag, and whether an informalized note already stands in for the
missing citation -- aggregated by tag, so the answer is "attach AB09 chapter 9" rather
than a list of 300 names.

Usage:
    python3 scripts/reference_coverage.py                          # the shipped dataset
    python3 scripts/reference_coverage.py --dataset dataset/.pipeline/pass1.jsonl \
        --previous dataset/.pipeline/previous.jsonl --report dataset/.pipeline/coverage.json
    python3 scripts/reference_coverage.py --register AB09=arora-barak-ch09-...   # tag -> doc
    python3 scripts/reference_coverage.py --rebuild-registry       # from existing citations
    python3 scripts/reference_coverage.py --modules Complexity --only-new --strict

With --strict the exit status is 1 when a *new* theorem (absent from --previous) has a
docstring tag for which no document is registered and no --source was attached; the
pipeline uses this to stop before writing proof notes for theorems whose text the
submitter simply forgot to attach (`--without-sources` waives it).
"""

from __future__ import annotations

import argparse
import collections
import importlib.util
import json
import re
import sys
from pathlib import Path

BASE = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(BASE))

from proofmatch.dataset_io import open_dataset, resolve_dataset  # noqa: E402


def _load_sibling(name: str):
    spec = importlib.util.spec_from_file_location(name, Path(__file__).resolve().parent / f"{name}.py")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


bd = _load_sibling("build_dataset")
bpn = _load_sibling("build_proof_notes")
be = _load_sibling("blueprint_enumerate")

REFERENCES = BASE / "blueprint" / "src" / "references"
REGISTRY = REFERENCES / "sources.json"
DATASET = BASE / "dataset" / "tcslib_theorems.jsonl"

#: `[AB09, Thm 6.18]`, `[RY20, Ch. 6, eq. (6.3)]`, `[Sha79]`, `[HILL99, §2]`.
TAG_RE = re.compile(r"\[([A-Z][A-Za-z]{0,7}\d{2,4}[a-z]?)(?:,\s*([^\]]{1,80}))?\]")
#: `* [AB09] S. Arora, B. Barak, *Computational Complexity*, ...` in a `## References` section.
REF_LINE_RE = re.compile(r"^\s*[*-]\s*\[([A-Z][A-Za-z]{0,7}\d{2,4}[a-z]?)\]\s*(.+?)\s*$")


# --------------------------------------------------------------------------- #
# Registry
# --------------------------------------------------------------------------- #
def load_registry() -> dict:
    if not REGISTRY.exists():
        return {"tags": {}}
    try:
        data = json.loads(REGISTRY.read_text(encoding="utf-8"))
    except ValueError:
        return {"tags": {}}
    data.setdefault("tags", {})
    return data


def save_registry(data: dict) -> None:
    data["_comment"] = (
        "Maps the [TAG] of policy.md §2 docstring citations to the reference documents "
        "under this directory (stems of <name>.md). Maintained by "
        "scripts/reference_coverage.py (--register, --rebuild-registry) and by "
        "scripts/dataset_pipeline.py --source TAG=path."
    )
    ordered = {"_comment": data["_comment"],
               "tags": {t: data["tags"][t] for t in sorted(data["tags"])}}
    REGISTRY.write_text(json.dumps(ordered, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")


def register(data: dict, tag: str, document: str, title: str | None = None) -> bool:
    document = Path(document).name
    for suffix in (".raw.md", ".md", ".pdf"):
        if document.endswith(suffix):
            document = document[: -len(suffix)]
    row = data["tags"].setdefault(tag, {"title": "", "documents": []})
    if title and not row.get("title"):
        row["title"] = title
    if document in row["documents"]:
        return False
    row["documents"].append(document)
    row["documents"].sort()
    return True


def ingested_documents() -> set[str]:
    return {p.name[:-3] for p in REFERENCES.glob("*.md") if not p.name.endswith(".raw.md")}


# --------------------------------------------------------------------------- #
# Docstring tags
# --------------------------------------------------------------------------- #
class Sources:
    """Docstring tags of declarations and the `## References` titles of modules."""

    def __init__(self, index: dict):
        self.index = index
        self._lines: dict[str, list[str]] = {}

    def lines(self, module: str) -> list[str]:
        if module not in self._lines:
            path = bd.module_to_lean_path(module)
            try:
                self._lines[module] = path.read_text(encoding="utf-8", errors="ignore").splitlines()
            except OSError:
                self._lines[module] = []
        return self._lines[module]

    def tags(self, name: str, module: str | None = None) -> list[tuple[str, str]]:
        """`[(tag, location), ...]` from the declaration's docstring.

        A declaration the dependency graph does not know (its module is not built, or
        the record predates a rename) is looked up by name in `module`'s source file."""
        rec = self.index.get(name)
        if rec is not None:
            module, kidx = rec["module"], rec["kidx"]
        else:
            kidx = self.declaration_line(module or "", name)
            if kidx is None:
                return []
        doc = be.extract_docstring(self.lines(module), kidx)
        if not doc:
            return []
        return [(m.group(1), (m.group(2) or "").strip()) for m in TAG_RE.finditer(doc)]

    _DECL = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|nonrec\s+)*"
                       r"(?:theorem|lemma|def|abbrev|instance)\s+([^\s:({\[⦃]+)")

    def declaration_line(self, module: str, name: str) -> int | None:
        """Line index of `theorem <name>` (by full name, then by short name) in the module."""
        if not module:
            return None
        short = name.rsplit(".", 1)[-1]
        fallback = None
        for i, line in enumerate(self.lines(module)):
            m = self._DECL.match(line)
            if not m:
                continue
            declared = m.group(1)
            if declared == name or name.endswith("." + declared):
                return i
            if fallback is None and declared.rsplit(".", 1)[-1] == short:
                fallback = i
        return fallback

    def titles(self, module: str) -> dict[str, str]:
        """`{tag: full citation}` from the module docstring's `## References` section."""
        out: dict[str, str] = {}
        lines = self.lines(module)
        header = "\n".join(lines[:200])
        if "## References" not in header:
            return out
        after = header.split("## References", 1)[1].split("-/", 1)[0]
        current = None
        for line in after.splitlines():
            m = REF_LINE_RE.match(line)
            if m:
                current = m.group(1)
                out[current] = m.group(2)
            elif current and line.startswith("  ") and line.strip():
                out[current] += " " + line.strip()
        return out


def load_records(path: Path) -> list[dict]:
    if not resolve_dataset(path).exists():
        return []
    with open_dataset(path) as handle:
        return [json.loads(l) for l in handle if l.strip()]


# --------------------------------------------------------------------------- #
# Report
# --------------------------------------------------------------------------- #
def coverage(records: list[dict], previous_ids: set[str], index: dict, sources: Sources,
             registry: dict, attached: set[str]) -> dict:
    citations = bpn.blueprint_citations()
    notes = bpn.load_notes()
    docs = ingested_documents()
    registered = {t: [d for d in row["documents"] if d in docs]
                  for t, row in registry["tags"].items()}

    per_tag: dict[str, dict] = {}
    untagged: list[str] = []
    cited = noted = 0
    uncited: list[str] = []
    for record in records:
        if record.get("kind") not in bd.PROOF_KINDS:
            continue
        rid = record["id"]
        cite = citations.get(rid) or {}
        if cite.get("proof_sources") or cite.get("statement_sources"):
            cited += 1
            continue
        uncited.append(rid)
        has_note = bpn.note_for(rid, notes) is not None
        noted += has_note
        tags = sources.tags(rid, record.get("source_module"))
        new = rid not in previous_ids
        if not tags:
            untagged.append(rid)
            continue
        for tag, location in tags:
            row = per_tag.setdefault(tag, {
                "tag": tag, "title": "", "uncited": 0, "new": 0, "with_note": 0,
                "locations": collections.Counter(), "modules": collections.Counter(),
                "examples": [],
            })
            row["uncited"] += 1
            row["new"] += new
            row["with_note"] += has_note
            if location:
                row["locations"][location.split(",")[0].strip()] += 1
            row["modules"][record.get("source_module", "")] += 1
            if len(row["examples"]) < 5:
                row["examples"].append(rid)
            if not row["title"]:
                row["title"] = sources.titles(record.get("source_module", "")).get(tag, "")

    rows = []
    for tag, row in sorted(per_tag.items(), key=lambda kv: -kv[1]["uncited"]):
        have = registered.get(tag, [])
        rows.append({
            "tag": tag,
            "title": row["title"],
            "uncited": row["uncited"],
            "new": row["new"],
            "with_note": row["with_note"],
            "documents": have,
            "attached_now": tag in attached,
            "status": ("attached" if tag in attached else
                       "registered" if have else "missing"),
            "locations": [f"{loc} ({n})" for loc, n in row["locations"].most_common(6)],
            "modules": [m for m, _ in row["modules"].most_common(4)],
            "examples": row["examples"],
        })
    return {
        "in_scope": sum(1 for r in records if r.get("kind") in bd.PROOF_KINDS),
        "cited": cited,
        "uncited": len(uncited),
        "uncited_with_note": noted,
        "uncited_untagged": len(untagged),
        "untagged_examples": untagged[:10],
        "tags": rows,
        "documents_ingested": sorted(docs),
        "documents_unregistered": sorted(docs - {d for v in registered.values() for d in v}),
    }


def print_report(report: dict, only_new: bool) -> None:
    print(f"{report['in_scope']} theorems in scope: {report['cited']} cited, "
          f"{report['uncited']} uncited ({report['uncited_with_note']} of them have an "
          f"informalized note, {report['uncited_untagged']} carry no docstring tag)")
    rows = [r for r in report["tags"] if not only_new or r["new"]]
    if rows:
        print("\nuncited theorems by docstring tag "
              "(`missing` = no reference document registered for the tag):")
        print(f"  {'tag':8s} {'uncited':>7s} {'new':>5s} {'noted':>5s}  status      documents / where")
        for r in rows:
            docs = ", ".join(r["documents"]) if r["documents"] else "-"
            print(f"  {r['tag']:8s} {r['uncited']:7d} {r['new']:5d} {r['with_note']:5d}  "
                  f"{r['status']:10s}  {docs}")
            if r["title"]:
                print(f"           {r['title'][:100]}")
            if r["locations"]:
                print(f"           cited at: {', '.join(r['locations'])}")
    missing = [r for r in rows if r["status"] == "missing"]
    if missing:
        print("\nTo give these theorems citations instead of informalized proof notes, attach "
              "the text they were formalized from: copy its PDF under "
              f"{REFERENCES.relative_to(BASE)}/ and rerun the pipeline, or name it with its tag:")
        for r in missing:
            print(f"    python3 scripts/dataset_pipeline.py --source {r['tag']}=<path to the "
                  f"{r['tag']} text{' (' + r['locations'][0].split(' (')[0] + ' ...)' if r['locations'] else ''}>")
    if report["documents_unregistered"]:
        print(f"\n{len(report['documents_unregistered'])} ingested document(s) are registered "
              f"under no tag (python3 scripts/reference_coverage.py --register TAG=<doc>): "
              + ", ".join(report["documents_unregistered"][:8])
              + (" ..." if len(report["documents_unregistered"]) > 8 else ""))


def rebuild_registry(index: dict, sources: Sources, registry: dict) -> int:
    """tag -> document from declarations that carry both a docstring tag and a citation."""
    citations = bpn.blueprint_citations()
    votes: dict[tuple[str, str], int] = collections.Counter()
    titles: dict[str, str] = {}
    for name, cite in citations.items():
        docs = {row["document"] for group in ("proof_sources", "statement_sources")
                for row in cite.get(group, [])}
        if not docs or name not in index:
            continue
        tags = {t for t, _ in sources.tags(name)}
        # A declaration citing two sources cannot say which document covers which
        # tag; only single-tag, single-document declarations are evidence.
        if len(tags) != 1 or len(docs) != 1:
            continue
        tag, doc = next(iter(tags)), next(iter(docs))
        titles.setdefault(tag, sources.titles(index[name]["module"]).get(tag, ""))
        votes[(tag, doc)] += 1
    added = 0
    for (tag, doc), n in sorted(votes.items()):
        # One stray citation is not evidence; three or more declarations agreeing is.
        if n >= 3 and register(registry, tag, doc, titles.get(tag)):
            added += 1
            print(f"  {tag:8s} -> {doc}  ({n} declarations)")
    return added


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--dataset", type=Path, default=DATASET)
    ap.add_argument("--previous", type=Path, help="earlier dataset; its records are not `new`")
    ap.add_argument("--only", nargs="+", metavar="NAME")
    ap.add_argument("--modules", nargs="+", metavar="MODULE")
    ap.add_argument("--only-new", action="store_true", help="report only tags with new theorems")
    ap.add_argument("--attached", nargs="*", default=[], metavar="TAG",
                    help="tags whose text is attached in this run (--source TAG=...)")
    ap.add_argument("--register", action="append", default=[], metavar="TAG=DOC",
                    help="record that document DOC (stem under references/) covers TAG")
    ap.add_argument("--rebuild-registry", action="store_true",
                    help="derive tag -> document pairs from existing citations")
    ap.add_argument("--report", type=Path, help="write the JSON report here")
    ap.add_argument("--strict", action="store_true",
                    help="exit 1 when a new theorem's tag has no registered or attached document")
    args = ap.parse_args()

    if not bd.DEP_GRAPH.exists():
        print(f"ERROR: {bd.DEP_GRAPH} not found")
        return 1
    graph = json.load(open(bd.DEP_GRAPH))["modules"]
    index = bd.build_index(graph)
    sources = Sources(index)
    registry = load_registry()

    changed = False
    for item in args.register:
        if "=" not in item:
            print(f"ERROR: --register wants TAG=DOC, got {item!r}")
            return 1
        tag, doc = item.split("=", 1)
        stem = doc.strip()
        for suffix in (".raw.md", ".md", ".pdf"):
            if stem.endswith(suffix):
                stem = stem[: -len(suffix)]
        stem = Path(stem).name
        if stem not in ingested_documents():
            print(f"WARNING: no validated {stem}.md under {REFERENCES.relative_to(BASE)} (yet)")
        changed |= register(registry, tag.strip(), stem)
    if args.rebuild_registry:
        print("registry from existing citations:")
        changed |= bool(rebuild_registry(index, sources, registry))
    if changed:
        save_registry(registry)
        print(f"registry -> {REGISTRY.relative_to(BASE)} ({len(registry['tags'])} tags)")

    records = load_records(args.dataset)
    if not records:
        print(f"ERROR: no records in {args.dataset}")
        return 1
    if args.only:
        wanted = set(args.only)
        records = [r for r in records if r["id"] in wanted]
    if args.modules:
        records = [r for r in records if bd.module_matches(r.get("source_module", ""), args.modules)]
    previous_ids = {r["id"] for r in load_records(args.previous)} if args.previous else set()

    report = coverage(records, previous_ids, index, sources, registry, set(args.attached))
    print_report(report, args.only_new)
    if args.report:
        args.report.parent.mkdir(parents=True, exist_ok=True)
        args.report.write_text(json.dumps(report, indent=2, ensure_ascii=False), encoding="utf-8")
        print(f"\nreport -> {args.report}")
    blocking = [r for r in report["tags"] if r["new"] and r["status"] == "missing"]
    if args.strict and blocking:
        n = sum(r["new"] for r in blocking)
        print(f"\nSTRICT: {n} new theorem(s) cite {', '.join(r['tag'] for r in blocking)} and no "
              f"text is attached or registered for those tags.")
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
