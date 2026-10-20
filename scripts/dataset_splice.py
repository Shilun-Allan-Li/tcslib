"""
Splice regenerated records into an existing dataset, field by field.

`build_dataset.py --only NAME ...` regenerates a handful of records (for example after a
flattener fix), but a full rebuild also changes every other record whose source moved
since the last build.  When the intent is "repair these records and nothing else", this
script copies the chosen fields of each regenerated record over the matching record of
the shipped dataset and leaves everything else byte-identical.

By default only the statement-derived fields are spliced -- the ones `build_dataset.py`
computes from the Lean sources, the blueprint and the reference texts without a proof
build:

    formal_statement, upstream_defs, n_upstream_defs, definitions,
    informal_statement, informal_source, title, difficulty

Pass `--fields all` to replace every field the patch carries (a patch built with the
proof enabled then also refreshes `proof`, `proof_complete`, ...).

`--merge` is the incremental-build mode used by scripts/dataset_pipeline.py: the patch
is a complete build (every column) of some or all records, and
the result is the previous dataset with those records replaced or added.  Records of the
previous dataset that the build does not contain are

    kept      when the build was a selection (`--selected`: --only / --modules);
    carried   when their module is not in dep_graph.json (not built, so they could not
              be regenerated; reported -- pass --drop-unbuilt to drop them instead;
              dataset_check.py lists them as `stale-module`);
    skipped   when the graph still lists the declaration but the build left it out
              (the builder could not place it: stale graph, no blueprint entry) -- kept
              and reported, since the declaration exists;
    renamed   when the declaration no longer exists under the record's name but a BUILT
              module declares the same short name under another full name (a namespace
              or file rename): the old record is dropped and the new name reported --
              the build adds the record under its new name as soon as it has a blueprint
              entry, and the blueprint carries citations under the new name;
    moved     when the graph no longer lists the declaration under its old module but a
              Lean source file that is NOT built still declares it (it moved to a module
              nobody imports yet) -- kept and reported, like `carried`;
    dropped   when no built module and no source file declares it any more (deleted).

The merged dataset is sorted by id, the order build_dataset.py writes.

Usage:
    python3 scripts/dataset_splice.py PATCH.jsonl                   # patch dataset/ in place
    python3 scripts/dataset_splice.py PATCH.jsonl --dataset X.jsonl --out Y.jsonl
    python3 scripts/dataset_splice.py PATCH.jsonl --fields all --dry-run
    python3 scripts/dataset_splice.py BUILT.jsonl --merge                   # full build
    python3 scripts/dataset_splice.py BUILT.jsonl --merge --selected        # partial build
    python3 scripts/dataset_splice.py BUILT.jsonl --merge --report merge.json
"""

from __future__ import annotations

import argparse
import gzip
import json
import re
import shutil
import sys
from pathlib import Path

BASE = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(BASE))

from proofmatch.dataset_io import open_dataset, resolve_dataset  # noqa: E402

DEFAULT_DATASET = BASE / "dataset" / "tcslib_theorems.jsonl"
DEP_GRAPH = BASE / "dep_graph.json"

STATEMENT_FIELDS = (
    "formal_statement",
    "upstream_defs",
    "n_upstream_defs",
    "definitions",
    "informal_statement",
    "informal_source",
    "title",
    "difficulty",
)


def load_patch(path: Path) -> dict[str, dict]:
    out: dict[str, dict] = {}
    with open_dataset(path) as handle:
        for line in handle:
            if line.strip():
                record = json.loads(line)
                out[record["id"]] = record
    return out


def write_dataset(records: list[dict], out_path: Path) -> Path:
    """Write the .jsonl and refresh its .gz twin, as build_dataset.py does."""
    out_path.parent.mkdir(parents=True, exist_ok=True)
    tmp = out_path.with_suffix(out_path.suffix + ".tmp")
    with open(tmp, "w", encoding="utf-8") as handle:
        for record in records:
            handle.write(json.dumps(record, ensure_ascii=False) + "\n")
    tmp.replace(out_path)
    gz_path = out_path.with_suffix(out_path.suffix + ".gz")
    gz_tmp = gz_path.with_suffix(gz_path.suffix + ".tmp")
    with open(out_path, "rb") as src, gzip.open(gz_tmp, "wb", compresslevel=9) as dst:
        shutil.copyfileobj(src, dst)
    gz_tmp.replace(gz_path)
    return gz_path


PRIVATE_RE = re.compile(r"^_private\..*?\.\d+\.")   # build_dataset.normalize_name


def graph_declarations(path: Path) -> dict[str, set[str]]:
    """module -> declaration names (normalized as build_dataset does), from dep_graph.json."""
    if not path.exists():
        return {}
    try:
        modules = json.loads(path.read_text(encoding="utf-8"))["modules"]
    except (ValueError, KeyError):
        return {}
    return {m: {PRIVATE_RE.sub("", n) for n in md.get("declarations", {})}
            for m, md in modules.items()}


DECL_RE = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+|"
                     r"nonrec\s+|scoped\s+|unsafe\s+|partial\s+)*"
                     r"(?:theorem|lemma|def|abbrev|structure|inductive|class|instance|opaque|axiom)"
                     r"\s+([^\s:({\[⦃]+)", re.M)


def source_short_names(root: Path) -> dict[str, set[str]]:
    """Short name -> modules whose Lean source declares it, for every file on disk (built
    or not)."""
    names: dict[str, set[str]] = {}
    for path in root.rglob("*.lean"):
        try:
            text = path.read_text(encoding="utf-8", errors="ignore")
        except OSError:
            continue
        module = "TCSlib." + str(path.relative_to(root).with_suffix("")).replace("/", ".")
        for m in DECL_RE.finditer(text):
            names.setdefault(m.group(1).rsplit(".", 1)[-1], set()).add(module)
    return names


def module_source_exists(module: str) -> bool:
    rel = module[len("TCSlib."):] if module.startswith("TCSlib.") else module
    return (BASE / "TCSlib" / (rel.replace(".", "/") + ".lean")).exists()


def merge(previous: list[dict], built: dict[str, dict], graph: dict[str, set[str]], *,
          selected: bool, drop_unbuilt: bool,
          declared: dict[str, set[str]] | None = None) -> tuple[list[dict], dict]:
    """The previous dataset with the built records replaced/added; see the module doc.

    `declared` maps short names to the modules on disk declaring them (None when the
    build was a selection).  `summary["renamed"]` holds `[old_id, new_id]` pairs."""
    summary = {"replaced": [], "added": [], "kept": [], "carried": [], "skipped": [],
               "renamed": [], "moved": [], "dropped": []}
    by_short: dict[str, set[str]] = {}
    for names in graph.values():
        for full in names:
            by_short.setdefault(full.rsplit(".", 1)[-1], set()).add(full)
    out: dict[str, dict] = {}
    for record in previous:
        rid = record["id"]
        if rid in built:
            summary["replaced"].append(rid)
            continue
        module = record.get("source_module", "")
        short = rid.rsplit(".", 1)[-1]
        successors = sorted(by_short.get(short, set()) - {rid})
        unbuilt_declarers = sorted(m for m in (declared or {}).get(short, set()) if m not in graph)
        if selected:
            summary["kept"].append(rid)
            out[rid] = record
        elif module in graph:
            if rid in graph[module]:
                summary["skipped"].append(rid)
                out[rid] = record
            elif successors:
                summary["renamed"].append([rid, successors[0]])
            elif unbuilt_declarers and not drop_unbuilt:
                summary["moved"].append(rid)
                out[rid] = record
            else:
                summary["dropped"].append(rid)
        elif not graph or drop_unbuilt:
            summary["dropped"].append(rid)
        elif not module_source_exists(module):
            # The module file is gone: the record survives only through a declaration
            # of the same name somewhere else.
            if successors:
                summary["renamed"].append([rid, successors[0]])
            elif unbuilt_declarers:
                summary["moved"].append(rid)
                out[rid] = record
            else:
                summary["dropped"].append(rid)
        else:
            summary["carried"].append(rid)
            out[rid] = record
    previous_ids = {r["id"] for r in previous}
    for rid, record in built.items():
        if rid not in previous_ids:
            summary["added"].append(rid)
        out[rid] = record
    records = [out[rid] for rid in sorted(out)]
    return records, summary


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("patch", type=Path, help="JSONL of regenerated records (build_dataset.py --only)")
    ap.add_argument("--merge", action="store_true",
                    help="incremental build: replace/add every patched record whole, keep or "
                         "drop the others as described above")
    ap.add_argument("--selected", action="store_true",
                    help="--merge: the build was a selection (--only/--modules); keep every "
                         "record it does not contain")
    ap.add_argument("--drop-unbuilt", action="store_true",
                    help="--merge: drop records whose module is not in dep_graph.json "
                         "instead of carrying them over")
    ap.add_argument("--graph", type=Path, default=DEP_GRAPH, help="dep_graph.json to consult")
    ap.add_argument("--report", type=Path, help="--merge: write the id lists here (JSON)")
    ap.add_argument("--dataset", type=Path, default=DEFAULT_DATASET,
                    help="dataset to patch (.jsonl; its .gz is used when the .jsonl is absent)")
    ap.add_argument("--out", type=Path, default=None,
                    help="where to write (default: the dataset itself)")
    ap.add_argument("--fields", default="statement",
                    help="'statement' (default), 'all', or a comma-separated field list")
    ap.add_argument("--dry-run", action="store_true", help="report, write nothing")
    args = ap.parse_args()

    if args.fields == "statement":
        fields = STATEMENT_FIELDS
    elif args.fields == "all":
        fields = None
    else:
        fields = tuple(f.strip() for f in args.fields.split(",") if f.strip())

    patch = load_patch(args.patch)
    if not patch and not args.merge:
        print(f"ERROR: no records in {args.patch}")
        return 1

    source = resolve_dataset(args.dataset)
    if args.merge:
        previous: list[dict] = []
        if source.exists():
            with open_dataset(args.dataset) as handle:
                previous = [json.loads(l) for l in handle if l.strip()]
        else:
            print(f"no previous dataset at {args.dataset}; the build is the dataset")
        graph = graph_declarations(args.graph)
        if not graph and previous and not args.selected:
            print(f"WARNING: {args.graph} unreadable; every previous record the build lacks "
                  "is dropped")
        declared = None if args.selected else source_short_names(BASE / "TCSlib")
        records, summary = merge(previous, patch, graph, selected=args.selected,
                                 drop_unbuilt=args.drop_unbuilt, declared=declared)
        print(f"merge: {len(previous)} previous + {len(patch)} built -> {len(records)} records")
        for key in ("replaced", "added", "kept", "carried", "skipped", "renamed", "moved", "dropped"):
            print(f"  {len(summary[key]):5d}  {key}")
        for old, new in summary["renamed"][:10]:
            print(f"  dropped (renamed; the build carries it as {new}): {old}")
        if len(summary["renamed"]) > 10:
            print(f"  ... and {len(summary['renamed']) - 10} more renamed")
        for rid in summary["skipped"][:10]:
            print(f"  kept, not regenerated (still declared, but the builder left it out): {rid}")
        if len(summary["skipped"]) > 10:
            print(f"  ... and {len(summary['skipped']) - 10} more skipped")
        for rid in summary["moved"][:10]:
            print(f"  kept, not regenerated (moved to a module that is not built): {rid}")
        if len(summary["moved"]) > 10:
            print(f"  ... and {len(summary['moved']) - 10} more moved")
        by_module: dict[str, int] = {}
        for rid in summary["carried"]:
            module = next(r.get("source_module", "") for r in previous if r["id"] == rid)
            by_module[module] = by_module.get(module, 0) + 1
        if by_module:
            print("  carried over unchanged (module not in dep_graph.json; not regenerated):")
            for module, count in sorted(by_module.items(), key=lambda kv: -kv[1])[:15]:
                print(f"    {count:5d}  {module}")
            if len(by_module) > 15:
                print(f"    ... and {len(by_module) - 15} more modules")
        for rid in summary["dropped"][:15]:
            print(f"  dropped (declaration no longer built under this name): {rid}")
        if len(summary["dropped"]) > 15:
            print(f"  ... and {len(summary['dropped']) - 15} more dropped")
        if args.report:
            args.report.parent.mkdir(parents=True, exist_ok=True)
            args.report.write_text(json.dumps({k: sorted(v) for k, v in summary.items()},
                                              indent=2), encoding="utf-8")
            print(f"  report -> {args.report}")
        if args.dry_run:
            return 0
        out_path = (args.out or args.dataset).resolve()
        gz_path = write_dataset(records, out_path)
        print(f"Wrote {out_path.relative_to(BASE) if out_path.is_relative_to(BASE) else out_path}")
        print(f"Refreshed gzip copy -> {gz_path.name}")
        return 0

    if not source.exists():
        print(f"ERROR: {args.dataset} (or its .gz) not found")
        return 1

    records: list[dict] = []
    touched: dict[str, list[str]] = {}
    with open_dataset(args.dataset) as handle:
        for line in handle:
            if not line.strip():
                continue
            record = json.loads(line)
            new = patch.get(record["id"])
            if new is not None:
                changed = []
                for key in (fields if fields is not None else list(new)):
                    if key in new and record.get(key) != new[key]:
                        record[key] = new[key]
                        changed.append(key)
                if changed:
                    touched[record["id"]] = changed
            records.append(record)

    unmatched = sorted(set(patch) - {r["id"] for r in records})
    print(f"{len(records)} records read from {source.name}; patch carries {len(patch)}; "
          f"{len(touched)} changed; {len(unmatched)} patch ids absent from the dataset")
    for name in unmatched:
        print(f"  absent: {name}")
    by_field: dict[str, int] = {}
    for changed in touched.values():
        for key in changed:
            by_field[key] = by_field.get(key, 0) + 1
    for key, count in sorted(by_field.items(), key=lambda kv: -kv[1]):
        print(f"  {count:5d}  {key}")

    if args.dry_run:
        return 0
    out_path = (args.out or args.dataset).resolve()
    gz_path = write_dataset(records, out_path)
    print(f"Wrote {out_path.relative_to(BASE) if out_path.is_relative_to(BASE) else out_path}")
    print(f"Refreshed gzip copy -> {gz_path.name}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
