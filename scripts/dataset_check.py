r"""Structural checks on a built dataset: is every column there, and is it usable?

dataset_hygiene.py and statement_quality.py judge the *prose*.  This script checks
the *shape* of the shipped file -- the things a consumer trips over before reading
a single statement:

HARD (exit 1 with --strict)
    schema          every record carries every column, with the right JSON type
    duplicate-id    two records share an id
    formal-leak     a `formal_statement` carries a line that is not Lean: a docstring
                    line scraped as `open` / `variable` / `namespace` / `end` /
                    `set_option` (the class fixed in build_dataset.parse_file_context)
    formal-shape    `formal_statement` does not start with `import` or does not end in
                    `:= sorry`
    proof-flag      `proof_complete` disagrees with whether `proof` contains `sorry`
    stub-prose      the informal statement is a blueprint_stub.py placeholder
    informal-source `informal_source` is not `citation` / `lean`, or `informal_statement`
                    is empty
    row-loss        with --previous: a record of the previous dataset is gone (its
                    module dropped out of dep_graph.json, usually because the file is
                    no longer imported from TCSlib.lean)
    lean-error      with --lean-check N: a sampled `formal_statement` does not compile

ADVISORY (always reported)
    formal-leak-sorried  the same leak on a record whose proof is incomplete (its module
                    is often absent from dep_graph.json, so it cannot be regenerated)
    unrated         complete proof with null `difficulty`
    no-account      a `lean` record has no informalized proof account appended (no
                    citation and no note under references/informalized/)
    stale-module    the record's module is not in dep_graph.json: the row was carried over
                    from the previous dataset by `dataset_splice.py --merge` because its
                    module is not built (not imported from TCSlib.lean), so it was not
                    regenerated and may lag behind the Lean source
    coverage        `informal_source` values by area

Usage:
    python3 scripts/dataset_check.py                         # dataset/tcslib_theorems.jsonl(.gz)
    python3 scripts/dataset_check.py --strict --previous OLD.jsonl.gz
    python3 scripts/dataset_check.py --lean-check 20 --seed 1 # compile 20 sampled statements
    python3 scripts/dataset_check.py --report dataset/.pipeline/check.json
"""

from __future__ import annotations

import argparse
import collections
import json
import random
import subprocess
import sys
import tempfile
from pathlib import Path

BASE = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(BASE))

from proofmatch.dataset_io import open_dataset, resolve_dataset  # noqa: E402

DEFAULT_DATASET = BASE / "dataset" / "tcslib_theorems.jsonl"
LEAN_CHECK = BASE / "scripts" / "lean_check.sh"
DEP_GRAPH = BASE / "dep_graph.json"

#: Column -> accepted JSON types (scripts/informal_sources.py owns the informal pair).
SCHEMA: dict[str, tuple[type, ...]] = {
    "id": (str,),
    "informal_statement": (str,),
    "informal_source": (str,),
    "formal_statement": (str,),
    "lean_name": (str,),
    "title": (str,),
    "definitions": (list,),
    "source_module": (str,),
    "kind": (str,),
    "upstream_defs": (list,),
    "n_upstream_defs": (int,),
    "difficulty": (int, type(None)),
    "proof": (str,),
    "proof_upstream_decls": (list,),
    "n_proof_upstream_decls": (int,),
    "proof_unresolved_deps": (list,),
    "proof_complete": (bool,),
}

HARD = {"schema", "duplicate-id", "formal-leak", "formal-shape", "proof-flag",
        "stub-prose", "informal-source", "row-loss", "lean-error"}
INFORMAL_SOURCES = {"citation", "lean"}
PROOF_SEP = "\n\nProof: "   # scripts/informal_sources.py: statement | proof account

import re  # noqa: E402

OK_OPEN = re.compile(r"^open( scoped)?( [A-Za-z_][\w.«»'₀-₉]*(\s*\([^)]*\))?)+( in)?\s*$")
OK_VAR = re.compile(r"^variable\s*[({\[⦃]")
OK_NS = re.compile(r"^namespace\s+[A-Za-z_][\w.'«»]*\s*$")
OK_END = re.compile(r"^end(\s+[A-Za-z_][\w.'«»]*)?\s*$")
OK_SETOPT = re.compile(r"^set_option\s+[\w.]+\s+\S+(\s+in)?\s*$")
STUB_RE = re.compile(r"Statement pending regeneration|dataset-pipeline: stub")


def leaked_line(line: str) -> bool:
    if line.startswith("open ") and not OK_OPEN.match(line):
        return True
    if line.startswith("variable") and not OK_VAR.match(line):
        return True
    if line.startswith("namespace") and not OK_NS.match(line):
        return True
    if re.match(r"^end\b", line) and not OK_END.match(line):
        return True
    if line.startswith("set_option") and not OK_SETOPT.match(line):
        return True
    return False


def area_of(record: dict) -> str:
    parts = record.get("source_module", "").split(".")
    return parts[1] if len(parts) > 1 else parts[0]


def load(path: Path) -> list[dict]:
    out = []
    with open_dataset(path) as handle:
        for line in handle:
            if line.strip():
                out.append(json.loads(line))
    return out


def lean_check_sample(records: list[dict], n: int, seed: int) -> list[tuple[str, int, str]]:
    """Compile `n` sampled formal statements; (id, error_count, first_error) per failure."""
    rng = random.Random(seed)
    sample = rng.sample(records, min(n, len(records)))
    failures = []
    with tempfile.TemporaryDirectory(prefix="dataset-check-") as tmp:
        for record in sample:
            path = Path(tmp) / (record["id"].replace(".", "_") + ".lean")
            path.write_text(record["formal_statement"], encoding="utf-8")
            proc = subprocess.run(["zsh", str(LEAN_CHECK), str(path)],
                                  capture_output=True, text=True)
            errors = [l for l in proc.stdout.splitlines() if "error:" in l]
            if proc.returncode != 0 or errors:
                failures.append((record["id"], len(errors),
                                 errors[0] if errors else proc.stdout[-300:]))
            print(f"  lean {'FAIL' if errors or proc.returncode else 'ok  '} {record['id']}")
    return failures


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--dataset", type=Path, default=DEFAULT_DATASET)
    ap.add_argument("--previous", type=Path, help="earlier dataset to compare row sets with")
    ap.add_argument("--allow-row-loss", action="store_true",
                    help="demote row-loss to advisory")
    ap.add_argument("--lean-check", type=int, default=0, metavar="N",
                    help="compile N randomly sampled formal statements with scripts/lean_check.sh")
    ap.add_argument("--seed", type=int, default=0)
    ap.add_argument("--strict", action="store_true", help="exit 1 on any HARD finding")
    ap.add_argument("--report", type=Path, help="write a JSON summary here")
    ap.add_argument("--show", type=int, default=10, help="examples to print per finding")
    args = ap.parse_args()

    source = resolve_dataset(args.dataset)
    if not source.exists():
        print(f"ERROR: {args.dataset} (or its .gz) not found")
        return 1
    records = load(args.dataset)
    findings: dict[str, list[str]] = collections.defaultdict(list)

    # schema / ids
    seen: set[str] = set()
    for record in records:
        rid = record.get("id", "<no id>")
        for key, types in SCHEMA.items():
            if key not in record:
                findings["schema"].append(f"{rid}: missing {key}")
            elif not isinstance(record[key], types):
                findings["schema"].append(f"{rid}: {key} is {type(record[key]).__name__}")
        extra = set(record) - set(SCHEMA)
        if extra:
            findings["schema"].append(f"{rid}: unexpected columns {sorted(extra)}")
        if rid in seen:
            findings["duplicate-id"].append(rid)
        seen.add(rid)

    # formal statements
    for record in records:
        rid = record["id"]
        fs = record.get("formal_statement", "")
        lines = fs.splitlines()
        leaks = [l for l in lines if leaked_line(l)]
        if leaks:
            # A sorried record's module may be absent from dep_graph.json (unbuilt), so
            # its statement cannot be regenerated; report it, but do not fail on it.
            key = "formal-leak" if record.get("proof_complete") else "formal-leak-sorried"
            findings[key].append(f"{rid}: {leaks[0][:70]}")
        # The target is the last declaration; it is followed only by the `end NS`
        # lines of its namespace wrapper.
        tail = next((l for l in reversed(lines)
                     if l.strip() and not re.match(r"^end\b", l)), "")
        if not fs.startswith("import") or not tail.rstrip().endswith(":= sorry"):
            findings["formal-shape"].append(rid)
        proof = record.get("proof", "")
        if isinstance(proof, str) and record.get("proof_complete") != ("sorry" not in proof):
            findings["proof-flag"].append(rid)
        informal = record.get("informal_statement", "")
        if STUB_RE.search(informal):
            findings["stub-prose"].append(rid)
        origin = record.get("informal_source")
        if origin not in INFORMAL_SOURCES or not informal.strip():
            findings["informal-source"].append(f"{rid}: {origin!r}, {len(informal)} chars")
        if record.get("proof_complete") and record.get("difficulty") is None:
            findings["unrated"].append(rid)
        if origin == "lean" and PROOF_SEP not in informal:
            findings["no-account"].append(rid)

    # carried-over rows (module not built)
    if DEP_GRAPH.exists():
        try:
            graph_modules = set(json.loads(DEP_GRAPH.read_text(encoding="utf-8"))["modules"])
        except (ValueError, KeyError):
            graph_modules = set()
        if graph_modules:
            for record in records:
                if record.get("source_module") not in graph_modules:
                    findings["stale-module"].append(f"{record['id']} ({record.get('source_module')})")

    # row loss
    lost_by_module: dict[str, int] = {}
    if args.previous:
        previous = load(args.previous)
        now = {r["id"] for r in records}
        for record in previous:
            if record["id"] not in now:
                key = "row-loss" if not args.allow_row_loss else "row-loss-allowed"
                findings[key].append(record["id"])
                lost_by_module[record["source_module"]] = \
                    lost_by_module.get(record["source_module"], 0) + 1

    # lean sample
    if args.lean_check:
        print(f"compiling {args.lean_check} sampled formal statements ...")
        complete = [r for r in records if not any(leaked_line(l) for l in r["formal_statement"].splitlines())]
        for rid, nerr, first in lean_check_sample(complete, args.lean_check, args.seed):
            findings["lean-error"].append(f"{rid}: {nerr} error(s): {first[:120]}")

    # coverage
    by_area_total = collections.Counter(area_of(r) for r in records)
    by_area_cited = collections.Counter(
        area_of(r) for r in records if r.get("informal_source") == "citation")
    by_area_incomplete = collections.Counter(area_of(r) for r in records if not r.get("proof_complete"))
    sources = collections.Counter(r.get("informal_source") for r in records)

    print(f"{len(records)} records from {source.name}")
    print(f"columns: {len(SCHEMA)} expected; informal_source: {dict(sources)}")
    print("\narea                      rows  incomplete  cited")
    for area, total in by_area_total.most_common():
        print(f"  {area:24s} {total:5d}  {by_area_incomplete[area]:9d}  {by_area_cited[area]:5d}")
    print("\nfindings:")
    hard_total = 0
    for key in sorted(findings, key=lambda k: (k not in HARD, k)):
        items = findings[key]
        tag = "HARD" if key in HARD else "advisory"
        print(f"  {len(items):5d}  {key} ({tag})")
        for item in items[: args.show]:
            print(f"           {item}")
        if len(items) > args.show:
            print(f"           ... and {len(items) - args.show} more")
        if key in HARD:
            hard_total += len(items)
    if lost_by_module:
        print("\nrows lost by module:")
        for module, count in sorted(lost_by_module.items(), key=lambda kv: -kv[1]):
            print(f"  {count:5d}  {module}")
    if not findings:
        print("  none")

    if args.report:
        args.report.parent.mkdir(parents=True, exist_ok=True)
        args.report.write_text(json.dumps({
            "dataset": str(source),
            "records": len(records),
            "by_area": {a: {"rows": by_area_total[a], "incomplete": by_area_incomplete[a],
                            "cited": by_area_cited[a]} for a in by_area_total},
            "informal_source": {str(k): v for k, v in sources.items()},
            "findings": {k: len(v) for k, v in findings.items()},
            "hard_failures": hard_total,
            "examples": {k: v[:50] for k, v in findings.items()},
        }, indent=2), encoding="utf-8")
        print(f"\nreport -> {args.report}")

    print(f"\nhard failures: {hard_total}")
    return 1 if (args.strict and hard_total) else 0


if __name__ == "__main__":
    raise SystemExit(main())
