#!/usr/bin/env python3
"""
Viewer for tcslib theorem datasets.

Choosing which dataset to read:
  (default)                             # tcslib_theorems.jsonl
  python read_json.py --graph ...       # graphtheory_theorems.jsonl
  python read_json.py --file <path> ... # any .jsonl with the same schema
  python read_json.py --datasets        # list the dataset files available here

  The selector goes before the command, e.g.
      python read_json.py --graph --list
      python read_json.py --graph --id SimpleGraph.whitney_inequalities
      python read_json.py --file ../other.jsonl --search connectivity

Main dataset (tcslib_theorems.jsonl):
  python read_json.py                   # summary + module breakdown
  python read_json.py --list            # list all IDs
  python read_json.py --module <name>   # entries for one module (substring match)
  python read_json.py --id <id>         # show one entry in full
  python read_json.py --search <term>   # search IDs and titles
  python read_json.py --sample <n>      # show n random entries

  Tip: scripts/view_dataset.py is a full TUI browser for this file.
  python3 scripts/view_dataset.py --filter <term>
  python3 scripts/view_dataset.py --print <n>

Graph curation file (graph_curation.jsonl):
  python read_json.py --curate                        # summary by status + topic
  python read_json.py --curate --list                 # all entries: status / topic / id
  python read_json.py --curate --status <status>      # filter by status value
  python read_json.py --curate --id <id>              # full detail for one entry

  status values: already_in_mathlib | bridge_lemma | new_project_lemma | unclear
"""

import json
import random
import sys
import textwrap
from collections import Counter
from pathlib import Path

HERE = Path(__file__).parent
DATASET = HERE / "tcslib_theorems.jsonl"          # default; overridden by --graph/--file
GRAPH_DATASET = HERE / "graphtheory_theorems.jsonl"
CURATION = HERE / "graph_curation.jsonl"
W = 90  # display width

STATUS_ORDER = ["new_project_lemma", "bridge_lemma", "already_in_mathlib", "unclear"]


def load(path=None):
    path = Path(path) if path else DATASET
    if not path.exists():
        print(f"Dataset not found: {path}")
        print("\nAvailable in this directory:")
        for p in list_datasets():
            print(f"  {p.name}")
        sys.exit(1)
    with open(path) as f:
        return [json.loads(line) for line in f if line.strip()]


def list_datasets():
    """Every .jsonl here that looks like a theorem dataset (has an `id` field)."""
    out = []
    for p in sorted(HERE.glob("*.jsonl")):
        try:
            with open(p) as f:
                first = f.readline()
            if first.strip() and "id" in json.loads(first):
                out.append(p)
        except (json.JSONDecodeError, OSError):
            continue
    return out


def cmd_datasets():
    rows = list_datasets()
    if not rows:
        print(f"No .jsonl datasets found in {HERE}")
        return
    hr("═")
    print(f"  Datasets in {HERE}")
    hr()
    for p in rows:
        with open(p) as f:
            entries = [json.loads(line) for line in f if line.strip()]
        mods = {e.get("source_module", "?") for e in entries}
        flag = ""
        if p == DATASET:
            flag = "  (default)"
        elif p == GRAPH_DATASET:
            flag = "  (--graph)"
        print(f"  {p.name:34s} {len(entries):5d} entries  {len(mods):3d} modules{flag}")
    hr("═")


def load_curation():
    if not CURATION.exists():
        print(f"Curation file not found: {CURATION}")
        sys.exit(1)
    with open(CURATION) as f:
        return [json.loads(line) for line in f if line.strip()]


# ── formatting helpers ────────────────────────────────────────────────────────

def hr(char="─"):
    print(char * W)


def wrap(text, indent=2):
    prefix = " " * indent
    for para in text.split("\n"):
        if para.strip() == "":
            print()
        else:
            for line in textwrap.wrap(para, W - indent, initial_indent=prefix,
                                      subsequent_indent=prefix):
                print(line)


def print_entry(e, verbose=True):
    hr("═")
    print(f"  ID      : {e['id']}")
    print(f"  Module  : {e['source_module']}")
    print(f"  Kind    : {e['kind']}")
    print(f"  Title   : {e.get('title', '—')}")
    hr()
    if verbose:
        print("  INFORMAL STATEMENT")
        wrap(e.get("informal_statement", "").strip())
        print()
        print("  FORMAL STATEMENT (Lean 4)")
        wrap(e.get("formal_statement", "").strip())
        if e.get("upstream_defs"):
            print()
            print(f"  UPSTREAM DEFS ({e['n_upstream_defs']})")
            for d in e["upstream_defs"]:
                print(f"    • {d}")


def print_curation_entry(e, verbose=True):
    hr("═")
    print(f"  ID       : {e['id']}")
    print(f"  Title    : {e.get('title', '—')}")
    print(f"  Status   : {e.get('status', '—')}")
    print(f"  Difficulty: {e.get('difficulty', '—')}")
    topics = ", ".join(e.get("graph_topic") or []) or "—"
    print(f"  Topics   : {topics}")
    hr()
    if verbose:
        print("  INFORMAL STATEMENT")
        wrap(e.get("informal_statement", "").strip())
        print()
        print("  FORMAL STATEMENT (draft Lean)")
        wrap(e.get("formal_statement", "").strip())
        concepts = e.get("mathlib_concepts") or []
        lemmas = e.get("existing_mathlib_lemmas") or []
        if concepts:
            print()
            print("  MATHLIB CONCEPTS")
            for c in concepts:
                print(f"    • {c}")
        if lemmas:
            print()
            print("  EXISTING MATHLIB LEMMAS")
            for lm in lemmas:
                print(f"    • {lm}")
        notes = (e.get("notes") or "").strip()
        if notes:
            print()
            print("  NOTES")
            wrap(notes)


# ── main dataset commands ─────────────────────────────────────────────────────

def cmd_summary(entries, name="tcslib_theorems"):
    hr("═")
    print(f"  {name}  —  {len(entries)} entries")
    hr()
    print("  Entries by source module:\n")
    counts = Counter(e["source_module"] for e in entries)
    for mod, n in counts.most_common():
        bar = "█" * (n // 2)
        print(f"  {n:4d}  {bar}  {mod}")
    hr()
    kinds = Counter(e["kind"] for e in entries)
    print("  Kinds: " + "  |  ".join(f"{k} ({v})" for k, v in kinds.most_common()))
    hr("═")


def cmd_list(entries):
    for e in entries:
        print(f"  {e['kind']:8s}  {e['id']}")
    print(f"\n  {len(entries)} entries total")


def cmd_module(entries, pattern):
    pattern = pattern.lower()
    matched = [e for e in entries if pattern in e["source_module"].lower()]
    if not matched:
        print(f"No entries found for module pattern '{pattern}'")
        return
    print(f"  {len(matched)} entries matching '{pattern}'\n")
    for e in matched:
        print_entry(e, verbose=False)
    print()
    answer = input("Show full detail for one entry? Enter ID (or blank to skip): ").strip()
    if answer:
        hits = [e for e in matched if e["id"] == answer]
        if hits:
            print_entry(hits[0])
        else:
            print("ID not found.")


def cmd_id(entries, eid):
    hits = [e for e in entries if e["id"] == eid]
    if not hits:
        print(f"No entry with id '{eid}'")
    else:
        print_entry(hits[0])


def cmd_search(entries, term):
    term = term.lower()
    hits = [e for e in entries
            if term in e["id"].lower()
            or term in (e.get("title") or "").lower()
            or term in (e.get("statement_informal") or "").lower()]
    if not hits:
        print(f"No results for '{term}'")
        return
    print(f"  {len(hits)} results for '{term}'\n")
    for e in hits:
        print_entry(e, verbose=False)


def cmd_sample(entries, n):
    for e in random.sample(entries, min(n, len(entries))):
        print_entry(e)


# ── curation commands ─────────────────────────────────────────────────────────

def cmd_curate_summary(entries):
    hr("═")
    print(f"  graph_curation  —  {len(entries)} entries")
    hr()
    print("  By status:\n")
    status_counts = Counter(e.get("status", "unclear") for e in entries)
    for s in STATUS_ORDER:
        n = status_counts.get(s, 0)
        bar = "█" * n
        print(f"  {n:4d}  {bar}  {s}")
    hr()
    print("  By graph topic:\n")
    topic_counts: Counter = Counter()
    for e in entries:
        for t in (e.get("graph_topic") or []):
            topic_counts[t] += 1
    for topic, n in topic_counts.most_common():
        print(f"  {n:4d}  {'█' * n}  {topic}")
    hr()
    diff_counts = Counter(e.get("difficulty", "—") for e in entries)
    print("  Difficulty: " + "  |  ".join(f"{k} ({v})" for k, v in diff_counts.most_common()))
    hr("═")


def cmd_curate_list(entries):
    col = max((len(e.get("status") or "") for e in entries), default=10)
    for e in entries:
        status = (e.get("status") or "unclear").ljust(col)
        topics = ",".join(e.get("graph_topic") or []) or "—"
        print(f"  {status}  {topics:<30s}  {e['id']}")
    print(f"\n  {len(entries)} entries total")


def cmd_curate_status(entries, status_val):
    matched = [e for e in entries if e.get("status") == status_val]
    if not matched:
        print(f"No entries with status '{status_val}'")
        print(f"  Valid values: {' | '.join(STATUS_ORDER)}")
        return
    print(f"  {len(matched)} entries with status '{status_val}'\n")
    for e in matched:
        print_curation_entry(e, verbose=False)


def cmd_curate_id(entries, eid):
    hits = [e for e in entries if e["id"] == eid]
    if not hits:
        print(f"No curation entry with id '{eid}'")
    else:
        print_curation_entry(hits[0])


# ── main ──────────────────────────────────────────────────────────────────────

def parse_selector(args):
    """Strip a leading dataset selector; return (path_or_None, remaining_args).

    Accepted anywhere before the command so `--graph --list` and `--list --graph`
    both work: the selector is not a command, so order should not matter.
    """
    path = None
    rest = []
    i = 0
    while i < len(args):
        a = args[i]
        if a == "--graph":
            path = GRAPH_DATASET
        elif a == "--file":
            if i + 1 >= len(args):
                print("--file needs a path")
                sys.exit(1)
            path = Path(args[i + 1])
            i += 1
        else:
            rest.append(a)
        i += 1
    return path, rest


def main():
    args = sys.argv[1:]

    if args and args[0] == "--datasets":
        cmd_datasets()
        return

    if args and args[0] == "--curate":
        rest = args[1:]
        entries = load_curation()
        if not rest:
            cmd_curate_summary(entries)
        elif rest[0] == "--list":
            cmd_curate_list(entries)
        elif rest[0] == "--status" and len(rest) >= 2:
            cmd_curate_status(entries, rest[1])
        elif rest[0] == "--id" and len(rest) >= 2:
            cmd_curate_id(entries, rest[1])
        else:
            print(__doc__)
        return

    path, args = parse_selector(args)
    entries = load(path)
    if not args:
        cmd_summary(entries, (Path(path) if path else DATASET).stem)
    elif args[0] == "--list":
        cmd_list(entries)
    elif args[0] == "--module" and len(args) >= 2:
        cmd_module(entries, " ".join(args[1:]))
    elif args[0] == "--id" and len(args) >= 2:
        cmd_id(entries, args[1])
    elif args[0] == "--search" and len(args) >= 2:
        cmd_search(entries, " ".join(args[1:]))
    elif args[0] == "--sample" and len(args) >= 2:
        cmd_sample(entries, int(args[1]))
    else:
        print(__doc__)


if __name__ == "__main__":
    main()
