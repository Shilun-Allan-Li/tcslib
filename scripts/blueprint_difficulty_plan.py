"""
Plan the \\difficulty backfill sweep deterministically from dep_graph.json + the blueprint.

Companion to blueprint_enumerate.py, but for a different gap: blueprint_enumerate finds
declarations with NO blueprint entry yet; this finds blueprint entries that already exist
(theorem/lemma/sublemma/proposition/corollary environments with \\lean + \\leanok) but have
no \\difficulty rating yet. It does NOT write any prose or rating — it only decides *what
needs rating* and hands the exact proof text along, so a rating subagent never has to go
hunting through Lean source for line ranges.

For every chapter .tex file with at least one unrated entry, this emits a work unit JSON
under blueprint/.work/difficulty/ listing, for each unrated theorem/lemma-kind binding:
the name, its full proof source (statement + tactic body, sliced from the Lean file), and
whether the proof is still a bare `sorry` (which should never be rated).

Usage:
    python3 scripts/blueprint_difficulty_plan.py                  # plan everything
    python3 scripts/blueprint_difficulty_plan.py --file <path>     # restrict to one chapter tex
    python3 scripts/blueprint_difficulty_plan.py --file a.tex --file b.tex
"""

import argparse
import json
import sys
from pathlib import Path

BASE = Path(__file__).resolve().parent.parent
CHAPTER_DIR = BASE / "blueprint" / "src" / "chapter"
WORK_DIR = BASE / "blueprint" / ".work" / "difficulty"
DEP_GRAPH = BASE / "dep_graph.json"

sys.path.insert(0, str(Path(__file__).resolve().parent))
import build_dataset as bd  # reuse build_index / parse_blueprint / split_signature

RATEABLE_ENVS = {"theorem", "lemma", "sublemma", "proposition", "corollary"}


def is_bare_sorry(rec) -> bool:
    full = "\n".join(rec["slice"])
    sig = bd.split_signature(full)
    body = full[len(sig):].replace(":=", "").strip()
    return body == "sorry"


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--file", action="append", default=None,
                     help="Restrict to this chapter .tex (relative to BASE or absolute). Repeatable.")
    args = ap.parse_args()

    if not DEP_GRAPH.exists():
        print(f"ERROR: {DEP_GRAPH} not found.")
        return 1

    graph = json.load(open(DEP_GRAPH))["modules"]
    print("Indexing declarations ...")
    index = bd.build_index(graph)

    print("Parsing blueprint ...")
    informal = bd.parse_blueprint()

    wanted_files = None
    if args.file:
        wanted_files = {(BASE / f).resolve() if not Path(f).is_absolute() else Path(f).resolve()
                         for f in args.file}

    WORK_DIR.mkdir(parents=True, exist_ok=True)
    units = []
    total_entries = 0
    total_sorry = 0

    for tex in sorted(CHAPTER_DIR.rglob("*.tex")):
        if wanted_files is not None and tex.resolve() not in wanted_files:
            continue
        lines = tex.read_text(encoding="utf-8", errors="ignore").splitlines()
        names_here = []
        for line in lines:
            m = bd.LEAN_BIND_RE.match(line)
            if not m:
                continue
            for part in m.group(1).split(","):
                part = part.strip()
                if part and not part.startswith("["):
                    names_here.append(part)

        entries = []
        n_sorry = 0
        for name in names_here:
            entry = informal.get(name)
            if entry is None or entry.get("env") not in RATEABLE_ENVS:
                continue
            if entry.get("difficulty") is not None:
                continue  # already rated
            rec = index.get(name)
            if rec is None:
                continue  # not in dep_graph (e.g. non-compiling / stray file) — skip
            if is_bare_sorry(rec):
                n_sorry += 1
                continue
            entries.append({
                "name": name,
                "proof_source": "\n".join(rec["slice"]),
            })

        if entries:
            unit = {
                "target_tex": str(tex.relative_to(BASE)),
                "n_unrated_sorry_skipped": n_sorry,
                "entries": entries,
            }
            out_path = WORK_DIR / (str(tex.relative_to(CHAPTER_DIR)).replace("/", "_").replace(".tex", ".json"))
            out_path.write_text(json.dumps(unit, indent=2, ensure_ascii=False), encoding="utf-8")
            units.append({"target_tex": unit["target_tex"], "work_file": str(out_path.relative_to(BASE)),
                          "n_entries": len(entries), "n_sorry_skipped": n_sorry})
            total_entries += len(entries)
            total_sorry += n_sorry

    manifest = {"units": units, "total_files_with_work": len(units),
                "total_entries_to_rate": total_entries, "total_sorry_skipped": total_sorry}
    (WORK_DIR / "manifest.json").write_text(json.dumps(manifest, indent=2), encoding="utf-8")

    print()
    print(f"Files needing difficulty ratings : {len(units)}")
    print(f"Entries to rate                  : {total_entries}")
    print(f"Bare-sorry entries skipped        : {total_sorry}")
    print(f"Manifest                          : {WORK_DIR.relative_to(BASE)}/manifest.json")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
