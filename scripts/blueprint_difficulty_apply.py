"""
Apply difficulty ratings produced by the rating agents to the blueprint chapter tex.

Companion to blueprint_difficulty_plan.py. The plan step emits work units under
blueprint/.work/difficulty/; rating agents read those and write ratings files to
blueprint/.work/difficulty/ratings/*.json, each of the form:

    {"target_tex": "blueprint/src/chapter/.../X.tex",
     "ratings": {"Namespace.declName": 4, ...}}

This script then rewrites each target tex deterministically: for every rated name it
locates the entry's \\lean{...} line and replaces the entry's existing \\difficulty{N}
line (or inserts one after \\uses / \\leanok / \\label if the entry has none). Keeping
the tex edit mechanical means the agents only ever judge proofs — they never touch tex.

When several \\lean names share one environment, the environment gets the MAX of their
ratings (an environment has a single \\difficulty line).

Usage:
    python3 scripts/blueprint_difficulty_apply.py                # apply everything
    python3 scripts/blueprint_difficulty_apply.py --dry-run      # report only
"""

import argparse
import json
import re
from pathlib import Path

BASE = Path(__file__).resolve().parent.parent
RATINGS_DIR = BASE / "blueprint" / ".work" / "difficulty" / "ratings"

LEAN_RE = re.compile(r"^\s*\\lean\{([^}]*)\}")
DIFF_RE = re.compile(r"^\s*\\difficulty\{[^}]*\}")
END_RE = re.compile(r"^\s*\\(end\{|begin\{)")
ANCHOR_RES = [re.compile(r"^\s*\\uses\{"), re.compile(r"^\s*\\leanok\b"),
              re.compile(r"^\s*\\label\{")]
WINDOW = 12  # insertion-anchor scan: metadata block right after \lean{}
# The search for an EXISTING \difficulty must scan the whole environment, not a fixed
# window — long wrapped \uses lists push \difficulty past any small cap, and a capped
# scan then inserts a duplicate line instead of replacing.


def find_lean_line(lines, name):
    for i, line in enumerate(lines):
        m = LEAN_RE.match(line)
        if m and name in [p.strip() for p in m.group(1).split(",")]:
            return i
    return None


def apply_to_tex(tex_path, ratings, dry_run):
    lines = tex_path.read_text(encoding="utf-8").splitlines()
    # Group by \lean line so multi-name environments get one (max) rating.
    by_line = {}
    missing = []
    for name, rating in ratings.items():
        i = find_lean_line(lines, name)
        if i is None:
            missing.append(name)
            continue
        by_line[i] = max(by_line.get(i, 0), int(rating))

    n_replaced = n_inserted = 0
    # Edit bottom-up so earlier line indices stay valid across insertions.
    for i in sorted(by_line, reverse=True):
        rating = by_line[i]
        env_end = i + 1
        while env_end < len(lines) and not END_RE.match(lines[env_end]):
            env_end += 1
        indent = re.match(r"\s*", lines[i]).group(0)
        placed = False
        for j in range(i + 1, env_end):
            if DIFF_RE.match(lines[j]):
                lines[j] = f"{indent}\\difficulty{{{rating}}}"
                n_replaced += 1
                placed = True
                break
        if not placed:
            anchor = i
            for j in range(i + 1, min(i + WINDOW, env_end)):
                if any(r.match(lines[j]) for r in ANCHOR_RES):
                    anchor = j
            lines.insert(anchor + 1, f"{indent}\\difficulty{{{rating}}}")
            n_inserted += 1
    if not dry_run and (n_replaced or n_inserted):
        tex_path.write_text("\n".join(lines) + "\n", encoding="utf-8")
    return n_replaced, n_inserted, missing


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--dry-run", action="store_true")
    args = ap.parse_args()

    files = sorted(RATINGS_DIR.glob("*.json"))
    if not files:
        print(f"No ratings files in {RATINGS_DIR.relative_to(BASE)}")
        return 1

    tot_r = tot_i = 0
    all_missing = []
    bad_values = []
    for f in files:
        data = json.loads(f.read_text(encoding="utf-8"))
        tex_path = BASE / data["target_tex"]
        ratings = {}
        for name, v in data["ratings"].items():
            if not isinstance(v, int) or not (0 <= v <= 7):
                bad_values.append((f.name, name, v))
                continue
            ratings[name] = v
        if not tex_path.exists():
            print(f"  MISSING TEX: {data['target_tex']} ({f.name})")
            continue
        r, i, missing = apply_to_tex(tex_path, ratings, args.dry_run)
        tot_r += r
        tot_i += i
        all_missing += [(f.name, n) for n in missing]

    print(f"Ratings files          : {len(files)}")
    print(f"\\difficulty replaced   : {tot_r}")
    print(f"\\difficulty inserted   : {tot_i}")
    if bad_values:
        print(f"REJECTED (not int 0-7) : {len(bad_values)}")
        for fn, n, v in bad_values:
            print(f"  {fn}: {n} = {v!r}")
    if all_missing:
        print(f"NAMES NOT FOUND IN TEX : {len(all_missing)}")
        for fn, n in all_missing:
            print(f"  {fn}: {n}")
    if args.dry_run:
        print("(dry run — no files written)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
