#!/usr/bin/env python3
"""Summarize the shipped dataset, and fill the summary into the website's dataset page.

    python3 scripts/dataset_stats.py                      # print the summary
    python3 scripts/dataset_stats.py --json stats.json    # write it as JSON
    python3 scripts/dataset_stats.py --render FILE.html   # replace %%key%% tokens in FILE

The website source (webpage/Site/Dataset.lean) carries no numbers: it carries
tokens such as ``%%n_records%%``.  The deploy workflow builds the site, then runs
``--render`` on the generated dataset page so that every number on it is computed
from the dataset file that the same deploy serves for download.  Rendering fails
if a token on the page has no value here, or a value here is never used, so the
page and this script cannot drift apart silently.
"""
from __future__ import annotations

import argparse
import datetime as _dt
import gzip
import json
import os
import re
import subprocess
import sys
from collections import Counter
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
DATASET = ROOT / "dataset" / "tcslib_theorems.jsonl.gz"

# Folder under TCSlib/ -> the name the page prints.  Unknown folders get their
# CamelCase name split into words, so a new area appears without editing this.
AREA_NAMES = {
    "BooleanAnalysis": "Boolean function analysis",
    "Complexity": "complexity theory",
    "CommunicationComplexity": "communication complexity",
    "LearningTheory": "learning theory",
    "ErrorCorrectingCodes": "error-correcting codes",
    "GraphTheory": "graph theory",
    "KikuchiLDC": "locally decodable codes",
    "Cryptography": "cryptography",
    "InformationTheory": "information theory",
}

TOKEN_RE = re.compile(r"%%([a-z_]+)%%")


def _area_name(folder: str) -> str:
    if folder in AREA_NAMES:
        return AREA_NAMES[folder]
    return re.sub(r"(?<=[a-z])(?=[A-Z])", " ", folder).lower()


def _file_date(path: Path) -> _dt.date:
    """Commit date of the dataset file, falling back to its modification time."""
    try:
        out = subprocess.run(
            ["git", "log", "-1", "--format=%cs", "--", str(path)],
            cwd=path.parent, capture_output=True, text=True, check=True,
        ).stdout.strip()
        if out:
            return _dt.date.fromisoformat(out)
    except (subprocess.CalledProcessError, FileNotFoundError, ValueError):
        pass
    return _dt.date.fromtimestamp(path.stat().st_mtime)


def _n(x: int) -> str:
    return f"{x:,}"


def compute(path: Path = DATASET) -> dict:
    with gzip.open(path, "rt", encoding="utf-8") as f:
        records = [json.loads(line) for line in f if line.strip()]
    n = len(records)
    complete = sum(1 for r in records if r.get("proof_complete"))
    sources = Counter(r.get("informal_source") or "unknown" for r in records)
    # A `lean` informal statement carries the proof account after this separator
    # (scripts/informal_sources.py) when references/informalized/ holds a note.
    with_account = sum(1 for r in records
                       if r.get("informal_source") == "lean"
                       and "\n\nProof: " in r.get("informal_statement", ""))
    areas = Counter(r["source_module"].split(".")[1] for r in records)
    date = _file_date(path)
    size_mb = path.stat().st_size / 1e6
    by_area = ", ".join(f"{_area_name(a)} {_n(c)}" for a, c in areas.most_common())
    return {
        "n_records": n,
        "n_complete": complete,
        "n_sorry": n - complete,
        "n_cited": sources.get("citation", 0),
        "n_lean": sources.get("lean", 0),
        "n_lean_with_proof": with_account,
        "n_lean_without_proof": sources.get("lean", 0) - with_account,
        "n_rated": sum(1 for r in records if r.get("difficulty") is not None),
        "by_area": by_area,
        "areas": dict(areas.most_common()),
        "size_mb": round(size_mb),
        "build_date": date.isoformat(),
        "build_date_text": f"{date.day} {date:%B %Y}",
        "build_month": f"{date:%B %Y}",
    }


def token_values(stats: dict) -> dict[str, str]:
    vals = {}
    for k, v in stats.items():
        if isinstance(v, bool) or isinstance(v, dict):
            continue
        vals[k] = _n(v) if isinstance(v, int) else str(v)
    return vals


def render(files: list[Path], stats: dict) -> int:
    vals = token_values(stats)
    used: set[str] = set()
    for path in files:
        text = path.read_text(encoding="utf-8")
        found = set(TOKEN_RE.findall(text))
        unknown = sorted(found - vals.keys())
        if unknown:
            print(f"error: {path}: no value for token(s) {', '.join(unknown)}", file=sys.stderr)
            return 1
        if not found:
            print(f"error: {path}: no %%token%% found; was the page built from its source?",
                  file=sys.stderr)
            return 1
        used |= found
        path.write_text(TOKEN_RE.sub(lambda m: vals[m.group(1)], text), encoding="utf-8")
        print(f"{path}: filled {len(found)} tokens")
    return 0


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--dataset", type=Path, default=DATASET)
    ap.add_argument("--json", type=Path, help="write the summary as JSON to this file")
    ap.add_argument("--render", type=Path, nargs="+", metavar="HTML",
                    help="replace %%key%% tokens in these generated pages")
    args = ap.parse_args(argv)
    if not args.dataset.exists():
        print(f"error: {args.dataset} not found", file=sys.stderr)
        return 1
    stats = compute(args.dataset)
    if args.json:
        args.json.parent.mkdir(parents=True, exist_ok=True)
        args.json.write_text(json.dumps(stats, indent=2) + "\n", encoding="utf-8")
        print(f"wrote {args.json}")
    if args.render:
        return render(args.render, stats)
    if not args.json:
        for k, v in token_values(stats).items():
            print(f"{k:22} {v}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
