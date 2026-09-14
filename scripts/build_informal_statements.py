r"""Regenerate the informal statement of every dataset record, with an LLM pass.

Why
---
`build_dataset.py` takes the informal half of each pair straight from the
blueprint.  The blueprint is a *document*: it quotes Bondy & Murty verbatim,
carries attributions, and is written for someone reading it in order.  That
makes poor dataset prose.  Entries say "The embedding uses one extra layer for
the inputs: `C.toFeedForward.depth = C.depth + 1`" -- anaphoric ("the
embedding"), with `C` never introduced, and with Lean dot-notation standing in
for mathematics.  Read on its own, as a dataset consumer reads it, that states
nothing.

This pass rewrites each statement from the *formal* statement, which is the
ground truth, to the standard of a textbook or handout: every object
introduced, every hypothesis rendered, mathematics in mathematical notation, no
reference to anything outside the sentence.  The blueprint is left alone -- it
stays the book-cited document it is.

Output is cached per declaration under
`blueprint/src/references/statements/<lean_name>.json`, keyed by a hash of the
formal statement, so a run is resumable and a re-run only revisits declarations
whose Lean statement actually changed.  `apply_informal_statements.py` folds the
cache into the dataset, in the same post-pass style as `build_proof_notes.py`.

Usage
-----
    python3 scripts/build_informal_statements.py --limit 30        # pilot
    python3 scripts/build_informal_statements.py --area GraphTheory
    python3 scripts/build_informal_statements.py --only NAME [NAME...]
    python3 scripts/build_informal_statements.py --jobs 8          # full run
    python3 scripts/build_informal_statements.py --force           # ignore cache
    python3 scripts/build_informal_statements.py --estimate        # cost only
"""

from __future__ import annotations

import argparse
import concurrent.futures
import json
import re
import random
import sys
import threading
from pathlib import Path

BASE = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(BASE))

from proofmatch.agents import (  # noqa: E402
    AgentInvocationError,
    AgentOutputError,
    ClaudeAgent,
)
from proofmatch.dataset_io import read_dataset_text  # noqa: E402
from proofmatch import statements as cache  # noqa: E402

# `scripts/proofmatch.py` shadows the `proofmatch` package on sys.path, so the
# sibling module is loaded by path rather than by putting scripts/ on the path.
import importlib.util  # noqa: E402

_spec = importlib.util.spec_from_file_location(
    "statement_quality", Path(__file__).resolve().parent / "statement_quality.py"
)
Q = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(Q)

DATASET = BASE / "dataset" / "tcslib_theorems.jsonl"
CACHE_DIR = cache.CACHE_DIR

#: How much of the upstream definition block to hand over.  The formal statement
#: already carries the definitions in full; this is the *informal* vocabulary.
MAX_DEFINITIONS = 24

#: Definitions are inlined above the statement in `informal_statement`, so the
#: generated prose may use their terms.  Statements are generated for every
#: record, definitions included (they are records too when a theorem depends on
#: them -- `kind` tells the prompt which mode to write in).


def cache_key(record: dict) -> str:
    return cache.cache_key(record["formal_statement"])


def cache_path(lean_name: str, root: Path | None = None) -> Path:
    return cache.cache_path(lean_name, root or CACHE_DIR)


def load_cached(record: dict) -> dict | None:
    return cache.load(record["id"], record["formal_statement"], CACHE_DIR)


def build_payload(record: dict) -> dict:
    definitions = [
        {"name": d["id"], "title": d.get("title", ""), "informal": d.get("informal", "")}
        for d in record.get("definitions", [])[:MAX_DEFINITIONS]
    ]
    return {
        "lean_name": record["id"],
        "kind": record.get("kind", ""),
        "formal_statement": record["formal_statement"],
        "definitions": definitions,
        "current": {
            "title": record.get("title", ""),
            "statement": record.get("statement_informal", ""),
        },
    }


#: The account ran out of quota; nothing about the next call will be different.
LIMIT_RE = re.compile(
    r"(?i)(session limit|usage limit|quota|credit balance|out of credits|"
    r"upgrade to increase)"
)

#: `tautology` is a fact about the *Lean* statement -- it assumes its own
#: conclusion -- not a defect in the prose, so re-asking cannot fix it.  It is
#: recorded and reported, never retried.
NOT_PROSE = {"tautology"}


def grade(result: dict) -> list[str]:
    return Q.check(result.get("statement", ""), result.get("title", ""), strict=True)


def generate(agent: ClaudeAgent, record: dict) -> dict:
    """One declaration: generate, grade, and re-ask once if the rubric bites."""
    payload = build_payload(record)
    result = agent.run("informalize_statement", payload)
    problems = grade(result)
    if [p for p in problems if p not in NOT_PROSE]:
        # One correction round.  The rubric names the defect precisely, so this
        # is cheap and fixes most of what it catches (dot-notation, "as above").
        retry = dict(payload)
        retry["rejected_draft"] = result
        retry["rule_violations"] = problems
        retry["instruction"] = (
            "The draft above was rejected by the style checks named in "
            "rule_violations. Rewrite it so that none of them apply, keeping it "
            "faithful to formal_statement."
        )
        result = agent.run("informalize_statement", retry)
        problems = grade(result)
    result["rubric"] = problems
    return result


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--dataset", default=str(DATASET))
    ap.add_argument("--limit", type=int, help="stop after this many declarations")
    ap.add_argument("--area", help="only this top-level area (GraphTheory, ...)")
    ap.add_argument("--only", nargs="+", help="only these lean names")
    ap.add_argument("--jobs", type=int, default=6, help="concurrent claude calls")
    ap.add_argument("--model", help="override the model")
    ap.add_argument("--force", action="store_true", help="ignore the cache")
    ap.add_argument("--sample", action="store_true",
                    help="with --limit, spread the selection across areas")
    ap.add_argument("--cache-dir", help="write elsewhere (for A/B comparisons)")
    ap.add_argument("--regrade", action="store_true",
                    help="re-check cached statements against the current rubric "
                         "and regenerate the ones that now fail")
    ap.add_argument("--estimate", action="store_true",
                    help="report how much work is outstanding, call nothing")
    args = ap.parse_args()

    global CACHE_DIR
    if args.cache_dir:
        CACHE_DIR = Path(args.cache_dir)

    records = [json.loads(line) for line in read_dataset_text(Path(args.dataset)).splitlines()
               if line.strip()]
    if args.area:
        records = [r for r in records
                   if r.get("source_module", "").split(".")[1:2] == [args.area]]
    if args.only:
        wanted = set(args.only)
        records = [r for r in records if r["id"] in wanted]

    if args.regrade:
        stale = []
        counts: dict[str, int] = {}
        for r in records:
            cached = load_cached(r)
            if cached is None:
                continue
            problems = Q.check(cached.get("statement", ""), cached.get("title", ""),
                               strict=True)
            prose = [p for p in problems if p not in NOT_PROSE]
            for p in problems:
                counts[p] = counts.get(p, 0) + 1
            if prose:
                stale.append(r)
        print("cached statements re-graded:",
              ", ".join(f"{v} {k}" for k, v in sorted(counts.items(), key=lambda kv: -kv[1]))
              or "all clean")
        todo = stale
    else:
        todo = records if args.force else [r for r in records if load_cached(r) is None]
    if args.sample and args.limit:
        by_area: dict[str, list[dict]] = {}
        for r in todo:
            by_area.setdefault(r.get("source_module", "?").split(".")[1:2] and
                               r["source_module"].split(".")[1] or "?", []).append(r)
        rng = random.Random(0)
        picked: list[dict] = []
        areas = sorted(by_area)
        while len(picked) < args.limit and any(by_area.values()):
            for area in areas:
                if by_area[area] and len(picked) < args.limit:
                    picked.append(by_area[area].pop(rng.randrange(len(by_area[area]))))
        todo = picked
    elif args.limit:
        todo = todo[: args.limit]

    print(f"{len(records)} records in scope; {len(todo)} to generate "
          f"({len(records) - len(todo)} cached)")
    if args.estimate or not todo:
        return 0

    CACHE_DIR.mkdir(parents=True, exist_ok=True)
    agent = ClaudeAgent(model=args.model) if args.model else ClaudeAgent()
    lock = threading.Lock()
    done = {"ok": 0, "flagged": 0, "failed": 0}
    #: A usage limit is not a per-declaration failure: every remaining call will
    #: fail the same way.  Stop submitting instead of printing 2000 identical
    #: errors and leaving the run looking like a quality problem.
    halted = threading.Event()

    def work(record: dict) -> None:
        if halted.is_set():
            return
        try:
            result = generate(agent, record)
        except (AgentOutputError, AgentInvocationError) as error:
            detail = str(error)
            with lock:
                done["failed"] += 1
                if LIMIT_RE.search(detail):
                    if not halted.is_set():
                        halted.set()
                        print(f"\n  STOPPING: {detail}")
                        print("  Progress is cached; re-run the same command to resume.")
                else:
                    print(f"  FAIL {record['id']}: {error}")
            return
        entry = {
            "lean_name": record["id"],
            "key": cache_key(record),
            "kind": record.get("kind", ""),
            "title": result.get("title", ""),
            "statement": result.get("statement", ""),
            "hypotheses_covered": result.get("hypotheses_covered", []),
            "confidence": result.get("confidence", ""),
            "caveat": result.get("caveat", ""),
            "rubric": result.get("rubric", []),
        }
        cache_path(record["id"]).write_text(
            json.dumps(entry, ensure_ascii=False, indent=1) + "\n", encoding="utf-8"
        )
        with lock:
            if entry["rubric"]:
                done["flagged"] += 1
                print(f"  ~~ {record['id']}: {','.join(entry['rubric'])}")
            else:
                done["ok"] += 1
            n = done["ok"] + done["flagged"] + done["failed"]
            if n % 25 == 0:
                print(f"  ... {n}/{len(todo)}")

    with concurrent.futures.ThreadPoolExecutor(max_workers=args.jobs) as pool:
        list(pool.map(work, todo))

    print(f"\nclean {done['ok']}   rubric-flagged {done['flagged']}   failed {done['failed']}")
    if halted.is_set():
        remaining = len(todo) - done["ok"] - done["flagged"]
        print(f"halted on a usage limit with {remaining} declarations left to do")
    print(f"spend: ${agent.spent_usd:.2f} for {len(todo)} declarations "
          f"(${agent.spent_usd / max(1, len(todo)):.3f} each)")
    return 1 if done["failed"] else 0



if __name__ == "__main__":
    raise SystemExit(main())
