r"""Rate proof difficulty headlessly, from the work units of blueprint_difficulty_plan.py.

The difficulty column of the dataset is the blueprint's `\difficulty{N}` -- an
intrinsic, tactic-only 1-7 rating of each proof script (rubric in
proofmatch/prompts/rate_difficulty.md, the same one .claude/agents/blueprint-writer.md
gives interactive agents).  Until now the ratings were produced by interactive
subagents reading the work units; this script does the same job through
the model CLI (`claude -p` or `codex exec`, proofmatch/agents.py) so the dataset pipeline can run end to end without a person in the
loop.

    blueprint_difficulty_plan.py   -> blueprint/.work/difficulty/<unit>.json   (what to rate)
    rate_difficulty.py             -> blueprint/.work/difficulty/ratings/<unit>.json
    blueprint_difficulty_apply.py  -> \difficulty{N} lines in the chapter .tex

Entries are rated in small batches (one call rates several proofs) and every
batch is written to the ratings file as soon as it returns, so a run is
resumable: entries already present in a ratings file are not re-asked.

Usage:
    python3 scripts/rate_difficulty.py --estimate          # how much is outstanding
    python3 scripts/rate_difficulty.py --limit 20          # pilot
    python3 scripts/rate_difficulty.py --jobs 4            # full run
    python3 scripts/rate_difficulty.py --model claude-fable-5-1
"""

from __future__ import annotations

import argparse
import concurrent.futures
import json
import re
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
from proofmatch.model_policy import DEFAULT_MODEL, check_model  # noqa: E402

sys.path.append(str(Path(__file__).resolve().parent))
from build_dataset import module_matches  # noqa: E402

WORK_DIR = BASE / "blueprint" / ".work" / "difficulty"
RATINGS_DIR = WORK_DIR / "ratings"

#: Proofs per call.  Small enough that the rubric is applied to each proof with
#: attention; large enough that the per-call overhead does not dominate.
BATCH_SIZE = 6
#: Characters of proof source per call; a single huge proof still goes alone.
BATCH_CHARS = 40_000

LIMIT_RE = re.compile(
    r"(?i)(session limit|usage limit|quota|credit balance|out of credits|"
    r"upgrade to increase)"
)


def load_units() -> list[dict]:
    manifest = WORK_DIR / "manifest.json"
    if not manifest.exists():
        print(f"ERROR: {manifest.relative_to(BASE)} not found; run "
              "scripts/blueprint_difficulty_plan.py first.")
        return []
    units = []
    for row in json.loads(manifest.read_text(encoding="utf-8"))["units"]:
        path = BASE / row["work_file"]
        if not path.exists():
            continue
        unit = json.loads(path.read_text(encoding="utf-8"))
        unit["work_file"] = path
        unit["ratings_file"] = RATINGS_DIR / path.name
        units.append(unit)
    return units


def load_ratings(path: Path) -> dict[str, int]:
    if not path.exists():
        return {}
    try:
        return dict(json.loads(path.read_text(encoding="utf-8")).get("ratings", {}))
    except (OSError, ValueError):
        return {}


def batches(entries: list[dict]) -> list[list[dict]]:
    out: list[list[dict]] = []
    cur: list[dict] = []
    chars = 0
    for entry in entries:
        size = len(entry["proof_source"])
        if cur and (len(cur) >= BATCH_SIZE or chars + size > BATCH_CHARS):
            out.append(cur)
            cur, chars = [], 0
        cur.append(entry)
        chars += size
    if cur:
        out.append(cur)
    return out


def rate_batch(agent: ClaudeAgent, batch: list[dict]) -> dict[str, tuple[int, str]]:
    payload = {"entries": [{"lean_name": e["name"], "proof_source": e["proof_source"]}
                           for e in batch]}
    result = agent.run("rate_difficulty", payload)
    wanted = {e["name"] for e in batch}
    out: dict[str, tuple[int, str]] = {}
    for row in result["ratings"]:
        name = row["lean_name"]
        if name in wanted:
            out[name] = (int(row["difficulty"]), row.get("reason", ""))
    missing = sorted(wanted - set(out))
    if missing:
        raise AgentOutputError(f"ratings missing for {missing}")
    return out


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--jobs", type=int, default=3, help="concurrent model calls")
    ap.add_argument("--limit", type=int, help="rate at most this many entries")
    ap.add_argument("--model", default=DEFAULT_MODEL)
    ap.add_argument("--allow-weak-models", action="store_true")
    ap.add_argument("--force", action="store_true", help="re-ask entries already rated")
    ap.add_argument("--only", nargs="+", metavar="NAME", help="only these lean names")
    ap.add_argument("--modules", nargs="+", metavar="MODULE",
                    help="only declarations of these modules (full name, dotted suffix or area)")
    ap.add_argument("--estimate", action="store_true", help="report, call nothing")
    args = ap.parse_args()

    verdict = check_model(args.model, "judgement", allow_weak=args.allow_weak_models)
    if verdict.startswith("WARNING"):
        print(verdict)

    units = load_units()
    if not units:
        print("0 rateable entries: blueprint_difficulty_plan.py found nothing unrated "
              "(or its work units are gone; rerun it)")
        return 0
    work: list[tuple[dict, list[dict]]] = []
    total = done_already = 0
    for unit in units:
        have = {} if args.force else load_ratings(unit["ratings_file"])
        entries = unit["entries"]
        if args.only:
            entries = [e for e in entries if e["name"] in set(args.only)]
        if args.modules:
            # `module` is written by blueprint_difficulty_plan.py; older work units
            # without it are kept in scope rather than silently dropped.
            entries = [e for e in entries
                       if "module" not in e or module_matches(e["module"], args.modules)]
        unit["entries"] = entries
        todo = [e for e in entries if e["name"] not in have]
        total += len(unit["entries"])
        done_already += len(unit["entries"]) - len(todo)
        if todo:
            work.append((unit, todo))
    outstanding = sum(len(t) for _, t in work)
    if args.limit is not None and outstanding > args.limit:
        trimmed: list[tuple[dict, list[dict]]] = []
        left = args.limit
        for unit, todo in work:
            if left <= 0:
                break
            trimmed.append((unit, todo[:left]))
            left -= len(todo[:left])
        work = trimmed
        outstanding = sum(len(t) for _, t in work)
    print(f"{total} rateable entries in {len(units)} work units; "
          f"{done_already} already rated; {outstanding} to rate now "
          f"(model {args.model})")
    if args.estimate or not outstanding:
        return 0

    RATINGS_DIR.mkdir(parents=True, exist_ok=True)
    agent = ClaudeAgent(model=args.model)
    lock = threading.Lock()
    halted = threading.Event()
    counts = {"rated": 0, "sorry": 0, "failed": 0}

    def commit(unit: dict, ratings: dict[str, tuple[int, str]]) -> None:
        with lock:
            path: Path = unit["ratings_file"]
            current = {"target_tex": unit["target_tex"], "ratings": {}, "reasons": {}}
            if path.exists():
                try:
                    current.update(json.loads(path.read_text(encoding="utf-8")))
                except (OSError, ValueError):
                    pass
            current.setdefault("ratings", {})
            current.setdefault("reasons", {})
            for name, (difficulty, reason) in ratings.items():
                if difficulty == 0:
                    counts["sorry"] += 1
                    continue          # bare sorry: never rated
                current["ratings"][name] = difficulty
                current["reasons"][name] = reason
                counts["rated"] += 1
            path.write_text(json.dumps(current, indent=2, ensure_ascii=False) + "\n",
                            encoding="utf-8")

    jobs: list[tuple[dict, list[dict]]] = []
    for unit, todo in work:
        for batch in batches(todo):
            jobs.append((unit, batch))

    def run(job: tuple[dict, list[dict]]) -> None:
        unit, batch = job
        if halted.is_set():
            return
        try:
            ratings = rate_batch(agent, batch)
        except (AgentOutputError, AgentInvocationError) as error:
            detail = str(error)
            with lock:
                counts["failed"] += len(batch)
                if LIMIT_RE.search(detail):
                    if not halted.is_set():
                        halted.set()
                        print(f"\n  STOPPING: {detail}")
                        print("  Ratings so far are saved; re-run the same command to resume.")
                else:
                    print(f"  FAIL {unit['target_tex']} [{batch[0]['name']} ...]: {detail[:200]}")
            return
        commit(unit, ratings)
        with lock:
            n = counts["rated"] + counts["sorry"] + counts["failed"]
            if n % 30 < len(batch):
                print(f"  ... {n}/{outstanding}")

    with concurrent.futures.ThreadPoolExecutor(max_workers=args.jobs) as pool:
        list(pool.map(run, jobs))

    print(f"\nrated {counts['rated']}   bare-sorry skipped {counts['sorry']}   "
          f"failed {counts['failed']}")
    print(f"spend: ${agent.spent_usd:.2f}")
    print("next: python3 scripts/blueprint_difficulty_apply.py")
    return 1 if counts["failed"] else 0


if __name__ == "__main__":
    raise SystemExit(main())
