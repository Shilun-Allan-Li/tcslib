r"""Dataset hygiene checks for the informal side of the blueprint / dataset pair.

The dataset pairs an *informal statement* with a *formal* Lean statement, so the
informal half must say what the declaration claims and nothing else.  In
particular it must not contain the proof: an entry that hands over the proof
idea alongside the statement is useless for the task the dataset exists to pose.

The contract is the one in `.claude/agents/blueprint-writer.md`:

    Informal description: 1-3 sentences stating *what the declaration says* ...
    For a lemma/theorem, state the claim (hypotheses => conclusion).
    **Describe the statement, never the proof.**

This script checks that contract.  Run it over the blueprint sources (the thing
you edit) or over a built dataset (the thing you ship):

    python3 scripts/dataset_hygiene.py                       # blueprint/src/chapter
    python3 scripts/dataset_hygiene.py --dataset             # dataset/*.jsonl
    python3 scripts/dataset_hygiene.py --show 40             # print the offenders
    python3 scripts/dataset_hygiene.py --strict              # exit 1 on a HARD check

Checks
------
proof-leak      prose that narrates a proof rather than stating a claim
proof-env       a literal `\begin{proof}` or `Proof:` heading
repo-note       repo/editorial status notes (`sorry` bodies, "currently vacuous",
                triage logs, "worth extracting", "step 3 is the real work")
lean-internals  Mathlib/Lean implementation talk in the informal half
                ("0 hits in Mathlib", "is load-bearing", `Nat.card` juggling)
identifier-title  the title is the bare Lean name, so the informal statement
                leads with a formal identifier
mangled-title   the title is the Lean name merely re-spaced ("Two Mul Xdistance
                Sq Le Xfiberkl")
title-note      a repo status marker in the title ("BLOCKED", "MISSING from
                Mathlib") -- the title is folded into the informal statement
no-statement    the informal text is too short to be a statement

`proof-env`, `proof-leak`, `repo-note` and `title-note` are HARD: they are always defects, and
`--strict` fails on them.  The rest are advisory.  In particular `lean-internals`
has honest exceptions -- a definition that introduces a Lean typeclass really is
about `Fintype` instances -- and `no-statement` fires on claims that are terse
because the mathematics is (`$\chi_\varnothing \equiv 1$.`).
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

BASE = Path(__file__).resolve().parent.parent
CHAPTER_DIR = BASE / "blueprint" / "src" / "chapter"
DATASET = BASE / "dataset" / "tcslib_theorems.jsonl"

# --------------------------------------------------------------------------- #
# Checks
# --------------------------------------------------------------------------- #
#: Narration of a proof.  These read as "here is how you get there", which is
#: precisely what the formal half is supposed to be asking for.
PROOF_LEAK = re.compile(
    r"(?ix)\b("
    r"proof\s+sketch|proof\s+idea|sketch\s+of\s+(?:the\s+)?proof|proof\s+plan"
    r"|the\s+proof\s+(?:is|uses|goes|proceeds|combines|applies|extracts|decomposes"
    r"|shows|follows|requires|needs|runs|works|begins|starts)"
    r"|this\s+follows\s+(?:by|from|because)"
    r"|follows\s+by\s+combining|follows\s+from\s+the\s+(?:naive|collision|geometric)"
    r"|we\s+(?:first|then|now|next)\s+(?:prove|show|argue|apply|conclude|obtain|deduce"
    r"|derive|check|verify|observe|note|reduce|construct\s+the\s+proof)"
    r"|to\s+see\s+this|the\s+argument\s+(?:is|goes|uses|runs)"
    r"|step\s+\d|steps?\s+\d\s+and\s+\d"
    r"|the\s+(?:whole|real|only)\s+(?:content|work|exercise)"
    r"|by\s+induction\s+on\b"
    r")"
)
PROOF_ENV = re.compile(r"(?i)(\\begin\{proof\}|^\s*proof\s*[:.]|\\emph\{proof)")

#: A `definition` has no proof, so proof-narration is not a defect there: for a
#: definition the construction *is* the statement.  `\begin{proof}` still is.
PROOF_LEAK_ENVS = {"theorem", "lemma", "proposition", "corollary", "sublemma"}

#: Repo bookkeeping: true of the formalisation effort, not of the mathematics.
REPO_NOTE = re.compile(
    r"(?ix)("
    r"currently\s+(?:vacuous|false|defective)|\btodo\b|\bfixme\b"
    r"|\\texttt\{sorry\}|`sorry`|\bsorry\b\s*(?:body|bodies|-bodied)"
    r"|statement\s+repaired|statement\s+defect|not\s+yet\s+(?:proved|the\s+intended)"
    r"|worth\s+extracting|should\s+be\s+extracted|good\s+candidate\s+to\s+prove"
    r"|budget\s+for\s+it|log/|EXERCISE_TRIAGE|triage"
    r"|this\s+repo|out\s+of\s+chapter|dropped\s+(?:here|from\s+this\s+file)"
    r"|cheapest\s+win|NOT\s+a\s+missing\s+def|MISSING\s+from\s+Mathlib"
    r")"
)

#: Lean/Mathlib implementation detail leaking into the informal half.
LEAN_INTERNALS = re.compile(
    r"(?ix)("
    r"\d+\s+hits?\s+in\s+Mathlib|in\s+Mathlib\b.*\bhits?\b"
    r"|load[- ]bearing|Mathlib(?:'s)?\s+(?:supplies|has|proves|calls)"
    r"|\bDecidableRel\b|\bFintype\b|\bNat\.card\b|\bopen\s+scoped\b"
    r"|\bType\*|\binstance\b\s+(?:is|does)|elaborat|typecheck"
    r"|the\s+outline|\.lean\b"
    r")"
)

#: A terse claim like `$\chi_\varnothing \equiv 1$.` is a perfectly good statement,
#: so length alone is not the test: a statement must carry either some mathematics
#: or enough prose to say something.
#: Checks that are always defects, and that `--strict` gates on.
HARD = {"proof-env", "proof-leak", "repo-note", "title-note"}

#: Repo status markers in a blueprint `[title]`.  The title is folded into the
#: informal statement, so "BLOCKED"/"MISSING from Mathlib" would ship with it.
TITLE_NOTE = re.compile(
    r"(?i)(BLOCKED|MISSING\s+from\s+Mathlib|\bsorry\b|\bTODO\b|vacuous|"
    r"repo\s+has\s+the\s+real\s+one|absent\s+from\s+Mathlib|NEEDED-TO-STATE|"
    r"body\s+deferred|opaque\s+stub|\u26a0)"
)

MIN_MATH_CHARS = 18
MIN_PROSE_CHARS = 40


def checks(text: str, title: str, lean_name: str, env: str = "") -> list[str]:
    found = []
    if PROOF_ENV.search(text):
        found.append("proof-env")
    if PROOF_LEAK.search(text) and (not env or env in PROOF_LEAK_ENVS):
        found.append("proof-leak")
    if REPO_NOTE.search(text):
        found.append("repo-note")
    if LEAN_INTERNALS.search(text):
        found.append("lean-internals")
    if TITLE_NOTE.search(title):
        found.append("title-note")
    bare = title.replace("\\_", "_").replace("\\", "").strip()
    short = lean_name.split(".")[-1]
    if bare and (bare == lean_name or bare == short):
        found.append("identifier-title")
    elif bare and _squash(bare) == _squash(short):
        #: `two_mul_xDistance_sq_le_xFiberKL` -> "Two Mul Xdistance Sq Le Xfiberkl":
        #: still the formal name, only re-spaced.
        found.append("mangled-title")
    flat = re.sub(r"\s+", " ", text).strip()
    has_math = "$" in flat
    if len(flat) < (MIN_MATH_CHARS if has_math else MIN_PROSE_CHARS):
        found.append("no-statement")
    return found


def _squash(s: str) -> str:
    return re.sub(r"[^a-z0-9]", "", s.lower())


# --------------------------------------------------------------------------- #
# Sources
# --------------------------------------------------------------------------- #
def from_blueprint():
    """(lean_name, title, informal_text, env, where) for every blueprint entry."""
    sys.path.insert(0, str(Path(__file__).resolve().parent))
    import build_dataset as B

    for name, entry in B.parse_blueprint(CHAPTER_DIR).items():
        env = entry.get("env", "")
        yield name, entry.get("title", ""), entry.get("informal", ""), env, env


def from_dataset(path: Path):
    #: `kind` is the Lean kind (`theorem`/`lemma`/`def`/...); map it onto the
    #: blueprint environment names the env-sensitive checks are written against.
    for line in path.open():
        d = json.loads(line)
        kind = d.get("kind", "")
        env = {"def": "definition", "abbrev": "definition", "structure": "definition",
               "inductive": "definition", "class": "definition",
               "instance": "definition"}.get(kind, kind)
        yield (d["id"], d.get("title", ""), d.get("statement_informal", ""), env,
               d.get("source_module", ""))


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--dataset", nargs="?", const=str(DATASET),
                    help="check a built .jsonl instead of the blueprint sources")
    ap.add_argument("--show", type=int, default=0, help="print this many offenders in full")
    ap.add_argument("--only", help="report only this check")
    ap.add_argument("--strict", action="store_true", help="exit 1 when anything is flagged")
    args = ap.parse_args()

    rows = list(from_dataset(Path(args.dataset)) if args.dataset else from_blueprint())
    tally: dict[str, int] = {}
    hits = []
    for name, title, text, env, where in rows:
        found = checks(text, title or "", name, env)
        if args.only:
            found = [f for f in found if f == args.only]
        for f in found:
            tally[f] = tally.get(f, 0) + 1
        if found:
            hits.append((name, where, found, title, text))

    src = args.dataset or str(CHAPTER_DIR.relative_to(BASE))
    print(f"{len(rows)} entries from {src}")
    print(f"{len(hits)} flagged")
    for k in sorted(tally, key=lambda k: -tally[k]):
        print(f"  {tally[k]:5d}  {k}{'   (HARD)' if k in HARD else ''}")

    for name, where, found, title, text in hits[: args.show]:
        print("\n" + "=" * 78)
        print(f"{name}  [{','.join(found)}]  {where}")
        print(f"TITLE: {title}")
        print(re.sub(r"\n{2,}", "\n", text)[:900])

    hard = sum(v for k, v in tally.items() if k in HARD)
    if args.strict:
        print(f"\nhard failures: {hard}")
    return 1 if (args.strict and hard) else 0


if __name__ == "__main__":
    raise SystemExit(main())
