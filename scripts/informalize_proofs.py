r"""Informalize uncited Lean proofs into blueprint/src/references/informalized/<name>.md.

A dataset record's informal statement is the cited passage of a reference document
when its blueprint entry carries a `\proofsource` or `\statementsource` citation,
and otherwise prose written from the Lean (see informal_sources.py).  Citations come
from proofmatch runs against a reference document.  A theorem that no reference
document proves -- too granular for the text, a bridging lemma, a bare exercise --
gets a note instead: a human-readable account of its Lean proof, appended to its
informal statement.  Those notes were written by interactive agents from
proofmatch's `informalize_queue.md`; this script writes them headlessly through
the model CLI (`claude -p` or `codex exec`; prompt: proofmatch/prompts/informalize_proof.md) so the pipeline can
fill the gap for every uncited, sorry-free theorem.

Selection (what gets a note):
    * theorem / lemma records of the dataset (definitions are described by the
      blueprint entry, not by a proof note);
    * no `\proofsource` or `\statementsource` on its blueprint entry;
    * no informalized note yet (by the same lookup informal_sources.py uses);
    * the proof is sorry-free.

Usage:
    python3 scripts/informalize_proofs.py --estimate
    python3 scripts/informalize_proofs.py --limit 5            # pilot
    python3 scripts/informalize_proofs.py --area BooleanAnalysis --jobs 4
    python3 scripts/informalize_proofs.py --only NAME [NAME ...]
    python3 scripts/informalize_proofs.py --dataset dataset/.pipeline/pass1.jsonl
"""

from __future__ import annotations

import argparse
import concurrent.futures
import hashlib
import importlib.util
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
from proofmatch.dataset_io import open_dataset  # noqa: E402
from proofmatch.model_policy import DEFAULT_MODEL, check_model  # noqa: E402


def _load_sibling(name: str):
    # `scripts/proofmatch.py` shadows the package on sys.path, so siblings are
    # loaded by path, as build_informal_statements.py does.
    spec = importlib.util.spec_from_file_location(name, Path(__file__).resolve().parent / f"{name}.py")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


bd = _load_sibling("build_dataset")
bpn = _load_sibling("informal_sources")

DATASET = BASE / "dataset" / "tcslib_theorems.jsonl"
INFORMALIZED_DIR = BASE / "blueprint" / "src" / "references" / "informalized"
DEP_GRAPH = BASE / "dep_graph.json"

MAX_UPSTREAM = 30
MAX_UPSTREAM_CHARS = 700

LIMIT_RE = re.compile(
    r"(?i)(session limit|usage limit|quota|credit balance|out of credits|"
    r"upgrade to increase)"
)


def note_path(lean_name: str) -> Path:
    # informal_sources.note_for finds a note by its stem, so the stem is the full
    # Lean name whenever the filesystem can hold it.
    stem = lean_name
    if len(stem) > 180:
        stem = stem[:150] + "-" + hashlib.sha256(lean_name.encode()).hexdigest()[:12]
    return INFORMALIZED_DIR / f"{stem}.md"


def proof_has_sorry(slice_lines: list[str]) -> bool:
    text = "\n".join(slice_lines)
    text = re.sub(r"/-[\s\S]*?-/", "", text)
    text = re.sub(r"--.*", "", text)
    return re.search(r"\bsorry\b", text) is not None


def build_payload(record: dict, rec: dict, index: dict) -> dict:
    upstream = []
    for dep in rec.get("all_deps", []):
        drec = index.get(dep)
        if drec is None or drec["kind"] not in bd.PROOF_KINDS:
            continue
        statement = bd.split_signature("\n".join(drec["slice"]))
        if len(statement) > MAX_UPSTREAM_CHARS:
            statement = statement[:MAX_UPSTREAM_CHARS] + " ..."
        upstream.append({"lean_name": dep, "statement": statement})
        if len(upstream) >= MAX_UPSTREAM:
            break
    return {
        "lean_name": record["id"],
        "kind": record.get("kind", ""),
        "informal_statement": bpn.statement_part(record.get("informal_statement", "")),
        "formal_statement": record["formal_statement"],
        "proof_source": "\n".join(rec["slice"]),
        "upstream": upstream,
    }


def render_note(record: dict, rec: dict, result: dict, model: str) -> str:
    lean_file = bd.module_to_lean_path(rec["module"]).relative_to(BASE).as_posix()
    lines = [
        "<!-- generated-by: proofmatch informalization (uncited) -->",
        f"<!-- lean-source: {lean_file} :: {record['id']} -->",
        "<!-- origin: no source citation; informalized directly from the Lean proof -->",
        f"<!-- model: {model}; confidence: {result.get('confidence', '')} -->",
        "",
        f"# {result['title'].strip()}",
        "",
        f"**Claim.** {result['claim'].strip()}",
        "",
        f"**Proof.** {result['proof'].strip()}",
    ]
    facts = [f for f in result.get("key_facts", []) if f]
    if facts:
        lines += ["", "**Key facts.** " + ", ".join(f"`{f}`" for f in facts) + "."]
    if result.get("caveat"):
        lines += ["", f"**Caveat.** {result['caveat'].strip()}"]
    return "\n".join(lines) + "\n"


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--dataset", default=str(DATASET))
    ap.add_argument("--limit", type=int)
    ap.add_argument("--area", help="only this top-level area (BooleanAnalysis, ...)")
    ap.add_argument("--only", nargs="+", help="only these lean names")
    ap.add_argument("--modules", nargs="+", metavar="MODULE",
                    help="only declarations of these modules (full name, dotted suffix or area)")
    ap.add_argument("--jobs", type=int, default=3)
    ap.add_argument("--model", default=DEFAULT_MODEL)
    ap.add_argument("--allow-weak-models", action="store_true")
    ap.add_argument("--force", action="store_true", help="rewrite notes that already exist")
    ap.add_argument("--include-cited", action="store_true",
                    help="also write notes for theorems that carry a citation")
    ap.add_argument("--estimate", action="store_true", help="report, call nothing")
    args = ap.parse_args()

    verdict = check_model(args.model, "prose", allow_weak=args.allow_weak_models)
    if verdict.startswith("WARNING"):
        print(verdict)

    if not DEP_GRAPH.exists():
        print(f"ERROR: {DEP_GRAPH} not found.")
        return 1
    graph = json.load(open(DEP_GRAPH))["modules"]
    index = bd.build_index(graph)
    bd.make_proof_builder(graph, index)   # widens all_deps the way the proof builder does
    citations = bpn.blueprint_citations()
    notes = bpn.load_notes()

    records: list[dict] = []
    with open_dataset(Path(args.dataset)) as handle:
        for line in handle:
            if line.strip():
                records.append(json.loads(line))
    if args.area:
        records = [r for r in records if r.get("source_module", "").split(".")[1:2] == [args.area]]
    if args.only:
        wanted = set(args.only)
        records = [r for r in records if r["id"] in wanted]
    if args.modules:
        records = [r for r in records
                   if bd.module_matches(r.get("source_module", ""), args.modules)]

    skipped = {"not-proof": 0, "not-indexed": 0, "cited": 0, "has-note": 0, "sorry": 0}
    todo: list[tuple[dict, dict]] = []
    for record in records:
        if record.get("kind") not in bd.PROOF_KINDS:
            skipped["not-proof"] += 1
            continue
        rec = index.get(record["id"])
        if rec is None:
            skipped["not-indexed"] += 1
            continue
        cited = citations.get(record["id"]) or {}
        if not args.include_cited and (cited.get("proof_sources") or cited.get("statement_sources")):
            skipped["cited"] += 1
            continue
        if not args.force and bpn.note_for(record["id"], notes) is not None:
            skipped["has-note"] += 1
            continue
        if proof_has_sorry(rec["slice"]):
            skipped["sorry"] += 1
            continue
        todo.append((record, rec))
    if args.limit:
        todo = todo[: args.limit]

    print(f"{len(records)} records in scope; {len(todo)} proofs to informalize "
          f"(skipped: {', '.join(f'{v} {k}' for k, v in skipped.items() if v)}) "
          f"(model {args.model})")
    if args.estimate or not todo:
        return 0

    INFORMALIZED_DIR.mkdir(parents=True, exist_ok=True)
    agent = ClaudeAgent(model=args.model)
    lock = threading.Lock()
    halted = threading.Event()
    done = {"ok": 0, "low": 0, "failed": 0}

    def work(item: tuple[dict, dict]) -> None:
        record, rec = item
        if halted.is_set():
            return
        try:
            result = agent.run("informalize_proof", build_payload(record, rec, index))
        except (AgentOutputError, AgentInvocationError) as error:
            detail = str(error)
            with lock:
                done["failed"] += 1
                if LIMIT_RE.search(detail):
                    if not halted.is_set():
                        halted.set()
                        print(f"\n  STOPPING: {detail}")
                        print("  Notes written so far are kept; re-run to resume.")
                else:
                    print(f"  FAIL {record['id']}: {detail[:200]}")
            return
        path = note_path(record["id"])
        path.write_text(render_note(record, rec, result, args.model), encoding="utf-8")
        with lock:
            if result.get("confidence") == "low":
                done["low"] += 1
                print(f"  ~~ {record['id']}: low confidence -- {result.get('caveat', '')[:120]}")
            else:
                done["ok"] += 1
            n = done["ok"] + done["low"] + done["failed"]
            if n % 25 == 0:
                print(f"  ... {n}/{len(todo)}")

    with concurrent.futures.ThreadPoolExecutor(max_workers=args.jobs) as pool:
        list(pool.map(work, todo))

    print(f"\nwritten {done['ok']}   low-confidence {done['low']}   failed {done['failed']}")
    print(f"spend: ${agent.spent_usd:.2f} for {len(todo)} proofs "
          f"(${agent.spent_usd / max(1, len(todo)):.3f} each)")
    print("next: python3 scripts/build_dataset.py  (appends the notes to the informal statements)")
    return 1 if done["failed"] else 0


if __name__ == "__main__":
    raise SystemExit(main())
