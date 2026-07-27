from __future__ import annotations

import argparse
import json
from dataclasses import asdict
from decimal import Decimal
from pathlib import Path

from proofmatch.agents import CodexAgent
from proofmatch.artifacts import RunStore, sha256_file
from proofmatch.blueprint import ProofSource, insert_approved_source
from proofmatch.budget import Budget, StageEstimate, estimate_cleanup, token_cost
from proofmatch.compare import compare_candidate, render_difference_report
from proofmatch.document import parse_validated_markdown, repair_document
from proofmatch.extraction import extract_pdf
from proofmatch.models import Candidate
from proofmatch.search import prepare_rerank_payload, search_candidates


REPOSITORY = Path(__file__).resolve().parent.parent
DEFAULT_DATASET = REPOSITORY / "dataset" / "tcslib_theorems.jsonl"
WORK_ROOT = REPOSITORY / ".proofmatch-work"
FIXTURE_NAME = "switching-lemma.pdf"


class ProofmatchParser(argparse.ArgumentParser):
    def parse_args(self, args=None, namespace=None):
        parsed = super().parse_args(args, namespace)
        source = getattr(parsed, "source", None)
        if (
            getattr(parsed, "max_cost", None) is None
            and source is not None
            and Path(source).name == FIXTURE_NAME
        ):
            parsed.max_cost = Decimal("1.00")
        return parsed


def _add_budget(parser: argparse.ArgumentParser) -> None:
    parser.add_argument("--max-cost", type=Decimal)


def build_parser() -> argparse.ArgumentParser:
    parser = ProofmatchParser(prog="proofmatch")
    subcommands = parser.add_subparsers(dest="command", required=True)

    estimate = subcommands.add_parser("estimate")
    estimate.add_argument("source", type=Path)
    _add_budget(estimate)

    extract = subcommands.add_parser("extract")
    extract.add_argument("source", type=Path)
    extract.add_argument("--local-only", action="store_true")
    _add_budget(extract)

    match = subcommands.add_parser("match")
    match.add_argument("source", type=Path)
    match.add_argument("--dataset", type=Path, default=DEFAULT_DATASET)
    match.add_argument("--dry-run", action="store_true")
    _add_budget(match)

    run = subcommands.add_parser("run")
    run.add_argument("source", type=Path)
    run.add_argument("--dataset", type=Path, default=DEFAULT_DATASET)
    run.add_argument("--dry-run", action="store_true")
    _add_budget(run)

    review = subcommands.add_parser("review")
    review.add_argument("run_id")
    review.add_argument(
        "decision",
        choices=("approve", "reject", "defer"),
        nargs="?",
    )
    return parser


def _budget(args: argparse.Namespace) -> Budget:
    if args.max_cost is None:
        raise ValueError("--max-cost is required for non-fixture paid runs")
    return Budget(args.max_cost)


def _estimate_source(source: Path) -> StageEstimate:
    if source.suffix.casefold() == ".md":
        characters = len(source.read_text(encoding="utf-8"))
    else:
        raw = source.with_suffix(".raw.md")
        characters = (
            len(raw.read_text(encoding="utf-8"))
            if raw.exists()
            else max(source.stat().st_size * 4, 1)
        )
    return estimate_cleanup(characters)


def _candidate_dict(candidate: Candidate) -> dict[str, object]:
    value = asdict(candidate)
    value["document_blocks"] = list(candidate.document_blocks)
    return value


def _extract(
    source: Path,
    budget: Budget,
    *,
    local_only: bool,
) -> Path:
    raw = source.with_suffix(".raw.md")
    report = extract_pdf(source, raw)
    print(
        f"Extracted {report.page_count} pages to {raw} "
        f"({sum(bool(item.reasons) for item in report.diagnostics)} suspect pages)"
    )
    if local_only:
        return raw
    output = source.with_suffix(".md")
    repair_document(
        raw,
        output,
        CodexAgent(model="gpt-5.6-luna"),
        budget,
        pdf_path=source,
    )
    print(f"Validated Markdown: {output}")
    return output


def _match(
    source: Path,
    dataset: Path,
    budget: Budget,
    *,
    dry_run: bool,
) -> str:
    index = parse_validated_markdown(source)
    candidates = list(search_candidates(index, dataset, limit=12))
    if not candidates:
        raise ValueError("candidate retrieval returned no TCSlib theorems")
    if dry_run:
        print("Top deterministic candidates:")
        for candidate in candidates:
            print(f"{candidate.score:8.2f}  {candidate.lean_name}")
        return index.source_fingerprint[:12]

    rerank_input = sum(
        len(str(item))
        for item in prepare_rerank_payload(candidates, index)["candidates"]
    ) // 4 + 2_000
    rerank_estimate = StageEstimate(
        "candidate reranking",
        rerank_input,
        2_000,
        token_cost("gpt-5.6-luna", rerank_input, 2_000),
    )
    budget.require(rerank_estimate)
    reranked = CodexAgent(model="gpt-5.6-luna").run(
        "rerank",
        prepare_rerank_payload(candidates, index),
    )
    order = [
        item.get("lean_name")
        for item in reranked.get("candidates", [])
        if isinstance(item, dict)
    ]
    by_name = {candidate.lean_name: candidate for candidate in candidates}
    selected = next((by_name[name] for name in order if name in by_name), candidates[0])
    verdict = compare_candidate(
        selected,
        index,
        CodexAgent(model="gpt-5.6-terra"),
        budget,
    )

    run_id = index.source_fingerprint[:12]
    store = RunStore(WORK_ROOT, run_id)
    store.write_json(
        "review",
        {
            "source_markdown": str(source.resolve()),
            "document": source.name.removesuffix(".md"),
            "candidate": _candidate_dict(selected),
            "verdict": asdict(verdict),
            "estimated_spend_usd": str(budget.spent_usd),
        },
    )
    report = render_difference_report([verdict])
    if report is not None:
        report_path = store.stage_path("differences", ".md")
        report_path.parent.mkdir(parents=True, exist_ok=True)
        report_path.write_text(report, encoding="utf-8")
        print(f"Differences or uncertainties: {report_path}")
    print(f"Review run {run_id}: {verdict.lean_name} -> {verdict.verdict}")
    print(f"Next: python3 scripts/proofmatch.py review {run_id}")
    return run_id


def _find_blueprint(lean_name: str) -> Path:
    needle = f"\\lean{{{lean_name}}}"
    matches = [
        path
        for path in (REPOSITORY / "blueprint" / "src" / "chapter").rglob("*.tex")
        if needle in path.read_text(encoding="utf-8", errors="ignore")
    ]
    if len(matches) != 1:
        raise ValueError(f"expected one blueprint file for {lean_name}, found {len(matches)}")
    return matches[0]


def _review(run_id: str, decision: str | None) -> int:
    store = RunStore(WORK_ROOT, run_id)
    review = store.read_json("review")
    if review is None:
        raise ValueError(f"unknown review run: {run_id}")
    verdict = review["verdict"]
    print(json.dumps(verdict, ensure_ascii=False, indent=2))
    if decision is None:
        decision = input("Decision [approve/reject/defer]: ").strip().casefold()
    if decision not in {"approve", "reject", "defer"}:
        raise ValueError("decision must be approve, reject, or defer")
    if decision == "approve":
        candidate = review["candidate"]
        if not isinstance(candidate, dict) or not isinstance(verdict, dict):
            raise ValueError("review artifact is malformed")
        blocks = tuple(str(item) for item in verdict["document_blocks"])
        tex_path = _find_blueprint(str(candidate["lean_name"]))
        insert_approved_source(
            tex_path,
            str(candidate["lean_name"]),
            ProofSource(str(review["document"]), blocks),
            approved=True,
        )
        print(f"Approved proof source written to {tex_path}")
    else:
        print(f"Decision recorded as {decision}; blueprint unchanged.")
    store.write_json("decision", {"decision": decision})
    return 0


def main(argv: list[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    if args.command == "review":
        return _review(args.run_id, args.decision)
    if args.command == "estimate":
        estimate = _estimate_source(args.source)
        print(
            f"Estimated cleanup: {estimate.input_tokens} input + "
            f"{estimate.output_tokens} output tokens = ${estimate.usd:.4f}"
        )
        return 0
    budget = _budget(args)
    if args.command == "extract":
        _extract(args.source, budget, local_only=args.local_only)
        return 0
    if args.command == "match":
        _match(args.source, args.dataset, budget, dry_run=args.dry_run)
        return 0
    if args.command == "run":
        if args.dry_run:
            estimate = _estimate_source(args.source)
            budget.require(estimate)
            print(f"Dry-run estimate: ${estimate.usd:.4f}")
            return 0
        markdown = _extract(args.source, budget, local_only=False)
        _match(markdown, args.dataset, budget, dry_run=False)
        return 0
    raise AssertionError(f"unhandled command: {args.command}")
