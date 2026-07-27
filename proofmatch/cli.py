from __future__ import annotations

import argparse
import json
from dataclasses import asdict
from decimal import Decimal
from pathlib import Path

from proofmatch.agents import CodexAgent
from proofmatch.artifacts import RunStore, sha256_file
from proofmatch.blueprint import (
    ProofSource,
    ProofStep,
    insert_approved_source,
    insert_approved_steps,
)
from proofmatch.budget import Budget, StageEstimate, estimate_cleanup, token_cost
from proofmatch.compare import compare_candidate, render_difference_report
from proofmatch.chapter import run_chapter_match
from proofmatch.document import parse_validated_markdown, repair_document
from proofmatch.extraction import extract_pdf
from proofmatch.models import Candidate, ComparisonVerdict, ProofStepManifest
from proofmatch.search import prepare_rerank_payload, search_candidates
from proofmatch.upstream import (
    batch_declarations,
    build_manifest,
    estimate_upstream_batches,
    load_upstream_declarations,
    map_upstream_batches,
    render_upstream_review,
    validate_manifest,
)


REPOSITORY = Path(__file__).resolve().parent.parent
DEFAULT_DATASET = REPOSITORY / "dataset" / "tcslib_theorems.jsonl"
DEFAULT_DEPENDENCY_GRAPH = REPOSITORY / "dep_graph.json"
DEFAULT_BLUEPRINT_ROOT = REPOSITORY / "blueprint" / "src" / "chapter"
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

    map_upstream = subcommands.add_parser("map-upstream")
    map_upstream.add_argument("run_id")
    map_upstream.add_argument("--dataset", type=Path, default=DEFAULT_DATASET)
    map_upstream.add_argument(
        "--dependency-graph",
        type=Path,
        default=DEFAULT_DEPENDENCY_GRAPH,
    )
    map_upstream.add_argument("--dry-run", action="store_true")
    _add_budget(map_upstream)

    review_upstream = subcommands.add_parser("review-upstream")
    review_upstream.add_argument("run_id")
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


def write_difference_report(store: RunStore, report: str | None) -> Path | None:
    report_path = store.stage_path("differences", ".md")
    if report is None:
        if report_path.exists():
            report_path.unlink()
        return None

    report_path.parent.mkdir(parents=True, exist_ok=True)
    report_path.write_text(report, encoding="utf-8")
    return report_path


def select_primary_candidate(
    candidates: list[Candidate],
    reranked: dict[str, object],
    index,
) -> Candidate:
    by_name = {candidate.lean_name: candidate for candidate in candidates}
    block_order = {
        block.block_id: position for position, block in enumerate(index.blocks)
    }
    ranked_rows = reranked.get("candidates")
    if not isinstance(ranked_rows, list):
        return candidates[0]
    choices = []
    for rerank_position, row in enumerate(ranked_rows):
        if not isinstance(row, dict):
            continue
        candidate = by_name.get(str(row.get("lean_name") or ""))
        if candidate is None:
            continue
        source_position = min(
            (
                block_order[block]
                for block in candidate.document_blocks
                if block in block_order
            ),
            default=len(block_order),
        )
        choices.append((source_position, rerank_position, candidate))
    if not choices:
        return candidates[0]
    choices.sort(key=lambda item: (item[0], item[1]))
    return choices[0][2]


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
    result = run_chapter_match(
        source,
        index,
        dataset,
        DEFAULT_DEPENDENCY_GRAPH,
        DEFAULT_BLUEPRINT_ROOT,
        budget,
        dry_run=dry_run,
    )
    run_id = index.source_fingerprint[:12]
    if dry_run:
        print("Blueprint-scoped chapter candidates:")
        for name in result["candidates"]:
            print(f"  {name}")
        print(
            "Relevance pass estimate: "
            f"${Decimal(str(result['estimated_relevance_spend_usd'])):.4f}"
        )
        print(
            "Worst-case total estimate (if every candidate is compared): "
            f"${Decimal(str(result['estimated_total_spend_usd'])):.4f}"
        )
        return run_id
    store = RunStore(WORK_ROOT, run_id)
    store.write_json("chapter_review", result)
    verdicts = [
        ComparisonVerdict(
            lean_name=str(row["lean_name"]),
            document_blocks=tuple(row["document_blocks"]),
            verdict=str(row["verdict"]),
            confidence=float(row["confidence"]),
            differences=tuple(row["differences"]),
            evidence=tuple(row["evidence"]),
            pdf_outline=tuple(row.get("pdf_outline", ())),
            lean_outline=tuple(row.get("lean_outline", ())),
        )
        for row in result["verdicts"]
    ]
    report_path = write_difference_report(
        store, render_difference_report(verdicts)
    )
    if report_path is not None:
        print(f"Differences or uncertainties: {report_path}")
    same = sum(item.verdict == "same" for item in verdicts)
    print(
        f"Chapter run {run_id}: {len(verdicts)} compared; "
        f"{same} same and propagated"
    )
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


def _approved_same_review(store: RunStore) -> dict[str, object]:
    review = store.read_json("review")
    decision = store.read_json("decision")
    if review is None:
        raise ValueError("upstream mapping requires a theorem-level review")
    verdict = review.get("verdict")
    if not isinstance(verdict, dict) or verdict.get("verdict") != "same":
        raise ValueError("upstream mapping requires a same theorem verdict")
    if decision is None or decision.get("decision") != "approve":
        raise ValueError("upstream mapping requires theorem-level approval")
    return review


def _proof_context(index, verdict: dict[str, object]):
    raw_blocks = verdict.get("document_blocks")
    if not isinstance(raw_blocks, list):
        raise ValueError("theorem review has no document block list")
    requested = [str(item) for item in raw_blocks]
    by_id = {block.block_id: block for block in index.blocks}
    missing = [block for block in requested if block not in by_id]
    if missing:
        raise ValueError(
            "theorem review cites stale Markdown blocks: "
            + ", ".join(missing)
        )
    return tuple(by_id[block] for block in requested)


def apply_upstream_manifest(
    tex_path: Path,
    manifest: ProofStepManifest,
) -> None:
    steps = tuple(
        ProofStep(
            assignment.lean_name,
            assignment.relation,
            manifest.document,
            assignment.document_blocks,
        )
        for assignment in manifest.assignments
    )
    insert_approved_steps(
        tex_path,
        manifest.theorem,
        steps,
        approved=True,
    )


def _map_upstream(
    run_id: str,
    dataset: Path,
    dependency_graph: Path,
    max_cost: Decimal | None,
    *,
    dry_run: bool,
) -> int:
    if max_cost is None:
        raise ValueError("--max-cost is required for upstream mapping")
    store = RunStore(WORK_ROOT, run_id)
    review = _approved_same_review(store)
    candidate = review.get("candidate")
    verdict = review.get("verdict")
    if not isinstance(candidate, dict) or not isinstance(verdict, dict):
        raise ValueError("theorem review artifact is malformed")
    theorem = str(candidate.get("lean_name") or "")
    proof_text = str(candidate.get("proof") or "")
    source = Path(str(review.get("source_markdown") or ""))
    if not theorem or not proof_text or not source.is_file():
        raise ValueError("theorem review lacks proof or source Markdown")
    index = parse_validated_markdown(source)
    proof_blocks = _proof_context(index, verdict)
    declarations = load_upstream_declarations(
        dataset,
        dependency_graph,
        theorem,
    )
    batches = batch_declarations(declarations)
    estimates = estimate_upstream_batches(batches, proof_blocks)
    prior_spend = Decimal(str(review.get("estimated_spend_usd") or "0"))
    estimate_budget = Budget(max_cost, prior_spend)
    for estimate in estimates:
        estimate_budget.require(estimate)
    mapping_estimate = estimate_budget.spent_usd - prior_spend
    print(
        f"Upstream mapping: {len(declarations)} declarations in "
        f"{len(batches)} batches; estimated additional ${mapping_estimate:.6f}; "
        f"estimated total ${estimate_budget.spent_usd:.6f}/{max_cost:.2f}"
    )
    if dry_run:
        return 0

    budget = Budget(max_cost, prior_spend)

    def load_batch(position: int, fingerprint: str):
        cached = store.read_json(f"upstream_batch_{position:03d}")
        if cached is None or cached.get("fingerprint") != fingerprint:
            return None
        output = cached.get("output")
        return output if isinstance(output, dict) else None

    def save_batch(
        position: int,
        fingerprint: str,
        output: dict[str, object],
    ) -> None:
        store.write_json(
            f"upstream_batch_{position:03d}",
            {"fingerprint": fingerprint, "output": output},
        )

    assignments = map_upstream_batches(
        declarations,
        proof_blocks,
        CodexAgent(model="gpt-5.6-luna"),
        budget,
        load_batch=load_batch,
        save_batch=save_batch,
    )
    manifest = build_manifest(
        theorem,
        str(review.get("document") or source.stem),
        index,
        proof_text,
        declarations,
        assignments,
    )
    allowed_blocks = {block.block_id for block in proof_blocks}
    validate_manifest(
        manifest,
        index,
        proof_text,
        declarations,
        allowed_blocks,
    )
    store.write_json(
        "upstream_input",
        {
            "dataset": str(dataset.resolve()),
            "dependency_graph": str(dependency_graph.resolve()),
            "source_markdown": str(source.resolve()),
            "estimated_prior_spend_usd": str(prior_spend),
            "estimated_mapping_spend_usd": str(mapping_estimate),
            "estimated_total_spend_usd": str(estimate_budget.spent_usd),
            "allowed_blocks": sorted(allowed_blocks),
        },
    )
    store.write_json("proof_steps", asdict(manifest))
    review_path = store.stage_path("proof_steps_review", ".md")
    review_path.parent.mkdir(parents=True, exist_ok=True)
    review_path.write_text(
        render_upstream_review(
            manifest,
            {block.block_id: block for block in proof_blocks},
        ),
        encoding="utf-8",
    )
    apply_upstream_manifest(_find_blueprint(theorem), manifest)
    store.write_json(
        "upstream_decision",
        {"decision": "inherited-theorem-approval"},
    )
    print(f"Upstream review: {review_path}")
    print("Validated upstream proof steps written to blueprint.")
    return 0


def _review_upstream(run_id: str) -> int:
    store = RunStore(WORK_ROOT, run_id)
    manifest_path = store.stage_path("proof_steps")
    review_path = store.stage_path("proof_steps_review", ".md")
    if not manifest_path.exists() or not review_path.exists():
        raise ValueError(f"upstream mapping for {run_id} is incomplete")
    print(review_path.read_text(encoding="utf-8"))
    return 0


def main(argv: list[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    if args.command == "review":
        return _review(args.run_id, args.decision)
    if args.command == "map-upstream":
        return _map_upstream(
            args.run_id,
            args.dataset,
            args.dependency_graph,
            args.max_cost,
            dry_run=args.dry_run,
        )
    if args.command == "review-upstream":
        return _review_upstream(args.run_id)
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
