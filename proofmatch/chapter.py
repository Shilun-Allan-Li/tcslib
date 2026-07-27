from __future__ import annotations

from collections.abc import Callable, Mapping, Sequence
from dataclasses import asdict, replace
from pathlib import Path

from proofmatch.agents import (
    COMPARE_MODEL,
    DEFAULT_MODEL,
    AgentOutputError,
    ClaudeAgent,
)
from proofmatch.blueprint import (
    ProofSource,
    ProofStep,
    SourceProposal,
    StepProposal,
    apply_blueprint_mutations,
    plan_blueprint_mutations,
)
from proofmatch.budget import Budget, BudgetExceeded
from proofmatch.catalog import (
    BlueprintBinding,
    load_blueprint_bindings,
    load_blueprint_candidates,
)
from proofmatch.compare import compare_candidate, estimate_comparison
from proofmatch.models import (
    Candidate,
    ComparisonVerdict,
    DocumentIndex,
    RelevanceDecision,
)
from proofmatch.relevance import requires_comparison
from proofmatch.relevance import classify_relevance, estimate_relevance
from proofmatch.search import discover_candidates
from proofmatch.upstream import (
    batch_declarations,
    build_manifest,
    estimate_upstream_batches,
    load_upstream_declarations,
    map_upstream_batches,
    validate_manifest,
)


def compare_relevant_candidates(
    candidates: Sequence[Candidate],
    decisions: Sequence[RelevanceDecision],
    index: DocumentIndex,
    agent_factory: Callable[[], object],
    budget: Budget,
) -> tuple[ComparisonVerdict, ...]:
    candidates_by_name = {item.lean_name: item for item in candidates}
    block_order = {
        block.block_id: position for position, block in enumerate(index.blocks)
    }
    selected = [
        decision for decision in decisions if requires_comparison(decision)
    ]
    selected.sort(
        key=lambda decision: (
            min(block_order[block] for block in decision.document_blocks),
            decision.lean_name,
        )
    )
    verdicts = []
    for decision in selected:
        candidate = candidates_by_name.get(decision.lean_name)
        if candidate is None:
            raise ValueError(
                f"relevance decision has no candidate: {decision.lean_name}"
            )
        scoped = replace(candidate, document_blocks=decision.document_blocks)
        try:
            verdicts.append(
                compare_candidate(scoped, index, agent_factory(), budget)
            )
        except BudgetExceeded:
            raise
        except (AgentOutputError, ValueError) as error:
            verdicts.append(
                ComparisonVerdict(
                    candidate.lean_name,
                    scoped.document_blocks,
                    "uncertain",
                    0,
                    (f"Comparison output was invalid: {error}",),
                    (),
                )
            )
    return tuple(verdicts)


def discover_blueprint_candidates(
    index: DocumentIndex,
    dataset: Path,
    blueprint_root: Path,
) -> tuple[Candidate, ...]:
    bindings = load_blueprint_bindings(blueprint_root)
    catalog = load_blueprint_candidates(dataset, bindings)
    return discover_candidates(index, catalog)


def expand_seed_blueprint_files(
    index: DocumentIndex,
    seeds: Sequence[Candidate],
    catalog: Sequence[Candidate],
    bindings: Mapping[str, BlueprintBinding],
    *,
    max_files: int = 2,
) -> tuple[Candidate, ...]:
    if max_files < 1:
        raise ValueError("max_files must be positive")
    selected_files: list[Path] = []
    for seed in sorted(seeds, key=lambda item: (-item.score, item.lean_name)):
        path = bindings[seed.lean_name].tex_path
        if path not in selected_files:
            selected_files.append(path)
        if len(selected_files) == max_files:
            break
    scoped = tuple(
        candidate
        for candidate in catalog
        if bindings[candidate.lean_name].tex_path in selected_files
    )
    return discover_candidates(
        index,
        scoped,
        per_segment_limit=1,
        reverse_min_score=0,
    )


def _upstream_inputs(
    candidate: Candidate,
    index: DocumentIndex,
    dataset: Path,
    dependency_graph: Path,
):
    try:
        declarations = load_upstream_declarations(
            dataset, dependency_graph, candidate.lean_name
        )
    except ValueError as error:
        if "has no proof_upstream_decls" in str(error):
            return (), (), ()
        raise
    # Upstream helpers may be introduced or used outside the narrow segment
    # selected for the top-level theorem, so map them against the whole chapter.
    blocks = tuple(index.blocks)
    batches = batch_declarations(declarations)
    estimates = estimate_upstream_batches(batches, blocks)
    return declarations, blocks, estimates


def preflight_chapter(
    candidates: Sequence[Candidate],
    index: DocumentIndex,
    dataset: Path,
    dependency_graph: Path,
    budget: Budget,
) -> tuple[object, ...]:
    estimates = [estimate_relevance(candidates, index)]
    estimates.extend(estimate_comparison(item, index) for item in candidates)
    shadow = Budget(budget.cap_usd, budget.spent_usd)
    for estimate in estimates:
        shadow.require(estimate)
    return tuple(estimates)


def apply_theorem_proposals(
    proposal_groups: Mapping[str, Sequence[object]],
) -> tuple[tuple[object, ...], tuple[dict[str, str], ...]]:
    applied = []
    failures = []
    for lean_name in sorted(proposal_groups):
        try:
            mutations = plan_blueprint_mutations(
                tuple(proposal_groups[lean_name])
            )
            apply_blueprint_mutations(mutations)
            applied.extend(mutations)
        except Exception as error:
            failures.append(
                {
                    "lean_name": lean_name,
                    "stage": "blueprint",
                    "error": str(error),
                }
            )
    return tuple(applied), tuple(failures)


def run_chapter_match(
    source: Path,
    index: DocumentIndex,
    dataset: Path,
    dependency_graph: Path,
    blueprint_root: Path,
    budget: Budget,
    *,
    dry_run: bool = False,
) -> dict[str, object]:
    bindings = load_blueprint_bindings(blueprint_root)
    catalog = load_blueprint_candidates(dataset, bindings)
    seeds = discover_candidates(index, catalog)
    if not seeds:
        raise ValueError("candidate retrieval returned no blueprint theorems")
    candidates = expand_seed_blueprint_files(
        index, seeds, catalog, bindings
    )
    if dry_run:
        estimates = preflight_chapter(
            candidates, index, dataset, dependency_graph, budget
        )
        estimated_total = budget.spent_usd + sum(
            (item.usd for item in estimates), start=0
        )
        return {
            "source_markdown": str(source.resolve()),
            "candidates": [item.lean_name for item in candidates],
            "seed_candidates": [item.lean_name for item in seeds],
            "estimated_relevance_spend_usd": str(estimates[0].usd),
            "estimated_total_spend_usd": str(estimated_total),
            "dry_run": True,
        }
    relevance_estimate = estimate_relevance(candidates, index)
    relevance_shadow = Budget(budget.cap_usd, budget.spent_usd)
    relevance_shadow.require(relevance_estimate)
    decisions = classify_relevance(
        candidates,
        index,
        ClaudeAgent(model=DEFAULT_MODEL),
        budget,
    )
    selected_names = {
        decision.lean_name
        for decision in decisions
        if requires_comparison(decision)
    }
    comparison_shadow = Budget(budget.cap_usd, budget.spent_usd)
    for candidate in candidates:
        if candidate.lean_name in selected_names:
            comparison_shadow.require(estimate_comparison(candidate, index))
    verdicts = compare_relevant_candidates(
        candidates,
        decisions,
        index,
        lambda: ClaudeAgent(model=COMPARE_MODEL),
        budget,
    )
    by_candidate = {item.lean_name: item for item in candidates}
    document = source.name.removesuffix(".md")
    proposal_groups: dict[str, list[object]] = {}
    propagation_failures = []
    manifests = []
    same_candidates = []
    for verdict in verdicts:
        if verdict.verdict != "same":
            continue
        candidate = replace(
            by_candidate[verdict.lean_name],
            document_blocks=verdict.document_blocks,
        )
        same_candidates.append(candidate)
    upstream_inputs = {}
    upstream_shadow = Budget(budget.cap_usd, budget.spent_usd)
    for candidate in same_candidates:
        try:
            inputs = _upstream_inputs(
                candidate, index, dataset, dependency_graph
            )
        except ValueError as error:
            propagation_failures.append(
                {
                    "lean_name": candidate.lean_name,
                    "stage": "upstream-preflight",
                    "error": str(error),
                }
            )
            inputs = ((), (), ())
        upstream_inputs[candidate.lean_name] = inputs
        for estimate in inputs[2]:
            upstream_shadow.require(estimate)
    for candidate in same_candidates:
        binding = bindings[candidate.lean_name]
        theorem_proposals = proposal_groups.setdefault(
            candidate.lean_name, []
        )
        try:
            theorem_proposals.append(
                SourceProposal(
                    binding.tex_path,
                    candidate.lean_name,
                    ProofSource(document, candidate.document_blocks),
                )
            )
        except ValueError as error:
            propagation_failures.append(
                {
                    "lean_name": candidate.lean_name,
                    "stage": "source-link",
                    "error": str(error),
                }
            )
            proposal_groups.pop(candidate.lean_name, None)
            continue
        declarations, blocks, _ = upstream_inputs[candidate.lean_name]
        if declarations:
            try:
                assignments = map_upstream_batches(
                    declarations,
                    blocks,
                    ClaudeAgent(model=DEFAULT_MODEL),
                    budget,
                )
                manifest = build_manifest(
                    candidate.lean_name,
                    document,
                    index,
                    candidate.proof,
                    declarations,
                    assignments,
                )
                validate_manifest(
                    manifest,
                    index,
                    candidate.proof,
                    declarations,
                    {block.block_id for block in index.blocks},
                )
            except BudgetExceeded:
                raise
            except (AgentOutputError, ValueError) as error:
                propagation_failures.append(
                    {
                        "lean_name": candidate.lean_name,
                        "stage": "upstream",
                        "error": str(error),
                    }
                )
                continue
            manifests.append(manifest)
            theorem_proposals.append(
                StepProposal(
                    binding.tex_path,
                    candidate.lean_name,
                    tuple(
                        ProofStep(
                            assignment.lean_name,
                            assignment.relation,
                            document,
                            assignment.document_blocks,
                        )
                        for assignment in manifest.assignments
                    ),
                )
            )
    mutations, blueprint_failures = apply_theorem_proposals(
        proposal_groups
    )
    propagation_failures.extend(blueprint_failures)
    return {
        "source_markdown": str(source.resolve()),
        "source_fingerprint": index.source_fingerprint,
        "candidates": [asdict(item) for item in candidates],
        "relevance": [asdict(item) for item in decisions],
        "verdicts": [asdict(item) for item in verdicts],
        "upstream_manifests": [asdict(item) for item in manifests],
        "propagation_failures": propagation_failures,
        "estimated_spend_usd": str(budget.spent_usd),
        "propagation_status": (
            "partial" if propagation_failures else "applied"
        ),
        "mutated_files": [str(item.tex_path) for item in mutations],
    }
