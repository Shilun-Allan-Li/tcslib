from __future__ import annotations

from collections.abc import Callable, Mapping, Sequence
from dataclasses import asdict, replace
from pathlib import Path
from threading import Event
from concurrent.futures import CancelledError

from proofmatch.agents import (
    COMPARE_MODEL,
    DEFAULT_MODEL,
    AgentInvocationError,
    AgentOutputError,
    ClaudeAgent,
)
from proofmatch.blueprint import (
    ProofSource,
    blueprint_write_lock,
    ProofStep,
    SourceProposal,
    StepProposal,
    apply_blueprint_mutations,
    plan_blueprint_mutations,
)
from proofmatch.budget import Budget, BudgetExceeded
from proofmatch.parallel import bounded_map
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
from proofmatch.routing import (
    RoutedDeclaration,
    build_blueprint_tree,
    load_blueprint_entries,
    merge_catalogs,
    route_chapters,
    route_declarations,
)
from proofmatch.search import discover_candidates
from proofmatch.upstream import (
    batch_declarations,
    build_manifest,
    estimate_upstream_batches,
    load_upstream_declarations,
    map_upstream_batches,
    validate_manifest,
    UpstreamDeclarationLoader,
)


def compare_relevant_candidates(
    candidates: Sequence[Candidate],
    decisions: Sequence[RelevanceDecision],
    index: DocumentIndex,
    agent_factory: Callable[[], object],
    budget: Budget,
    *,
    jobs: int = 1,
    cache_dir: Path | None = None,
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
    stop = Event()
    def compare_one(decision):
        candidate = candidates_by_name.get(decision.lean_name)
        if candidate is None:
            raise ValueError(f"relevance decision has no candidate: {decision.lean_name}")
        scoped = replace(candidate, document_blocks=decision.document_blocks)
        options = {"cache_dir": cache_dir, "stop_event": stop} if cache_dir is not None else {}
        return compare_candidate(scoped, index, agent_factory(), budget, **options)
    results = bounded_map(compare_one, selected, jobs, stop_event=stop, return_exceptions=True,
                          stop_on=(BudgetExceeded, AgentInvocationError))
    halt = next((result for result in results if isinstance(result, (BudgetExceeded, AgentInvocationError))),
                "dispatch cancelled")
    verdicts = []
    for decision, result in zip(selected, results):
        if isinstance(result, (BudgetExceeded, AgentInvocationError, CancelledError)):
            verdicts.append(ComparisonVerdict(decision.lean_name, decision.document_blocks,
                            "uncertain", 0, (f"Comparison skipped: {halt}",), ()))
        elif isinstance(result, (AgentOutputError, ValueError)):
            verdicts.append(ComparisonVerdict(decision.lean_name, decision.document_blocks,
                            "uncertain", 0, (f"Comparison output was invalid: {result}",), ()))
        elif isinstance(result, Exception):
            raise result
        else:
            verdicts.append(result)
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
    *,
    loader=None,
):
    try:
        declarations = loader.load(candidate.lean_name) if loader is not None else load_upstream_declarations(
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


def map_upstream_candidates(candidates, inputs, document, index, budget, *, jobs=1,
                            cache_dir=None, agent_factory=None):
    """Map independent targets concurrently; mutation stays in the caller."""
    factory = agent_factory or (lambda: ClaudeAgent(model=DEFAULT_MODEL))
    stop = Event()

    def map_candidate(candidate):
        declarations, blocks, _ = inputs[candidate.lean_name]
        assignments = map_upstream_batches(
            declarations, blocks, factory(), budget, cache_dir=cache_dir,
            stop_event=stop, label=candidate.lean_name)
        manifest = build_manifest(candidate.lean_name, document, index,
                                  candidate.proof, declarations, assignments)
        validate_manifest(manifest, index, candidate.proof, declarations,
                          {block.block_id for block in index.blocks})
        return manifest

    return bounded_map(map_candidate, candidates, jobs, stop_event=stop,
                       return_exceptions=True, stop_on=(BudgetExceeded, AgentInvocationError))


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
            # plan reads the .tex and apply writes it back, so concurrent matches on
            # documents citing the same chapter must not interleave here.
            with blueprint_write_lock():
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


#: Routing tiers map onto the relevance statuses the comparison stage already
#: understands: a document that argues the result deserves a full proof
#: comparison, one that merely states it is compared as a statement match.
#:
#: `background` is included deliberately. It used to be absent, which made the
#: tier a dead end *by construction*: any declaration the router judged as
#: relied-upon-but-not-originated was dropped before comparison and could never
#: receive a citation, no matter what the text said. That single gap accounted
#: for 85 of the 86 uncited Hypercontractivity declarations — with rationales
#: like "the Paley-Zygmund inequality is standard probability the document
#: invokes but does not originate" and "avgLast is the operator E_n f whose
#: definition comes from Chapter 2". Those are real, citable relationships to
#: the text. Routing them as `uncertain` sends them to the comparer, which then
#: decides honestly: `method_divergence` gives a `\statementsource`,
#: `not_in_text` queues an informalization. Only `unrelated` stays dropped,
#: since that tier asserts the declaration is off-topic.
#:
#: This widens the comparison set substantially, so a `background`-heavy
#: document costs materially more to match than it did before.
_TIER_STATUS = {
    "proves": "relevant",
    "states": "uncertain",
    "background": "uncertain",
}

# Verdicts that earn a `\proofsource`.
#
# `same` alone is far too strict in practice. Over 270 comparisons the comparer
# returned `same` exactly zero times, while emitting `uncertain` at 0.90+ for
# proofs whose only recorded difference was cosmetic — a generalised constant
# ("Lean generalises rho = 1/sqrt 3 to any rho^2 <= 1/3; method is unchanged"),
# or renamed variables (`Dn`/`En` versus `diffLast`/`avgLast`). The prompt already
# tells the comparer to call those `same`, and it still does not, so the bar is
# relaxed here rather than by asking the prompt again.
#
# A comparer that cannot distinguish "renamed" from "different" is not a reliable
# discriminator, so we do not treat its hedging as evidence against a match.
# Excluded are only the verdicts that assert a *specific* negative finding:
# `different` (wrong anchor), `not_in_text` (absent from the document), and
# `method_divergence` (the method genuinely differs — that is a statement-level
# citation, handled separately below).
PROOF_CITATION_VERDICTS = frozenset({"same", "uncertain"})
# A floor of 0.0 was tried and audited: it admitted 45 citations at confidence
# *exactly* zero, 31 of which anchored k-ary (ZMod k) statements to boolean-only
# sources — e.g. `ZkBLR.re_fourier_coeff_upper_bound`, whose (1 - cos(2*pi/k))
# factor appears nowhere in the cited boolean BLR block. Zero confidence is the
# comparer declining to judge at all, which is different from hedging over
# packaging, so it must not clear the bar.
PROOF_CITATION_MIN_CONFIDENCE = 0.5


def accepts_proof_citation(
    verdict,
    *,
    min_confidence: float = PROOF_CITATION_MIN_CONFIDENCE,
) -> bool:
    """Whether a comparison verdict is strong enough for a `\\proofsource`."""
    if verdict.verdict not in PROOF_CITATION_VERDICTS:
        return False
    return (verdict.confidence or 0.0) >= min_confidence


def routed_candidates(
    index: DocumentIndex,
    catalog: Sequence[Candidate],
    blueprint_root: Path,
    budget: Budget,
    *,
    max_chapters: int | None = None,
    jobs: int = 1,
) -> tuple[
    tuple[Candidate, ...],
    tuple[RelevanceDecision, ...],
    tuple[RoutedDeclaration, ...],
    dict,
]:
    """Select candidates by descending the blueprint tree with a model.

    Returns the candidates to compare, the equivalent relevance decisions, and
    a report of which chapters were chosen and why.
    """
    # Candidates come from the dataset where a proof exists and from the
    # blueprint otherwise, so definitions and declarations of modules that do
    # not currently compile can still receive statement-level citations.
    dataset_by_name = {candidate.lean_name: candidate for candidate in catalog}
    by_name = merge_catalogs(
        dataset_by_name, load_blueprint_entries(blueprint_root)
    )
    nodes = build_blueprint_tree(blueprint_root)
    chapters = route_chapters(
        index,
        nodes,
        ClaudeAgent(model=DEFAULT_MODEL),
        budget,
        model=DEFAULT_MODEL,
        max_chapters=max_chapters,
        jobs=jobs,
        cache_dir=blueprint_root.resolve().parents[2] / ".proofmatch-work" / "routing",
    )
    candidates: list[Candidate] = []
    decisions: list[RelevanceDecision] = []
    statement_only: list[RoutedDeclaration] = []
    chapter_report = []
    stop = Event()
    def route_node(node):
        return route_declarations(
            index, node, by_name, lambda: ClaudeAgent(model=DEFAULT_MODEL), budget,
            model=DEFAULT_MODEL,
            cache_dir=blueprint_root.resolve().parents[2] / ".proofmatch-work" / "routing",
            stop_event=stop)
    routed_nodes = bounded_map(route_node, chapters, jobs, stop_event=stop)
    for node, (routed, rejected) in zip(chapters, routed_nodes):
        # A chapter whose module is absent from the dataset contributes no
        # comparable declarations; record it so the gap is visible rather
        # than looking like a routing miss.
        in_catalog = sum(1 for name in node.lean_names if name in by_name)
        tier_counts: dict[str, int] = {}
        for item in (*routed, *rejected):
            tier_counts[item.tier] = tier_counts.get(item.tier, 0) + 1
        chapter_report.append(
            {
                "chapter": str(node.tex_path),
                "declarations": len(node.lean_names),
                "in_dataset": in_catalog,
                "routed": len(routed),
                "tiers": tier_counts,
                "rejected": [
                    {
                        "lean_name": item.lean_name,
                        "tier": item.tier,
                        "rationale": item.rationale,
                    }
                    for item in rejected
                ],
            }
        )
        for item in routed:
            candidate = by_name.get(item.lean_name)
            if candidate is None:
                continue
            if not candidate.proof:
                # Blueprint-only entry: there is no Lean proof to compare
                # against, so the router's statement match is the decision.
                statement_only.append(item)
                continue
            candidates.append(
                replace(candidate, document_blocks=item.document_blocks)
            )
            decisions.append(
                RelevanceDecision(
                    lean_name=item.lean_name,
                    status=_TIER_STATUS[item.tier],
                    document_blocks=item.document_blocks,
                    rationale=item.rationale,
                )
            )
    return (
        tuple(candidates),
        tuple(decisions),
        tuple(statement_only),
        {"chapters": chapter_report},
    )


def run_chapter_match(
    source: Path,
    index: DocumentIndex,
    dataset: Path,
    dependency_graph: Path,
    blueprint_root: Path,
    budget: Budget,
    *,
    dry_run: bool = False,
    use_routing: bool = True,
    jobs: int = 1,
) -> dict[str, object]:
    if not dry_run:
        print(f"Citation matching: up to {jobs} concurrent model requests per phase", flush=True)
    bindings = load_blueprint_bindings(blueprint_root)
    catalog = load_blueprint_candidates(dataset, bindings)
    routing_report: dict = {}
    if use_routing and not dry_run:
        candidates, decisions, statement_only, routing_report = routed_candidates(
            index, catalog, blueprint_root, budget, jobs=jobs
        )
        if not candidates and not statement_only:
            raise ValueError("routing selected no citable declarations")
        return _compare_and_propagate(
            source,
            index,
            candidates,
            decisions,
            bindings,
            dataset,
            dependency_graph,
            budget,
            routing_report=routing_report,
            direct_statements=statement_only,
            jobs=jobs,
            comparison_cache=blueprint_root.resolve().parents[2] / ".proofmatch-work" / "comparisons",
        )
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
    return _compare_and_propagate(
        source,
        index,
        candidates,
        decisions,
        bindings,
        dataset,
        dependency_graph,
        budget,
        routing_report=routing_report,
        jobs=jobs,
        comparison_cache=blueprint_root.resolve().parents[2] / ".proofmatch-work" / "comparisons",
    )


def _compare_and_propagate(
    source: Path,
    index: DocumentIndex,
    candidates: Sequence[Candidate],
    decisions: Sequence[RelevanceDecision],
    bindings: Mapping[str, BlueprintBinding],
    dataset: Path,
    dependency_graph: Path,
    budget: Budget,
    *,
    routing_report: Mapping[str, object] | None = None,
    direct_statements: Sequence[RoutedDeclaration] = (),
    jobs: int = 1,
    comparison_cache: Path | None = None,
) -> dict[str, object]:
    """Compare the selected candidates and write approved citations back."""
    selected_names = {
        decision.lean_name
        for decision in decisions
        if requires_comparison(decision)
    }
    comparison_shadow = Budget(budget.cap_usd, budget.spent_usd)
    try:
        for candidate in candidates:
            if candidate.lean_name in selected_names:
                comparison_shadow.require(estimate_comparison(candidate, index))
    except BudgetExceeded as error:
        # Advisory only: comparisons run in document order until the budget is
        # spent, and the rest are recorded as skipped by the compare loop.
        print(f"Comparison set exceeds remaining budget; will cap: {error}")
    verdicts = compare_relevant_candidates(
        candidates,
        decisions,
        index,
        lambda: ClaudeAgent(model=COMPARE_MODEL),
        budget,
        jobs=jobs,
        cache_dir=comparison_cache,
    )
    by_candidate = {item.lean_name: item for item in candidates}
    document = source.name.removesuffix(".md")
    proposal_groups: dict[str, list[object]] = {}
    propagation_failures = []
    manifests = []
    same_candidates = []
    relaxed_accepted = []
    for verdict in verdicts:
        if not accepts_proof_citation(verdict):
            continue
        if verdict.verdict != "same":
            relaxed_accepted.append(
                {
                    "lean_name": verdict.lean_name,
                    "verdict": verdict.verdict,
                    "confidence": verdict.confidence,
                    "differences": list(verdict.differences),
                }
            )
        candidate = replace(
            by_candidate[verdict.lean_name],
            document_blocks=verdict.document_blocks,
        )
        same_candidates.append(candidate)
    if relaxed_accepted:
        print(
            f"Accepted {len(relaxed_accepted)} proof citation(s) under the relaxed "
            f"rule (verdict != 'same'); listed in chapter_review.relaxed_proof_sources"
        )
    # Statement-level citations: the document states the result but the Lean
    # proof takes a different route (or fills in a cited black box).
    statement_verdicts = [
        verdict for verdict in verdicts if verdict.verdict == "method_divergence"
    ]
    # Lemmas the document never engages with (too granular, or bare exercises):
    # queued for later LLM informalization of the Lean proofs into .md files.
    informalize = [
        {
            "lean_name": verdict.lean_name,
            "confidence": verdict.confidence,
            "note": (
                verdict.differences
                or ("statement not present in the document",)
            )[0],
            "nearest_blocks": list(verdict.document_blocks),
        }
        for verdict in verdicts
        if verdict.verdict == "not_in_text"
    ]
    upstream_inputs = {}
    print(f'Upstream preflight: loading dependency metadata for {len(same_candidates)} targets once', flush=True)
    upstream_loader = UpstreamDeclarationLoader(dataset, dependency_graph,
                        (candidate.lean_name for candidate in same_candidates)) if same_candidates else None
    upstream_shadow = Budget(budget.cap_usd, budget.spent_usd)
    for candidate in same_candidates:
        try:
            inputs = _upstream_inputs(
                candidate, index, dataset, dependency_graph, loader=upstream_loader
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
        try:
            for estimate in inputs[2]:
                upstream_shadow.require(estimate)
        except BudgetExceeded as error:
            # Advisory only: upstream mapping is optional enrichment and is
            # capped per-candidate below; the source proposals are free.
            print(f"Upstream mapping may exceed remaining budget: {error}")
    mapping_candidates = []
    for candidate in same_candidates:
        binding = bindings[candidate.lean_name]
        theorem_proposals = proposal_groups.setdefault(candidate.lean_name, [])
        try:
            theorem_proposals.append(SourceProposal(
                binding.tex_path, candidate.lean_name,
                ProofSource(document, candidate.document_blocks)))
        except ValueError as error:
            propagation_failures.append({"lean_name": candidate.lean_name,
                                         "stage": "source-link", "error": str(error)})
            proposal_groups.pop(candidate.lean_name, None)
            continue
        if upstream_inputs[candidate.lean_name][0]:
            mapping_candidates.append(candidate)
    upstream_cache = comparison_cache.parent / "upstream" if comparison_cache is not None else None
    print(f'Upstream mapping: {len(mapping_candidates)} targets, up to {jobs} workers', flush=True)
    mapped = map_upstream_candidates(mapping_candidates, upstream_inputs, document,
                                     index, budget, jobs=jobs, cache_dir=upstream_cache)
    for candidate, result in zip(mapping_candidates, mapped, strict=True):
        if isinstance(result, Exception):
            stage = ("upstream-agent-unavailable" if isinstance(result, AgentInvocationError)
                     else "upstream-budget" if isinstance(result, BudgetExceeded)
                     else "upstream-not-dispatched" if isinstance(result, CancelledError)
                     else "upstream")
            propagation_failures.append({"lean_name": candidate.lean_name,
                                         "stage": stage, "error": str(result)})
            continue
        manifests.append(result)
        proposal_groups[candidate.lean_name].append(StepProposal(
            bindings[candidate.lean_name].tex_path, candidate.lean_name,
            tuple(ProofStep(assignment.lean_name, assignment.relation, document,
                            assignment.document_blocks)
                  for assignment in result.assignments)))
    # Router-decided statement citations for entries with no comparable proof
    # (definitions, and declarations of modules absent from the dataset).
    for statement in direct_statements:
        binding = bindings.get(statement.lean_name)
        if binding is None:
            propagation_failures.append(
                {
                    "lean_name": statement.lean_name,
                    "stage": "statement-source",
                    "error": "no blueprint binding",
                }
            )
            continue
        try:
            proposal_groups.setdefault(statement.lean_name, []).append(
                SourceProposal(
                    binding.tex_path,
                    statement.lean_name,
                    ProofSource(document, statement.document_blocks),
                    macro="statementsource",
                )
            )
        except ValueError as error:
            propagation_failures.append(
                {
                    "lean_name": statement.lean_name,
                    "stage": "statement-source",
                    "error": str(error),
                }
            )
    for verdict in statement_verdicts:
        binding = bindings.get(verdict.lean_name)
        if binding is None:
            continue
        try:
            proposal_groups.setdefault(verdict.lean_name, []).append(
                SourceProposal(
                    binding.tex_path,
                    verdict.lean_name,
                    ProofSource(document, verdict.document_blocks),
                    macro="statementsource",
                )
            )
        except ValueError as error:
            propagation_failures.append(
                {
                    "lean_name": verdict.lean_name,
                    "stage": "statement-source",
                    "error": str(error),
                }
            )
    mutations, blueprint_failures = apply_theorem_proposals(
        proposal_groups
    )
    propagation_failures.extend(blueprint_failures)
    return {
        "source_markdown": str(source.resolve()),
        "source_fingerprint": index.source_fingerprint,
        "routing": dict(routing_report or {}),
        "direct_statements": [asdict(item) for item in direct_statements],
        "candidates": [asdict(item) for item in candidates],
        "relevance": [asdict(item) for item in decisions],
        "verdicts": [asdict(item) for item in verdicts],
        # Proof citations admitted by the relaxed rule rather than a `same`
        # verdict, kept separately so they can be audited or reverted.
        "relaxed_proof_sources": relaxed_accepted,
        "informalize": informalize,
        "upstream_manifests": [asdict(item) for item in manifests],
        "propagation_failures": propagation_failures,
        "estimated_spend_usd": str(budget.spent_usd),
        "propagation_status": (
            "partial" if propagation_failures else "applied"
        ),
        "mutated_files": [str(item.tex_path) for item in mutations],
    }
