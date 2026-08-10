"""LLM-assisted hierarchical routing from a source document to blueprint entries.

The lexical retrieval in :mod:`proofmatch.search` scores token overlap between
document blocks and Lean declaration names/titles. That assumes the paper and
the formalization share vocabulary, which is false in general: a paper may
develop the same mathematics in entirely different notation (Hilbert-space
operators versus symplectic linear algebra, say), and then every lexical score
is noise.

Routing replaces that with a descent down the blueprint's natural tree ---
area, then chapter file, then declaration --- where each level is decided by a
model reading *mathematical content* rather than matching words. Only the
chapters selected at one level have their declarations enumerated at the next,
so the cost scales with the part of the library the document actually touches
instead of with the library's size.
"""

from __future__ import annotations

import re
from dataclasses import dataclass
from pathlib import Path
from collections.abc import Mapping, Sequence

from proofmatch.blueprint import ENV_RE, LEAN_RE
from proofmatch.budget import Budget, StageEstimate, token_cost
from proofmatch.models import Candidate, DocumentIndex


CHAPTER_RE = re.compile(r"\\chapter\{([^}]*)\}")
ENV_TITLE_RE = re.compile(r"\\begin\{(\w+)\}\s*\[([^\]]*)\]")

# Declarations are described to the router by name and title only; a chapter
# with more entries than this is split across calls so no single request grows
# unbounded.
DECLARATIONS_PER_CALL = 120

# How much of a chapter's prose is shown to the chapter-level router.
CHAPTER_OVERVIEW_CHARS = 700

# Router tiers that can carry a citation. `background` means the document relies
# on the result at the cited block without originating it — still a real link to
# the text — so it is compared like the others; `unrelated` asserts the
# declaration is off-topic and is the only tier dropped outright.
CITABLE_TIERS = frozenset({"proves", "states", "background"})


@dataclass(frozen=True)
class ChapterNode:
    """One blueprint chapter file, summarized for routing."""

    tex_path: Path
    area: str
    title: str
    overview: str
    lean_names: tuple[str, ...]
    entry_titles: tuple[str, ...]

    @property
    def key(self) -> str:
        return str(self.tex_path)


@dataclass(frozen=True)
class RoutedDeclaration:
    """A declaration the router believes the document is a source for."""

    lean_name: str
    tier: str
    document_blocks: tuple[str, ...]
    rationale: str


def _strip_tex(text: str) -> str:
    without_comments = re.sub(r"(?<!\\)%.*", "", text)
    # Longest alternatives first: `lean` would otherwise match inside
    # `leanok` and leave a stray "ok" in the informal text.
    without_commands = re.sub(
        r"\\(leanok|lean|uses|label|difficulty|proofsource|statementsource|proofstep)"
        r"(\{[^}]*\})*",
        "",
        without_comments,
    )
    return re.sub(r"\s+", " ", without_commands).strip()


def _chapter_overview(tex: str) -> str:
    """Prose before the first environment, which is where chapters explain themselves."""
    head = ENV_RE.split(tex)[0] if ENV_RE.search(tex) else tex
    body = CHAPTER_RE.sub("", head)
    body = re.sub(r"\\section\{([^}]*)\}", r"\1. ", body)
    body = re.sub(r"^%+.*$", "", body, flags=re.MULTILINE)
    return _strip_tex(body)[:CHAPTER_OVERVIEW_CHARS]


def build_blueprint_tree(blueprint_root: Path) -> tuple[ChapterNode, ...]:
    """Summarize every blueprint chapter file that carries Lean bindings."""
    nodes = []
    for path in sorted(blueprint_root.rglob("*.tex")):
        text = path.read_text(encoding="utf-8", errors="ignore")
        lean_names = []
        for environment in ENV_RE.findall(text):
            for match in LEAN_RE.finditer(environment):
                for raw_name in match.group(1).split(","):
                    name = raw_name.strip()
                    if name and not name.startswith("["):
                        lean_names.append(name)
        if not lean_names:
            continue
        relative = path.relative_to(blueprint_root)
        chapter_match = CHAPTER_RE.search(text)
        title = (
            chapter_match.group(1).strip()
            if chapter_match
            else relative.stem
        )
        nodes.append(
            ChapterNode(
                tex_path=path,
                area=relative.parts[0] if len(relative.parts) > 1 else "",
                title=title,
                overview=_chapter_overview(text),
                lean_names=tuple(lean_names),
                entry_titles=tuple(
                    title.strip()
                    for _, title in ENV_TITLE_RE.findall(text)
                    if title.strip()
                )[:40],
            )
        )
    return tuple(nodes)


def document_profile(
    index: DocumentIndex,
    *,
    max_blocks: int = 200,
    excerpt_chars: int = 700,
) -> dict:
    """A content-bearing description of the source document, block by block.

    Every block is offered to the router. Block ``kind`` is inferred from a
    first-line heuristic and is therefore unreliable --- a paragraph that
    states a numbered theorem mid-flow is classified as prose --- so filtering
    the profile by kind would hide exactly the statements routing must see. If
    a document exceeds ``max_blocks``, labelled claims are kept first and the
    remainder fills in document order, and the shortfall is reported so the
    truncation is never silent.
    """
    blocks = [block for block in index.blocks if block.markdown.strip()]

    def summarize(block) -> dict:
        return {
            "block_id": block.block_id,
            "kind": block.kind,
            "title": block.title,
            "text": block.markdown.strip()[:excerpt_chars],
        }

    if len(blocks) <= max_blocks:
        selected = blocks
        omitted = 0
    else:
        labelled = [
            block
            for block in blocks
            if block.kind in {"theorem", "definition", "proof"}
        ]
        keep = {block.block_id for block in labelled[:max_blocks]}
        for block in blocks:
            if len(keep) >= max_blocks:
                break
            keep.add(block.block_id)
        selected = [block for block in blocks if block.block_id in keep]
        omitted = len(blocks) - len(selected)
    return {
        "headings": [
            block.markdown.strip()[:excerpt_chars]
            for block in index.blocks
            if block.kind == "heading"
        ][:40],
        "blocks": [summarize(block) for block in selected],
        "omitted_block_count": omitted,
    }


ENV_OPEN_RE = re.compile(r"\\begin\{(\w+)\}\s*(?:\[([^\]]*)\])?")


def load_blueprint_entries(blueprint_root: Path) -> dict[str, Candidate]:
    """Build candidates from the blueprint itself rather than the proof dataset.

    :func:`proofmatch.catalog.load_blueprint_candidates` sources candidates from
    ``tcslib_theorems.jsonl``, which carries only theorems and lemmas from
    modules that compiled. Definitions are therefore absent, as is every
    declaration of a module that currently fails to build --- and those are
    exactly the entries a foundational paper is most often the source *of*.

    A statement-level citation needs only the informal statement, which the
    blueprint already holds, so entries are read straight from the ``.tex``.
    The resulting candidates carry no proof text and cannot support proof
    comparison; callers that need a proof should prefer the dataset candidate
    of the same name.
    """
    entries: dict[str, Candidate] = {}
    for path in sorted(blueprint_root.rglob("*.tex")):
        text = path.read_text(encoding="utf-8", errors="ignore")
        for environment in ENV_RE.findall(text):
            names = [
                name.strip()
                for match in LEAN_RE.finditer(environment)
                for name in match.group(1).split(",")
                if name.strip() and not name.strip().startswith("[")
            ]
            if not names:
                continue
            open_match = ENV_OPEN_RE.search(environment)
            title = (open_match.group(2) or "").strip() if open_match else ""
            body = ENV_OPEN_RE.sub("", environment, count=1)
            body = re.sub(r"\\end\{\w+\}\s*$", "", body)
            statement = _strip_tex(body)
            for name in names:
                entries[name] = Candidate(
                    lean_name=name,
                    title=title or name,
                    source_module=str(path.relative_to(blueprint_root)),
                    statement=f"{title}. {statement}" if title else statement,
                    formal_statement="",
                    proof="",
                    proof_tokens=0,
                    score=0.0,
                    document_blocks=(),
                )
    return entries


def merge_catalogs(
    dataset_candidates: Mapping[str, Candidate],
    blueprint_entries: Mapping[str, Candidate],
) -> dict[str, Candidate]:
    """Dataset candidates win (they carry proofs); blueprint entries fill gaps."""
    merged = dict(blueprint_entries)
    merged.update(dataset_candidates)
    return merged


def _chapter_payload(nodes: Sequence[ChapterNode]) -> list[dict]:
    return [
        {
            "chapter_key": node.key,
            "area": node.area,
            "title": node.title,
            "overview": node.overview,
            "sample_entries": list(node.entry_titles[:18]),
            "declaration_count": len(node.lean_names),
        }
        for node in nodes
    ]


def estimate_routing(
    nodes: Sequence[ChapterNode],
    profile: Mapping[str, object],
    model: str,
) -> StageEstimate:
    payload_chars = sum(
        len(node.title) + len(node.overview) + sum(map(len, node.entry_titles))
        for node in nodes
    )
    profile_chars = len(str(profile))
    input_tokens = (payload_chars + profile_chars) // 4 + 1_000
    output_tokens = 60 * max(len(nodes), 1)
    return StageEstimate(
        name="chapter routing",
        input_tokens=input_tokens,
        output_tokens=output_tokens,
        usd=token_cost(model, input_tokens, output_tokens),
    )


def route_chapters(
    index: DocumentIndex,
    nodes: Sequence[ChapterNode],
    agent,
    budget: Budget,
    *,
    model: str,
    max_chapters: int = 8,
) -> tuple[ChapterNode, ...]:
    """Pick the blueprint chapters whose mathematics the document covers."""
    if not nodes:
        return ()
    profile = document_profile(index)
    budget.require(estimate_routing(nodes, profile, model))
    output = agent.run(
        "route_chapters",
        {"document": profile, "chapters": _chapter_payload(nodes)},
    )
    by_key = {node.key: node for node in nodes}
    selected: list[tuple[float, ChapterNode]] = []
    for row in output.get("chapters", []):
        if not isinstance(row, dict):
            continue
        node = by_key.get(str(row.get("chapter_key") or ""))
        if node is None or not bool(row.get("selected")):
            continue
        selected.append((float(row.get("confidence") or 0.0), node))
    selected.sort(key=lambda item: (-item[0], item[1].key))
    return tuple(node for _, node in selected[:max_chapters])


def _declaration_payload(
    node: ChapterNode,
    candidates: Mapping[str, Candidate],
) -> list[dict]:
    rows = []
    for name in node.lean_names:
        candidate = candidates.get(name)
        if candidate is None:
            continue
        rows.append(
            {
                "lean_name": name,
                "title": candidate.title,
                "statement": candidate.statement[:600],
            }
        )
    return rows


def estimate_declaration_routing(
    rows: Sequence[Mapping[str, object]],
    profile: Mapping[str, object],
    model: str,
) -> StageEstimate:
    input_tokens = (len(str(rows)) + len(str(profile))) // 4 + 500
    output_tokens = 80 * max(len(rows), 1)
    return StageEstimate(
        name="declaration routing",
        input_tokens=input_tokens,
        output_tokens=output_tokens,
        usd=token_cost(model, input_tokens, output_tokens),
    )


def route_declarations(
    index: DocumentIndex,
    node: ChapterNode,
    catalog: Mapping[str, Candidate],
    agent_factory,
    budget: Budget,
    *,
    model: str,
) -> tuple[tuple[RoutedDeclaration, ...], tuple[RoutedDeclaration, ...]]:
    """Assign each declaration of one chapter a citation tier for this document.

    Returns the citable declarations and the rejected ones, so a chapter that
    routes to nothing can be told apart from one that was never examined.
    """
    profile = document_profile(index)
    rows = _declaration_payload(node, catalog)
    routed: list[RoutedDeclaration] = []
    rejected: list[RoutedDeclaration] = []
    valid_blocks = {block.block_id for block in index.blocks}
    for start in range(0, len(rows), DECLARATIONS_PER_CALL):
        chunk = rows[start : start + DECLARATIONS_PER_CALL]
        budget.require(estimate_declaration_routing(chunk, profile, model))
        output = agent_factory().run(
            "route_declarations",
            {
                "document": profile,
                "chapter_title": node.title,
                "declarations": chunk,
            },
        )
        for row in output.get("declarations", []):
            if not isinstance(row, dict):
                continue
            tier = str(row.get("tier") or "")
            blocks = tuple(
                str(block)
                for block in (row.get("document_blocks") or [])
                if str(block) in valid_blocks
            )
            declaration = RoutedDeclaration(
                lean_name=str(row.get("lean_name") or ""),
                tier=tier,
                document_blocks=blocks,
                rationale=str(row.get("rationale") or ""),
            )
            # A citable tier with no usable block citation cannot be compared;
            # keep it on the rejected list so it is diagnosable rather than
            # vanishing.
            #
            # `background` counts as citable: the document relies on the result
            # at the cited block even though it does not originate it, which is
            # a real relationship worth recording. Excluding it here made the
            # tier unreachable and silently lost 85 of 86 uncited
            # Hypercontractivity declarations. Only `unrelated` is dropped.
            if tier in CITABLE_TIERS and blocks:
                routed.append(declaration)
            else:
                rejected.append(declaration)
    return (
        tuple(item for item in routed if item.lean_name in catalog),
        tuple(rejected),
    )
