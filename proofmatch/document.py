from __future__ import annotations

import re
import hashlib
import json
import os
import tempfile
from concurrent.futures import ThreadPoolExecutor
from threading import Event
from collections.abc import Callable
from decimal import Decimal
from pathlib import Path

from proofmatch.agents import DEFAULT_MODEL, ClaudeAgent
from proofmatch.budget import Budget, StageEstimate, estimate_cleanup, token_cost
from proofmatch.extraction import render_page
from proofmatch.models import DocumentAmbiguity, DocumentBlock, DocumentIndex


FINGERPRINT_RE = re.compile(r"<!-- source-pdf-sha256: ([0-9a-f]{12,64}) -->")
PAGE_RE = re.compile(r"<!-- pdf-page: (\d+) -->")
ANCHOR_RE = re.compile(r'<a id="(pdf-[0-9a-f]{12}-p(\d{3})-b(\d{3}))"></a>')
PROVENANCE_RE = re.compile(
    r"<!-- pdf-source: page=(\d+); block=(\d+); confidence=([0-9.]+) -->"
)

# Pages per cleanup call. Small chunks keep each response short enough to
# stay under the API's verbatim-reproduction content filter and make
# extraction restartable per chunk.
CLEANUP_PAGES_PER_CALL = 3
VISUAL_VALIDATION_PAGES_PER_CALL = 8


def stable_block_id(source_fingerprint: str, page: int, sequence: int) -> str:
    if len(source_fingerprint) < 12:
        raise ValueError("source fingerprint must contain at least 12 characters")
    if page < 1 or sequence < 1:
        raise ValueError("page and sequence must be positive")
    return f"pdf-{source_fingerprint[:12]}-p{page:03d}-b{sequence:03d}"


def _raw_payload(raw_markdown: str) -> tuple[str, list[dict[str, object]]]:
    fingerprint_match = FINGERPRINT_RE.search(raw_markdown)
    if not fingerprint_match:
        raise ValueError("raw Markdown lacks source PDF fingerprint")
    matches = list(PAGE_RE.finditer(raw_markdown))
    if not matches:
        raise ValueError("raw Markdown contains no PDF page markers")
    pages = []
    for index, match in enumerate(matches):
        end = matches[index + 1].start() if index + 1 < len(matches) else len(raw_markdown)
        pages.append(
            {
                "page": int(match.group(1)),
                "raw_text": raw_markdown[match.end() : end].strip(),
            }
        )
    return fingerprint_match.group(1), pages


def _blocks_from_output(
    source_fingerprint: str,
    pages: set[int],
    value: dict[str, object],
) -> list[DocumentBlock]:
    raw_blocks = value.get("blocks")
    if not isinstance(raw_blocks, list):
        raise ValueError("cleanup output must contain a blocks array")
    blocks = []
    seen: set[tuple[int, int]] = set()
    for raw in raw_blocks:
        if not isinstance(raw, dict):
            raise ValueError("cleanup block must be an object")
        page = int(raw["page"])
        sequence = int(raw["sequence"])
        key = (page, sequence)
        if page not in pages:
            raise ValueError(f"cleanup block cites nonexistent page {page}")
        if key in seen:
            raise ValueError(f"duplicate block at page {page}, sequence {sequence}")
        seen.add(key)
        blocks.append(
            DocumentBlock(
                block_id=stable_block_id(source_fingerprint, page, sequence),
                page=page,
                sequence=sequence,
                kind=str(raw["kind"]),
                title=str(raw["title"]),
                markdown=str(raw["markdown"]).strip(),
                confidence=float(raw["confidence"]),
            )
        )
    return blocks


def _ambiguities_from_output(
    source_fingerprint: str,
    known: set[tuple[int, int]],
    value: dict[str, object],
) -> list[tuple[DocumentAmbiguity, int, int]]:
    raw_ambiguities = value.get("ambiguities")
    if not isinstance(raw_ambiguities, list):
        raise ValueError("cleanup output must contain an ambiguities array")
    ambiguities = []
    unresolved = []
    for raw in raw_ambiguities:
        if not isinstance(raw, dict):
            raise ValueError("cleanup ambiguity must be an object")
        page, sequence = int(raw["page"]), int(raw["sequence"])
        if (page, sequence) not in known:
            # The model flagged a block it never emitted — most often a page it
            # could not parse at all. There is nothing to visually validate, so
            # the reference is unactionable rather than fatal; the caller
            # reports it so the page can still be checked by hand.
            unresolved.append((page, sequence, str(raw.get("reason", ""))))
            continue
        ambiguities.append(
            (
                DocumentAmbiguity(
                    stable_block_id(source_fingerprint, page, sequence),
                    str(raw["reason"]),
                    False,
                ),
                page,
                sequence,
            )
        )
    return ambiguities, unresolved


def _render_markdown(index: DocumentIndex) -> str:
    lines = [
        "<!-- generated-by: proofmatch Claude repair -->",
        f"<!-- source-pdf-sha256: {index.source_fingerprint} -->",
        "",
    ]
    for block in index.blocks:
        lines.extend(
            [
                f'<a id="{block.block_id}"></a>',
                (
                    f"<!-- pdf-source: page={block.page}; block={block.sequence}; "
                    f"confidence={block.confidence:.2f} -->"
                ),
                block.markdown,
                "",
            ]
        )
    return "\n".join(lines).rstrip() + "\n"


def parse_validated_markdown(path: Path) -> DocumentIndex:
    text = path.read_text(encoding="utf-8")
    fingerprint_match = FINGERPRINT_RE.search(text)
    if not fingerprint_match:
        raise ValueError("validated Markdown lacks source PDF fingerprint")
    anchors = list(ANCHOR_RE.finditer(text))
    if not anchors:
        raise ValueError("validated Markdown contains no proofmatch block anchors")
    blocks = []
    for index, anchor in enumerate(anchors):
        end = anchors[index + 1].start() if index + 1 < len(anchors) else len(text)
        body = text[anchor.end() : end].strip()
        provenance = PROVENANCE_RE.search(body)
        if not provenance:
            raise ValueError(f"{anchor.group(1)} lacks PDF provenance")
        page, sequence = int(provenance.group(1)), int(provenance.group(2))
        if page != int(anchor.group(2)) or sequence != int(anchor.group(3)):
            raise ValueError(f"{anchor.group(1)} has inconsistent provenance")
        markdown = PROVENANCE_RE.sub("", body, count=1).strip()
        first_line = markdown.splitlines()[0] if markdown else ""
        if first_line.startswith("#"):
            title = first_line.lstrip("# ").strip()
        elif first_line.startswith("**") and "**" in first_line[2:]:
            title = first_line[2 : first_line.index("**", 2)].strip(" .")
        else:
            title = ""
        if first_line.startswith("#"):
            kind = "heading"
        else:
            kind = "prose"
            lowered = title.casefold()
            for named_kind in ("definition", "theorem", "lemma", "proof"):
                if named_kind in lowered:
                    kind = "theorem" if named_kind == "lemma" else named_kind
                    break
        blocks.append(
            DocumentBlock(
                anchor.group(1),
                page,
                sequence,
                kind,
                title,
                markdown,
                float(provenance.group(3)),
            )
        )
    return DocumentIndex(fingerprint_match.group(1), tuple(blocks), ())


def repair_document(
    raw_md: Path,
    output_md: Path,
    agent: ClaudeAgent,
    budget: Budget,
    *,
    pdf_path: Path | None = None,
    renderer: Callable[[Path, int, Path], Path] = render_page,
    cache_dir: Path | None = None,
    jobs: int = 1,
) -> DocumentIndex:
    raw_text = raw_md.read_text(encoding="utf-8")
    fingerprint, pages = _raw_payload(raw_text)
    budget.require(estimate_cleanup(len(raw_text)))
    # Pages are cleaned in small chunks rather than one monolithic call: a
    # whole-paper response is long enough to trip the API's verbatim-output
    # content filter, and a chunk failure loses only that chunk's retry.
    blocks = []
    ambiguity_rows = []
    failed = Event()

    def clean_chunk(chunk):
        if failed.is_set():
            raise RuntimeError("PDF cleanup stopped after an earlier chunk failed")
        payload = {"source_fingerprint": fingerprint, "pages": chunk}
        cache = None
        if cache_dir is not None:
            resources = getattr(agent, "resource_root", Path(__file__).parent)
            resource_text = "".join((resources / resource).read_text()
                                    for resource in ("prompts/cleanup.md", "schemas/cleanup.json"))
            def cache_for(model):
                key_text = json.dumps(payload, sort_keys=True) + model + resource_text
                return cache_dir / fingerprint / f"{hashlib.sha256(key_text.encode()).hexdigest()}.json"
            cache = cache_for(str(getattr(agent, "model", "")))
            # Explicitly trusted earlier models can supply completed chunks after
            # a model change. Payload, prompt and schema hashes must still match.
            if not cache.is_file():
                for prior in os.environ.get("PROOFMATCH_CLEANUP_CACHE_MODELS", "").split(","):
                    if prior.strip() and cache_for(prior.strip()).is_file():
                        cache = cache_for(prior.strip())
                        break
        cached = cache is not None and cache.is_file()
        try:
            cleanup = json.loads(cache.read_text()) if cached else agent.run("cleanup", payload)
        except Exception:
            failed.set()
            raise
        chunk_blocks = _blocks_from_output(
            fingerprint, {int(page["page"]) for page in chunk}, cleanup
        )
        chunk_ambiguities, unresolved = _ambiguities_from_output(
            fingerprint,
            {(block.page, block.sequence) for block in chunk_blocks},
            cleanup,
        )
        if cache is not None and not cached:
            cache.parent.mkdir(parents=True, exist_ok=True)
            pending = cache.with_suffix(".tmp")
            pending.write_text(json.dumps(cleanup, ensure_ascii=False))
            pending.replace(cache)
        print(f"  PDF pages {chunk[0]['page']}-{chunk[-1]['page']}: "
              f"{'cached' if cached else 'cleaned'}", flush=True)
        for page, sequence, reason in unresolved:
            print(
                f"Warning: cleanup flagged block {page}:{sequence}, which it "
                f"never emitted — check that page by hand ({reason})"
            )
        return chunk_blocks, chunk_ambiguities

    chunks = [pages[start:start + CLEANUP_PAGES_PER_CALL]
              for start in range(0, len(pages), CLEANUP_PAGES_PER_CALL)]
    if jobs < 1:
        raise ValueError("Extraction jobs must be positive")
    with ThreadPoolExecutor(max_workers=jobs) as pool:
        for chunk_blocks, chunk_ambiguities in pool.map(clean_chunk, chunks):
            blocks.extend(chunk_blocks)
            ambiguity_rows.extend(chunk_ambiguities)
    by_key = {(block.page, block.sequence): block for block in blocks}

    if ambiguity_rows:
        if pdf_path is None:
            raise ValueError("PDF path is required to validate ambiguous blocks")
        ambiguous_pages = sorted({page for _, page, _ in ambiguity_rows})
        visual_cost = token_cost(
            DEFAULT_MODEL,
            input_tokens=5_000 * len(ambiguous_pages),
            output_tokens=1_000 * len(ambiguous_pages),
        )
        budget.require(
            StageEstimate(
                "visual validation",
                5_000 * len(ambiguous_pages),
                1_000 * len(ambiguous_pages),
                visual_cost,
            )
        )
        resolved_keys: set[tuple[int, int]] = set()
        for start in range(0, len(ambiguous_pages), VISUAL_VALIDATION_PAGES_PER_CALL):
            page_batch = ambiguous_pages[start : start + VISUAL_VALIDATION_PAGES_PER_CALL]
            page_set = set(page_batch)
            batch_rows = [row for row in ambiguity_rows if row[1] in page_set]
            with tempfile.TemporaryDirectory(prefix="proofmatch-pages-") as tmp:
                images = [
                    renderer(pdf_path, page, Path(tmp) / f"page-{page:03d}.png")
                    for page in page_batch
                ]
                visual = agent.run(
                    "visual_validate",
                    {
                        "blocks": [
                            {
                                "block_id": ambiguity.block_id,
                                "page": page,
                                "sequence": sequence,
                                "reason": ambiguity.reason,
                                "markdown": by_key[(page, sequence)].markdown,
                            }
                            for ambiguity, page, sequence in batch_rows
                        ]
                    },
                    images=images,
                )
            corrections = visual.get("corrections")
            if not isinstance(corrections, list):
                raise ValueError("visual output must contain a corrections array")
            allowed_corrections = {
                (page, sequence) for _, page, sequence in batch_rows
            }
            for correction in corrections:
                if not isinstance(correction, dict):
                    raise ValueError("visual correction must be an object")
                key = (int(correction["page"]), int(correction["sequence"]))
                if key not in allowed_corrections or key not in by_key:
                    print(
                        f"Warning: visual validation returned an unrequested block {key}; "
                        "ignoring correction",
                        flush=True,
                    )
                    continue
                original = by_key[key]
                by_key[key] = DocumentBlock(
                    block_id=original.block_id,
                    page=original.page,
                    sequence=original.sequence,
                    kind=original.kind,
                    title=original.title,
                    markdown=str(correction["markdown"]).strip(),
                    confidence=float(correction["confidence"]),
                )
                if correction.get("unresolved_reason") is None:
                    resolved_keys.add(key)
        ambiguities = tuple(
            DocumentAmbiguity(
                ambiguity.block_id,
                ambiguity.reason,
                (page, sequence) in resolved_keys,
            )
            for ambiguity, page, sequence in ambiguity_rows
        )
        blocks = [by_key[(block.page, block.sequence)] for block in blocks]
    else:
        ambiguities = ()

    index = DocumentIndex(fingerprint, tuple(blocks), ambiguities)
    output_md.parent.mkdir(parents=True, exist_ok=True)
    output_md.write_text(_render_markdown(index), encoding="utf-8")
    return index
