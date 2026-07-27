# PDF–Lean Proof Matching Pipeline Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Build a resumable Codex CLI that converts local PDFs to traceable Markdown, finds matching TCSlib proofs, compares mathematical proof structure, and writes blueprint proof-source metadata only after user approval.

**Architecture:** A standard-library Python package implements deterministic extraction, artifact storage, retrieval, budgeting, and blueprint edits. Narrow Codex invocations consume versioned prompts and JSON schemas. Each stage writes fingerprinted artifacts so later stages can resume or accept an existing validated Markdown file without running PDF conversion.

**Tech Stack:** Python 3.14 standard library, `pdf2txt.py`/`pdfminer`, Ghostscript, Codex CLI non-interactive mode, JSON Schema files, `unittest`, existing TCSlib JSONL and blueprint LaTeX.

## Global Constraints

- Target Codex as the first agent runtime.
- Accept local PDF and validated Markdown inputs only.
- Always perform local PDF-to-text extraction before paid visual processing.
- Attempt text-only repair first and inspect page images only for ambiguous or suspect blocks.
- Commit both `blueprint/src/references/<stem>.raw.md` and `<stem>.md`.
- Keep PDF conversion optional; proof matching must start directly from validated Markdown.
- Never emit a user-facing differences report for a `same` verdict.
- Never edit blueprint metadata without explicit user approval.
- Never edit generated `dataset/tcslib_theorems.jsonl` directly.
- Enforce a USD 1.00 hard cap for the initial four-page fixture.
- Preserve unrelated existing worktree changes.

---

## File Structure

- `proofmatch/__init__.py`: package version and public entry point.
- `proofmatch/models.py`: typed dataclasses and strict JSON loading for all stage artifacts.
- `proofmatch/artifacts.py`: run directories, fingerprints, cache metadata, atomic JSON/text writes.
- `proofmatch/budget.py`: conservative stage estimates and hard-cap accounting.
- `proofmatch/extraction.py`: page-aware local extraction, diagnostics, and selective page rendering.
- `proofmatch/agents.py`: safe `codex exec` adapter using prompt files and output schemas.
- `proofmatch/document.py`: cleanup orchestration, ambiguity escalation, stable block anchors, Markdown index.
- `proofmatch/search.py`: deterministic TCSlib retrieval and bounded Codex reranking inputs.
- `proofmatch/compare.py`: proof-outline and verdict orchestration plus difference-report suppression.
- `proofmatch/blueprint.py`: proof-source macro parsing and approved insertion.
- `proofmatch/cli.py`: `extract`, `estimate`, `match`, `review`, and `run` commands.
- `scripts/proofmatch.py`: repository-local executable wrapper.
- `proofmatch/prompts/*.md`: cleanup, visual validation, reranking, comparison, and resource prompts.
- `proofmatch/schemas/*.json`: Codex final-output schemas.
- `tests/proofmatch/`: standard-library unit and integration tests.
- `blueprint/src/references/switching-lemma.raw.md`: committed raw fixture extraction.
- `blueprint/src/references/switching-lemma.md`: committed repaired fixture Markdown.
- `blueprint/src/preamble/common.tex`: invisible `\proofsource` macro.
- `scripts/build_dataset.py`: parse approved proof-source metadata into generated records.

### Task 1: Artifact Models and Run Store

**Files:**
- Create: `proofmatch/__init__.py`
- Create: `proofmatch/models.py`
- Create: `proofmatch/artifacts.py`
- Create: `tests/proofmatch/__init__.py`
- Create: `tests/proofmatch/test_artifacts.py`

**Interfaces:**
- Produces: `sha256_file(path: Path) -> str`
- Produces: `RunStore(root: Path, source_fingerprint: str)`
- Produces: `RunStore.write_json(stage: str, value: Mapping[str, object]) -> Path`
- Produces: `RunStore.read_json(stage: str) -> dict[str, object] | None`
- Produces: `load_typed(path: Path, cls: type[T]) -> T`
- Consumes: only Python standard library.

- [ ] **Step 1: Write failing artifact tests**

```python
class RunStoreTests(unittest.TestCase):
    def test_atomic_round_trip_and_stage_cache(self):
        with tempfile.TemporaryDirectory() as tmp:
            store = RunStore(Path(tmp), "abc123")
            store.write_json("extract", {"pages": 4})
            self.assertEqual(store.read_json("extract"), {"pages": 4})

    def test_typed_loader_rejects_missing_required_fields(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "verdict.json"
            path.write_text('{"verdict":"same"}')
            with self.assertRaisesRegex(ValueError, "lean_name"):
                load_typed(path, ComparisonVerdict)
```

- [ ] **Step 2: Run tests and verify RED**

Run: `python3 -m unittest tests.proofmatch.test_artifacts -v`

Expected: import failure because `proofmatch.artifacts` does not exist.

- [ ] **Step 3: Implement immutable artifact dataclasses and atomic run storage**

```python
@dataclass(frozen=True)
class ComparisonVerdict:
    lean_name: str
    document_blocks: tuple[str, ...]
    verdict: Literal["same", "different", "uncertain"]
    confidence: float
    differences: tuple[str, ...]
    evidence: tuple[str, ...]

class RunStore:
    def write_json(self, stage, value):
        target = self.stage_path(stage, ".json")
        tmp = target.with_suffix(".json.tmp")
        tmp.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n")
        tmp.replace(target)
        return target
```

- [ ] **Step 4: Run tests and verify GREEN**

Run: `python3 -m unittest tests.proofmatch.test_artifacts -v`

Expected: all tests pass.

- [ ] **Step 5: Commit**

```bash
git add proofmatch/__init__.py proofmatch/models.py proofmatch/artifacts.py tests/proofmatch
git commit -m "feat: add proof matching artifact store"
```

### Task 2: Cost Estimation and Fixture Cap

**Files:**
- Create: `proofmatch/budget.py`
- Create: `tests/proofmatch/test_budget.py`

**Interfaces:**
- Produces: `StageEstimate(name: str, input_tokens: int, output_tokens: int, usd: Decimal)`
- Produces: `Budget(cap_usd: Decimal, spent_usd: Decimal = Decimal("0"))`
- Produces: `Budget.require(estimate: StageEstimate) -> None`
- Consumes: page counts, raw character counts, ambiguity counts, candidate proof sizes.

- [ ] **Step 1: Write failing cap and estimate tests**

```python
class BudgetTests(unittest.TestCase):
    def test_rejects_stage_that_exceeds_remaining_fixture_cap(self):
        budget = Budget(Decimal("1.00"), Decimal("0.82"))
        with self.assertRaisesRegex(BudgetExceeded, r"remaining \\$0.18"):
            budget.require(StageEstimate("compare", 80_000, 8_000, Decimal("0.25")))

    def test_text_estimate_is_conservative_and_nonzero(self):
        estimate = estimate_cleanup(raw_characters=20_000)
        self.assertGreaterEqual(estimate.input_tokens, 5_000)
        self.assertGreater(estimate.usd, Decimal("0"))
```

- [ ] **Step 2: Run tests and verify RED**

Run: `python3 -m unittest tests.proofmatch.test_budget -v`

Expected: import failure for `proofmatch.budget`.

- [ ] **Step 3: Implement Decimal-based model price table and pre-stage guard**

Use configurable per-million-token prices with initial conservative defaults:

```python
MODEL_PRICES = {
    "gpt-5.6-luna": (Decimal("1.00"), Decimal("6.00")),
    "gpt-5.6-terra": (Decimal("2.50"), Decimal("15.00")),
}

def token_cost(model, input_tokens, output_tokens):
    in_rate, out_rate = MODEL_PRICES[model]
    return (
        Decimal(input_tokens) * in_rate
        + Decimal(output_tokens) * out_rate
    ) / Decimal(1_000_000)
```

- [ ] **Step 4: Run tests and verify GREEN**

Run: `python3 -m unittest tests.proofmatch.test_budget -v`

Expected: all tests pass.

- [ ] **Step 5: Commit**

```bash
git add proofmatch/budget.py tests/proofmatch/test_budget.py
git commit -m "feat: enforce proof matching cost budgets"
```

### Task 3: Local PDF Extraction and Diagnostics

**Files:**
- Create: `proofmatch/extraction.py`
- Create: `tests/proofmatch/test_extraction.py`
- Modify: `.gitignore`

**Interfaces:**
- Produces: `extract_pdf(pdf: Path, raw_markdown: Path, runner=subprocess.run) -> ExtractionReport`
- Produces: `diagnose_page(page_number: int, text: str) -> PageDiagnostic`
- Produces: `render_page(pdf: Path, page_number: int, output_png: Path) -> Path`
- Consumes: local `pdf2txt.py` and Ghostscript executables.

- [ ] **Step 1: Write failing page-boundary and diagnostic tests**

```python
class ExtractionTests(unittest.TestCase):
    def test_writes_faithful_page_delimited_raw_markdown(self):
        pages = ["Theorem 1\\nA → B", "Proof\\nB follows."]
        markdown = format_raw_markdown("sha256:abc", "pdf2txt.py 20250506", pages)
        self.assertIn("<!-- pdf-page: 1 -->", markdown)
        self.assertIn("<!-- pdf-page: 2 -->", markdown)
        self.assertIn("A → B", markdown)

    def test_flags_detached_math_and_repeated_footer(self):
        diagnostic = diagnose_page(1, "f :\\n{0,1}\\nn\\n→\\n{0,1}\\nLecture-1")
        self.assertIn("fragmented-lines", diagnostic.reasons)
        self.assertLess(diagnostic.confidence, 1.0)
```

- [ ] **Step 2: Run tests and verify RED**

Run: `python3 -m unittest tests.proofmatch.test_extraction -v`

Expected: import failure for `proofmatch.extraction`.

- [ ] **Step 3: Implement extraction with Form Feed page splitting**

Invoke `pdf2txt.py` with UTF-8 output, split on `\f`, retain text verbatim inside
page sections, and add only provenance comments. Add `.proofmatch-work/` to
`.gitignore`. Render a requested page with:

```python
[
    "gs", "-q", "-dSAFER", "-dBATCH", "-dNOPAUSE",
    "-sDEVICE=png16m", "-r180",
    f"-dFirstPage={page_number}", f"-dLastPage={page_number}",
    f"-sOutputFile={output_png}", str(pdf),
]
```

- [ ] **Step 4: Run unit tests and the real four-page extraction**

Run: `python3 -m unittest tests.proofmatch.test_extraction -v`

Run: `python3 -c 'from pathlib import Path; from proofmatch.extraction import extract_pdf; print(extract_pdf(Path("blueprint/src/references/switching-lemma.pdf"), Path("blueprint/src/references/switching-lemma.raw.md")))'`

Expected: tests pass; command writes `switching-lemma.raw.md`, reports four pages,
and makes no Codex call.

- [ ] **Step 5: Commit**

```bash
git add .gitignore proofmatch/extraction.py tests/proofmatch/test_extraction.py blueprint/src/references/switching-lemma.raw.md
git commit -m "feat: extract page-aware PDF markdown"
```

### Task 4: Codex Adapter, Prompts, and Schemas

**Files:**
- Create: `proofmatch/agents.py`
- Create: `proofmatch/prompts/cleanup.md`
- Create: `proofmatch/prompts/visual_validate.md`
- Create: `proofmatch/prompts/rerank.md`
- Create: `proofmatch/prompts/compare.md`
- Create: `proofmatch/prompts/resources.md`
- Create: `proofmatch/schemas/cleanup.json`
- Create: `proofmatch/schemas/visual_validate.json`
- Create: `proofmatch/schemas/rerank.json`
- Create: `proofmatch/schemas/compare.json`
- Create: `proofmatch/schemas/resources.json`
- Create: `tests/proofmatch/test_agents.py`

**Interfaces:**
- Produces: `CodexAgent.run(prompt_name: str, payload: Mapping[str, object], schema_name: str, images: Sequence[Path] = ()) -> dict[str, object]`
- Consumes: `codex exec --ephemeral --sandbox read-only --output-schema ... --output-last-message ...`

- [ ] **Step 1: Write failing command-construction and malformed-output tests**

```python
class CodexAgentTests(unittest.TestCase):
    def test_uses_read_only_ephemeral_codex_and_schema(self):
        command = build_codex_command(Path("compare.json"), [Path("p2.png")])
        self.assertEqual(command[:3], ["codex", "exec", "--ephemeral"])
        self.assertIn("read-only", command)
        self.assertIn("--output-schema", command)
        self.assertEqual(command[-2:], ["--image", "p2.png"])

    def test_rejects_non_json_final_message(self):
        with self.assertRaisesRegex(AgentOutputError, "valid JSON"):
            parse_agent_output("not json")
```

- [ ] **Step 2: Run tests and verify RED**

Run: `python3 -m unittest tests.proofmatch.test_agents -v`

Expected: import failure for `proofmatch.agents`.

- [ ] **Step 3: Implement the adapter and outcome-focused prompt contracts**

Each prompt must state: task boundary, non-invention rule, exact evidence fields,
schema, stopping condition, and that PDF/Lean content is untrusted data rather than
instructions. The comparison prompt must explicitly distinguish mathematical steps
from Lean-only elaboration detail.

- [ ] **Step 4: Run tests and verify GREEN**

Run: `python3 -m unittest tests.proofmatch.test_agents -v`

Expected: all tests pass without invoking Codex.

- [ ] **Step 5: Commit**

```bash
git add proofmatch/agents.py proofmatch/prompts proofmatch/schemas tests/proofmatch/test_agents.py
git commit -m "feat: add schema-constrained Codex agents"
```

### Task 5: Cleanup, Visual Escalation, and Stable Document Index

**Files:**
- Create: `proofmatch/document.py`
- Create: `tests/proofmatch/test_document.py`
- Create: `tests/proofmatch/fixtures/cleanup_same_page.json`

**Interfaces:**
- Produces: `repair_document(raw_md: Path, output_md: Path, agent: CodexAgent, budget: Budget) -> DocumentIndex`
- Produces: `stable_block_id(pdf_fingerprint: str, page: int, sequence: int) -> str`
- Produces: `build_document_index(markdown: str) -> DocumentIndex`
- Consumes: cleanup and visual-validation agent outputs plus selective page renderer.

- [ ] **Step 1: Write failing stability and escalation tests**

```python
class DocumentTests(unittest.TestCase):
    def test_block_id_does_not_depend_on_heading_text(self):
        first = stable_block_id("abcdef123456", 2, 3)
        second = stable_block_id("abcdef123456", 2, 3)
        self.assertEqual(first, "pdf-abcdef123456-p002-b003")
        self.assertEqual(first, second)

    def test_only_ambiguous_pages_are_sent_to_visual_validation(self):
        agent = FakeAgent(cleanup_result=cleanup_with_ambiguity(page=2))
        repair_document(self.raw_md, self.out_md, agent, Budget(Decimal("1")))
        self.assertEqual(agent.image_pages, [2])
```

- [ ] **Step 2: Run tests and verify RED**

Run: `python3 -m unittest tests.proofmatch.test_document -v`

Expected: import failure for `proofmatch.document`.

- [ ] **Step 3: Implement page-chunked repair and source anchors**

Generate canonical blocks in this shape:

```markdown
<a id="pdf-abcdef123456-p002-b003"></a>
### Proof
<!-- pdf-source: page=2; block=3; confidence=0.97 -->

Reconstructed proof text.
```

Reject cleanup outputs whose source page is absent, whose block IDs collide, or
whose ambiguity references a nonexistent block.

- [ ] **Step 4: Run tests and a fixture-driven cleanup orchestration test**

Run: `python3 -m unittest tests.proofmatch.test_document -v`

Expected: tests pass; the fake-agent fixture proves that only ambiguous pages are
rendered and passed to visual validation; no live Codex call occurs yet.

- [ ] **Step 5: Commit**

```bash
git add proofmatch/document.py tests/proofmatch/test_document.py tests/proofmatch/fixtures
git commit -m "feat: repair and index extracted proof documents"
```

### Task 6: Deterministic Candidate Retrieval

**Files:**
- Create: `proofmatch/search.py`
- Create: `tests/proofmatch/test_search.py`

**Interfaces:**
- Produces: `search_candidates(index: DocumentIndex, dataset: Path, limit: int = 12) -> tuple[Candidate, ...]`
- Produces: `prepare_rerank_payload(candidates: Sequence[Candidate], index: DocumentIndex) -> dict[str, object]`
- Consumes: existing theorem JSONL without modifying it.

- [ ] **Step 1: Write failing switching-lemma retrieval test**

```python
class SearchTests(unittest.TestCase):
    def test_switching_lemma_is_in_bounded_candidates(self):
        index = fixture_document_index(
            title="Håstad's Switching Lemma",
            terms=["DNF", "restriction", "decision tree", "(10σw)^d"],
        )
        candidates = search_candidates(
            index, Path("dataset/tcslib_theorems.jsonl"), limit=12
        )
        self.assertIn(
            "SwitchingLemma2.switching_lemma",
            [candidate.lean_name for candidate in candidates],
        )
```

- [ ] **Step 2: Run test and verify RED**

Run: `python3 -m unittest tests.proofmatch.test_search -v`

Expected: import failure for `proofmatch.search`.

- [ ] **Step 3: Implement normalized BM25-style scoring**

Tokenize Unicode mathematical prose, split Lean qualified names, weight exact
title/name matches above body tokens, and add overlap bonuses for identifiers and
formula fragments. Return only metadata and proof-size estimates; do not load every
full proof into the reranking prompt.

- [ ] **Step 4: Run tests and verify GREEN**

Run: `python3 -m unittest tests.proofmatch.test_search -v`

Expected: switching lemma appears within the top 12 and all tests pass.

- [ ] **Step 5: Commit**

```bash
git add proofmatch/search.py tests/proofmatch/test_search.py
git commit -m "feat: retrieve TCSlib proof candidates"
```

### Task 7: Bidirectional Proof Comparison and Quiet Reports

**Files:**
- Create: `proofmatch/compare.py`
- Create: `tests/proofmatch/test_compare.py`
- Create: `tests/proofmatch/fixtures/same_verdict.json`
- Create: `tests/proofmatch/fixtures/different_verdict.json`

**Interfaces:**
- Produces: `choose_comparison_direction(pdf_tokens: int, lean_tokens: int) -> Literal["pdf_to_lean", "lean_to_pdf"]`
- Produces: `compare_candidate(candidate: Candidate, document: DocumentIndex, agent: CodexAgent, budget: Budget) -> ComparisonVerdict`
- Produces: `render_difference_report(verdicts: Sequence[ComparisonVerdict]) -> str | None`

- [ ] **Step 1: Write failing direction and report-suppression tests**

```python
class CompareTests(unittest.TestCase):
    def test_searches_from_shorter_side(self):
        self.assertEqual(choose_comparison_direction(2_000, 20_000), "pdf_to_lean")
        self.assertEqual(choose_comparison_direction(30_000, 8_000), "lean_to_pdf")

    def test_same_verdict_produces_no_difference_report(self):
        verdict = load_fixture_verdict("same_verdict.json")
        self.assertIsNone(render_difference_report([verdict]))

    def test_different_verdict_reports_only_material_differences(self):
        verdict = load_fixture_verdict("different_verdict.json")
        report = render_difference_report([verdict])
        self.assertIn("different induction parameter", report)
        self.assertNotIn("typeclass", report)
```

- [ ] **Step 2: Run tests and verify RED**

Run: `python3 -m unittest tests.proofmatch.test_compare -v`

Expected: import failure for `proofmatch.compare`.

- [ ] **Step 3: Implement bounded comparison payloads and verdict validation**

Include the selected PDF blocks, theorem statement, complete proof only for the
current candidate, and dependency names. Reject `same` verdicts that contain
material differences, and normalize them to `uncertain` for review rather than
silently discarding contradictory evidence.

- [ ] **Step 4: Run tests and verify GREEN**

Run: `python3 -m unittest tests.proofmatch.test_compare -v`

Expected: all tests pass.

- [ ] **Step 5: Commit**

```bash
git add proofmatch/compare.py tests/proofmatch/test_compare.py tests/proofmatch/fixtures
git commit -m "feat: compare informal and Lean proof structure"
```

### Task 8: Blueprint Proof Sources and Dataset Integration

**Files:**
- Modify: `blueprint/src/preamble/common.tex`
- Modify: `scripts/build_dataset.py`
- Create: `proofmatch/blueprint.py`
- Create: `tests/proofmatch/test_blueprint.py`
- Create: `tests/proofmatch/fixtures/blueprint_entry.tex`

**Interfaces:**
- Produces: `parse_proof_sources(tex: str) -> dict[str, tuple[ProofSource, ...]]`
- Produces: `insert_approved_source(tex_path: Path, lean_name: str, source: ProofSource) -> None`
- Extends dataset records with `proof_sources: list[dict[str, object]]`.

- [ ] **Step 1: Write failing parse, insertion, and approval tests**

```python
class BlueprintTests(unittest.TestCase):
    def test_parses_source_bound_to_lean_environment(self):
        parsed = parse_proof_sources(FIXTURE_TEX)
        source = parsed["SwitchingLemma2.switching_lemma"][0]
        self.assertEqual(source.document, "switching-lemma")
        self.assertEqual(source.blocks, ("pdf-abcdef123456-p002-b003",))

    def test_insert_requires_explicit_approved_state(self):
        with self.assertRaisesRegex(PermissionError, "explicit approval"):
            insert_review_decision(self.tex_path, verdict="same", decision="deferred")
```

- [ ] **Step 2: Run tests and verify RED**

Run: `python3 -m unittest tests.proofmatch.test_blueprint -v`

Expected: import failure for `proofmatch.blueprint`.

- [ ] **Step 3: Implement a multi-block invisible macro**

Define and parse:

```latex
\newcommand{\proofsource}[2]{}

\proofsource{switching-lemma}{
  pdf-abcdef123456-p002-b003,
  pdf-abcdef123456-p003-b001
}
```

Bind each `\proofsource` to the standalone `\lean{...}` in the same blueprint
environment. Insert after `\leanok`, or after the binding `\lean` when `\leanok` is
absent. Extend dataset generation with parsed approved metadata.

- [ ] **Step 4: Run focused and builder tests**

Run: `python3 -m unittest tests.proofmatch.test_blueprint -v`

Run: `python3 scripts/build_dataset.py --limit 2 --out /tmp/proofmatch-dataset.jsonl`

Expected: tests pass; the builder completes; generated records without annotations
contain an empty `proof_sources` list.

- [ ] **Step 5: Commit**

```bash
git add blueprint/src/preamble/common.tex scripts/build_dataset.py proofmatch/blueprint.py tests/proofmatch
git commit -m "feat: record approved proof sources in blueprint"
```

### Task 9: CLI Orchestration and Resumption

**Files:**
- Create: `proofmatch/cli.py`
- Create: `scripts/proofmatch.py`
- Create: `tests/proofmatch/test_cli.py`
- Modify: `README.md`

**Interfaces:**
- Produces commands:
  - `proofmatch estimate SOURCE --max-cost USD`
  - `proofmatch extract PDF [--local-only] [--max-cost USD]`
  - `proofmatch match MARKDOWN [--max-cost USD]`
  - `proofmatch review RUN_ID`
  - `proofmatch run SOURCE --max-cost USD`
- Consumes all earlier package interfaces.

- [ ] **Step 1: Write failing CLI tests**

```python
class CliTests(unittest.TestCase):
    def test_match_accepts_markdown_without_extraction(self):
        result = run_cli(["match", "blueprint/src/references/switching-lemma.md"])
        self.assertEqual(result.exit_code, 0)
        self.assertFalse(result.called_extractor)

    def test_review_same_requires_yes_before_blueprint_write(self):
        result = run_cli(["review", "run-123"], stdin="defer\\n")
        self.assertEqual(result.exit_code, 0)
        self.assertFalse(result.blueprint_changed)

    def test_fixture_run_defaults_to_one_dollar_only_for_fixture(self):
        args = parse_args(["run", "blueprint/src/references/switching-lemma.pdf"])
        self.assertEqual(args.max_cost, Decimal("1.00"))
```

- [ ] **Step 2: Run tests and verify RED**

Run: `python3 -m unittest tests.proofmatch.test_cli -v`

Expected: import failure for `proofmatch.cli`.

- [ ] **Step 3: Implement commands, stage cache, and exact resume output**

The wrapper adds the repository root to `sys.path` and calls
`proofmatch.cli.main()`. For non-fixture inputs, `run` requires `--max-cost`.
`review` accepts only explicit `approve`, `reject`, or `defer`; only `approve`
calls blueprint insertion.

- [ ] **Step 4: Run CLI and full deterministic suite**

Run: `python3 -m unittest discover -s tests -v`

Run: `python3 scripts/proofmatch.py estimate blueprint/src/references/switching-lemma.pdf`

Run: `python3 scripts/proofmatch.py match blueprint/src/references/switching-lemma.md --dry-run --max-cost 1.00`

Expected: tests pass; estimate is below USD 1.00; dry-run finds the switching-lemma
candidate and performs no blueprint edit.

- [ ] **Step 5: Commit**

```bash
git add proofmatch/cli.py scripts/proofmatch.py tests/proofmatch/test_cli.py README.md
git commit -m "feat: add resumable proof matching CLI"
```

### Task 10: Live Fixture Evaluation and Final Verification

**Files:**
- Create: `tests/proofmatch/fixtures/switching_lemma_rubric.json`
- Create: `blueprint/.proofmatch-evals/switching-lemma-report.md`
- Modify only after user approval: matching switching-lemma blueprint `.tex` entry.

**Interfaces:**
- Consumes: complete CLI and fixture PDF.
- Produces: auditable run artifacts, final fixture Markdown, candidate/verdict report.

- [ ] **Step 1: Add an evaluation rubric before the live run**

```json
{
  "required_repairs": [
    "reading order",
    "overbar attachment",
    "function and set notation",
    "inequalities and exponents",
    "display equation ordering",
    "ligatures and accented names",
    "header and footer removal"
  ],
  "required_candidate": "SwitchingLemma2.switching_lemma",
  "requires_page_provenance": true,
  "difference_report_for_same": false,
  "blueprint_write_before_approval": false,
  "max_cost_usd": "1.00"
}
```

- [ ] **Step 2: Run all deterministic verification**

Run: `python3 -m unittest discover -s tests -v`

Run: `git diff --check`

Expected: all tests pass and diff check is clean.

- [ ] **Step 3: Run the live fixture pipeline**

Run: `python3 scripts/proofmatch.py run blueprint/src/references/switching-lemma.pdf --max-cost 1.00`

Expected: raw and validated Markdown exist; required corruption classes are
addressed; `SwitchingLemma2.switching_lemma` is a candidate; the run stops for
review; no blueprint source file has changed; recorded cost is below USD 1.00.

- [ ] **Step 4: Review the generated verdict with the user**

Present exact Markdown anchors and any material differences or uncertainty. If the
verdict is `same`, present no differences section. Do not approve on the user's
behalf.

- [ ] **Step 5: Run post-review verification**

After the user chooses approve/reject/defer:

Run: `python3 -m unittest discover -s tests -v`

Run: `git diff --check`

Run: `git status --short`

Expected: all tests pass; only approved in-scope files plus pre-existing unrelated
changes are present.

- [ ] **Step 6: Commit the evaluated fixture without auto-approving**

```bash
git add tests/proofmatch/fixtures/switching_lemma_rubric.json blueprint/.proofmatch-evals/switching-lemma-report.md blueprint/src/references/switching-lemma.raw.md blueprint/src/references/switching-lemma.md
git commit -m "test: evaluate switching lemma proof matching"
```
