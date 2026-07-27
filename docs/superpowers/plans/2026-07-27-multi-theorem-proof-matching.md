# Multi-Theorem Proof Matching Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Make chapter-scale proof matching compare every relevant blueprint theorem, automatically propagate every `same` theorem and its upstream mappings, and never partially mutate the blueprint.

**Architecture:** Add a blueprint-scoped theorem catalog, per-segment high-recall discovery, and a statement-only relevance gate. A chapter orchestrator performs all comparisons and upstream mappings into a manifest, then commits conflict-checked blueprint updates atomically only after the entire budgeted run succeeds.

**Tech Stack:** Python 3 standard library, existing `proofmatch` modules, Codex CLI structured outputs, `unittest`/`pytest`, LaTeX blueprint annotations.

## Global Constraints

- Only declarations bound by `\lean{...}` in the blueprint are top-level candidates.
- `same` verdicts propagate automatically; `different` and `uncertain` are report-only.
- Upstream mappings inherit a `same` verdict and have no second human-review gate.
- Paid work uses one run-wide hard cap and blueprint writes occur only after all stages validate.
- Existing source anchors, `\proofsource`, and `\proofstep` formats remain unchanged.
- Existing single-theorem run artifacts remain readable.
- A narrower Lean projection of a stronger source result may be `same` when it uses the corresponding proof component.

---

### Task 1: Build the Blueprint-Bound Theorem Catalog

**Files:**
- Create: `proofmatch/catalog.py`
- Test: `tests/proofmatch/test_catalog.py`

**Interfaces:**
- Consumes: blueprint root `Path`, dataset JSONL `Path`.
- Produces:
  - `BlueprintBinding(lean_name: str, tex_path: Path)`
  - `load_blueprint_bindings(blueprint_root: Path) -> dict[str, BlueprintBinding]`
  - `load_blueprint_candidates(dataset: Path, bindings: Mapping[str, BlueprintBinding]) -> tuple[Candidate, ...]`

- [ ] **Step 1: Write failing catalog tests**

```python
def test_load_blueprint_bindings_collects_each_lean_name_once(self):
    (chapter / "A.tex").write_text(
        "\\begin{theorem}\n\\lean{A.one, A.two}\n\\end{theorem}\n"
    )
    bindings = load_blueprint_bindings(chapter)
    self.assertEqual(set(bindings), {"A.one", "A.two"})

def test_duplicate_blueprint_binding_is_rejected(self):
    (chapter / "A.tex").write_text("\\begin{theorem}\\lean{A.one}\\end{theorem}")
    (chapter / "B.tex").write_text("\\begin{lemma}\\lean{A.one}\\end{lemma}")
    with self.assertRaisesRegex(ValueError, "multiple blueprint environments"):
        load_blueprint_bindings(chapter)

def test_dataset_is_filtered_to_blueprint_names(self):
    candidates = load_blueprint_candidates(dataset, {"A.one": binding})
    self.assertEqual([item.lean_name for item in candidates], ["A.one"])
```

- [ ] **Step 2: Run the tests and verify RED**

Run: `python3 -m pytest tests/proofmatch/test_catalog.py -q`

Expected: collection fails because `proofmatch.catalog` does not exist.

- [ ] **Step 3: Implement the minimal catalog**

```python
@dataclass(frozen=True)
class BlueprintBinding:
    lean_name: str
    tex_path: Path

def load_blueprint_bindings(blueprint_root: Path) -> dict[str, BlueprintBinding]:
    found: dict[str, BlueprintBinding] = {}
    for path in sorted(blueprint_root.rglob("*.tex")):
        for environment in ENV_RE.findall(path.read_text(encoding="utf-8")):
            for match in LEAN_RE.finditer(environment):
                for raw_name in match.group(1).split(","):
                    name = raw_name.strip()
                    if not name or name.startswith("["):
                        continue
                    if name in found:
                        raise ValueError(
                            f"{name} appears in multiple blueprint environments"
                        )
                    found[name] = BlueprintBinding(name, path)
    return found
```

Parse matching dataset rows into existing `Candidate` values with empty
`document_blocks` and `score=0.0`.

- [ ] **Step 4: Run catalog tests and the existing blueprint tests**

Run: `python3 -m pytest tests/proofmatch/test_catalog.py tests/proofmatch/test_blueprint.py -q`

Expected: PASS.

- [ ] **Step 5: Commit the catalog**

```bash
git add proofmatch/catalog.py tests/proofmatch/test_catalog.py
git commit -m "feat: index blueprint-bound theorem candidates"
```

---

### Task 2: Discover Candidates Independently Per Document Segment

**Files:**
- Modify: `proofmatch/search.py`
- Modify: `tests/proofmatch/test_search.py`

**Interfaces:**
- Consumes: `DocumentIndex`, blueprint-filtered `Sequence[Candidate]`, `per_segment_limit`.
- Produces:
  - `document_segments(index: DocumentIndex) -> tuple[tuple[DocumentBlock, ...], ...]`
  - `discover_candidates(index: DocumentIndex, catalog: Sequence[Candidate], per_segment_limit: int = 8, reverse_min_score: float = 25.0) -> tuple[Candidate, ...]`
- Preserve `search_candidates(...)` as a legacy wrapper.

- [ ] **Step 1: Add failing per-segment and reverse-discovery tests**

```python
def test_discovery_keeps_top_candidate_from_every_segment(self):
    discovered = discover_candidates(index_with_two_theorems, catalog, per_segment_limit=1)
    self.assertEqual(
        {candidate.lean_name for candidate in discovered},
        {"T.first", "T.second"},
    )

def test_discovery_merges_blocks_for_same_theorem(self):
    discovered = discover_candidates(index_with_split_statement_and_proof, catalog)
    theorem = next(item for item in discovered if item.lean_name == "T.joined")
    self.assertEqual(
        theorem.document_blocks,
        ("pdf-abcdef123456-p001-b001", "pdf-abcdef123456-p002-b001"),
    )

def test_non_blueprint_candidate_cannot_enter_discovery(self):
    discovered = discover_candidates(index, blueprint_catalog)
    self.assertNotIn("Outside.theorem", {item.lean_name for item in discovered})

def test_reverse_discovery_keeps_theorems_below_each_segment_quota(self):
    discovered = discover_candidates(
        index_with_two_theorems,
        catalog,
        per_segment_limit=1,
        reverse_min_score=25.0,
    )
    self.assertIn("T.reverse_match", {item.lean_name for item in discovered})
```

- [ ] **Step 2: Run focused tests and verify RED**

Run: `python3 -m pytest tests/proofmatch/test_search.py -q`

Expected: FAIL because `discover_candidates` and `document_segments` are absent.

- [ ] **Step 3: Expose segmentation and implement union discovery**

```python
def discover_candidates(index, catalog, per_segment_limit=8, reverse_min_score=25.0):
    if per_segment_limit < 1:
        raise ValueError("per_segment_limit must be positive")
    merged: dict[str, Candidate] = {}
    best_by_theorem: dict[str, Candidate] = {}
    for segment in document_segments(index):
        ranked = sorted(
            (
                replace(
                    candidate,
                    score=_score(*_query(segment), candidate_record(candidate)),
                    document_blocks=tuple(block.block_id for block in segment),
                )
                for candidate in catalog
            ),
            key=lambda item: (-item.score, item.lean_name),
        )
        for candidate in ranked[:per_segment_limit]:
            merged[candidate.lean_name] = merge_candidate(
                merged.get(candidate.lean_name), candidate
            )
        for candidate in ranked:
            prior = best_by_theorem.get(candidate.lean_name)
            if prior is None or candidate.score > prior.score:
                best_by_theorem[candidate.lean_name] = candidate
    for candidate in best_by_theorem.values():
        if candidate.score >= reverse_min_score:
            merged[candidate.lean_name] = merge_candidate(
                merged.get(candidate.lean_name), candidate
            )
    return tuple(sorted(merged.values(), key=lambda item: (-item.score, item.lean_name)))
```

Keep each candidate's best score and the ordered union of its blocks. Ensure
every segment supplies its own quota. The reverse pass retains the best
segment for every blueprint theorem with meaningful lexical overlap even when
that theorem falls below a crowded segment's forward quota.

- [ ] **Step 4: Run search and catalog tests**

Run: `python3 -m pytest tests/proofmatch/test_search.py tests/proofmatch/test_catalog.py -q`

Expected: PASS.

- [ ] **Step 5: Commit discovery**

```bash
git add proofmatch/search.py tests/proofmatch/test_search.py
git commit -m "feat: discover proof candidates per document segment"
```

---

### Task 3: Add Batched Statement-Only Relevance Classification

**Files:**
- Create: `proofmatch/relevance.py`
- Create: `proofmatch/prompts/relevance.md`
- Create: `proofmatch/schemas/relevance.json`
- Modify: `proofmatch/models.py`
- Create: `tests/proofmatch/test_relevance.py`

**Interfaces:**
- Produces:
  - `RelevanceDecision(lean_name: str, status: Literal["relevant", "irrelevant", "uncertain"], document_blocks: tuple[str, ...], rationale: str)`
  - `estimate_relevance(candidates: Sequence[Candidate], index: DocumentIndex) -> StageEstimate`
  - `classify_relevance(candidates, index, agent, budget) -> tuple[RelevanceDecision, ...]`
- The agent receives candidate statements and candidate-associated blocks, never proofs.

- [ ] **Step 1: Add failing validation and budget tests**

```python
def test_relevance_payload_omits_proofs(self):
    payload = prepare_relevance_payload((candidate,), index)
    self.assertNotIn("proof", json.dumps(payload))

def test_unknown_block_is_rejected(self):
    output = {"decisions": [{
        "lean_name": "T.one",
        "status": "relevant",
        "document_blocks": ["pdf-abcdef123456-p999-b001"],
        "rationale": "match",
    }]}
    with self.assertRaisesRegex(ValueError, "unknown source block"):
        decisions_from_agent(output, (candidate,), index)

def test_uncertain_relevance_advances_to_comparison(self):
    decisions = decisions_from_agent(agent_output, (candidate,), index)
    self.assertTrue(requires_comparison(decisions[0]))
```

- [ ] **Step 2: Run relevance tests and verify RED**

Run: `python3 -m pytest tests/proofmatch/test_relevance.py -q`

Expected: FAIL because relevance types and functions do not exist.

- [ ] **Step 3: Add the relevance schema and prompt**

Schema output:

```json
{
  "decisions": [
    {
      "lean_name": "T.one",
      "status": "relevant",
      "document_blocks": ["pdf-abcdef123456-p001-b002"],
      "rationale": "The block states and proves the same theorem."
    }
  ]
}
```

The prompt must instruct the agent to classify material use in context as
relevant and to choose `uncertain` rather than discard a plausible match.

- [ ] **Step 4: Implement strict decision validation and one budgeted call**

Validate that each discovered candidate appears exactly once, cited blocks
exist and belong to that candidate's proposed blocks, irrelevant candidates
cite no blocks, and relevant/uncertain candidates cite at least one block.

- [ ] **Step 5: Run relevance tests and schema validation tests**

Run: `python3 -m pytest tests/proofmatch/test_relevance.py tests/proofmatch/test_agents.py -q`

Expected: PASS.

- [ ] **Step 6: Commit relevance classification**

```bash
git add proofmatch/relevance.py proofmatch/models.py proofmatch/prompts/relevance.md proofmatch/schemas/relevance.json tests/proofmatch/test_relevance.py
git commit -m "feat: classify all chapter theorem candidates"
```

---

### Task 4: Compare Every Relevant Candidate and Build a Chapter Manifest

**Files:**
- Create: `proofmatch/chapter.py`
- Modify: `proofmatch/compare.py`
- Modify: `proofmatch/models.py`
- Create: `tests/proofmatch/test_chapter.py`
- Modify: `tests/proofmatch/test_compare.py`

**Interfaces:**
- Produces:
  - `ChapterMatchManifest(source_markdown, source_fingerprint, candidates, relevance, verdicts, estimated_spend_usd, propagation_status)`
  - `estimate_chapter_match(candidates, index) -> tuple[StageEstimate, ...]`
  - `compare_relevant_candidates(candidates, decisions, index, agent_factory, budget) -> tuple[ComparisonVerdict, ...]`
- `compare_candidate` receives only blocks selected by the relevance decision.

- [ ] **Step 1: Add a failing all-candidates comparison test**

```python
def test_every_relevant_or_uncertain_candidate_is_compared(self):
    verdicts = compare_relevant_candidates(
        candidates,
        decisions=("relevant", "irrelevant", "uncertain"),
        index=index,
        agent_factory=recording_agents,
        budget=Budget(Decimal("10")),
    )
    self.assertEqual([item.lean_name for item in verdicts], ["T.one", "T.three"])
    self.assertEqual(recording_agents.compare_calls, ["T.one", "T.three"])
```

Add tests proving irrelevant candidates are retained in the manifest but not
compared, and a narrower projection can validate as `same` with no
differences.

- [ ] **Step 2: Run chapter and compare tests and verify RED**

Run: `python3 -m pytest tests/proofmatch/test_chapter.py tests/proofmatch/test_compare.py -q`

Expected: FAIL because chapter orchestration is absent.

- [ ] **Step 3: Update comparison guidance for stronger source results**

Amend `proofmatch/prompts/compare.md` so a clearly isolated component of a
stronger theorem is `same` when Lean follows that component's proof. It remains
`different` if the Lean claim requires an argument absent from the source.

- [ ] **Step 4: Implement deterministic multi-comparison ordering**

Order comparisons by source block position and then Lean name. Construct a
candidate copy whose `document_blocks` are the relevance decision's validated
blocks before calling `compare_candidate`.

- [ ] **Step 5: Run focused tests**

Run: `python3 -m pytest tests/proofmatch/test_chapter.py tests/proofmatch/test_compare.py -q`

Expected: PASS.

- [ ] **Step 6: Commit chapter comparison**

```bash
git add proofmatch/chapter.py proofmatch/compare.py proofmatch/models.py proofmatch/prompts/compare.md tests/proofmatch/test_chapter.py tests/proofmatch/test_compare.py
git commit -m "feat: compare every relevant chapter theorem"
```

---

### Task 5: Plan and Apply Blueprint Updates Atomically

**Files:**
- Modify: `proofmatch/blueprint.py`
- Modify: `tests/proofmatch/test_blueprint.py`

**Interfaces:**
- Produces:
  - `BlueprintMutation(tex_path: Path, original: str, updated: str)`
  - `plan_source_insert(tex: str, lean_name: str, source: ProofSource) -> str`
  - `plan_step_insert(tex: str, theorem_name: str, steps: Iterable[ProofStep]) -> str`
  - `plan_blueprint_mutations(proposals) -> tuple[BlueprintMutation, ...]`
  - `apply_blueprint_mutations(mutations) -> None`
- Existing `insert_approved_source` and `insert_approved_steps` delegate to the
  pure planners for backward compatibility.

- [ ] **Step 1: Add failing idempotence and conflict-atomicity tests**

```python
def test_batch_plan_is_idempotent(self):
    first = plan_blueprint_mutations(proposals)
    apply_blueprint_mutations(first)
    second = plan_blueprint_mutations(proposals)
    self.assertEqual(second, ())

def test_conflict_in_second_file_writes_neither_file(self):
    before_a, before_b = a.read_text(), b.read_text()
    with self.assertRaisesRegex(ValueError, "proof-source conflict"):
        plan_blueprint_mutations((valid_for_a, conflicting_for_b))
    self.assertEqual(a.read_text(), before_a)
    self.assertEqual(b.read_text(), before_b)
```

- [ ] **Step 2: Run blueprint tests and verify RED**

Run: `python3 -m pytest tests/proofmatch/test_blueprint.py -q`

Expected: FAIL because pure and batch planners are absent.

- [ ] **Step 3: Extract pure string transformations**

Move environment lookup and annotation rendering into functions returning
updated strings. Treat an exact annotation as a no-op and a different source
for the same document/theorem binding as a conflict.

- [ ] **Step 4: Implement all-files preflight and atomic replacement**

Read every target first, calculate every updated value, and raise before
writing if any conflict occurs. Write each changed value to a sibling
temporary file, then replace targets only after all temporary files exist.

- [ ] **Step 5: Run all blueprint and dataset-export tests**

Run: `python3 -m pytest tests/proofmatch/test_blueprint.py tests/proofmatch/test_dataset.py -q`

Expected: PASS.

- [ ] **Step 6: Commit atomic blueprint mutations**

```bash
git add proofmatch/blueprint.py tests/proofmatch/test_blueprint.py
git commit -m "feat: apply proof mappings atomically"
```

---

### Task 6: Automate Upstream Mapping for Every Same Theorem

**Files:**
- Modify: `proofmatch/chapter.py`
- Modify: `proofmatch/upstream.py`
- Modify: `tests/proofmatch/test_chapter.py`
- Modify: `tests/proofmatch/test_upstream.py`

**Interfaces:**
- Produces:
  - `estimate_chapter_upstream(verdicts, candidates, index, dataset, dependency_graph) -> tuple[StageEstimate, ...]`
  - `build_chapter_upstream_manifests(...) -> tuple[ProofStepManifest, ...]`
  - `build_propagation_proposals(...) -> tuple[SourceProposal | StepProposal, ...]`

- [ ] **Step 1: Add a failing propagation-coverage test**

```python
def test_same_theorems_receive_source_and_complete_upstream_mappings(self):
    result = build_propagation_proposals(
        verdicts=(same_one, different_two, same_three),
        upstream_manifests=(manifest_one, manifest_three),
        bindings=bindings,
    )
    self.assertEqual(
        {proposal.theorem for proposal in result if isinstance(proposal, SourceProposal)},
        {"T.one", "T.three"},
    )
    self.assertNotIn("T.two", {proposal.theorem for proposal in result})
    self.assertEqual(
        {assignment.lean_name for assignment in manifest_one.assignments},
        expected_upstream_one,
    )
```

Add a test that any missing upstream declaration aborts before proposals are
returned.

- [ ] **Step 2: Run focused tests and verify RED**

Run: `python3 -m pytest tests/proofmatch/test_chapter.py tests/proofmatch/test_upstream.py -q`

Expected: FAIL because chapter-wide upstream orchestration is absent.

- [ ] **Step 3: Reuse existing batch mapping per same theorem**

For each same theorem, load declarations using
`load_upstream_declarations`, estimate all batches, map them, validate the
manifest against only the theorem's approved blocks, and retain the result in
the chapter manifest.

- [ ] **Step 4: Build source and step proposals without writing**

Create one source proposal per same theorem and one step proposal containing
the complete validated manifest. Submit the combined proposals to Task 5's
atomic planner only after every theorem succeeds.

- [ ] **Step 5: Run chapter and upstream tests**

Run: `python3 -m pytest tests/proofmatch/test_chapter.py tests/proofmatch/test_upstream.py -q`

Expected: PASS.

- [ ] **Step 6: Commit automatic upstream propagation**

```bash
git add proofmatch/chapter.py proofmatch/upstream.py tests/proofmatch/test_chapter.py tests/proofmatch/test_upstream.py
git commit -m "feat: propagate all same theorem dependencies"
```

---

### Task 7: Replace Single-Candidate CLI Runs with Atomic Chapter Runs

**Files:**
- Modify: `proofmatch/cli.py`
- Modify: `tests/proofmatch/test_cli.py`
- Modify: `proofmatch/artifacts.py`

**Interfaces:**
- `run SOURCE --max-cost N` performs discovery, conservative preflight,
  relevance, all comparisons, all same-theorem upstream mappings, artifact
  writes, and one atomic blueprint propagation.
- `review RUN_ID approve --theorem LEAN_NAME` explicitly overrides one
  non-same theorem and propagates it.
- Legacy `review.json` artifacts remain readable.

- [ ] **Step 1: Add failing CLI integration tests**

```python
def test_run_compares_and_propagates_multiple_theorems(self):
    result = run_chapter_fixture(agent_outputs)
    self.assertEqual(
        [item["lean_name"] for item in result["verdicts"]],
        ["T.one", "T.two", "T.three"],
    )
    self.assertIn("\\proofsource", tex_for_one.read_text())
    self.assertNotIn("\\proofsource", tex_for_different.read_text())
    self.assertIn("\\proofstep", tex_for_three.read_text())

def test_insufficient_cap_calls_no_agent_and_writes_no_blueprint(self):
    with self.assertRaises(BudgetExceeded):
        main(["run", str(source), "--max-cost", "0.01"])
    self.assertEqual(agent.calls, [])
    self.assertEqual(tex.read_text(), original)
```

Add tests for rerun idempotence, the theorem-specific override, a
differences-only report, and loading a legacy single review.

- [ ] **Step 2: Run CLI tests and verify RED**

Run: `python3 -m pytest tests/proofmatch/test_cli.py -q`

Expected: FAIL because `run` still selects one primary candidate.

- [ ] **Step 3: Add conservative preflight**

Discover candidates locally, estimate relevance plus comparison for every
candidate, and include upstream upper bounds for every candidate. Require the
sum from a fresh `Budget` before invoking any agent.

- [ ] **Step 4: Wire the chapter orchestrator**

Write `chapter_review.json`, per-theorem upstream artifacts, and a combined
difference report. Call the atomic blueprint planner only after the manifest
is complete and valid.

- [ ] **Step 5: Preserve legacy commands and artifacts**

Keep `map-upstream` and old review loading operational for historical runs.
For chapter artifacts, `review` requires `--theorem` and only accepts an
explicitly named result.

- [ ] **Step 6: Run CLI and complete proofmatch suite**

Run: `python3 -m pytest tests/proofmatch -q`

Expected: PASS.

- [ ] **Step 7: Commit the CLI migration**

```bash
git add proofmatch/cli.py proofmatch/artifacts.py tests/proofmatch/test_cli.py
git commit -m "feat: run chapter-wide proof matching"
```

---

### Task 8: Verify the Complete Pipeline and Run Chapter 2

**Files:**
- Modify as generated by the approved run: matching files under `blueprint/src/chapter/`
- Generate: `blueprint/src/references/boolean-ch02-social-choice-arrow.md`
- Generate: `.proofmatch-work/352ab7ff3113/chapter_review.json`

**Interfaces:**
- Consumes the already split Chapter 2 PDF and validated/local Markdown.
- Produces all same theorem `\proofsource` and upstream `\proofstep`
annotations across the blueprint.

- [ ] **Step 1: Run static and unit verification**

Run: `git diff --check`

Expected: no whitespace errors.

Run: `python3 -m pytest tests/proofmatch -q`

Expected: all tests pass.

- [ ] **Step 2: Run the Chapter 2 dry-run with an explicit cap**

Run:

```bash
python3 scripts/proofmatch.py run \
  blueprint/src/references/boolean-ch02-social-choice-arrow.md \
  --dry-run \
  --max-cost 1.20
```

Expected: lists every discovered blueprint-bound candidate and a conservative
aggregate estimate; performs no paid calls or blueprint writes.

- [ ] **Step 3: If the conservative estimate exceeds $1.20, report the exact estimate**

Do not increase the cap or start paid work without user authorization.

- [ ] **Step 4: If the estimate fits, run Chapter 2**

Run:

```bash
python3 scripts/proofmatch.py match \
  blueprint/src/references/boolean-ch02-social-choice-arrow.md \
  --max-cost 1.20
```

Expected: all relevant theorem comparisons and upstream mappings complete,
all same results propagate atomically, and only different/uncertain results
appear in the difference report.

- [ ] **Step 5: Verify propagation and idempotence**

Run the same command with `--dry-run --max-cost 1.20`, inspect the manifest,
then run:

```bash
python3 scripts/build_dataset.py
python3 -m pytest tests/proofmatch -q
git diff --check
```

Expected: no duplicate annotations, dataset parsing succeeds, and all tests
pass.

- [ ] **Step 6: Commit implementation-generated blueprint mappings separately**

```bash
git add blueprint/src/chapter blueprint/src/references/boolean-ch02-social-choice-arrow.md
git commit -m "docs: map boolean chapter 2 proof sources"
```
