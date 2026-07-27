# Upstream Proof-Step Mapping Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Add a resumable, budgeted pipeline stage that maps every declaration in a matched theorem's Lean proof dependency closure to direct or contextual blocks in the validated PDF Markdown, then writes approved mappings directly into the blueprint.

**Architecture:** A focused `proofmatch.upstream` module extracts and validates dependency records, batches agent inputs, and renders an audit review. Existing blueprint and dataset parsers gain an invisible repeated `\proofstep` macro. The CLI inherits authorization from the approved theorem match and atomically inserts a manifest only after strict validation.

**Tech Stack:** Python 3.14 standard library, existing TCSlib dependency graph and dataset builder, Codex CLI with JSON Schema, LaTeX blueprint metadata, `unittest`.

## Global Constraints

- Map every name in `proof_upstream_decls`; coverage must equal 100%.
- Each declaration has exactly one `direct` or `context` assignment and one or more valid Markdown block IDs.
- Formalization-only helpers map contextually to the informal proof step where they participate.
- Store mappings directly in the blueprint theorem environment as repeated `\proofstep` entries.
- Keep `\proofstep` independent of `\uses` and theorem-level `\proofsource`.
- Never write mappings without an approved theorem-level `same` match.
- Never partially update the blueprint.
- Preserve dependency order in artifacts, blueprint output, and dataset output.
- Enforce the Switching Lemma fixture's USD 1.00 total cap, including the already recorded USD 0.199915.
- Preserve unrelated worktree changes and do not edit generated JSONL directly.

---

## File Structure

- `proofmatch/upstream.py`: dependency records, batching, assignment validation, artifact construction, review rendering.
- `proofmatch/models.py`: strict immutable upstream mapping dataclasses.
- `proofmatch/prompts/map_upstream.md`: declaration-to-proof-block assignment instructions.
- `proofmatch/schemas/map_upstream.json`: strict batched assignment response schema.
- `proofmatch/blueprint.py`: `ProofStep` parsing, formatting, conflict detection, and atomic approved insertion.
- `proofmatch/cli.py`: `map-upstream` and `review-upstream` commands and stage preconditions.
- `proofmatch/budget.py`: conservative batched mapping estimates.
- `blueprint/src/preamble/common.tex`: invisible `\proofstep` macro.
- `scripts/build_dataset.py`: parse and emit ordered `proof_steps`.
- `tests/proofmatch/test_upstream.py`: extraction, batching, validation, review, and stale-fingerprint tests.
- `tests/proofmatch/test_blueprint.py`: macro parsing and insertion tests.
- `tests/proofmatch/test_cli.py`: command precondition and approval tests.
- `tests/proofmatch/test_budget.py`: mapping estimate tests.
- `tests/proofmatch/fixtures/switching_lemma_upstream.json`: closure summary and final validated fixture manifest.

### Task 1: Typed Dependency Records and Total-Coverage Validation

**Files:**
- Modify: `proofmatch/models.py`
- Create: `proofmatch/upstream.py`
- Create: `tests/proofmatch/test_upstream.py`

**Interfaces:**
- Produces: `UpstreamDeclaration(lean_name: str, kind: str, statement: str, source_module: str, direct_dependencies: tuple[str, ...], proof_excerpt: str)`
- Produces: `ProofStepAssignment(lean_name: str, relation: Literal["direct", "context"], document_blocks: tuple[str, ...], rationale: str)`
- Produces: `ProofStepManifest(theorem: str, document: str, source_fingerprint: str, proof_fingerprint: str, dependency_fingerprint: str, assignments: tuple[ProofStepAssignment, ...])`
- Produces: `validate_assignments(declarations, assignments, allowed_blocks) -> tuple[ProofStepAssignment, ...]`
- Consumes: ordered dependency records and the allowed Markdown block IDs.

- [ ] **Step 1: Write failing tests for exact coverage and stable order**

```python
class UpstreamTests(unittest.TestCase):
    def test_validation_requires_every_dependency_once_in_closure_order(self):
        declarations = (
            declaration("T.first"),
            declaration("T.second"),
        )
        assignments = (
            assignment("T.second", "context", ("pdf-abcdef123456-p002-b002",)),
            assignment("T.first", "direct", ("pdf-abcdef123456-p002-b001",)),
        )

        result = validate_assignments(
            declarations,
            assignments,
            {
                "pdf-abcdef123456-p002-b001",
                "pdf-abcdef123456-p002-b002",
            },
        )

        self.assertEqual([item.lean_name for item in result], ["T.first", "T.second"])

    def test_validation_rejects_incomplete_coverage(self):
        with self.assertRaisesRegex(ValueError, "missing.*T.second"):
            validate_assignments(
                (declaration("T.first"), declaration("T.second")),
                (assignment("T.first", "direct", ("pdf-abcdef123456-p002-b001",)),),
                {"pdf-abcdef123456-p002-b001"},
            )

    def test_validation_rejects_duplicate_unknown_and_invalid_blocks(self):
        # Use separate subtests asserting duplicate T.first, unknown T.other,
        # and pdf-abcdef123456-p099-b999 outside allowed_blocks.
```

- [ ] **Step 2: Run the focused tests and verify RED**

Run: `python3 -m unittest tests.proofmatch.test_upstream.UpstreamTests -v`

Expected: import failure because `proofmatch.upstream` does not exist.

- [ ] **Step 3: Implement immutable records and validation**

Implement `validate_assignments` by comparing declaration and assignment
name counters, reporting sorted missing/unknown/duplicate names, validating
nonempty blocks against `allowed_blocks`, and returning assignments reordered
to the declaration sequence. Do not silently discard or repair agent output.

- [ ] **Step 4: Run focused and full tests**

Run: `python3 -m unittest tests.proofmatch.test_upstream -v`

Run: `python3 -m unittest discover -s tests -t . -v`

Expected: all tests pass.

- [ ] **Step 5: Commit**

```bash
git add proofmatch/models.py proofmatch/upstream.py tests/proofmatch/test_upstream.py
git commit -m "feat: validate complete upstream proof mappings"
```

### Task 2: Dependency Extraction, Compact Records, Batching, and Costing

**Files:**
- Modify: `proofmatch/upstream.py`
- Modify: `proofmatch/budget.py`
- Modify: `tests/proofmatch/test_upstream.py`
- Modify: `tests/proofmatch/test_budget.py`

**Interfaces:**
- Produces: `load_upstream_declarations(dataset: Path, dependency_graph: Path, lean_name: str) -> tuple[UpstreamDeclaration, ...]`
- Produces: `batch_declarations(declarations, max_characters: int = 48_000) -> tuple[tuple[UpstreamDeclaration, ...], ...]`
- Produces: `estimate_upstream_batches(batches, proof_blocks, model="gpt-5.6-luna") -> tuple[StageEstimate, ...]`
- Consumes: the selected JSONL record's ordered `proof_upstream_decls` and
  declaration bodies/dependencies from the existing dependency graph index.

- [ ] **Step 1: Write failing extraction and batching tests**

```python
def test_loader_preserves_proof_upstream_order_and_excludes_target(self):
    dataset = write_dataset(
        proof_upstream_decls=["T.a", "T.b"],
        declaration_records={
            "T.a": {"kind": "lemma", "statement": "A", "proof": "by exact h"},
            "T.b": {"kind": "def", "statement": "B", "proof": ""},
        },
    )
    result = load_upstream_declarations(dataset, dependency_graph, "T.target")
    self.assertEqual([item.lean_name for item in result], ["T.a", "T.b"])

def test_batching_is_deterministic_and_never_splits_a_record(self):
    batches = batch_declarations(
        (declaration("T.a", proof_excerpt="a" * 30),
         declaration("T.b", proof_excerpt="b" * 30)),
        max_characters=50,
    )
    self.assertEqual([[d.lean_name for d in batch] for batch in batches],
                     [["T.a"], ["T.b"]])
```

Add a budget test proving that estimates are summed and rejected before a
batch that exceeds the remaining fixture cap.

- [ ] **Step 2: Run focused tests and verify RED**

Run: `python3 -m unittest tests.proofmatch.test_upstream tests.proofmatch.test_budget -v`

Expected: failures because the loader, batcher, and estimate function are absent.

- [ ] **Step 3: Implement deterministic extraction and conservative estimates**

Read the theorem record once, require a nonempty `proof_upstream_decls`, build
the dependency-graph index through the existing dataset-builder helpers, and
construct declaration records without asking an agent to identify names.
Truncate only `proof_excerpt`, recording the truncation marker explicitly;
never truncate names, kinds, statements, or direct dependencies. Estimate each
batch from serialized payload characters plus all allowed proof-block text,
rounding up at four characters per token and reserving 160 output tokens per
declaration.

- [ ] **Step 4: Run focused and full tests**

Run: `python3 -m unittest tests.proofmatch.test_upstream tests.proofmatch.test_budget -v`

Run: `python3 -m unittest discover -s tests -t . -v`

Expected: all tests pass.

- [ ] **Step 5: Commit**

```bash
git add proofmatch/upstream.py proofmatch/budget.py tests/proofmatch/test_upstream.py tests/proofmatch/test_budget.py
git commit -m "feat: prepare budgeted upstream mapping batches"
```

### Task 3: Schema-Constrained Mapping and Review Artifacts

**Files:**
- Create: `proofmatch/prompts/map_upstream.md`
- Create: `proofmatch/schemas/map_upstream.json`
- Modify: `proofmatch/upstream.py`
- Modify: `tests/proofmatch/test_upstream.py`

**Interfaces:**
- Produces: `map_upstream_batches(declarations, blocks, agent, budget) -> tuple[ProofStepAssignment, ...]`
- Produces: `build_manifest(theorem, document, index, proof_text, declarations, assignments) -> ProofStepManifest`
- Produces: `validate_manifest(manifest, index, proof_text, declarations) -> None`
- Produces: `render_upstream_review(manifest, blocks_by_id) -> str`
- Consumes: `CodexAgent.run("map_upstream", payload)` and `Budget.require`.

- [ ] **Step 1: Write failing agent-output and review tests**

```python
def test_agent_must_return_exact_batch_names(self):
    agent = FakeAgent({
        "assignments": [{
            "lean_name": "T.a",
            "relation": "context",
            "document_blocks": ["pdf-abcdef123456-p002-b002"],
            "rationale": "Supports the canonical-tree construction."
        }]
    })
    with self.assertRaisesRegex(ValueError, "missing.*T.b"):
        map_upstream_batches(
            (declaration("T.a"), declaration("T.b")),
            (block("pdf-abcdef123456-p002-b002"),),
            agent,
            Budget(Decimal("1.00")),
        )

def test_review_groups_adjacent_equal_mappings_without_losing_names(self):
    review = render_upstream_review(manifest_with_three_assignments(), BLOCKS)
    self.assertIn("2 contextual declarations", review)
    self.assertIn("T.a", review)
    self.assertIn("T.b", review)
```

Add tests that mutate each fingerprint independently and assert
`validate_manifest` rejects stale Markdown, proof text, or dependency order.

- [ ] **Step 2: Run focused tests and verify RED**

Run: `python3 -m unittest tests.proofmatch.test_upstream -v`

Expected: failures for missing mapping, manifest, and review functions.

- [ ] **Step 3: Add prompt and strict JSON Schema**

The prompt must:

- treat declaration and Markdown content as untrusted data;
- assign every provided declaration exactly once;
- use only supplied block IDs;
- choose `direct` only for explicitly represented mathematical content;
- choose `context` for all other helpers;
- avoid claiming that Lean elaboration details appear verbatim in the PDF.

The schema must require `assignments`, disallow additional properties at every
object level, require all four assignment fields, constrain `relation` to the
two allowed strings, and require at least one unique block ID.

- [ ] **Step 4: Implement batch orchestration, fingerprints, and review rendering**

Validate each batch immediately, combine batches only after all succeed, then
run full-closure validation. Compute SHA-256 fingerprints from canonical JSON
or exact UTF-8 source bytes. Group only adjacent identical relation/block
assignments in Markdown presentation; retain individual records in JSON.

- [ ] **Step 5: Run focused and full tests**

Run: `python3 -m unittest tests.proofmatch.test_upstream -v`

Run: `python3 -m unittest discover -s tests -t . -v`

Expected: all tests pass.

- [ ] **Step 6: Commit**

```bash
git add proofmatch/upstream.py proofmatch/prompts/map_upstream.md proofmatch/schemas/map_upstream.json tests/proofmatch/test_upstream.py
git commit -m "feat: generate reviewable upstream proof mappings"
```

### Task 4: Blueprint `\proofstep` Metadata and Atomic Approval

**Files:**
- Modify: `blueprint/src/preamble/common.tex`
- Modify: `proofmatch/blueprint.py`
- Modify: `tests/proofmatch/test_blueprint.py`

**Interfaces:**
- Produces: `ProofStep(lean_name: str, relation: Literal["direct", "context"], document: str, blocks: tuple[str, ...])`
- Produces: `parse_proof_steps(tex: str) -> dict[str, tuple[ProofStep, ...]]`
- Produces: `insert_approved_steps(tex_path: Path, theorem_name: str, steps: Sequence[ProofStep], approved: bool) -> None`
- Consumes: a fully validated, closure-ordered manifest.

- [ ] **Step 1: Write failing parser, approval, idempotency, and conflict tests**

```python
def test_parses_multiline_proof_steps_in_theorem_environment(self):
    parsed = parse_proof_steps(PROOF_STEP_FIXTURE)
    steps = parsed["SwitchingLemma2.switching_lemma"]
    self.assertEqual(steps[0].lean_name, "SwitchingLemma2.canonicalDTree_correct")
    self.assertEqual(steps[0].relation, "context")

def test_identical_reapproval_is_idempotent(self):
    insert_approved_steps(path, "T.target", steps, approved=True)
    once = path.read_text()
    insert_approved_steps(path, "T.target", steps, approved=True)
    self.assertEqual(path.read_text(), once)

def test_conflicting_existing_step_is_preserved_and_rejected(self):
    with self.assertRaisesRegex(ValueError, "conflict.*T.helper"):
        insert_approved_steps(path, "T.target", changed_steps, approved=True)
    self.assertEqual(path.read_text(), original)
```

Also assert `approved=False` raises before writing and malformed relations or
block IDs are rejected.

- [ ] **Step 2: Run focused tests and verify RED**

Run: `python3 -m unittest tests.proofmatch.test_blueprint -v`

Expected: import failure for the new symbols.

- [ ] **Step 3: Implement the invisible macro, parser, formatter, and atomic insertion**

Add `\newcommand{\proofstep}[4]{}` to the preamble. Format one independent
multiline macro per declaration. Before writing, parse all existing steps in
the target theorem environment, reject any changed mapping for an existing
name, merge only missing identical-order records, build the complete updated
text in memory, and replace the file once.

- [ ] **Step 4: Run focused and full tests**

Run: `python3 -m unittest tests.proofmatch.test_blueprint -v`

Run: `python3 -m unittest discover -s tests -t . -v`

Expected: all tests pass.

- [ ] **Step 5: Commit**

```bash
git add blueprint/src/preamble/common.tex proofmatch/blueprint.py tests/proofmatch/test_blueprint.py
git commit -m "feat: store approved proof-step mappings in blueprint"
```

### Task 5: Dataset Builder Integration

**Files:**
- Modify: `scripts/build_dataset.py`
- Modify: `tests/proofmatch/test_blueprint.py`

**Interfaces:**
- Produces: blueprint metadata key `proof_steps: list[dict[str, object]]`
- Produces: dataset record field `proof_steps`, ordered by `proof_upstream_decls`
- Consumes: repeated `\proofstep` macros within a bound blueprint environment.

- [ ] **Step 1: Write failing dataset parser tests**

```python
def test_dataset_parser_emits_proof_steps_without_leaking_macros_into_prose(self):
    parsed = parse_blueprint_fixture(PROOF_STEP_FIXTURE)
    record = parsed["SwitchingLemma2.switching_lemma"]
    self.assertEqual(
        record["proof_steps"],
        [{
            "lean_name": "SwitchingLemma2.canonicalDTree_correct",
            "relation": "context",
            "document": "switching-lemma",
            "blocks": ["pdf-abcdef123456-p002-b002"],
        }],
    )
    self.assertNotIn("\\proofstep", record["informal"])
```

Add tests for duplicate declaration rejection and output ordering according to
an explicit `proof_upstream_decls` sequence.

- [ ] **Step 2: Run focused tests and verify RED**

Run: `python3 -m unittest tests.proofmatch.test_blueprint -v`

Expected: assertion failure because `proof_steps` is absent.

- [ ] **Step 3: Extend metadata parsing and record emission**

Add a multiline `PROOF_STEP_RE`, include `proofstep` in metadata-line
suppression, parse the four arguments, validate unique names, and emit the
records. When building a record with proof data, reorder parsed steps by
`proof_upstream_decls`; reject missing, extra, or duplicate names rather than
emitting partial coverage.

- [ ] **Step 4: Run focused tests, a temporary dataset build, and full tests**

Run: `python3 -m unittest tests.proofmatch.test_blueprint -v`

Run:

```bash
tmp_dir="$(mktemp -d)"
python3 scripts/build_dataset.py --out "$tmp_dir/proofsteps.jsonl" --limit 20
```

Inspect the temporary JSONL only; do not overwrite
`dataset/tcslib_theorems.jsonl`.

Run: `python3 -m unittest discover -s tests -t . -v`

Expected: all tests pass and the temporary builder exits zero.

- [ ] **Step 5: Commit**

```bash
git add scripts/build_dataset.py tests/proofmatch/test_blueprint.py
git commit -m "feat: export blueprint proof-step mappings"
```

### Task 6: CLI Generation, Resumption, and Separate Review Gate

**Files:**
- Modify: `proofmatch/cli.py`
- Modify: `tests/proofmatch/test_cli.py`

**Interfaces:**
- Produces: `proofmatch map-upstream RUN_ID [--max-cost USD] [--dry-run]`
- Produces: `proofmatch review-upstream RUN_ID` as a read-only audit command
- Writes: `upstream_input.json`, `proof_steps.json`, `proof_steps_review.md`, `upstream_decision.json`
- Consumes: approved theorem-level `review.json` and `decision.json`.

- [ ] **Step 1: Write failing CLI precondition and dry-run tests**

```python
def test_map_upstream_requires_same_and_approved_theorem_match(self):
    store.write_json("review", {"verdict": {"verdict": "same"}})
    store.write_json("decision", {"decision": "defer"})
    with self.assertRaisesRegex(ValueError, "theorem-level approval"):
        main(["map-upstream", run_id, "--max-cost", "1.00"])

def test_map_upstream_dry_run_writes_no_manifest_or_blueprint(self):
    result = main(["map-upstream", run_id, "--max-cost", "1.00", "--dry-run"])
    self.assertEqual(result, 0)
    self.assertFalse(store.stage_path("proof_steps", ".json").exists())
    self.assertEqual(tex_path.read_text(), original_tex)

def test_map_upstream_auto_inserts_after_validation(self):
    main(["map-upstream", run_id, "--max-cost", "1.00"])
    self.assertIn("\\proofstep", tex_path.read_text())
    self.assertEqual(
        store.read_json("upstream_decision"),
        {"decision": "inherited-theorem-approval"},
    )
```

Add tests for non-`same` verdicts, missing artifacts, stale fingerprints,
budget exhaustion, and a failed batch leaving no final manifest.

- [ ] **Step 2: Run focused tests and verify RED**

Run: `python3 -m unittest tests.proofmatch.test_cli -v`

Expected: parser rejection of the new commands.

- [ ] **Step 3: Implement `map-upstream`**

Resolve the original source Markdown and theorem from `review.json`; require
`same` plus theorem-level `approve`; load the dependency closure; limit allowed
blocks to the theorem-level proof source plus its section heading; compute and
print all batch estimates. In dry-run mode stop there. In paid mode reserve
each estimate before invoking Codex, write intermediate batch artifacts for
resumption, validate full coverage, then atomically write the final JSON and
review Markdown.

- [ ] **Step 4: Implement automatic insertion and read-only audit**

After generation, rerun all fingerprint and coverage checks before calling
`insert_approved_steps`; record inherited theorem authorization.
`review-upstream` prints the grouped audit and performs no mutation.

- [ ] **Step 5: Run focused and full tests**

Run: `python3 -m unittest tests.proofmatch.test_cli -v`

Run: `python3 -m unittest discover -s tests -t . -v`

Expected: all tests pass.

- [ ] **Step 6: Commit**

```bash
git add proofmatch/cli.py tests/proofmatch/test_cli.py
git commit -m "feat: add upstream proof mapping workflow"
```

### Task 7: Switching Lemma End-to-End Fixture

**Files:**
- Create: `tests/proofmatch/fixtures/switching_lemma_upstream.json`
- Modify after successful validated mapping: `blueprint/src/chapter/BooleanAnalysis/SwitchingLemma.tex`
- Modify: `blueprint/.proofmatch-evals/switching-lemma-report.md`

**Interfaces:**
- Consumes: run `b5e074215b9e`, the current validated Markdown, and the current `SwitchingLemma2.switching_lemma` closure.
- Produces: a 100%-coverage audit artifact and blueprint `\proofstep` entries.

- [ ] **Step 1: Run the cost-only fixture command**

Run:

```bash
python3 scripts/proofmatch.py map-upstream b5e074215b9e --dry-run --max-cost 1.00
```

Expected: report the exact dependency count and batch estimates, make no agent
call, preserve the blueprint, and show total estimated spend including
USD 0.199915 below USD 1.00. If the estimate exceeds the cap, stop and redesign
batch payloads; do not raise the cap automatically.

- [ ] **Step 2: Write the live-fixture coverage test and verify RED**

Add a test that expects
`tests/proofmatch/fixtures/switching_lemma_upstream.json`, loads it through
strict typed loading, and compares its assignment names with the current
ordered closure. Run:

```bash
python3 -m unittest tests.proofmatch.test_upstream.UpstreamTests.test_switching_lemma_fixture_has_total_coverage -v
```

Expected: fail because the validated fixture manifest does not exist.

- [ ] **Step 3: Run paid mapping within the approved cap**

Run:

```bash
python3 scripts/proofmatch.py map-upstream b5e074215b9e --max-cost 1.00
```

Expected: write a complete manifest and grouped audit, report 100% coverage,
and atomically insert the validated blueprint mappings.

- [ ] **Step 4: Validate and install the live fixture manifest**

Validate the generated manifest manually, then copy only the compact validated
manifest into the fixture path required by the failing test. The test asserts:

```python
self.assertEqual(manifest.theorem, "SwitchingLemma2.switching_lemma")
self.assertEqual(
    {item.lean_name for item in manifest.assignments},
    set(current_proof_upstream_decls),
)
self.assertTrue(all(item.document_blocks for item in manifest.assignments))
self.assertTrue(all(item.relation in {"direct", "context"}
                    for item in manifest.assignments))
```

Do not copy transient agent prompts or credentials.

- [ ] **Step 5: Run fixture and full tests**

Run: `python3 -m unittest tests.proofmatch.test_upstream -v`

Run: `python3 -m unittest discover -s tests -t . -v`

Expected: all tests pass.

- [ ] **Step 6: Present the grouped mapping as an audit**

Report counts and the audit artifact path. Do not print a fabricated
differences section.

- [ ] **Step 7: Verify automatic insertion**

Run:

```bash
python3 scripts/proofmatch.py review-upstream b5e074215b9e
```

Then verify:

```bash
python3 -m unittest discover -s tests -t . -v
python3 -c 'from scripts.build_dataset import parse_blueprint; r=parse_blueprint()["SwitchingLemma2.switching_lemma"]; assert len(r["proof_steps"]) == len(set(x["lean_name"] for x in r["proof_steps"]))'
git diff --check
```

Expected: blueprint mappings exactly cover the closure, both parsers agree,
all tests pass, and no unapproved file is modified.

- [ ] **Step 8: Update evaluation and commit**

Record the dependency count, direct/context counts, mapping-stage cost,
approval status, and verification evidence in the evaluation report.

```bash
git add tests/proofmatch/fixtures/switching_lemma_upstream.json \
  blueprint/src/chapter/BooleanAnalysis/SwitchingLemma.tex \
  blueprint/.proofmatch-evals/switching-lemma-report.md
git commit -m "docs: map switching lemma upstream proof steps"
```

### Task 8: Final Verification and Branch Handoff

**Files:**
- Verify only; no expected production changes.

**Interfaces:**
- Consumes: all preceding commits.
- Produces: reproducible verification evidence and a clean feature branch.

- [ ] **Step 1: Run the complete test suite**

Run: `python3 -m unittest discover -s tests -t . -v`

Expected: zero failures and zero errors.

- [ ] **Step 2: Verify CLI and source invariants**

Run:

```bash
python3 scripts/proofmatch.py --help
git diff --check
git status --short
```

Assert:

- both new commands appear in help;
- no stale differences report exists for the `same` theorem match;
- final mapping coverage is 100%;
- all referenced anchors exist in `switching-lemma.md`;
- `proof_steps` remain separate from `uses` and `proof_sources`;
- the working tree is clean except for any explicitly documented generated
  bytecode, which must not be committed.

- [ ] **Step 3: Review requirement coverage against the design spec**

Read
`docs/superpowers/specs/2026-07-27-upstream-proof-step-mapping-design.md`
line by line and record any unmet requirement. Do not claim completion if a
requirement or approval remains pending.

- [ ] **Step 4: Use the branch-finishing workflow**

Invoke `superpowers:finishing-a-development-branch` only after all required
approvals are complete and verification is green. Present integration options
without modifying the user's main checkout automatically.
