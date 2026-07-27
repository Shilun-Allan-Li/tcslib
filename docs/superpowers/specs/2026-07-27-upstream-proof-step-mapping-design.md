# Upstream Proof-Step Mapping Design

## Goal

Extend the PDF–Lean proof-matching pipeline so every declaration in the
selected theorem's ordered Lean proof dependency closure maps to one or more
stable blocks in the validated Markdown reference. A declaration that is not
stated explicitly in the PDF must map to the informal proof segment where it
is used.

The mapping is stored directly in the theorem's blueprint environment,
reviewed by a human before insertion, and exported by the existing dataset
builder independently of `\uses`.

## Scope

The stage covers every name in the selected theorem's
`proof_upstream_decls`, including definitions and implementation lemmas. The
selected theorem retains its existing theorem-level `\proofsource` entry.

Every upstream declaration must receive at least one mapping. The stage does
not allow an unclassified or silently omitted declaration. Lean-specific
bookkeeping declarations map contextually to the informal proof step they
implement.

## Blueprint Representation

The preamble defines an invisible four-argument macro:

```tex
\newcommand{\proofstep}[4]{}
```

Each approved mapping is recorded as a separate entry inside the theorem
environment:

```tex
\proofstep
  {SwitchingLemma2.canonicalDTree_correct}
  {context}
  {switching-lemma}
  {pdf-b5e074215b9e-p002-b002}

\proofstep
  {SwitchingLemma2.razborovEncode_injective}
  {direct}
  {switching-lemma}
  {pdf-b5e074215b9e-p002-b004}
```

The arguments are:

1. the fully qualified Lean declaration name;
2. `direct` or `context`;
3. the Markdown document stem;
4. a comma-separated nonempty list of stable PDF block identifiers.

`direct` means that the referenced blocks explicitly state or prove the
declaration's mathematical content. `context` means that the declaration
supports the proof step represented by the referenced blocks but is not
separately stated there.

Entries remain independent rather than being compressed by shared anchors.
This keeps declaration-level diffs, parsing, and later correction simple.
`\proofstep` is separate from `\uses`, whose existing dependency semantics and
dataset parsing remain unchanged.

## Dependency Source of Truth

The stage obtains the ordered dependency closure using the same proof builder
that produces `proof_upstream_decls` in `scripts/build_dataset.py`. It must not
derive the closure from prose, blueprint `\uses`, or agent output.

The stage accepts:

- the selected theorem name;
- its full Lean proof text and ordered upstream declaration names;
- the validated Markdown index and stable block IDs;
- the approved theorem-level `\proofsource`.

The theorem-level source bounds the primary proof region. Context may include
the section heading or immediately adjacent definition blocks when necessary,
but every emitted block ID must exist in the validated Markdown.

## Mapping Pipeline

### Deterministic preparation

The pipeline builds a compact record for each upstream declaration containing
its fully qualified name, kind, statement, source module, direct dependencies,
and a bounded proof outline or body excerpt. It groups declarations by
dependency locality and conceptual role while preserving the original ordered
closure.

Large closures are processed in bounded batches. Each batch includes the
validated PDF proof blocks and the already assigned neighboring declarations
needed for consistency. The full raw Lean proof is not repeated in every
agent request.

### Agent assignment

A schema-constrained Codex prompt assigns every declaration in a batch:

- `lean_name`;
- `relation`, exactly `direct` or `context`;
- one or more `document_blocks`;
- a concise rationale grounded in both the declaration and the PDF step.

Agent output may propose mappings but cannot add, remove, or rename dependency
declarations. It cannot cite block IDs outside the validated Markdown.

### Deterministic validation

Before review, the pipeline verifies:

- exact set equality between the dependency closure and mapped declarations;
- exactly one mapping record per declaration;
- a valid relation value;
- a nonempty block list;
- membership of every block in the Markdown index;
- membership of every cited block in the allowed proof context;
- stable dependency order in the rendered review and blueprint insertion.

Duplicate declarations, conflicting assignments, unknown declarations,
invented anchors, empty mappings, and incomplete coverage fail the stage.
They produce no blueprint edit.

## Review and Approval

The stage writes a resumable `proof_steps.json` artifact and a compact
`proof_steps_review.md`. The review groups adjacent declarations that share
the same relation and blocks for readability, while the JSON retains one
record per declaration.

The review summary reports:

- total upstream declarations;
- direct and contextual counts;
- coverage percentage, which must be 100%;
- mappings grouped by PDF block;
- declaration names and rationales;
- validation failures, if any.

This stage has its own explicit `approve`, `reject`, or `defer` decision.
Prior approval of the theorem-level proof match does not authorize inserting
dependency-level mappings. Only `approve` writes `\proofstep` entries.

Insertion is idempotent. Re-approving an identical manifest makes no change.
An existing mapping with a different relation or block list is a conflict and
must return to review rather than being overwritten silently.

## CLI Workflow

The existing CLI gains:

```text
proofmatch map-upstream RUN_ID [--max-cost USD] [--dry-run]
proofmatch review-upstream RUN_ID [approve|reject|defer]
```

`map-upstream` requires an existing successful theorem-level review artifact
whose verdict is `same` and whose theorem-level decision is `approve`.

`--dry-run` extracts the closure, reports batch sizes and a conservative cost
estimate, and makes no agent call or file edit. Paid execution enforces the
specified cost cap before each batch. The initial Switching Lemma run retains
the existing overall fixture cap of USD 1.00, including prior recorded spend.

`review-upstream` prints the grouped review. Approval validates the artifact
again against the current Markdown, dependency closure, and blueprint before
insertion.

## Dataset Output

The dataset builder parses `\proofstep` entries from blueprint metadata and
adds:

```json
{
  "proof_steps": [
    {
      "lean_name": "SwitchingLemma2.canonicalDTree_correct",
      "relation": "context",
      "document": "switching-lemma",
      "blocks": ["pdf-b5e074215b9e-p002-b002"]
    }
  ]
}
```

The list follows `proof_upstream_decls` order. Dataset construction validates
that names are unique. The theorem-level `proof_sources` field remains
unchanged. `\proofstep` lines are metadata and must not leak into informal
statement text.

## Artifacts and Resumption

The run store adds:

- `upstream_input.json`: dependency fingerprint, declaration summaries,
  allowed blocks, batching plan, and cost estimate;
- `proof_steps.json`: strict declaration-level assignments and rationales;
- `proof_steps_review.md`: grouped human review;
- `upstream_decision.json`: the explicit decision.

Artifacts include fingerprints of the validated Markdown, selected Lean
proof, dependency name sequence, prompt, and schema. A changed fingerprint
invalidates prior assignments and requires remapping and renewed approval.

## Failure Handling

- Missing or non-`same` theorem verdict: refuse to start.
- Missing theorem-level approval: refuse to start.
- Dependency extraction failure: report the declaration/build error without
  calling an agent.
- Cost estimate exceeds the remaining cap: stop before the paid batch.
- Partial or malformed agent output: reject the batch; do not infer omitted
  mappings.
- Invalid or stale block IDs: invalidate the manifest.
- Dependency closure changed since mapping: invalidate the manifest.
- Blueprint conflict: preserve existing metadata and return to review.

No failure path writes partial `\proofstep` metadata.

## Testing

Unit and integration tests cover:

- extraction of the ordered upstream closure;
- compact declaration records and deterministic batching;
- strict schema loading;
- total-coverage validation;
- rejection of missing, duplicate, unknown, and conflicting declarations;
- rejection of invalid, empty, and out-of-context block lists;
- parsing and formatting multiline `\proofstep` entries;
- idempotent approved insertion and conflict preservation;
- refusal to insert before explicit upstream approval;
- dataset parsing and output ordering;
- suppression of macros from informal prose;
- CLI preconditions, dry-run behavior, budget enforcement, resumption, and
  stale-fingerprint rejection;
- a Switching Lemma fixture asserting 100% coverage of its current upstream
  dependency closure.

The fixture test must not assert that all mappings are `direct`; contextual
mappings are expected for formalization-specific helpers.
