# Multi-Theorem Proof Matching and Blueprint Propagation

## Goal

A chapter-scale PDF or Markdown source must be matched against every relevant
TCSlib theorem represented in the blueprint. The pipeline must not stop after
selecting one primary candidate.

Every theorem whose Lean proof is judged `same` must be written to the
blueprint automatically. Its relevant upstream declarations must also be
mapped to source blocks as `direct` or `context` proof steps without a second
human-review gate. `different` and `uncertain` results are report-only.

## Scope

This change extends the existing local PDF extraction, Codex cleanup,
candidate search, proof comparison, proof-source insertion, and upstream
mapping workflow. It does not change PDF extraction or Markdown anchor
formats.

Only Lean declarations bound by `\lean{...}` in the blueprint are eligible
for chapter-level matching and propagation. Dataset declarations outside the
blueprint may still appear as upstream dependencies, but they cannot become
top-level chapter matches.

## Candidate Discovery

The validated Markdown is divided into semantic segments using headings,
theorem-like blocks, proofs, and their surrounding context. Candidate
discovery operates independently for every segment.

Discovery uses two complementary directions:

1. For each document segment, retrieve high-scoring blueprint-bound Lean
   declarations.
2. For each blueprint-bound Lean declaration with lexical overlap, retain its
   best-scoring document segments.

The union is deduplicated by Lean name. A candidate may cite multiple
noncontiguous source blocks when those blocks jointly contain its statement
and proof. Retrieval limits apply per segment rather than to the whole
document, preventing early sections from consuming the candidate quota.

## Relevance Classification

A batched Codex relevance pass receives document block summaries and candidate
statements, but not full Lean proofs. For every candidate it must return:

- whether the source contains the theorem or uses it materially in context;
- the exact source blocks supporting that classification;
- a short rationale.

Candidates classified as irrelevant are saved in the run manifest for audit
but receive no proof-comparison call. This stage is deliberately
high-recall: uncertainty about relevance advances a candidate to proof
comparison rather than discarding it.

## Proof Comparison

Every relevant candidate is compared independently using its selected source
blocks and full Lean proof. Verdicts retain the existing values:

- `same`: the mathematical argument agrees, allowing ordinary formalization
  detail and a Lean statement that projects a clearly identifiable component
  of a stronger source result;
- `different`: the source and Lean proof use materially different arguments,
  or the selected source does not establish the Lean result;
- `uncertain`: evidence is insufficient.

The comparison output continues to record evidence, proof outlines,
confidence, and substantive differences. A narrower Lean projection of a
stronger source theorem may be `same` when its proof is precisely the
corresponding part of the stronger proof. This incorporates the Chapter 4
decision-tree-to-DNF/CNF case into the standard verdict semantics.

## Automatic Propagation

After all comparisons and upstream mappings have completed successfully:

1. Insert an idempotent `\proofsource` annotation into every blueprint
   environment whose verdict is `same`.
2. Map every relevant upstream declaration used by each same theorem to the
   theorem's approved source blocks.
3. Insert those mappings as idempotent `\proofstep` annotations with relation
   `direct` or `context`.

No second granular human review is required. Existing identical annotations
are preserved. Conflicting annotations abort propagation and leave all
blueprint files unchanged.

Verdicts of `different` and `uncertain` never mutate the blueprint. A
theorem-specific override command may convert an explicitly accepted result,
such as a narrower formal projection, into an approved source and trigger its
upstream propagation.

## Atomicity and Budgeting

Before paid work begins, the pipeline estimates:

- batched relevance classification;
- every anticipated proof comparison;
- upstream mapping for candidates expected to be approved.

Because exact relevant candidates are not known until classification, the
estimate uses a conservative upper bound over all discovered candidates.
If the supplied cap cannot cover this bound, the run stops before paid work.

Paid stages charge one shared run budget. Blueprint mutations occur only
after all paid stages and validation succeed. Mutations are prepared in
memory, checked for conflicts across every affected file, then written
atomically. A failure or exhausted budget therefore produces artifacts but
no partial blueprint propagation.

## Run Artifacts and CLI

A chapter run stores one manifest containing:

- source Markdown and fingerprint;
- all discovered candidates and their proposed blocks;
- relevance decisions;
- comparison verdicts;
- per-stage and aggregate estimated spend;
- upstream manifests for same or overridden theorems;
- propagation status.

The difference report contains only `different` and `uncertain` verdicts.

The existing `run` command becomes multi-theorem by default. Dry-run output
lists all discovered candidates and the conservative total estimate. Existing
single-theorem artifacts remain readable for backward compatibility.

The review command supports theorem-specific overrides. `same` results need
no review command because they propagate automatically.

## Failure Handling

The run fails without blueprint mutation when:

- a source block cited by an agent does not exist;
- the same Lean theorem receives incompatible block assignments;
- a candidate has no unique blueprint environment;
- an upstream manifest fails coverage or fingerprint validation;
- an existing blueprint annotation conflicts with the proposed annotation;
- the run budget is insufficient;
- an agent output fails schema validation.

Irrelevant candidates and valid `different` or `uncertain` verdicts are normal
results, not failures.

## Testing

Tests must establish:

- per-segment retrieval does not collapse to a document-global top candidate;
- only blueprint-bound declarations become top-level candidates;
- relevance classification retains all supported theorem/block pairs;
- all relevant candidates are compared, not merely the first;
- `same` verdicts propagate source and upstream annotations automatically;
- `different` and `uncertain` verdicts produce reports without mutation;
- accepted narrower projections can be represented as `same`;
- duplicate annotations are idempotent and conflicts are atomic;
- insufficient budgets prevent paid work and blueprint writes;
- legacy single-theorem artifacts remain readable;
- a chapter fixture with multiple source theorems updates every corresponding
  blueprint environment.

## Acceptance Criteria

A rerun on Boolean Analysis Chapter 2 must consider all relevant
blueprint-bound theorems, compare each supported match, automatically annotate
every `same` result and its relevant upstream declarations, emit differences
only for nonmatching results, and make no duplicate changes on a second run.
