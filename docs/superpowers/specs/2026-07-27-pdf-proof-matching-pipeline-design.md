# PDF–Lean Proof Matching Pipeline Design

## Goal

Build a Codex-oriented command-line workflow that:

1. optionally converts a local PDF into traceable Markdown,
2. searches TCSlib for corresponding theorems and proofs in either direction,
3. determines whether the informal and Lean proofs have the same mathematical structure,
4. reports only material differences or uncertainty,
5. asks the user to adjudicate every proposed match, and
6. writes approved proof-source links into the existing blueprint metadata.

The first end-to-end fixture is
`blueprint/src/references/switching-lemma.pdf`, a four-page lecture note.

## Scope

The initial implementation targets Codex as the agent runtime and local PDF files
only. It uses TCSlib's existing blueprint and generated theorem JSONL dataset.

PDF conversion is an optional preprocessing subsystem. Proof matching accepts an
already validated Markdown file directly, so the extraction audit, selective OCR,
and fixture-specific cost cap can be removed later without changing search,
comparison, review, or blueprint integration.

The workflow does not publish or download PDFs, silently accept agent judgments,
or directly edit generated JSONL records.

## Architecture

The pipeline is staged and artifact-driven. Each stage has a narrow responsibility,
reads versioned artifacts, emits schema-validated artifacts, and can be resumed
without replaying successful paid work.

The stages are:

1. local PDF text extraction,
2. Codex text cleanup,
3. selective visual validation,
4. document indexing,
5. bidirectional TCSlib candidate discovery,
6. proof-structure comparison,
7. human adjudication,
8. blueprint annotation or resource suggestions.

Successful artifacts are cached using fingerprints of the PDF or Markdown input,
prompt version, model configuration, TCSlib dataset record, and relevant Lean
source. A changed input invalidates only dependent stages.

## Durable Reference Files

For the initial fixture, the durable source files are:

```text
blueprint/src/references/switching-lemma.pdf
blueprint/src/references/switching-lemma.raw.md
blueprint/src/references/switching-lemma.md
```

Both Markdown files are committed:

- `switching-lemma.raw.md` is a faithful, page-delimited local extraction with no
  silent cleanup.
- `switching-lemma.md` is the Codex-repaired and selectively visually validated
  document.

Both record the source PDF fingerprint and extraction tool/version. Regenerable
diagnostics, page renders, prompt inputs and outputs, cost logs, and intermediate
JSON remain in a separate work directory.

## PDF Extraction and Repair

Local extraction always precedes paid vision processing. The extractor operates
page by page and records diagnostics including:

- empty or nearly empty pages,
- suspicious symbol density,
- detached mathematical operators,
- broken reading order,
- repeated headers and footers,
- unusual line fragmentation, and
- likely encoding or ligature corruption.

A Codex cleanup agent receives page-bounded raw text first. It reconstructs
headings, prose order, theorem and proof boundaries, and mathematical notation.
The acceptance criterion is accurate semantic unscrambling, not byte-for-byte
transcription or visual-layout preservation.

The cleanup agent must not invent missing mathematics. It attaches confidence and
ambiguity records to uncertain blocks. Only ambiguous or diagnostically suspect
blocks are escalated to inspection of the corresponding PDF page image.

The validated Markdown uses stable block IDs derived from the PDF fingerprint,
page number, and block sequence. IDs do not depend on agent-written headings.
Every block retains PDF page provenance and, when available, a bounding box.

## Document Index

The indexing stage divides validated Markdown into:

- definitions,
- theorem and lemma statements,
- proof blocks,
- named or inferred proof steps, and
- surrounding explanatory material.

It preserves the original block IDs and creates compact searchable summaries.
Summaries assist retrieval but never replace the cited source text.

## Candidate Discovery

Candidate discovery is bidirectional:

- When the PDF proof block is shorter, the pipeline uses its statement,
  definitions, and proof outline to search TCSlib theorem metadata.
- When the relevant Lean proof is shorter, the pipeline uses the Lean statement,
  proof dependencies, and proof outline to search indexed PDF blocks.

The first retrieval pass is deterministic and uses lexical terms, mathematical
identifiers, titles, informal statements, source modules, and existing dependency
metadata in `dataset/tcslib_theorems.jsonl`. Codex reranks a bounded candidate set.
It must not place all complete Lean proofs and the entire document into one prompt.

Only plausible candidates receive a complete proof-structure comparison.

## Proof-Structure Comparison

For each candidate, Codex produces normalized outlines for the informal and Lean
proofs. Comparison focuses on mathematical content:

- assumptions and quantifiers,
- intermediate mathematical claims,
- constructions,
- induction parameters,
- substantive case splits,
- key identities or inequalities, and
- final assembly of the conclusion.

The comparison disregards formalization-only details such as coercions, typeclass
and decidability instances, finite-set plumbing, normalization tactics, and helper
lemmas whose only role is satisfying Lean.

The verdict is one of:

- `same`: the essential strategy and mathematical steps correspond;
- `different`: the argument, claim strength, hypotheses, direction, construction,
  or another essential mathematical step differs;
- `uncertain`: extraction or mathematical evidence is insufficient.

A user-facing differences report is emitted only for `different` or `uncertain`.
A `same` verdict remains quiet and proceeds directly to human approval.

## Human Review

No agent verdict modifies the blueprint automatically. For each candidate, the CLI
presents:

- the Lean theorem name,
- exact Markdown block links,
- normalized proof outlines,
- confidence and evidence, and
- material differences or unresolved ambiguity only when they exist.

The user can approve, reject, or defer:

- Approval adds a proof-source annotation to the existing blueprint entry.
- Rejection records the decision in run state and invokes a resource-suggestion
  agent for the proof actually formalized.
- Deferral leaves the case resumable and makes no source edit.

## Blueprint Metadata

The blueprint remains the source of truth. Formal dependencies continue to use
`\uses{...}`. Informal proof correspondence uses a separate macro, conceptually:

```latex
\proofsource{switching-lemma}{pdf-block-id}
```

The exact macro syntax will be fixed in the implementation plan. It must support
one or more exact Markdown blocks and resolve those blocks through Markdown
provenance to the PDF fingerprint and page.

The dataset builder will parse approved proof-source metadata and add it to theorem
records. Generated JSONL is never edited directly.

## Cost Controls

The initial four-page fixture has a hard API-equivalent cost cap of USD 1.00. The
CLI estimates the next paid stage before starting it and stops if the stage could
exceed the remaining budget. It records actual token usage and cost when the
runtime exposes them; otherwise it records a conservative estimate.

The USD 1.00 cap is fixture-specific, not a permanent default. Later runs require
an explicit budget appropriate to their document size.

The cost-control strategy is:

- use free local extraction first,
- attempt text-only cleanup before page images,
- inspect images only for ambiguous or suspect blocks,
- use deterministic retrieval before Codex reranking, and
- compare complete Lean proofs only for plausible candidates.

## Failure Handling and Resumption

Every agent output is schema-validated before use. Malformed output is retained for
diagnosis and retried only within a bounded policy. Failed stages preserve all
previous successful artifacts and print an exact resume command.

Uncertain reconstruction is not silently accepted. It becomes an ambiguity that
either triggers visual validation or appears in the review report.

An interrupted or rejected run never modifies the blueprint.

## Testing

Deterministic tests cover:

- page delimiters and PDF fingerprinting,
- stable block IDs,
- extraction diagnostics,
- cache invalidation,
- candidate scoring,
- schema validation,
- cost-cap enforcement,
- blueprint proof-source parsing, and
- suppression of difference reports for `same` verdicts.

Prompt contracts have fixture outputs for malformed, uncertain, same-proof, and
different-proof responses.

The four-page switching-lemma document is an integration and evaluation fixture,
not a brittle exact-text snapshot. Its rubric checks that:

- known reading-order and notation corruption is repaired,
- theorem and proof boundaries are recovered,
- reconstructed formulas preserve mathematical meaning,
- every repaired block traces to a PDF page,
- ambiguous repairs trigger visual escalation,
- candidate discovery finds `SwitchingLemma2.switching_lemma`,
- a `same` verdict emits no difference report,
- no blueprint edit occurs before explicit approval, and
- the run remains within the USD 1.00 fixture cap.

The extraction integration fixture is optional and removable. Core proof-matching
tests operate on validated Markdown fixtures so they do not depend on PDF
conversion, vision access, or the initial lecture note.

## Success Criteria

The initial pipeline is successful when it can:

1. produce and retain both raw and validated Markdown for the four-page fixture,
2. identify and repair the fixture's representative extraction failures,
3. find the relevant TCSlib switching-lemma theorem,
4. produce a reviewable mathematical-structure verdict,
5. suppress differences when the proofs match,
6. preserve human authority over blueprint changes,
7. resume without repeating completed paid stages, and
8. stay below the fixture's USD 1.00 cap.
