# Source-validation preparation during adapter statement review

This is an undispatched handoff draft. The user's Codex selection and dispatch
apply to gate 04's adapter statement audit. A separate external source job still
needs its own reviewer selection and user dispatch. This preparation changes no
Lean file, issued review input, shared registry, blueprint or dataset.

`source-validation-scope.json` enumerates the exact 143 owned source declarations
across 19 modules at `6eec97be8f54d9990340900a5595dab32fb477f5`. It combines the
existing 61 foundation, 62 construction-core and 20 adapter declaration inventories.
It records all literal citation occurrences with source lines, including module
reference headers. These are search inputs, not approved declaration-to-passage
matches. Generated readers and compiler constants are outside this source-declaration
count; the audited axiom inventories retain them separately.

## Exact primary inputs

| Tag | Document | Pages | PDF SHA-256 |
|---|---|---:|---|
| Pei16 | Peikert, *A Decade of Lattice Cryptography*, 17 February 2016 author version | 90 | `1a9802b66031a2b863fd498a5de4a71cdb1bd46ac1d47dc1f4a67ae341357488` |
| Wu24 | Wu, CS395T Spring 2024 notes, updated 30 April 2024 | 106 | `c0f87bf2e871180d62b2b27d38b916bce1a7b2228dbb68de72341597341d6d87` |

The manifest rehashes both PDFs and raw extractions in this chat's earlier own
archive, verifies the full PDF fingerprint in each raw file, and checks every raw
page marker in order: all 196 pages are present. This verifies identity and
extraction coverage; it does not validate mathematical transcription. PS10/AB09
citations identify existing surrounding conventions; this two-document handoff
does not commission new ingestion of those sources or change their registrations.

## Required validated delivery

Use the existing `proofmatch` document/index/matching formats. Keep each unchanged
`.raw.md` alongside its repaired `.md`, with the full original PDF SHA-256.
`proofmatch.document.parse_validated_markdown` reads the repaired document. Anchors
must use its `pdf-<12-character fingerprint>-pNNN-bNNN` convention and agree with
the page/block provenance comments. Check unique anchors, the correct fingerprint
prefix, page range and order, nonempty blocks, and complete page coverage as well;
the current parser alone does not enforce all these properties.

Return per-page validation diagnostics and explicit unresolved ambiguities.
Wu pages 39, 65 and 91 were flagged by the deterministic extraction diagnostics;
absence of a diagnostic elsewhere does not establish correctness. Give truthful
worker/method provenance: the current `_render_markdown` helper hardcodes a Claude
repair label, so its header cannot be attributed to a different worker unchanged.
Record full repaired-document fingerprints separately from original PDF identity.

Only after validation, prepare scoped relevance/candidate/comparison records in
the existing `RelevanceDecision`, `Candidate` and `ComparisonVerdict` formats.
Restrict candidate declarations to the supplied ownership inventory. Distinguish
source results, local specializations, representation glue and contextual machine
conventions; do not force every reader or glue lemma into a direct source match.
Do not invent final block anchors before the validated document exists. No
comparison is approved merely by appearing in a worker delivery.

The generic dataset pipeline also considers pending documents outside explicit
source/module arguments. Use the per-document interfaces and an isolated owned
dataset/output directory; do not run the broad wrapper against shared references
or launch cleanup/matching model calls as part of this preparation.

## Fidelity questions that the matching must preserve

| Passage | Required distinction |
|---|---|
| Pei16 PDF p.20, Definition 4.1.1/equation (4.1.1) | SIS uses a nonzero integer vector in the modular kernel. The formal natural squared-norm budget is an explicit adaptation of the source's Euclidean bound. |
| Pei16 PDF p.21 | Binary collisions yield integer differences in minus one, zero and one. Compression and solution existence do not prove SIS hardness. |
| Pei16 PDF p.24, Definitions 4.2.1/4.2.3 | Preserve integer noise reduced modulo the modulus and one uniform common secret for the entire batch. A fixed-sample family does not imply hardness for all polynomial sample schedules. |
| Wu24 PDF pp.82–83, Definitions 20.4/20.5 | Preserve the direct Regev symmetric construction. Finite actual-law noise, every-seed bounded correctness and the strict modular decoding separation are disclosed refinements. |
| Wu24 PDF p.85, Lecture 21 | The mathematical translation argument does not supply the existing machine/game bridge or uniform worst-message bounds. |
| Wu24 PDF pp.86–87 | Future PKE needs the strict aggregate-error separation and augmented-matrix leftover-hash argument. These are preflight material, not current formal PKE results. |

Earlier targeted page comparisons and the explicit rounding boundary examples are
in `../proof-audit/`. They remain supporting evidence; complete PDF validation and
approved source matching are still open. Retain the earlier four findings reports
and continuing N01–N03 notes unchanged.

## Registration and landing boundary

The exact two-tag shared-registry proposal is already in
`proposed-source-registry.patch`; its baseline/proposed identities are in
`registry-proposal.json`. It remains unapplied. After validated pairs and scoped
matching are available, coordinate that concrete shared-file diff through the
user before applying it. Approved matching must precede blueprint source macros.
Keep all source records on this campaign's own PR branch and preserve the
adapter statement freeze while its audit is pending.

Reproduce the preparation locally, without a model call or native build:

```sh
python3 -I briefs/lwe-sis-constructions/continuation/source-ingestion/prepare_source_scope.py
```

**Not yet clear to merge — primary identities and raw coverage are checked;
validated ingestion, approved matching and relevant landing checks remain.**
