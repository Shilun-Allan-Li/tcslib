# Partial source-policy delivery: intake

The returned artifact is retained as **partial, proposed and unapproved**.
This is an identity/format intake, not a new mathematical audit PASS or source
approval. The ten earlier scoped proof/statement gate verdicts are unchanged.

The user supplied the local ZIP after connector downloads failed. Its original
bytes are preserved in `lwe-sis-earlier-stack-source-policy-r1-proposed.zip`.
`REPORT.md`, `SOURCE-NOTES.md`, `161-name-disposition.md` and
`delivery-manifest.json` are exact member copies for convenient reading.
`provenance.json` records their identities and the limits of the intake.

| Item | Verified result |
|---|---|
| ZIP SHA-256 | `b471b0496950c07ad1c260e00bfd33bc21f0af52ecd349c71ce3761f46bbf785` |
| ZIP bytes / members | 4,300,147 / 59 |
| Delivery checksums / manifest member records | 58 / 57 |
| Original input checksums / frozen revision-path blobs | 10 / 191 |
| Unchanged primary assets | Both original PDFs and both raw Markdown files |
| Scoped source / target PRs | `ec72ed773a690c17ac253707350935cc9e0acb34` / #236–#239 |
| Matching targets / mathematical modules | 161 / 20 |
| Typed JSONL records / substantive candidates | 703 / 59 |
| Proposed name classifications | 6 source results; 31 adaptations; 124 implementation/context items |
| Repaired transcription / unvalidated transcription pages | 10 / 186 |

`check_return.py` reproduces the checks against the original ZIP and extracted
members. It checks both document indexes with the existing data models and pure
parser, complete name/page accounting, candidate source slices, anchor validity,
and the two reported decoding-boundary examples. All candidate anchors refer to
repaired, render-reviewed pages. `checks.json` contains the results. These checks
establish integrity and structure, not mathematical approval of all matches.

The worker distinguishes twelve inspected page renders from ten repaired
transcriptions. Twelve additional render-generation claims have no retained
images; none is used as a candidate's reviewed anchor. The explicit ambiguity
records are retained rather than replaced by the parser's empty ambiguity list.
This intake spot-read the supplied renders of Pei16 PDF page 21 and Wu24 PDF page
83. It did not independently rerender or mathematically review all reference pages
or all 59 proposed correspondences. No Lean, cache or model execution was needed.

## Revised scope after the user's feedback

The original job requested whole-document Markdown preparation. Its partial
status refers to that transcription request, not to missing formalization of
186 pages. The user subsequently asked to postpone transcription of material
we are not formalizing. That direction supersedes the original full-document
transcription work item for future campaign work; the issued JOB.md and returned
report remain unchanged historical records.

All 59 proposed candidates use seven already-repaired pages: Pei16 PDF pages
20, 21, 24 and Wu24 PDF pages 75, 82, 83, 85. Review can proceed against those
original PDF passages, adding a specific passage only if a consumed citation
needs it. Unrelated transcription is deferred and is not an independent landing
requirement. See `../SCOPED-REVIEW.md` and `../scoped-review.json`.

The useful retained findings distinguish integer SIS from residue-only wording,
finite bounded noise from an exact Gaussian, strict decoding separation from an
informal real-quarter bound, and single-sample prose from common-secret batches.
The modulus-five tie example supports the disclosed strict-bound adaptation;
it identifies no defect in the already proved Lean theorem. Adjacent trapdoor or
lattice-reduction source issues do not commission work outside campaign scope.

Remaining work is focused source-fidelity review, proposed-match approval and
the applicable scoped reference integration/shared-registry coordination and
landing checks. No matching approval, whole-reference validation, registry edit,
blueprint/dataset mutation, worker dispatch, code change, push or merge follows
from this intake. Later #250/PW10 obligations remain separate.

**Not yet clear to merge — consumed-source review, approved matching and the
applicable integration/landing checks remain; bulk transcription is deferred.**
