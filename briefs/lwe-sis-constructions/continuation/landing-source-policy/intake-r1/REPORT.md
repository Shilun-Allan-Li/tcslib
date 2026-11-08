# Earlier LWE/SIS source-policy preparation, round 1

**Verdict: PARTIAL. Input integrity and structural checks pass. Reference ingestion is incomplete; all matches remain proposed and unapproved. This delivery does not close source policy or clear a code merge.**

The scope is the 161 owned source declarations in 20 modules for PRs #236–#239. Later #250/PW10 work remains deferred. No owned name is missing from the disposition records.

## Frozen identities and integrity

| Item | Exact identity |
|---|---|
| Exchange commit | `a4e19bd3cf029b9bf5fb2e53989ddc0d61006ac1` |
| Lean source matched | `ec72ed773a690c17ac253707350935cc9e0acb34` |
| Bundled records | `e88f9ecc36033e468f8c345f2d1088b59ba50e08` |
| Bundle SHA-256 | `2ff8cbd5ea276b99eaa49987519d9b5e63c96e0591f0278d27871bcecd7b2ae7` |
| Bundle size / sections | 3,099,027 bytes / 191 |

All ten `SHA256SUMS` entries pass. The ordered JSON/TXT indexes agree, and all 191 extracted payloads match their lengths, hashes and revision-qualified entries: 151 at the Lean pin and 40 at the records pin. The four inventory hashes and all 20 owned module hashes also match. Independent downloads of those 20 Lean files at the exact source commit match the bundled bytes. The pure extractor was also run with `python3 -I` into a new isolated directory.

| Unchanged primary file | Bytes | SHA-256 |
|---|---:|---|
| `peikert2016-lattice-survey.pdf` | 703,532 | `1a9802b66031a2b863fd498a5de4a71cdb1bd46ac1d47dc1f4a67ae341357488` |
| `peikert2016-lattice-survey.raw.md` | 313,935 | `f34120e30a8bcbbbd248ac7a3be9b93da97a43c50ad20c0d2a13d19b787262db` |
| `wu2024-topics-cryptography.pdf` | 1,035,395 | `c0f87bf2e871180d62b2b27d38b916bce1a7b2228dbb68de72341597341d6d87` |
| `wu2024-topics-cryptography.raw.md` | 340,753 | `345aad6425678069c5f1afbc328457c4c21c61e2019507a241e5e71376cf7814` |

`PRIMARY-SOURCES.json` agrees with these files, their full PDF fingerprints, the PDFs' 90/106 page counts and every ordered raw-page marker. Both PDFs and raw files are delivered unchanged under `references/`.

## Reference review and its limits

One Codex agent performed local review using the frozen inputs, `pdftotext`, PDF renders and isolated structural checks. No helper agent, model subprocess, paid cleanup/matching call, GUI, Lean execution or broad dataset pipeline was used. The two repaired Markdown files use truthful Codex provenance, the original full PDF fingerprints and the existing anchor convention. One block represents each PDF page.

| Document | Pages accounted for | Renders inspected | Repaired transcription pages | Still unrepaired |
|---|---:|---:|---|---:|
| Pei16 | 90/90 | 5 | 20, 21, 24 | 87 |
| Wu24 | 106/106 | 7 | 39, 65, 75, 82, 83, 85, 91 | 99 |

**The 186 unrepaired pages are not validated ingestion.** They are retained as explicitly unvalidated raw-layout blocks, with unresolved ambiguities and low confidence. These anchors are not used for substantive candidates. Unresolved control glyphs are displayed as placeholders; the original raw files preserve their bytes. PDF renders of Pei16 pages 8 and 10 were inspected for context but did not receive repaired transcriptions.

Every unrepaired page is identified in `page-review.json` and `index.json`: Pei16 pages **1–19, 22–23, 25–90**; Wu24 pages **1–38, 40–64, 66–74, 76–81, 84, 86–90, 92–106**. Automated fresh-text agreement on 184/196 pages is an extraction check, not mathematical validation. `rendered` records render generation; `render_reviewed` records actual visual inspection. Twelve inspected page images are included as evidence.

The original Wu extraction flags are addressed: page 39's policy tree, page 65's circuit/table, and page 91's workflow/cases were checked against renders; exact figure crops preserve the diagrams. Source-level slips remain separately unresolved. The full list is in `validation/SOURCE-NOTES.md`, with typed block ambiguities in each document directory. In particular, the residue/integer SIS mismatch on page 75, preimage-sampling notation on page 82, Gaussian/support-bound and reduction-direction language on page 83, and coordinate/single-sample security issues on page 85 are preserved as printed, without silently repairing the source.

Both indexes load as `DocumentIndex`, and the existing pure Markdown parser reproduces all blocks. Additional checks establish full fingerprint agreement, unique anchors, page/provenance agreement, increasing page/block order, nonempty blocks, complete page accounting and valid figure paths. The parser's empty ambiguity result is not used: the explicit ambiguity files remain authoritative. Repaired Markdown hashes are recorded separately in `evidence/coverage-summary.json` and `MANIFEST.json`.

## Proposed matching

Each document has exactly 161 ordered `RelevanceDecision` rows and 161 ordered `ComparisonVerdict` rows, plus substantive `Candidate` rows only. All 703 JSONL rows pass the frozen data models, without added fields. Exact Lean names and normalized module strings are preserved. Every substantive candidate cites a repaired, render-inspected block. Confidence scores are review judgments; proof-token counts are character-based estimates.

| Document | Candidates | `same` | `different` | `not_in_text` | Missing names |
|---|---:|---:|---:|---:|---:|
| Pei16 | 24 | 5 | 19 | 137 | 0 |
| Wu24 | 35 | 4 | 31 | 126 | 0 |

Across the **161 distinct names**, six have a proposed source-result correspondence, 31 have disclosed adaptations, and 124 have implementation/context-only dispositions. All names, including readers and instances, appear in `matching/161-name-disposition.md` and `dispositions.json`. A name can have candidates in both documents. `not_in_text` means no direct counterpart was identified in the checked source sections; it is not a certified absence search over every unreviewed page. Contextual relevance does not create a substantive candidate.

The comparisons preserve the following distinctions:

* SIS witnesses are nonzero integer vectors before modular reduction. Natural squared-norm budgets and the explicit dyadic profile are disclosed adaptations. Compression/existence and the collision reduction do not establish hardness.
* LWE uses integer noise, actual finite-seed multiplicities and one uniform common secret across the batch. Finite noise is neither an exact infinite Gaussian nor an efficient sampler merely because its seed type is finite. A fixed sample schedule does not imply hardness for every polynomial schedule.
* Regev encryption is the direct construction with a fresh row per bit and a common secret. The total nearest-codepoint decoder, false-on-ties convention and strict floor separation are adaptations. Every-seed bounded correctness is not a tail bound.
* Uniform translation and the two-hybrid probability inequality do not finish machine reductions, uniform worst-message bounds, polynomial sample quantification, adaptive games or the final primitive security definition.
* Binary encodings, parsing, endian conversion, scalar arithmetic and their machine contracts remain repository glue. Existing PS10/AB09 conventions are context; no direct Pei16/Wu24 proof match is manufactured for them.

`evidence/rounding-boundaries.json` checks the decoder distinction concretely. At modulus 5, the true codepoint is 2; error −1 gives residue 1, at distance 1 from both codepoints, so the formal decoder returns false. The source real-quarter bound holds, while the formal strict floor-separation premise fails. This comparison does not alter the frozen theorem.

## Proposed landing steps

1. Finish transcription review of the 186 identified pages and retain or resolve the explicit source ambiguities. Until then, do not ingest these proposed pairs as fully validated references.
2. Review the 59 document-specific candidates and all 161 dispositions, accepting adaptations explicitly and keeping technical/context-only records separate from direct source matches.
3. After that review, coordinate the existing two-tag registry proposal and any approved source integration. The delivered patch is unchanged and unapplied; its baseline/proposed hashes were reproduced in memory. No additional owner/code diff is proposed by this delivery.
4. Perform the separately applicable exact-target landing checks for #236–#239, followed by the user's merge decision. Later #250/PW10 source scope remains deferred.

Matching approval, shared registration, source-policy closure and merge approval are all **false**. No Lean, shared registry, blueprint or dataset was changed; no worker was dispatched and nothing was pushed or merged.
