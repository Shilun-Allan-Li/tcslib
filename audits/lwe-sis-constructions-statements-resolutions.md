# Combined construction statements: round 1 disposition

The returned Codex report passes the frozen mathematical statement gate with
**0 blockers, 0 majors, 1 documentation minor and 4 notes**. It reviewed all 19
modules, 220 declarations, 101 admitted obligations, 62 closed source readers,
40 generated readers, 13 compiler auxiliaries, 575 owned constants and 48 backing
contracts. The auditor did not rerun Lean. No mathematical statement repair is
required, and no proof-completion or merge approval follows from this PASS.

| Identity | Value |
|---|---|
| Frozen Lean/root | `17b2a282b545c6ebca3fccc88d518d18ae78f485` |
| Bundled records | `03f13bc817f4d281801e2025d3722bcab513c6c0` |
| Published exchange | `64e245b345d908d835030efede1c91312a4e6cce` |
| Published draft PR | #250, target `cryptography/lwe-sis-constructions` |
| Remotely verified draft head at intake | `c74f629c03933bc4abb4cb24aeff049996cd2b33` |
| Bundle SHA-256 | `04b19eff425cc268426662a4352f2be4cfa96a97d965a559c1f82f2e51444d8d` |
| Comment-only minor repair | `f1b75a7d17dc7ef5fddd7403a2d7c740ba365c9c` |

## F01: stale registration wording — repaired

The `Encoding/BooleanVector.lean` overview still called the counted loop a
registered host. This contradicted the unapplied catalogue proposal and the
preparation records' claim that all such wording had been corrected. The audit
was correct: the original preparation missed this sentence.

The overview now calls it the existing public counted loop, explicitly records
its pending registry disposition, and keeps dependent FP fills paused. The repair
changes only that comment. The existing comment-aware scanner verifies identical
comment-stripped source, declarations and theorem bodies. A serial per-module
check passes with zero errors and the same six admissions; Encoding style is
0 FAIL/0 WARN over seven files. No source signature, definition, proof body,
import, attribute, owner API or registry is changed. Original issued inputs and
their historical evidence remain fixed. See the `intake-r1/doc-repair.json`
receipt and raw module/style logs.

## Continuing notes and readiness holds

| Note | Disposition |
|---|---|
| N01: source policy | Keep full frozen-primary validation, ingestion and approved matching open, including PW10. No source-registry proposal is applied or paid pipeline launched. |
| N02: execution and landing | Retain the auditor's no-native-rerun limit, all 101 frozen admissions, 17 inherited warnings, physical/cache/freshness attestations and applicable landing checks. User approval controls all dependency-stack and #250 merges. |
| N03: consumers | Retain efficient uniform sampling/schedules, required common-secret quantifiers, uniform message bounds, primitive/game bridges, exact-seed PRG integration, all-but-one inverse, strong one-time signatures and final CCA2 as separate obligations. SIS hardness remains independent. |
| N04: narrower proof readiness | Mathematical statement review passes. Do not fill routes needing the missing `blockVal_eq`, earlier `isUniversal_iff`/`hasMinEntropy_iff`, or counted-loop registry/host-gate disposition. Retain any applicable head-envelope requirement. The audit authorizes no shared-owner edit or policy exception. Independent proof routes may continue under the passed statements. |

The exact two newer patches and earlier probability/source proposals remain
unapplied data. No external worker is dispatched by intake. Root may continue
independent fills; the two authorized internal agents provide read-only research
and run no native/cache jobs or edits. No affected fill brief is issued while
its required reader or host disposition remains open.

## Intake and report provenance

Maintainer intake verifies the live 153 frozen source paths before repair, all
2,395 revision/path attachment blobs, seven owned published payload hashes and all
ten nested checksum sets. GitHub verifies #250 is open/draft with the exact target
and head above, and verifies the exchange tree identity. This is integrity intake,
not a second independent mathematical audit or a full native rerun.

`lwe-sis-constructions-statements-findings.md` preserves the complete text returned
by the authoritative report read, without editorial changes: 13,818 UTF-8 bytes,
SHA-256 `8588df8f02701a29cf9ca3332759985d8ba26ef0d57360657927ab4ea8bad345`.
The original file metadata reports 13,819 bytes. Raw download failed; no missing
byte is guessed and no original-file byte identity is claimed. The retained
intake provenance distinguishes this exact received text from the native file.
This limit does not remove or abbreviate any returned finding.

**Not yet clear to merge — the mathematical statement gate passes and F01 is
repaired; proof fills, N04 readiness holds, source-policy work, landing checks
and user approval remain.**
