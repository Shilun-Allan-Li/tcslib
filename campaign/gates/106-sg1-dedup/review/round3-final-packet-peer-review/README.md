# Independent SG1 final-packet peer review

**Not yet clear to merge: #215 — external Codex round3 remains open.**

This is a data-only peer review of frozen candidate manifest
`3bf0f54a07d9a4c96abc3a92fdbd007c593ab6788611e23fe26cd0cc438d5fed`,
not external audit findings or gate closure. The checked source is clean
`79e7c63a6bfa5f002663924f5c7d4e72db705026`, based on
`3023dc1408c3d216fc07a7cbba9ae30135b861ed`.

One concrete input-completeness correction is required in the root-owned final publication;
no source or further human ruling is requested. Root has agreed to add it, preserving the
frozen candidate. Final supplement inclusion/render/publication is not attested by this review.

| ID | Severity | Evidence | Required action |
| --- | --- | --- | --- |
| PQ1 | minor, packet preparation | `devtools/seyoon/mkdownmulti.py` imports `graph.imports_of` from its graph directory, but no `graph.py` or equivalent section exists among the frozen1,539 inputs. The actual scratch generation helper is byte-identical to `R/devtools/seyoon/graph.py`:4,784bytes, SHA256 `c4c1aa599a091c88f77062fd2fca4482ed8017e683819a650e343760ac78d72c`. Its only imports are standard-library `os`/`sys`. | Add that exact file and provenance to the final publication supplement/list, then verify its rendered section. Keep the frozen candidate untouched. |

The current generator/checker transitive helper inspection found no other missing local
Python import. Scratch `mkdownmulti.py` and `mkreplay.py` exactly match their included root
copies. Actual scratch `mk-next.sh` exactly matches the INCLUDED
`campaign/status/2026-11-06-mac-bootstrap/mk-next-codex.sh`; it differs from the generic
root `devtools/seyoon/mk-next.sh`, which is not relabeled as the actual generator.

The following independent checks completed:

- All48 candidate-manifest payloads match. At the first complete pass all1,519 original
  input pins matched with no drift. The later consolidated pass records only the parent's
  expected `STATUS.md`/`HANDOFF.md` publication edits; these require final publication
  rebinding, as planned. No native/source/frozen input drift was observed.
- The1,539 sections are unique UTF8 and the frozen payload is98,855,551bytes. All40 original
  large records are represented losslessly by31 deterministic gzip9/mtime0/empty-filename
  Base64 sections, with independently reconstructed compressed bytes, raw hashes and full
  roundtrips. All3 existing binary companions are byte-exact. No original representation
  is omitted. Entire gate106 evidence/history/review coverage is uncapped; only the unissued
  canonical pack role is intentionally replaced, with its exact old bytes preserved.
- All50 current screen source captures stay plaintext and exactly match both Git blobs and
  archive members at the pinned commits. The five changed Lean files and exactly the two
  approved Hardness imports match. The first-live canonical API is absent from SG1 source.
  All16 advertised private public-citation mappings and the seventeenth raw Tautology
  repoint are present in actual current source.
- The three complete25-source screen manifests validate131/123/101 payloads. Raw screen
  output independently reparses to2,013→1,995 candidates and646,340→645,729characters;
  all35 dispositions match the exact2new/20gone/13changed rows. All435 eligible term spans
  and259 term candidates are identical. Relative to63, only four directed Tautology rows
  disappear, from one retained private adapter's implementation replacement. BASE adoption
  is preserved as adoption; no new BASE tiling is claimed.
- All84 final compiled-manifest payloads and71BASE/94historicalD0 payloads match. All six
  raw compiler stages independently decode/reparse without supplied-code execution, including
  every full raw type, structural CI, reflected attribute, ALLAX/PUBLICAX row and simp rule.
  Totals7,101→7,063, private5,750→5,712, all1,351 nonprivate rows and168 effective owned simp
  rules are exact. The+6/-44 delta is private; ten common type changes are private; the one
  shared AX change is `clA5Pair_sizes`. All43 current roots plus93 descendants/136 distinct
  constants have standard AX. Nine inherited Primitives nonstandard/sorry closures remain.
- Own header parser rebuilt the entire929-module committed source import graph at each
  generation and reproduced the complete supplied replay orders329/26/2 exactly. All raw
  native rows, module ordering, per-module enforced-j4 launches, zero failure/static mismatch
  results and admission counts66/0/0 reconcile. Whole `cp -cR` drivers are inspected. This
  does not claim a final329-module execution or campaign admission freedom.
- Final Hardness21-definition/all11-section and Tautology14-definition seals have exact
  native/sealed zero-error receipts. Independent raw-control counts match42/28 distinct
  kernel-checked positives and42/28 distinct expected negative diagnostic identities.
  Removing only recorded guards and metadata recovers exact full current source bytes.
- The prior49 affected names equal the historical set; the five unchanged live-stop chunks
  are exact in both pinned source sides and their quote hashes match. The sets are disjoint
  and their union is54/544. This is only a named affected lower bound across separate
  dispositions, not54 copies, a global census or one-fifth clearance. Seven SG1 kinds stay
  separate from FE-LIVE-1. None-halt/future-copy extensions are excluded. Unmerged canonical
  API119 is unused. `clNative_image` remains a bounded unacknowledged class-level residual,
  distinct from exact raw Tautology composition retirement on merge.

No delivered script was executed. No Lean/screen/native probe, snapshot/cache operation,
Git mutation, commit/push, external dispatch, or source/canonical/frozen edit was performed.
Read-only Git source inspection and own standard-library checkers were used. Historical
binary attestations retain their stated limits; this reviewer did not read snapshots or
claim a new native check. Definition semantics/F1/F2/F3 gate dispositions remain for the
selected external auditor. Root owns final canonical chronology/status, records pin, bundle
prologue/hash/sections, publication and prompt; no self-commit hash is required inside its
own not-yet-committed blob.

Detailed checks and every current source pin are in `QA.json`,
`seals-and-dependencies.json` and `additional-data-review.json`. The own checker sources
are retained as data; `MANIFEST.json` hashes all peer-review payloads.
