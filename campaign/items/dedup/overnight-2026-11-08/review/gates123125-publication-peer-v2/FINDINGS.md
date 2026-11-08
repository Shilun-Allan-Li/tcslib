# Gate123 V2 and gate125 published-packet peer check

This is internal publication QA for exchange `13a259b0998a5afa70abe27115a69cf608808e66`, records `cdebba2682df8a9f59c86dead83cfd9e436c0661`. It is not an external audit, dispatch, gate closure or merge-clearance decision. Gate123 V1 remains VOID; its prior report remains immutable.

**No remaining blocker or major was found.** Both packets now contain the full MAC8 adoption receipt/object map/source map and the checking/reproduction helpers. Gate123's old major input gap is resolved. One minor canonical path issue remains in reviewed V2; root plans to fix it before issuing the replacement prompt.

| # | Severity | Location | Finding / exact correction |
|---|---|---|---|
| 1 | minor | `campaign/gates/123-ch7-run/pack.md:65`, `:101`, `:102` | Use `review/qa/lint-comparison.json` and `review/source/BASE/TCSlib/...lean.txt`, `review/source/HEAD/TCSlib/...lean.txt`. The correct files are already present and earlier table paths are correct, so this is not an input-completeness gap. |
| 2 | note | gate123 `pack.md:81`; gate125 `pack.md:78` | Optional clarity: qualify the contextually clear bare `compiled-source-index.json` as `review/replay/compiled-source-index.json`. No missing primary gate125 input path was found. |

Exact publication bindings checked independently from Git objects:

| Gate | Source | Sections | Bytes | Bundle SHA256 |
|---|---|---:|---:|---|
| 123 V2 | `7c4b1a3e15b800cc4a98624f71a3b27458a41340` | 373 | 15,573,653 | `607f77f22ea26b05f78be059bf0e1649bf68c16da31a1d3d0cfb4fe2a29a6751` |
| 125 | `b8bb1f194b86c1b0c1d56e6c3f57e1defec37e80` | 291 | 16,566,614 | `b5269fc42eae9ee034c46cfe0bfbde8ab8135d1161df27cf3a621a4251e1152e` |

Every section's pinned bytes and exact order reproduce each published bundle. Exchange README/checksums, source/records/prompt pins, sizes, counts and Codex downloadable-findings filenames match. All full hashes were resolved and cat-file checked; exchange objects were read in the actual exchange clone without fetching. Canonical packs and prompts have no ROOT placeholders. The gate123 replacement prompt explicitly voids the original359 prompt.

All315 gate123 frozen review payloads are byte-identical to the independently checked V1 component, including source/log/census/scopes/control/screen data; the component itself was not rewritten. Its new895-object MAC8 anchor equals both replay input maps, and its new1003-source anchor equals BASE Git blobs. Both packets contain all11 reproduction files; exact copied screen code matches recorded helper SHA `f4feac91d3a1ec036f3bbcaafde83e6855a1bf1a62d31dac31a40a40d878f181`. Static helper bytes match their per-gate context hashes. The actual replay `leanelab-o.sh` is self-contained. Other helper/context copies remain disclosed current reproduction inputs rather than invented historical byte attestations.

Gate125's complete233 frozen payload hashes pass. Independent checks establish:

- all1,003 replay source-map entries and the prospective-tree Lean map equal exact pushed HEAD; only Hardness changes;
- exactly the two private proof/doc chunks restore BASE byte for byte; formal headers and every outside byte, public/runtime source, imports and attributes are preserved;
- all seven owner/API captures are exact BASE/HEAD; independent import graph gives the exact26-module closure/DFS order; all26 compiled sources/logs/rows bind to HEAD, actual static0/0, whole895 MAC8 input-before/after exact and output895 same keys with only Hardness object changed;
- both selected raw full Expr records match exactly, including universe/kernel/owner/privacy/kind/default-simp/AX; two private roots only, no selected private type auxiliaries and no whole-owner/private/global equality claim;
- actual instrumented native/sealed scope sources contain the two exact complete literal target chunks;15 ordinary guards, three default-simp removals and all30 effective positive/negative identity pairs match their original receipts/log hashes. The historical shared full-owner extras are not substituted for current PR-head replay;
- exact33 BASE/HEAD capture blobs and helper hashes bind to completed exit0 screens; independent directed-identity comparison is2,107→2,097, zero new, ten BASE-only with exact dispositions. Extraction2,433→2,431 and reproduced chars463,236→459,588 are parser measures, not interface/debt counts;
-19 style findings persist after only location/size normalization; campaign stdout changes only8685→8667 line counts. No fresh lint exit receipt or clean-tree claim is invented.

No new Lean, screen, mathematical fill, source/Git/canonical write or external dispatch occurred. Two local review-harness assumptions (exchange object location and context-key spelling) were corrected and disclosed in attempts; neither was an evidence/source failure. Later path-only publication rebuilds still require root's exact publication-byte/prompt checks; this report certifies the reviewed13a packets, not an unproduced replacement. The old481-payload report and FE121 draft remain unchanged.
