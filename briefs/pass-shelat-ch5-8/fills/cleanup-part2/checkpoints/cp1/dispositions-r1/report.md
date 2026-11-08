# CP1 retained-key disposition ledger

This is a complete retained-key ledger for a **partial** checkpoint, not an acceptance review. All 509 issued work keys remain `OPEN_PROVISIONAL`, all native acceptance fields are `UNKNOWN`, and zero keys or historical rows are closed. No source change, missing diagnostic, scanner class, or C3 count discharges work.

The source ancestor is `1aa5506f58f77c215e56d24311ec33bd931cacf1`. The received delivery is `8b133945c3ba4aa7abb3b896bec38441535959b2`; its seven-patch metadata ends at `51c245389deed467d75bcb1625627d8a4f97c4f8`. This review uses only the immutable CP1 snapshot, issued-r1 inputs, and the frozen independent source-review maps. Later local API-01 commit `8c047b8bcd3a2793795a02afd6d2d955c80e1806` and records commit `15706ceb2e92cba77b232d572ce57bc5468a5565` are excluded.

## Retention and source links

`matrix.json` retains the exact 509 issued key objects. `historical-row-links.json` retains each original row object and links every original row ID exactly once: 265 seal rows, 446 unfold rows, and 53 equation-term rows, totaling 764. The raw row spellings, original/current canonical keys, declaration kinds, source ranges, and raw block hashes were checked independently. Seal-row spelling normalization removes only the recorded `theorem`/`def` prefix and checks that kind against the historical record.

| CP1 source relation | Issued keys |
| --- | ---: |
| Same key, raw declaration block unchanged | 206 |
| Same key, source declaration changed | 296 |
| Same full name moved to its new owner | 4 |
| Removed key with an explicit contract replacement link | 3 |
| No exact current source target | 0 |

The four moved keys are `PPT.ofPolyTime`, `PPT.toNUPPT`, `PPT.toNUPPT_ofPolyTime`, and `PPT.uniform`, all from NonUniform to PPT. The two removed decoder keys in Collections/GGMReductionEval separately link to the public Adversary decoder theorem; neither issued key is merged away. The removed ZeroKnowledge `negligible_const_zero` key links to Foundations `negligible_zero`. These are source links, not accepted repair claims.

`source-delta-locations.json` projects all 754 already-reviewed source deltas with old/new locations and hashes, including all nine owner moves. It is provenance only and adds no work keys. `alias-link-supplement.json` records eight exact X1 delegation bodies and target declarations. The matrix additionally retains 37 simple term-head route candidates; 12 of those cannot be resolved uniquely by the bounded lexical namespace/open rule and remain explicit unresolved links.

## Received observations and matching limits

All 688 strict-baseline and 476 CP1-standard diagnostics are retained as received data. These are different variants: the strict baseline seals PolyExpr.eval, while CP1 standard leaves eval and its matcher/sunfold names unsealed. Their counts must not be subtracted as repair progress.

Of 1,164 received diagnostics, 1,147 match an exact declaration name, uniquely located raw probe block, and an error line inside that block. These link to 319 baseline and 296 CP1 issued keys; these are bounded diagnostic-link counts, not verified failure or repair counts. Seventeen records remain unresolved: 16 baseline and one CP1. Each has a unique reported declaration/raw block but its error line falls outside that block. Candidate locations and offsets remain in `unresolved-diagnostic-details.json`; no neighboring declaration is guessed. The received baseline source-line metadata also disagrees with independently derived declaration starts in 672 resolved records and remains visible in `observed-diagnostics.json`.

All 15,181 received CP1 explicit-scan items remain referenced; 48 cannot be matched by exact declaration spelling plus containing source range. Worker classification and unresolved IDs are retained without clearance. Received C3 totals (102 baseline pairs, 34 CP1 pairs) remain global worker observations; zero newly added pairs is not a per-key or policy discharge. Original issued observations are preserved intact.

## Validation and use

Own Python scripts ran under `python3 -I`; no incoming program, Lean command, cache/build command, application, Git mutation, or source edit ran. All 2,914 CP1 payload files were rehashed (32,239,080 bytes), and every frozen source-review input/output still matches its recorded hash. All 509 current targets also match the exact received raw source block and starting line. The source report remains unchanged.

The reproducible data checks are `build_matrix.py`, `finalize.py`, and `validate_retention.py`; their outputs are exclusive-create files. `manifest.json` binds the resulting files and immutable inputs. `unresolved.json` and the diagnostic details preserve matching limits. The ledger can be joined with an upcoming partial by retained issued key and original row ID; acceptance remains a separate maintainer review.

**Not yet clear to merge — CP1 is partial; every issued key remains open and native acceptance is unknown.**
