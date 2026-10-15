# Epoch C1 + S1a fill gate — resolutions (CLOSED, round 1)

## Round 1 (2026-10-11): 0 blockers, 0 majors, 2 minors, 14 notes

Findings verbatim in `audits/ch34-c1-fill-findings.md`. Pack:
`audits/ch34-c1-fill-pack.md`, bundle `audits/ch34-c1-fill-bundle.md`. The
auditor reversed the six fill patches to the 17 base blobs, confirmed all 154
existing declaration headers in the fill files and 69 in the promotion files
unchanged, and confirmed the additions are exactly 11 sanctioned publics, 48
privates and 8 promoted publics (note 3).

| Finding | Disposition |
|---|---|
| 1 (minor): two status descriptions are stale. `TQBF.lean` calls the collapse "proved modulo `P_subset_PSPACE`"; `ConfigGraph.lean`'s module docstring calls its counting bounds "(sorried)" | **Swept** (comment-only, comment-stripped identical; both modules re-check at 0 errors). The collapse docstring now says "proved, citing `P_subset_PSPACE`". The module docstring names `acceptsWithin_of_spaceUsedWith_le` as proved. The three summit statements keep their accurate labels |
| 2 (minor): the pack said "no pair involving `Catalog.lean`", but its C1a screen outputs contain 272 unchanged pairs internal to Catalog | **Erratum.** The correct statement is "no new pair, and no cross-file pair, involving Catalog". Catalog's internal population is the acknowledged debt of 12.2c (T3). Future packs word omitted-source attestations this way |
| 3–14, 16 (notes) | Freeze, exports, promotions, routes, the citation-rule discharge, and all six screen-pair families (ruled glue) confirmed. No action |
| 15 (note): E4/E5 against `Oracle.lean` are adaptations, not copies; retain the requested promotion of the blank-cell helper | **Carried** to `backlog.md`: promote C1c's private blank-cell bound to `TuringMachine/Oracle.lean`, so that `queryString_length_le` cites it. Its window is the next batch that owns `Oracle.lean` |

**Gate CLOSED.** Epoch C1 and S1a are complete: 42 statements, the 11
sanctioned exports, and both pre-issue promotions.
