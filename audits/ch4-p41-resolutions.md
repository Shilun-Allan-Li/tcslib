# Chapter 4, phase P4.1 (space classes) — audit loop resolutions

**Gate: CLOSED (round 1, 2026-10-08).** One round: **PASS — 0 blockers,
0 majors, 5 minors, 4 notes** (`audits/ch4-p41-findings.md`, verbatim). All 10
definitions blind-restated clean; all 14 sorried statements accepted with
independent derivations (including the König's-lemma argument that the
per-input budget existential adds no uniformity restriction, and the full
fixed-window ledger for `NP ⊆ PSPACE`); the commit comparison between landing
and audited revisions independently pinned.

## Minors, swept in the closing commit and re-verified

| # | Sweep |
|---|---|
| 1 | `spaceConstructible_logSpace`'s sketch now states the bits-length identity for positive inputs only (`Nat.bits 0 = []`), special-cases the empty input to emit `[true]`, and bounds the counters by `A·(logSpace n + 1)` before absorbing |
| 2 | `spaceConstructible_linear`'s sketch initializes the counter at `1` (an uncorrected length counter emits the wrong word), includes width and boundary cells in the ledger, and the docstring now describes the `+ 1` as preventing the inherited collapse rather than "avoiding a vacuous zero bound" |
| 3 | The `Constructible.lean` module docstring no longer claims the exact-space variant is refuted by the chapter-1 exact-time argument (a space deadline forces no premature halt); constant slack is described as implementing the book's own asymptotic convention |
| 4 | `evenLang_mem_LOGSPACE`'s sketch keeps the **direct** proof route and records why: deriving it from `ZeroSpace`'s zero-tape witness would invert the existing `ZeroSpace → Examples` import (the pack's deviation-8 suggestion was cycle-inducing — a pack erratum, acknowledged below) |
| 5 | Pack erratum, acknowledged here (shipped packs are never edited): the inventory undercounted the definitions (10, not "2 + 6"), did not declare the proved `visitedWith_nil` as skeleton-time surface, and omitted three referenced attachments (the P0 resolutions, `audits/TEMPLATE.md`, `ClassNP/NTIME.lean`), which the auditor recovered at the exact commit. Future manifests: count declarations programmatically (the standing pack-erratum lesson) |

Re-verification: `Constructible`, `Examples`, `Inclusions` re-elaborate with
zero errors; `SpaceComplexity` lint 0 FAIL / 0 WARN (42 files).

## Notes (dispositions recorded)

* **Note 6**: the `NSPACE` zero-bound collapse is inherited and contained by
  the normalized classes; the `NSPACE` sanity twins (tape-count bound,
  collapse, normalization identities — the auditor supplied the derivations)
  are recorded as a **future additive sanity layer**, alongside a local
  mention in the `NSPACE` documentation, scheduled with the fills.
* **Note 7**: the exact-length quantifier is sound; the **short-prefix
  argument** (not just post-halt invariance) goes into the
  `spaceUsedWith_append_of_halt` fill; no equivalence with the book's
  non-halting convention is advertised for unqualified bounds.
* **Note 8**: `NP_subset_PSPACE`'s fill has a **hard dependency** on
  space-preserving bank-embedding/seam/reset contracts (§12 R1/R2/R3) or a
  separately proved direct simulation; the five host obligations of the
  report's question 5 are carried into the fill brief verbatim.
* **Note 9**: `SAT3_mem_PSPACE`'s docstring now states its delivered
  (polynomial, not linear) strength.

## Consequences

1. **The `SpaceComplexity.lean` facade is unfrozen**: the phase-P4.2/P4.3/
   P4.4 modules (`ConfigGraph`, `Savitch`, `Hierarchy`, `Logspace/*`) are now
   wired through the facade, and the temporary root imports are removed.
2. The P4.2 statement-gate pack is unblocked (its layering caveat now cites
   a **closed** P4.1 gate).
3. Fill obligations and the carried notes join the chapter-3/4 fill-epoch
   briefs.
