# Resolutions — §12 routine layer, epoch F2 fill gate

Loop summary for the epoch-F2 external audit (`audits/routine-f2-pack.md`,
bundle `audits/routine-f2-bundle.md`, sha256 `72861b80…`, audited at
`41a06e08`). Findings preserved verbatim in
`audits/routine-f2-findings.md`.

## Outcome

**Round 1: PASS — 0 blockers, 0 majors, 1 minor (plus six explicit
no-findings rows). The epoch F2 gate is CLOSED.** With F1 (closed
2026-10-09, round 1) this completes the §12 fill campaign: **all 56
audited-true statements of the machine-routine layer are proved**, and
`Build/Embed.lean`, `Build/Seam.lean`, and `Build/Catalog.lean` are
zero-sorry with all twenty Catalog space theorems at the standard axiom
triple.

The auditor independently recomputed the bundle hash, reconstructed the
pre-F2A (72 declarations, blob `b239b408…`), post-F2A (378, blob
`f4b449b2…`), and final (423, blob `798fb8ac…`) sources, replayed both
patch series in both directions byte-identically, re-established both
freezes (F2A: all 72 heads and all 55 nonfilled bodies verbatim; A2:
exactly two removed `sorry` lines, all 378 heads verbatim), re-enumerated
the 306 + 45 private inventory head-for-head, blind-restated all 45 A2
declarations and the load-bearing F2A declarations individually with the
remaining 306 covered by a 30-family partition, verified the loop and
forwarding ledgers against the binding answer-5 and R4 contracts, audited
all six `f2_space_of_time` call sites, checked the seven requested
`catalog_redirect*` copies against the attached Wrappers originals, and
ran fourteen adversarial symbolic instantiations (zero-time startup, both
empty mapped components, empty virtual input at both boundaries, malformed
inputs, oversized payload output, zero coefficient/exponent, counter
carries, fixed-width overflow, zero fuel, many-round excursions,
delimiter-without-marker stripping, empty-input split, idle conditional
banks, empty accepting payloads).

## Disposition of the finding

| # | Severity | Disposition |
|---|---|---|
| F2-1 | minor | **Swept at close** (prose only, the audit's proposed fix verbatim in substance): the sketch above `f2_loopHost_start` claimed "the no-anchor prefix includes time zero"; at `t = 0` the premise `∀ u < t, …` is vacuous and the initial configuration **is** the anchor. The sketch now qualifies the captured-prefix clause with positive startup time and states that a zero-time startup already occupies the anchor and takes the two administrative steps directly. No statement, proof, or export changed; the formal proof was already correct (the auditor verified the zero-time route through `f2_loopHost_anchor_return` with `release = false`, and `a2_loop_start_prefix` independently corroborates the edge case). Post-sweep fresh sweep: `audits/logs/routine-f2-close-sweep.log` — Catalog and facade, 0 errors, 0 sorry warnings. |
| F2-2 — F2-7 | notes | No-findings rows (A2 declarations and ledgers; F2A declarations and rows; `f2_space_of_time` discipline with its complete six-site inventory; declared design anomalies; freeze and inventory attestations; integration/axiom/style evidence and the excluded shim). No action. |

## Evidence-scope notes carried forward

* The auditor's checks establish consistency of the supplied packet, not
  independent Lean execution; kernel evidence remains the maintainer's
  independent replay and axiom logs
  (`audits/logs/routine-f2a2-{integration-sweep,axioms}.log`), per the
  pack's attestations. The delivery archives and bundles stay
  maintainer-verified (checksums 14/14 and 20/20, bundle bases
  `ead9abf1`/`3099ad2a`).
* Historical copy provenance of the reopened Loop/Primitives/Composition/
  direct-counter families (and `a2_loop_halted_run`) is not certified
  byte-for-byte because the originals were not attached; the auditor
  audited each local transition table and contract on its own merits and
  found no semantic mismatch. The attached-Wrappers copies (all ten
  `f2_timed*`, the seven `catalog_redirect*`) were verified as
  name-adjusted literal copies.
* Queued items reaffirmed by the audit: the per-theme Catalog split
  (12.2c) as the dedup home (bank-sum facts to one owner; rewind and
  conditional projections to Wrappers; loop seam contracts to the loop
  controller); the public `redirectTM` head-trajectory projection beside
  `redirect_run`. **Optional regression corollaries at the refactor**
  (not acceptance requirements): the zero-startup case, the two
  empty-virtual-input clamps, and setup followed by a payload's emitting
  halting step.

## Gate state after this close

| Gate | State |
|---|---|
| Statement gates (P0, P3.1, P3.2, P3.3, P4.1, P4.2, P4.3, P4.4, §12) | all CLOSED |
| §12 epoch F1 (Embed 13, Seam 11, Catalog Part 1 + W1/W2 13) | CLOSED (round 1) |
| §12 epoch F2 (19 Catalog space rows) | **CLOSED (round 1)** |
| §12 routine layer | **COMPLETE — 56/56 proved, zero-sorry** |

The plan §4b stages that consume the routine layer are unblocked; the
next stage is the ARM extensions + colleague sync, with the chapter-3/4
fill epochs to follow on the §6 summit order.
