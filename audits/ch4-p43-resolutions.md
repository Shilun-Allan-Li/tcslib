# Chapter 4, phase P4.3 (PSPACE-completeness and the space hierarchy) — audit loop resolutions

**Gate: CLOSED (round 3, 2026-10-09).** Three rounds — the campaign's
longest statement loop:

| Round | Verdict | Findings files |
|---|---|---|
| 1 | FAIL — 1 blocker, 4 majors, 4 minors, 3 notes | `audits/ch4-p43-findings.md` |
| 2 | FAIL — 1 blocker, 0 majors, 4 minors, 3 notes | `audits/ch4-p43-r2-findings.md` |
| 3 | **PASS — 0 blockers, 0 majors, 0 minors, 2 notes** | `audits/ch4-p43-r3-findings.md` |

## The loop

* **Round 1's blocker**: `exists_adjacency_codec_cnf` demanded fixed-length
  injective codes on **full** configurations — impossible, the output tape
  being unbounded (pigeonhole at `n = s = 0`). Repaired by restating over
  the quotient carrier (input content + the closed P4.2 `coreSum`) on
  `Turing.Cfg.InWindow`-windowed configurations, with in-package validity,
  adjacency, and acceptance CNFs, cross-input rejection, and
  serialized-length size bounds. Round 1's majors (no uniform constructor;
  junk midpoints; the universal's window-membership test; the hierarchy's
  per-code constants) were resolved there too: the uniform emitter is a
  declared private fill obligation, the ψ-recursion is `Valid`-guarded with
  the `a = b ∨ Next` base, the universal probes by visited-interval
  cardinality with probe-then-replay, and the hierarchy uses the capped
  increasing-budget loop with one fixed padded code.
* **Round 2's blocker**: the repair's own size bound `C·(s+n+1)^C` was
  self-contradictory at `n = s = 0` — the code width equals the budget and
  one literal reading the second block serializes to `C + 6`. Repaired to
  base `s + n + 2`; the quotient clause became an **iff** (round-2 finding
  2), and the live-self-adjacency, check-count, padded-language,
  `Valid`-copy, and W1-discard wordings were corrected.
* **Round 3**: PASS with no sweeps. The auditor verified one shared
  constant now suffices uniformly (their singleton test `C + 6 ≤ C·2^C`),
  re-derived the full polynomial construction and common-constant
  calculation, confirmed all ten round-2 dispositions, and reconstructed
  every diff hunk and blob hash.

## Pack errata, acknowledged (shipped packs are never edited)

* The round-2 pack's disposition 1 asserted the then-current clause
  "required" equal codes for equal dead-summary vertices; it gave only one
  direction (round-2 finding 2). The round-3 statement's iff makes the
  claim true *now*; the pack overstated it *then*.

## Carried into the fill briefs

* The uniform emitter family (validity/adjacency/acceptance construction
  and serialization, the initial-vertex code, level-blocked indexing, the
  Tseitin-after-prefix equivalence) — private obligations of
  `TQBF_PSPACEHard`, never supplied by the existential package (round-3
  note 1).
* The quotient path lift (projection and lifting through
  `coreSum_stepWith`), the membership evaluator's validate-first
  discipline, the probe-then-replay universal with interval-cardinality
  accounting and discard-only W1 capture, the capped increasing-budget
  hierarchy loop with the space-preserving one-work-tape normal form, and
  the `∃ x ∈ L` padded language for `SPACE_linear_ne_NP`.

## Consequences

* **Chapter 4 is fully closed at the statement level**: P4.1, P4.2, P4.3,
  P4.4 all CLOSED.
* The `ClassPSPACE` and extended `Formulas` facades leave this gate's
  freeze; `Turing.Cfg.InWindow` joins the audited surface (a promotion to a
  more central home is fill-time housekeeping).
* Statement-freeze baseline: the closing commit.
