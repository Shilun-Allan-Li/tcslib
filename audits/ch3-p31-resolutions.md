# Chapter 3, phase P3.1 (oracle machines and classes) — audit loop resolutions

**Gate: CLOSED (round 1, 2026-10-08).** One round: **PASS — 0 blockers,
0 majors, 2 minors, 4 notes** (`audits/ch3-p31-findings.md`, verbatim). All 19
definitions blind-restated clean; all 10 sorried statements independently
argued true as stated; all nine declared skeleton-time proofs approved at
their claimed scope; the bundle hash independently recomputed.

## Minors, swept in the closing commit and re-verified

| # | Sweep |
|---|---|
| 1 | `ClassOracle/Classes.lean`'s module docstring now writes Theorem 2.6 as `NP = ⋃ c, NTIME (fun n => n ^ c + 1)`, matching the actual `Complexity.NP_eq_iUnion_NTIME` (the auditor supplied a full refutation of the `+1`-less reading under the exact-budget conventions — maintainer-verified against the Lean statement before sweeping) |
| 2 | `POracle_eq_P_of_mem_P`'s sketch rewritten with the auditor's explicit ledger: at most `t = c·(n^k+1)` queries of length ≤ `t`; per-query positioning/prefix-copy/restore `O(t+1)` plus decider-and-cleanup `O(d·((t+1)^e+1))`; total degree `k·(1 + max 1 e)` (not `k·e + O(1)`); the virtual input carries the **extracted prefix only**, blanked beyond the first blank (the cell-`1` garbage instance); preservation/reset invariants named as fill obligations |

Re-verification: `Classes.lean` and `SATOracle.lean` re-elaborate with zero
errors; `ClassOracle` lint 0 FAIL / 0 WARN.

## Notes (no change; dispositions recorded)

* **Note 3** (fixed-oracle clocks): the per-oracle class definitions stand;
  the timeout-wrapper reconciliation with [BGS75]'s all-oracle convention is
  exactly what phase P3.2's extrinsic budgets implement, and its round must
  justify its own clock coverage — carried as a P3.2-gate obligation.
* **Note 4**: the `SATᶜ` fallback polarity is confirmed benign.
* **Note 5**: the nine skeleton-time proofs are statement-approved; no fresh
  kernel replay was claimed.
* **Note 6**: build freshness, axiom closure, and the `edea2663 = 2cf44f1d`
  byte identity remain maintainer attestations, as every round records.

## Gifts recorded for the fill briefs

* The round's own construction for `compl_mem_POracle` — the direct
  emission-negating transformer — is simpler than the sketched capture
  wrapper; fills may take it.
* The explicit workhorse construction (redirect emissions to the query tape,
  replace the halting transition by query entry, two-step answer tail),
  including the `f x = []` case with no rewind.

## Standing obligations out of this gate

1. The ten fills, scheduled with the chapter-3/4 fill epochs; the Ex 3.6(2)
   fill carries the finding-2 ledger verbatim.
2. The natural-home promotions flagged by P3.2's skeleton into this surface
   (oracle locality lemmas, `stepWith` oracle-independence, relabelling)
   remain **deferred until the live P3.2 gate closes** — no file under a
   running audit moves.
