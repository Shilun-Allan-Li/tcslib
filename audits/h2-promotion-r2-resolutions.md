# H2-S statement gate, round 2: resolutions

**Round 2:** `audits/h2-promotion-r2-pack.md`; bundle `audits/h2-promotion-r2-bundle.md`, SHA-256
`6bc5f4154d0bc5e63c67d5bec5156a4a6568ae5a3a3945a1e98d8ee5693223d8`, 69 sections.
**Findings:** `audits/h2-promotion-r2-findings.md`, verbatim.
**Verdict: the gate CLOSES (2026-10-14): 0 blockers, 0 majors, 8 minors.** Round 1's findings 1, 3,
5, 7 and 8 are resolved; 2 at the consumer-interface level; 4 for physical forwarding; 6
partially (R2-1). The move H2-M proceeds as proposed.

| # | Finding (short) | Resolution |
|---|---|---|
| R2-1 | `fidelity-r2.py` accepts an additive restated as an `axiom`, and an indented extra `axiom` | Accepted. H2-M's freeze uses the maintainer's `declfreeze.py` and the move manifest. The axiom probe of the landed module (no `sorryAx`, standard axioms only) and an explicit `axiom` grep of the module are acceptance checks. |
| R2-2 | Block simulation: "off every boundary state" includes time zero | Recorded in the design: liveness for `0 ≤ u < L`; any boundary-state exclusion is `0 < u < L`, and H2's transport does not need it. |
| R2-3 | Cofinality does not supply intermediate frames | Recorded: the landing-form ruler host (B6 hosts' gate, closed) supplies the frames explicitly; the older statement plus a lower bound is not the full interface. |
| R2-4 | CO-RF's stationary-head claim does not cover buffered capture | Recorded: the claim holds for the core tapes and physical forwarding; a buffered variant needs a capture invariant and its visited-cell bound, or the existing capture-wrapper contracts. |
| R2-5 | The ruler's `C·(ℓ+1)` depends on `|bits t|` for timed consumers | Recorded: C1 uses the bounded window copy (decision 5, gated with C1's host contracts), not the ruler. U-1's timed device is its own design item: untimed `universal` and `timed_universal` are separated, and the budget-dependent overhead belongs to the latter's ledger and O8. |
| R2-6 | `inj` is called an injection; it is a state map | As B6 hosts' minor 2: "state map" at landing. |
| R2-7 | 35 counts name pairs (75 code occurrences); partition sizes are 471/1,075/870 | Recorded with the corrected metrics. |
| R2-8 | MIG-0b's `RoundContract` envelopes cover work heads only | Recorded: the adapter's envelopes are work-head envelopes; the input trajectory stays with `roundTM_effect` or a companion theorem. |

**Next:** H2-M, the maintainer's move PR, now, before any B5a brief, using round 2's manifest
recomputed at the landing base. It carries the authorized text edits (H1's frozen over-long
lines re-wrapped, `hr` → `_hr`) and the 56-name surface, with its own 8-module replay.
