# Chapter 3, phase P3.2 (relativization) — audit loop resolutions

**Gate: CLOSED (round 2, 2026-10-09).** Two rounds:

| Round | Verdict | Findings files |
|---|---|---|
| 1 | FAIL — 1 blocker, 0 majors, 2 minors, 2 notes | `audits/ch3-p32-findings.md` |
| 2 | **PASS — 0 blockers, 0 majors, 2 minors, 1 note** | `audits/ch3-p32-r2-findings.md` |

## The loop

* **Round 1's blocker** was the deepest finding of the campaign to date:
  `EXPCOM` was defined over the arbitrary `TimeHierarchy.code`, and
  `Turing.EffectiveMachineCode` bounds no decoding time (`canonizerTime` is
  arbitrary). The auditor built a *permitted* scheme embedding an
  arbitrarily hard decidable language into `decode` — putting `EXPCOM`
  outside `EXP` — and a second permitted scheme whose `EXPCOM` oracle
  separates relativized `P` from `NP`. The four EXP-side statements were
  unprovable as stated; the locality layer (7 statements), the stage
  construction, `U_B ∈ NP^B`, the enumeration, `exists_not_timeConstructible`,
  and the `baker_gill_solovay` existential all survived round 1 outright.
* **The repair**: `Turing.UniformMachineCode` — the scheme packaged with a
  bounded-acceptance simulator whose time is **one polynomial in
  `|α| + |x| + t + 1` jointly** — with its sorried existence
  (`exists_uniformMachineCode`) and `EXPCOM` redefined over the chosen
  scheme `Complexity.expCode` (the choice-over-a-sorried-existence declared
  openly). The hierarchy's own code is untouched: fixed-code arguments
  never needed uniformity.
* **Round 2**: PASS. The auditor verified both round-1 counterconstructions
  violate the new simulator clauses (their hypothetical simulators would
  decide the embedded hard languages in polynomial time), proved the
  existence statement true by an independent polynomial construction over
  the concrete grammar (binary minimum-length guard before state iteration;
  `|(codeDecode α).serialize| ≤ max |α| 84`; three-way output status;
  `C·S^e ≤ d·S^d`), and re-derived the full uniform ledger for
  `NP^EXPCOM ⊆ EXP` (`2^{(2d+2)·p(n)}`, absorbed at exponent `k + 1`).

## Minors, swept in the closing commit and re-verified

| # | Sweep |
|---|---|
| R2-1 | The existence sketch no longer claims the received construction's ledgers were "per-phase polynomial, never assembled" — `MathlibBridge` explicitly supersedes its polynomial variant with an arbitrary-time route. The sketch now commissions the **independent** polynomial parser/simulator for the concrete grammar (the auditor's own construction, adopted: binary guard, serialization bound, three-way status, degree arithmetic), reusing the decoder's correctness lemmas only |
| R2-2 | The enumeration sketch's residual "triple pairing" now reads "four-coordinate pairing" |

## Notes (dispositions recorded)

* **R2-3**: `EXPCOM` depends on the sorried existence through
  `Classical.choice` — declared; at the fill gate, verify the axiom closure
  of `exists_uniformMachineCode`, `expCode`, `EXPCOM`, and the completed
  consumers (carried obligation).
* The interface is mildly stronger than the consumers need (arbitrary
  deadlines, polynomial in the numerical deadline) — realizable and
  harmless, recorded.
* The fixed-oracle clock convention (round-1 note 4) stays as the declared
  P3.1-inherited deviation.

## Consequences

* **Natural-home promotions into the P3.1 files are unblocked** (they were
  deferred "until P3.2 closes") — fill-time housekeeping, flagged in the
  relevant sketches.
* The `Diagonalization.lean` facade leaves this gate's freeze; with P3.3
  closing the same day, it now carries `NTimeHierarchy`, and the root's
  temporary imports are removed.
* Statement-freeze baseline: the closing commit.
