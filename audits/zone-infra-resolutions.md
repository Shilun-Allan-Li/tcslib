# Resolutions — zone/virtual-input layer (§13), statement gate, tranche A-S2

Loop summary for the A-S2 external audit (rounds 1-3; packs
`audits/zone-infra-{,r2-,r3-}pack.md`, findings preserved verbatim in
`audits/zone-infra-{,r2-,r3-}findings.md`).

## Outcome

**Round 3: PASS — 0 blockers, 0 majors, 1 minor. The A-S2 statement gate
is CLOSED after three rounds.** The loop:

* **Round 1 (FAIL 1/1/2)** — A-S2-1: the maintainer's shared `hroom`
  premise made a full inward donor illegal (the classical case); the
  auditor proved the delivered interface forces `Ω(T²)` and supplied the
  repair and its analysis. A-S2-2: the Z4 sketch falsely credited the
  received `sweepTM` (unconditional window growth; the stationary-head
  scanner refutes it). Repairs: premise-free inward op, outward room
  inside the guard, hypothesis-free wrappers, guarded-total `zoneMove`,
  the cascade material added; the Z4 route replaced by the demand-grown
  witness with the all-`Γ'` retraction; the Ex 4.1 assessment downgraded
  to design level (§13c).
* **Round 2 (FAIL 1/0/1)** — the round-1 operational repair accepted and
  the Z4 major closed; A-S2-R2-1: the new cascade contracts lacked the
  **top-left receiving room** (false at `ℓ = 1, j = 0`); the auditor
  supplied the necessity argument, the weaker/stronger hypothesis split,
  and the two-pass induction. Repairs: the lengths theorem gained the
  necessary `+2^j` room hypothesis, the word theorem the weaker
  `+2^(j-1)` form; regressions `zoneCascadeRight_zero` and
  `zoneCascadeRight_blocked` added.
* **Round 3 (PASS 0/0/1)** — both amended contracts and both regressions
  verified true as literally stated, with the complete two-pass induction,
  the necessity and classical-invariant arguments, six boundary traces
  (including the intended word/length hypothesis separation and the
  repaired former dead end), and ~74,500 finite-model instances.

## Disposition of the round-3 minor

| # | Severity | Disposition |
|---|---|---|
| A-S2-R3-2 | minor | **Pack erratum acknowledged** (the shipped packs stay verbatim): the round-3 pack's inventory correction was itself wrong — the amended main contracts are not new declarations. **The auditor's inventory is canonical** and binds the fill brief: `Zone.lean` 20 definitions/structures, **20 sorried declarations, 24 literal `sorry` terms** (16 sorried theorems + 4 sorried definitions carrying the 8 capacity holes), 2 skeleton proofs, 38 explicit declarations; whole tranche (with the unchanged `Codes2Tape`/Z4/`alphabet_reduction_spaceUsed` rows): **26 definitions, 25 sorried declarations, 29 `sorry` terms, 3 skeleton proofs, 50 explicit declarations**. |

## Adopted and carried into the fill

* The auditors' analyses are the **binding fill routes**: the round-3
  two-pass induction (word and lengths), the round-2 schedule analysis,
  the round-1 Z3 grammar numbers (record width 13; table guard
  `351·(numStates+1)`; minimum complete serialization 354), the round-1
  demand-grown Z4 witness route with the retraction and the
  empty-alphabet/zero-tape cases, and the round-1 machine-row
  implementation notes (geometric navigation ledger, reserved invalid
  pair codes as temporary delimiters).
* The recommended sanity exports of rounds 1-3 are offered to the fill as
  optional permanent lemmas (fixed-`ℓ` `zoneTape` injectivity; `zoneSide`
  length arithmetic; the small-`s` index table; the sharper signed
  extent; guard-false identity specializations; serializer-length
  identity and parser-guard lemma; `numStates = 0` regression; the
  stationary-head scanner as a Z4 regression).
* Evidence boundaries carried: all three rounds are source-level audits;
  elaboration, lint, and historical byte identity remain maintainer
  attestations (logs in the repository).
* The **Ex 4.1 obligation** stands discharged at design level only
  (§13c): the stage-1 universal design must present a space-accounted
  input interface and parser ledger before the primary route is claimed.

## Gate state

| Item | State |
|---|---|
| §13 tranche A-S1 (Z5 + Z1 + rider) | statements CLOSED (round 1); fill integrated (vhost-f1); **fill gate awaiting findings** |
| §13 tranche A-S2 (Z2 + Z3 + Z4) statement gate | **CLOSED (round 3)** |
| A-S2 fill epoch | briefs to be drafted (three file-disjoint batches: Zone, Codes2Tape, Z4/Robustness) |
