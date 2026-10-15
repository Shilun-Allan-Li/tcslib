# External audit pack — zone/virtual-input layer (§13), tranche A-S2, round 2

Round 1 (`audits/zone-infra-pack.md`, findings verbatim in
`audits/zone-infra-findings.md`) returned **1 blocker, 1 major, 2 minors**.
This round audits the repairs. Audited at commit `fb721402` (branch
`complexity/arora-barak-ch3-4`); the repaired files are attached in full,
with the round-1 pack and findings. The gate closes on zero blockers and
zero majors.

## Disposition table (verify each)

| Round-1 finding | Disposition |
|---|---|
| A-S2-1 (blocker: the inward room premise; the full-chain `Ω(T²)` family) | **Repaired as proposed.** `zoneShiftInW` carries no room condition (its guard is `1 ≤ i < ℓ` and lower-zone emptiness only); `zoneShiftOutW`'s receiving-room condition moved **inside its guard**; the dependent-hypothesis wrapper `zoneShift` is **removed**, replaced by hypothesis-free `zoneShiftIn`/`zoneShiftOut`; the head steps gain the guarded-total `zoneMove`; both machine rows drop the room binder and now realize the total guarded operation, identity branch included. **The required gate material is added**: `zoneShiftInW_full_donor` (the full-donor regression), `zoneStepPair`/`zoneCascadeRight` (your descending/move/ascending schedule as a pure fold), `zoneSide_cascadeRight` and `zoneCascadeRight_lengths` (the one-virtual-move and half-full-restoration statements, your schedule analysis adopted verbatim as the binding sketches), and `zoneCascade_cost_le` (the geometric charge bound, stated over `Finset.range` for import hygiene: `∑_{i<j} 4·(2^(i+1) + (i+1) + 1) ≤ 16·2^j`). Re-run your dead-end and full-chain instantiations against the repaired interface: both must now be served by legal inward shifts. |
| A-S2-2 (major: the received `sweepTM` refuted as the Z4 witness) | **Repaired as proposed**: the `one_work_tape_spaceUsed` sketch now names your counterexample as binding, routes the fill through a **demand-grown** sweep witness (reuse-and-refactor, no copying), and carries the all-`Γ'` retraction with the empty-alphabet and zero-tape cases; the composite's sketch names the corrected first stage and your `c₂·(c₁+1)` calculation. The statements are unchanged, as you judged them true. |
| A-S2-3 (minor: 25 vs 22 definitions) | Pack erratum acknowledged (the shipped round-1 pack stays verbatim); your inventory is adopted for fill ownership. The repair adds 6 sorried declarations and 3 definitions (`zoneShiftIn`, `zoneShiftOut`, `zoneMove`, `zoneStepPair`, `zoneCascadeRight` — recount and report the round-2 inventory). |
| A-S2-4 (minor: guard semantics; export names) | Docstrings corrected: the rows "realize the total guarded operation, including its identity branch"; the module's main-results list names `zoneShiftInW`/`OutW`, the new wrappers, the cascade exports, and `MultiTapeTM.spaceUsedByTape_le_card_Icc`. |
| A-S2-5 (note: the Ex 4.1 assessment overstated) | Adopted: design §13c downgrades it to a design-level verdict — stage 1 must specify a space-accounted input interface and parser ledger; a materialized input copy's `Ω(|x|)` is named. |
| A-S2-6 — A-S2-11 | No-findings rows and the evidence-boundary note carried; your layout/capacity arithmetic and Z3 record/guard numbers (record length 13; `351·(numStates+1)`; minimum 354 bits) are adopted into the eventual fill brief. |

## Brief for the auditor

1. Verify each disposition above against the attached repaired sources —
   in particular, blind-restate the **new** declarations
   (`zoneShiftIn`/`zoneShiftOut`, `zoneMove`, `zoneStepPair`,
   `zoneCascadeRight`, `zoneShiftInW_full_donor`, the three cascade
   contracts) and re-run your round-1 counterexamples: the `ℓ = 2`
   dead end, the full-chain family, and the four-move cycle must all be
   served by the repaired interface with the geometric ledger intact.
2. Check the repaired guards for new defects: the outward guard now
   conjoins fullness and receiving room — verify the identity branch is
   taken (not an ill-typed state) when either fails, and that the six
   sorried capacity fields remain provable under the new guards.
3. Check the cascade statements' preconditions (the classical pre-state)
   are the ones your schedule analysis needs — no stronger, no weaker —
   and that `zoneCascade_cost_le`'s reindexed form is your charge bound.
4. Confirm the Z4 sketches now carry your binding route and that no
   statement changed.
5. Report in the standard table; the debt screen (failure mode 5) applies
   to the repair delta (expected: no new copies — the cascade is a fold of
   the layer's own ops).

## Repository-side attestations (verify or challenge)

* Elaboration: the repaired `Build/Zone.lean` (588 lines) and
  `Robustness/SingleTape.lean` check at exit 0, zero `error:` lines;
  `Zone.lean` carries **22** sorry warnings (the round-1 18 declarations
  minus the removed `zoneShift`, plus the six repair declarations); lint
  0 FAIL both directories.
* The repair touched only `Build/Zone.lean` (rework) and the two Z4
  sketches in `SingleTape.lean` (docstring prose; statements byte-equal);
  `Codes2Tape.lean` and `AlphabetReduction.lean` are unchanged from
  round 1.
* Duplication ledger: new copies — none.

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Severity guide as in `audits/TEMPLATE.md`; findings verbatim into
`audits/zone-infra-r2-findings.md`; the gate closes on zero blockers and
majors.
