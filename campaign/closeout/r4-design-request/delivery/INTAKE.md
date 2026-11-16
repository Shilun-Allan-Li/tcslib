# R4 design delivery: maintainer intake (2026-11-16)

**Delivery.** `r4-design.md` (51,083 bytes, SHA-256 `66a99292…95ce`), copied verbatim from the exchange
branch (`arora-barak-ch3-4/inbox/r4-design/r4-design.md`, exchange commit `3b5e3d4d7`). It was produced by a
Claude cloud worker from bundle `d8da8a45…` (Lean `68cba664`, records `4211cada`). No Lean was run. Treated
as data; the claims below were rechecked by the maintainer against the tree at `68cba664`.

## Rechecked and confirmed

- `clA5Compare_compute` cites `exists_first_entry_of_fixed` at `Hardness:7252`. The maintainer inventory's
  `7264` is wrong. Five more Hardness sites cite it: 1279, 1742, 2164, 3003, 3271.
- `sat_guard_add`/`clA5_guard_add` (`SAT:4035`/`Hardness:6368`) is an exact twin that is missing from the
  maintainer inventory. So is the SAT-side kind-4 instance `satScanTM/Cfg/_step/_run/_computes` (`SAT:230–301`).
  The inventory has no `guard_add` or `satScan` entry.
- Import reach (closure computed on the tree):
  - `SAT` reaches `Build/Loop` but not `Build/EmitIterEmbed`, `Build/WordTests`, `PolyTimeBlockLoop` or
    `BinaryArith/Iterate`.
  - `Hardness` reaches `EmitIterEmbed`, `WordTests` and `PolyTimeBlockLoop`, but not `Iterate`.
  - Neither `Iterate`'s closure nor `EmitIterEmbed`'s contains `SAT` or `Hardness`, so the imports below
    would create no cycle.
- `FinTM.computesFunInTime_decideEq` (PL-1's target) is in `Build/WordTests`, which imports only
  `Build/Primitives`.

## Maintainer additions (not in the delivery)

1. **K3 already has a public home.** `Build/EmitIterEmbed` publishes `padAction`, `embedCfg`,
   `embedCfg_ofWords`, `padAction_apply`, `embed_step` and `embed_run`. `satPad*`/`clA5Pad*` are its special
   case with an identity state map: the definitions match field for field.
   - K3 can therefore be retired as citations with **no new API**, separately from K6's host question.
   - `satPad_run` is unconditional, but `embed_run` takes an exit-avoidance hypothesis. The run lemma would
     come from `embed_step` plus `runFrom_comm_of_step` (est.).
   - Hardness needs no import. SAT needs `import …Build.EmitIterEmbed`, a new import into a frozen file.
2. **`guard_add` has a public counterpart.** `EmitIterEmbed.SafeRun.trans` states the same concatenation fact.
3. **The SG1-UH lead (delivery §4) is partly confirmed.**
   - `Complexity.BinArith.polyTimeComputable_iterate` (`ClassP/BinaryArith/Iterate.lean:190`) exists. It is
     public, built on `BlockLoop`, and needs only orbit-length bounds.
   - It is not a drop-in replacement: it fixes the iteration count at `a(|z|+1)^k`, whereas `clA5Iter_native`
     needs a count `N x` given in unary. A variable-count corollary is needed: a counter-guarded round
     iterated a polynomial number of times, using `PolyTimeComputable.output_length_le` to bound `N x`.
     Est. 50–110 lines.
   - `clVisitStep_native` exists, so `clVisitRows_native` can use the same closure.
   - The dead code would then be the 12 `clRepeat*` declarations, `clNative_cleanCall` and
     `clVisitStep_cleanCall`, whose only uses are the repeat path (`Hardness:5653`, `6042`, `6753`).
   - The SG1-UH lead changes from a host move costing an est. +170 to +370 lines to a private deletion of an
     est. −150 to −300 lines, with no new public API. It needs a new import into frozen `Hardness`
     (`ClassP/BinaryArith/Iterate`; cycle-free).
   - Measurement needed before any ruling. It would also remove 5 of item 13's 42 use sites.

## Disposition of the delivery's recommendations

| Family | Delivery | Maintainer view |
|---|---|---|
| SG1-A + PL-1 | Run (pilot) | Agree. SAT import of `WordTests` (PL-1) and of `PolyTimeBlockLoop` (head/tail) are optional and need rulings; without them those SAT bodies stay. |
| SG1-B | Run with stop rule (+50 lines, pairs) | Agree; needs API approval (`CleanModule`, `stopTM`, two corollaries, `exists_first_halt_pos`). |
| SG1-C | Carry by default | Split it. K3 → citations of `EmitIterEmbed` (no API; SAT import ruling). K6 (host) → carry. |
| SG1-UH | Carry | Re-measure with the iteration-closure route first (addition 3). |
| Item 13 | Carry | Agree. |
| FH-1 held | Records | Agree; recount the five reader-repaired owners at the tip. Move `call_run`/`cleanTM_run` to the reader-PR row. |
| FE-LIVE-1 | Close in records | Agree (already retired). |
