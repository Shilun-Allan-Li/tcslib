# Stage 2, Fill C: renamed configurations and the universal capture (RN-1, MIG-7)

Read `COMMON.md` first.

**Files you may change:**
- `TCSlib/Complexity/TuringMachine/CodeSimulator.lean`
- `TCSlib/Complexity/TuringMachine/UniversalStartup.lean`

`Build/Embed` may be cited but not edited. The consumers of `universalCaptureTM` (Universal,
UniversalInterpreter, UniversalK, Build/Wrappers, ClassNP/Nondeterminism) must not change. If
they would have to, stop and report.

## C1. RN-1 in CodeSimulator

Ledger: "RN-1, renamed configurations converted field by field, scoped by kind".

- `Turing.Cfg.mapState_eq_of_fields` (TuringMachine/CfgFacts, line 69) states that a renamed
  configuration equals any configuration with its data fields and the renamed state.
- Replace each inline five-line `Cfg.ext`/`Cfg.mapState_*` conversion in CodeSimulator with it.
  These are in `canonStageOuterSpec`, `canonStageInnerSpec`, and any that remain in the stage
  front after the CC7-1 template (#345: `canonStageLeg_of` and the legs).
- `us_start` stays as it is (RS-1 is carried).

## C2. MIG-7: the universal capture onto Embed (approved by Seyoon, 2026-11-16)

Backlog: `campaign/backlog.md`, the MIG table, row MIG-7 (about −130 lines).

- `TuringMachine/UniversalStartup` may now import `TuringMachine/Build/Embed`.
- Rebuild `universalCaptureTM` and its run lemmas on Embed's `embedSilentTM` and its public
  contract.
- Keep every public statement in UniversalStartup byte-identical, so that no consumer changes.
- Measured: 8 members, 126 lines, 6 uses, and 5 + 5 proofs exposed under rule 10. Expect
  repairs in the rewritten run lemmas.
