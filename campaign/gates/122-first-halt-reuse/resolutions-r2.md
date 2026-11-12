# Gate 122 round 2 resolutions for #242

Round 1 returned PASS for the frozen scope at `f3c8c050ef98375bc237c72bde74f83d33833374`
(0 blockers, 0 majors, 0 minors, 7 notes; `findings.md`, SHA-256
`194625851fc99e2e208077f350b14ad9df75bef7bf78f510ef4ce4aecee14437`). The maintainer then held the
gate on its own finding **M1** (`resolutions.md`): five step reads shared with gate 121 and seven
held operational fronts lacked a rule-10 disposition. The current PR head is
`e0b98ac2a2396324bc9ddf76f27dceb3eba5ffe3`, which merges the campaign after #241
(`3a10a32e8975b79621873626198356fdea61e988`). Seyoon selected Codex for this follow-up.

| Front (M1) | Resolution |
| --- | --- |
| Five shared gate 121 step donors (`clCopy_idle`, `clCmp_idle`, `clWipe_idle`, `clFresh_idle`, `clInput_idle`) | Repaired on the campaign by #241 (gate 121 closed) and merged into #242. They read the step through `MultiTapeTM.step_of_some`. #242 does not change them. |
| 52 `MARMTime.runFrom_count_eq` | Repaired (`f6d8f0f3`, using the readers #252 merged). Its whole-proof seal passes. |
| 58 `NDClockHostRun.startup` | Repaired (`f6d8f0f3`). Its whole-proof seal passes. |
| 83 `SingleTape.one_work_tape`, 84 `SingleTape.dg_all_inputs` | Repaired (`f6d8f0f3`). Both whole-proof seals pass. |
| 82 `clockStageCfg_captures` | Repaired by the approved clock-capture change (`6fe6b56c`): four non-simp `rfl` readers (`maskedClock_k`, `maskedClock_State`, `obliviousSchedule_k`, `obliviousSchedule_State`) in `ObliviousSchedule`, and a header that casts through them, definitionally equal to the old one. Its whole-proof seal passes. |
| 50 `Call.call_run`, 51 `Clean.cleanTM_run` | **Out of scope, scheduled (Seyoon, 2026-11-12).** #242 does not change `Call.lean` or `Clean.lean`. They are open rule-10 fronts, not debt, for a later reader PR (ledger: "Gate 122 held Call and Clean fronts"). |

**Consumers of the new header (Seyoon, 2026-11-12, same ruling).** `obliviousSchedule_ready`
(`Oblivious`) and `obliviousSchedule_halts` (`ObliviousLedger`) change by one line each,
`simp only [id_eq] at hclock`. Their whole-proof seals fail on reads that already exist on the
campaign: `ready`'s unchanged statement elaborates only by unfolding `obliviousSchedule`, and its
proof runs `simp [setupCfg]`; `halts` reads `clockStageCfg`'s fields by `change` and `rw`. They are
open rule-10 fronts for the same scheduled reader PR, not debt. The narrowed check
(`seals-narrow/`) seals everything except `obliviousSchedule` for `ready` (it passes) and except
`clockStageCfg` for `halts` (it still fails on a pre-existing read). Both outcomes are disclosed.

Notes 1–7 of round 1 are accepted within their stated scopes; this round's evidence replaces
their source, replay, seal, lint and screen inputs.
