# Gate 122 round 2 · first-halt and backward-liveness reuse after #241 (PR #242)

**Not yet clear to merge** · PR #242 is a draft. Seyoon dispatches and merges.
The current Lean commit is `e0b98ac2a2396324bc9ddf76f27dceb3eba5ffe3`, against campaign Lean `3a10a32e8975b79621873626198356fdea61e988`
(the campaign after #241). Round 1 audited `f3c8c050ef98375bc237c72bde74f83d33833374` and
returned PASS for its frozen scope (`findings.md`, verbatim). The maintainer held the gate on
its own finding M1 (`resolutions.md`). This round checks M1's resolution on the integrated head.

## What changed since round 1

- `f6d8f0f3`: `MARMTime.runFrom_count_eq`, `NDClockHostRun.startup` and SingleTape's
  `one_work_tape` and `dg_all_inputs` read through the readers #252 merged (gate 130).
- `6fe6b56c`: the approved clock-capture change. Four non-simp `rfl` readers in
  `ObliviousSchedule` (`maskedClock_k`, `maskedClock_State`, `obliviousSchedule_k`,
  `obliviousSchedule_State`); `clockStageCfg_captures` states its endpoint through them
  (definitionally equal to the old header); its two consumers add `simp only [id_eq] at hclock`.
- `e0b98ac2`: the merge of the campaign after #241, which repaired the five shared gate 121
  step donors in Hardness. It merged without conflicts.

`patch/round1-to-head.patch` in the carrier is the exact difference from the audited source.

## Brief for the auditor

1. Check each row of `resolutions-r2.md`, the M1 fronts, against the current sources.
2. Check the whole-proof seals: 24 changed proofs in 15 owners, with each ordinary foreign
   definition they reach made irreducible (52 definitions), and 104 paired controls
   (run in two halves of 26 definitions because Lean stops after 100 errors). 22 seals pass.
   The two failures, `obliviousSchedule_ready` and `obliviousSchedule_halts`, are the disclosed
   pre-existing reads Seyoon ruled out of scope (open fronts, not debt). Check that #242's only
   change in each is the `id_eq` line and that the failing reads exist on the campaign.
3. Check the copy screen on round 1's 44-file population: 3 new pairs (two first-halt adaptations, one initial-configuration field read) and 18 removed, all dispositioned.
   Report any exact reusable proof the changed declarations should cite instead.
4. Check that `Call.call_run` and `Clean.cleanTM_run` are unchanged by #242.

## Evidence

- `r2-evidence/SOURCE.json`: the 24 changed or added declarations per owner.
- `r2-evidence/REPLAY.json`: the merged-tree replay of the 354-module downstream closure of the
  15 changed files on the complete campaign snapshot after #241 (876 objects; prospective
  tree `f022343841bf297e4f5b40658bd28b8f286d3ca4`). 354 passed, 0 failed. The 65 inherited admissions are in nine downstream
  modules whose sources are byte-identical to earlier campaign replays; the owners have none.
- `r2-evidence/CHECKED-SUMMARY-r2.json`: seals, controls, metadata (standard axioms only), lint
  (no new finding) and the argument sweep (one candidate, `simp [setupCfg]` in
  `obliviousSchedule_ready`, one of the disclosed reads).
- The copy screen: BASE `declarations screened: 2659; copy pairs (target reproduces >= half of source): 2510; reproduced text: 529,911 chars`; HEAD `declarations screened: 2657; copy pairs (target reproduces >= half of source): 2495; reproduced text: 528,196 chars`.
  `PAIR-DISPOSITIONS.json` covers every new and removed pair.
- `r2-evidence/DATA-CARRIER-r2.json` and its recovery map hold 1314 logical files: every replay
  receipt and log, seal and control sources and logs (including the narrowed seal and the
  100-error control run), metadata, lint, both screen outputs, **all 44 population files at both
  commits and the scorer**, the campaign versions of the owners, both patches and the drivers.
- This round's checks ran on the cloud machine with the approved wrappers. The 20
  PFR-dependent NewmanTheorem modules are not built there; none is in or imported by the closure.

Use the campaign finding table and give a CLEAR or HOLD verdict.
**Deliver your findings as a downloadable file named
`gate122-first-halt-reuse-r2-findings.md`** (the findings table and the verdict
line, no other wrapping), and also paste its content in your reply.
