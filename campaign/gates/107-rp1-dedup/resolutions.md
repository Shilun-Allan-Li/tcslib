# Gate 107 (#216, RP-1 dedup): resolutions

## Round 1 findings (received 2026-11-06)

`findings.md`, verbatim (SHA-256
`edc38a27813278d98e7175f37b0893b34b664aa64f6ee0de117962af4731cbc9`). **Verdict: PASS with minor
evidence corrections: 0 blockers, 0 majors, 2 minors, 5 notes.** No remaining RP-1 read or
unintended proof change was found at `485cfbab`. **The gate is CLOSED.**

| # | Severity | Disposition |
|---|---|---|
| 1 | minor | **Accepted, fixed in the records.** The pack's account of the merge delta was incomplete. Between `f200144b` and `485cfbab`, 16 Lean files changed (979 lines added, 121 removed): the merges of #208, #212 and #213, with `SavitchARM/Deepen` new, plus `Savitch`, `Machines/Bin`, `ARMWidth`, `ARMWidthExample`, `ISCountGenCorrect`, `Mult`, `SpaceAmplifyPoly`, `SpaceAmplifyPolyCode`, `BPLInPCount`'s CE-1 re-point inside `stepRel_iff`, `ZoneRebalance` and the facade, as well as the four the pack named. The seal is regenerated at the merged head over the 53 eligible modules, `Deepen` included (`evidence/rule10-merged/`). The result is appended below. |
| 2 | minor | **Accepted.** `evidence/rule10/README.md` is corrected: the historical probes record 22 `sorry` warnings, 21 in `ClassPSPACE.TQBF` and one in `SpaceComplexity.Savitch` (`savitch`, before #208 closed it). The merged-head replay has only the 21. |
| 3–7 | note | No change. |
