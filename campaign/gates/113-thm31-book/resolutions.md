# Gate 113 (#223, the book-form time hierarchy): resolutions

## Round 1 findings (received 2026-11-06)

`findings.md`, verbatim (SHA-256 `9bf58c0b5e4d78b63a7ab56a5d21e88f5b3f33b7060ea8b1c56f0ef83f7857d4`). **Verdict: PASS: 0 blockers, 0 majors,
4 minors, 4 notes.** The statements and the proof construction pass. **The gate is CLOSED.**

| # | Severity | Disposition |
|---|---|---|
| 1 | minor | **Fixed** (`evidence/probes-r1fix/`). The seal is regenerated from the head's text at `09a10335`: three copies of the new section (lines 574–743 and 747–806), relocated to their own namespaces and otherwise verbatim. Section U has one unsealed control per sealed definition, each closing by `rfl`, eleven in all. Each sealed copy opens with one `fail_if_success` control per definition it seals. The run gives **exactly two errors**: copy A at the `DTIME` destructuring (line 208) and copy B at the `DecidesInTime` read (line 486). Section U and copy C elaborate, and every sealed control passes. A first run had two ill-formed unsealed controls (`EffectiveCodeK` has no `decode`; `indicator` needs classical decidability). They are fixed and that output is kept (`T31Seal-first-run.out`). The pack's 799 lines is corrected: the file has 807. |
| 2 | minor | **Accepted, kept deferred and explicit.** Publishing `mem_DTIME_iff` and `FinTM.decidesInTime_iff` beside their definitions in `ClassP/DTIME` would replay most of the tree. It is recorded as ledger family **DT-1** (below) for the dedup window. Once those are published, `normalForm` re-points and the seal runs without exceptions. |
| 3 | minor | **Accepted.** The pack's `f ≡ 1` "counterexample" is withdrawn: `TimeConstructible g` gives `g n ≥ n`, and the separation still holds there. The statement's `hf` is sufficient for absorbing the input length and controlling the floor logarithm. The docstring never made the claim, and no theorem changes. |
| 4 | minor | **Fixed** (`09a10335`). The module opening says "the self-universal machine for two-work-tape codes". The inherited authorization date and design-note path are removed from the module docstring; they remain in these records. `Diagonal.lean` elaborates at the new head against the current campaign snapshot with no messages (`Diagonal-head.out`). |
| 5–8 | note | No change. |
