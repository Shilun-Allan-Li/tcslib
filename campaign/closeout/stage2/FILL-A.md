# Stage 2, Fill A: rewinds and first halts (IR-1, RC-4)

Read `COMMON.md` first.

**Files you may change:**
- `TCSlib/Complexity/ClassNP/ExhaustiveReplay.lean`
- `TCSlib/Complexity/TuringMachine/UniversalK.lean`
- `TCSlib/Complexity/ClassNP/NDNormalForm.lean`
- `TCSlib/Complexity/TuringMachine/Nondeterministic.lean` (the new lemma only)

## A1. IR-1: the last input-rewind copies

Ledger: `campaign/duplication-ledger.md`, "IR-1, the input rewind family".

- **ExhaustiveReplay.** The private `xr_inRewindTM` and its run lemma re-prove the public
  `Build/InputRewind` row: `Turing.inputRewindTM` and `Turing.inputRewindTM_run` (exact time, with
  a first-visit cut). The screen gives 82% and 73%. Re-point the replay's phase host to the
  public row and delete the private machine and its run lemma.
- **UniversalK.** U2-S's private `ss_inputRewind` is a third copy; re-point it the same way.
  - The self-startup's phase-host arms change, so recheck the seam-time arithmetic inside the
    public `exists_selfStartupTMK`.
  - Its statement must stay byte-identical. If the time bound cannot be kept, stop and report.
- Use `Turing.Cfg.mapState_mapState` (InputRewind) wherever a composed state renaming is
  collapsed by hand.
- **Also in ExhaustiveReplay, from WS-1:** the private `xr_window_stepWith` (one choice step keeps
  the radius window) should be re-proved from the public `Turing.Cfg.InWindow.apply_iff` and
  `Cfg.InWindow.mono` (Build/CfgRecord). Its output-bound clause stays as it is.
- Measured: 6 members, 144 lines, 9 uses, 0 rule-10 exposure today.

## A2. RC-4: a public NDTM first-halt row (approved by Seyoon, 2026-11-16)

Ledger: "RC-4, row candidates from NF cont1", first bullet.

1. **Publish** in `TuringMachine/Nondeterministic` the nondeterministic form of
   `MultiTapeTM.exists_first_halt` (`TuringMachine/Finite`, line 218). If the run of `N` along a
   choice word `w` from `c` has halted, there is a least prefix length `u ≤ |w|` at which it has
   halted, every shorter prefix is live, and the run along `w` equals the run along `w.take u`.
   - Choose a name in the file's style, for example `Turing.NDTM.exists_first_halt`.
   - Prove it by `Nat.find` over the prefixes, with `NDTM.runWith_append` and
     `NDTM.runWith_of_halt`.
   - State it so that both sites below cite it directly.
2. **Cite it** at the two inline copies:
   - ClassNP/NDNormalForm's `nf_forward` (its `Nat.find` block);
   - ExhaustiveReplay's `xr_replay_host` (its `Nat.find` block).

The rebuild for this lemma is about 160 modules; the maintainer runs it.
