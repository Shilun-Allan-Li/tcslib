# C1-WC partial delivery — environment blocked

**The target is not proved.** `Turing.exists_inputWindowCopyTM` retains its original `sorry`.
The only source change is the authorized **Fill appendix (C1-WC)** in its docstring.
No unverified helper, partial proof term, new axiom, or additional admission is delivered.
This is a continuation record, not a completed fill or a successful verification attestation.

## Pin and input verification

- Base: `83ec6348b325f060cec2a917b45a4eda6e301d84`.
- Campaign branch checked out first: `complexity/arora-barak-ch3-4`, at
  `2cce48048b5875fae75d69ef70ee9032b6b5e744` when cloned.
- `git merge-base --is-ancestor 83ec6348b325f060cec2a917b45a4eda6e301d84 HEAD`: exit 0.
- Created `fill/c1-window` at exactly the base; no rebase, merge, cherry-pick, push, or PR.
- Delivery commit: `555f7f253828af2cb097401e094765e42ac47edf`.
- Brief SHA-256: `4c05c6af3164c5af837c141747b8bae14ff64c07b52769bb37bb46710582fc17` — matches.
- Addendum SHA-256: `a25474c52b6b8e8bc1295fad48278b3356b8fed482d2e49c5874554f6d8d2928` — matches.
- Repository brief matches the uploaded brief exactly after replacing `@ANCESTOR@` by the base.
- The bundle has one prerequisite, exactly the base, and one advertised fill-branch head.

## Escalation E1: the verification environment

The unmodified pinned Lean executable printed `error: failed to locate application`.
The exact attached fallback was then compiled and used. Its source SHA-256 is
`985924ad83d39e108c0a2107bab07e65cdeb88641453508ab5acda115534fba7`.
The source is included at `evidence/runtime/executable-path.c`; the compiled `.so` is excluded.

Only Lean/Lake launch wrappers set these exact variables:

```text
LEAN_SYSROOT=/workspace/scratch/edcf4c9982ed/runtime/lean-4.25.0-linux
LAKE_HOME=/workspace/scratch/edcf4c9982ed/runtime/lean-4.25.0-linux
LD_PRELOAD=/workspace/scratch/edf8bcbbbb4e/runtime/executable-path.so
```

Check and cache commands selected those wrappers with:

```text
PATH=/workspace/scratch/edf8bcbbbb4e/runtime/bin:$PATH
```

The successful version check reported Lean 4.25.0, commit
`cdd38ac5115bdeec5f609e9126cce00f51ae88b3`. However:

1. `lake exe cache get` failed during decompression with `No space left on device`
   and `leantar failed with error code 101`.
2. The required fresh bootstrap, invoked once from the 80-module order list, crashed
   on its first module, `TCSlib/Complexity/TuringMachine/Build/Zone`:
   `lean exited with status 135`; no fresh olean was produced.
3. An exploratory check of the pinned `Build/Convention`, started while the bootstrap
   was running, also crashed with status 135. Its cache provenance is recorded in
   `logs/bootstrap.log`. No exploratory proof check completed.

The cause of SIGBUS was not established; the disk-space failure is independently observed.
The fallback restored `--version`, but did not yield a usable verification session.
After these failures were observed, formal checking stopped under the addendum's stop rule;
no additional runtime workaround, permission change, toolchain patch, or sandbox escalation
was attempted. `lake build` was never run.

The initial toolchain extraction also ran out of disk space. Only this run's failed extraction,
redundant downloaded archive, and exploratory cache copies were removed for recovery/delivery.
The reused executable matched the downloaded pinned release, and dependency repository hashes
matched `lake-manifest.json`. Reuse did not replace the required fresh bootstrap.

**Requested resolution:** restore sufficient disk space and an intact pinned dependency cache,
then restart the required baseline, proof checks, probe, axiom prints, and final sweep. No
mathematical obstruction or missing public API has been established. No ground rule is relaxed.

## Open declaration and continuation sketch

The sole open declaration is `Turing.exists_inputWindowCopyTM`.

**Proof sketch.** Use a one-tape body with Boolean states: `false` is the anchor and `true`
is the escape. At `some b`, write `b` on its tape and move both heads right, returning to
`false`; at `none`, take one stationary silent step to `true`. The existing counter loop
adds the second tape as its last tape. A prefix invariant states that after each successful
round the copied interval has grown by one input cell, both copying heads have advanced by
one, the remaining cells are unchanged, and the output is unchanged. Read the orbit using
`roundOrbit_zero` and `roundOrbit_succ`, not by unfolding its abbreviation.

For exhaustion, apply `counterLoopTM_run_done`. For early input end, apply
`counterLoopTM_run_escape`, with the extra end-marker round. Instantiate the existing
`phaseHostTM` with two tags: both loop exits redirect in one silent step to a fresh common
exit. `phaseHostTM_run` preserves the earlier loop prefix, whose tag excludes this exit.
Finally apply R1's forwarding embedding to select `dst` and `j`; use its public configuration
and run equations for the endpoint and frame. No second loop, embedding, or seam is needed.

This sketch is not a checked proof. Scratch drafts were not elaborated successfully and are
not included as source or as claims of progress. No private declaration is delivered.

### Planned constant and both ledgers

The planned constant is **`C = 6`**, not yet instantiated by a Lean proof.
With one step per body round and one final join step:

- Exhaustion, `|y| = d`:
  `d + (4d + 2|w| + 2) + 1 = 5d + 2|w| + 3 <= 6(d + 1) + 2|w|`.
- Early end, `r = |y| + 1 <= d`, so `r >= 1`:
  `r + (4r + 2|w|) + 1 = 5r + 2|w| + 1 <= 6r + 2|w|`.

The first line uses `counterOverhead_le` once; the second uses
`counterOverhead_le_of_le`. The counter words would be all `true` on exhaustion and
`counterWord w (|y| + 1)` on escape, with width from `counterWord_length`.
The sketch includes zero counter value, starting at the right end, early input termination,
and leading zero bits; none of these cases has been formally checked in this run.

**Promotion candidate:** a generic counter-loop contract for a one-step returning/escaping
body, shared with input seek. This is a recommendation only; no such contract was introduced.

## Ownership, declarations, and public API

- Only region (c), the flagged target-docstring appendix, changes. Regions (a) and (b) are untouched.
- The target's entire statement and proof body are byte-identical to the base.
- No imports are added. The module header, module docstring, and all other tracked files are unchanged.
- New declarations and roles: **none**. Final counts: **1 public theorem, 0 private declarations**.
- File size: **91 lines**, from 84. No new line exceeds 100 characters.
- No body leaf is delivered. The proposed leaf is needed because the catalog has no one-step
  cyclic native-input copy body with this end-marker escape.
- No new executable proof citation or external definition unfolding is present.
- The only new source-level citation is the appendix's `Turing.phaseHostTM_run`, already public
  at the base in `Build/Seam.lean`. Its definition is not unfolded.
- The import probe rerun is **blocked**. The required future extension is
  `#check @Turing.phaseHostTM_run`. The existing 49-check probe remains unchanged.
- Proposed route names beyond that probe, not citations in a delivered proof:
  `Turing.phaseHostTM`, `Turing.roundOrbit_zero`, `Turing.roundOrbit_succ`,
  `Turing.inputSymbolInner`, `Turing.Cfg.ext`, and the published embedding field equations.
  A continuation must inventory and probe every name it actually uses.
- Added-diff grep for `copyTM_run`, `transferTM_run`, `clearTM_run`, `compareTM_run`,
  `incrementTM_run_succ`, and `incrementTM_run_overflow`: **no matches**.
- Added-diff grep against private declaration names collected from all other TCSlib Lean files:
  **no matches**. No new private name needs the `iw_` prefix.

## Verification status and axiom walk

Static checks pass: exact ownership/freeze checks, `git diff --check`, line-length checks,
style lint, and both duplication screens. **Lean verification is incomplete.**

The original base sorry-warning set is recorded by name below, before any proof edit. Its
expected size is 35 declarations in 15 modules. Because the bootstrap crashed at module 1,
there is **no observed complete warning set and no verified warning-set difference**. The
comment-only delivery removes no admission; its expected source-level set is unchanged.

```text
TuringMachine/Simulation: 1: branchTM_spaceUsed
TuringMachine/Composition: 3: idTM_computes, ifEqTM_computes, condTM_computes_iff
TuringMachine/Build/Wrappers: 2: timedCondTM_computes, timedCondTM_spaceUsed
TuringMachine/Build/Loop: 5: loopHostTM_contracts, loopHostTM_decides, loopHostTM_finds, loopHostTM_spaceUsed_le_budget, emitLoopTM_computes
TuringMachine/Encoding: 1: pairDiagTM_computes
ClassP/TimeConstructible: 2: _root_.Turing.FinTM.lengthBitsTM_computes, _root_.Turing.FinTM.lengthBitsTM_spaceUsed
TuringMachine/Build/NDHost: 1: ndWriterTM_run_block
TuringMachine/Build/Primitives: 3: polyUnaryTM_spaceUsed, unaryTokenTM_computes, appendBitTM_computes
TuringMachine/Build/ZoneRebalance: 2: exists_zoneRebalanceTM, exists_zoneExtendTM
TuringMachine/Build/InputWindow: 1: exists_inputWindowCopyTM
TuringMachine/Build/RecordTable: 4: exists_tableFindTM, exists_tableAppendTM, exists_recordValidTM, exists_recordNextTM
TuringMachine/CodeSimulator: 2: exists_canonGrammarStage [private], exists_uniformSimulator
TuringMachine/NDCodeSimulator: 2: exists_replayCanonizer, exists_ndInterpreterCore
TuringMachine/Build/InputDevice: 3: exists_rulerTestTM, exists_rulerDeviceTM, exists_rulerHostTM
TuringMachine/UniversalK: 3: exists_selfStartupTMK, exists_selfUniversalK, universalK
TOTAL 35
```

Final sweep tail:

```text
FINAL LEAN SWEEP: NOT RUN — ENVIRONMENT BLOCKED.
Bootstrap: FAIL(TCSlib/Complexity/TuringMachine/Build/Zone): lean exited with status 135
Bootstrap: FAIL(TCSlib/Complexity/TuringMachine/Build/Zone): no fresh .olean produced
Import probe: NOT RUN — same environment blocker.
```

Target axiom walk, **source-level only**:
`Turing.exists_inputWindowCopyTM -> unchanged by sorry -> sorryAx`.
No kernel axiom print was obtained. There are no new private declarations to print. The
allowed-axioms gate is not passed; `logs/axioms.log` records the exact outstanding print.

Lint result:

```text
style_lint: 0 FAIL, 30 WARN over 37 files
```

## Duplication

Both screens ran sequentially under `nice -n 10`, using the pinned v3 script and all five
population files. Each output is byte-identical to the recorded base: **125 declarations,
43 pairs, 11,684 reproduced characters**. No new cross-file or in-file pair exists.
**new copies: none**.

Before, quoted in full:

```text
declarations screened: 125; copy pairs (target reproduces >= half of source): 43; reproduced text: 11,684 chars
   Embed.lean::embedSilentRetTM  reproduces  Embed.lean::embedEmitRetTM: 215/219 = 98%
   Embed.lean::embedEmitRetTM  reproduces  Embed.lean::embedSilentRetTM: 215/224 = 96%
   CounterLoop.lean::counterLoopTMVia  reproduces  CounterLoop.lean::counterLoopTM: 261/287 = 91%
   Embed.lean::embedSilentCfg  reproduces  Embed.lean::embedEmitCfg: 165/192 = 86%
   CounterLoop.lean::counterLoopTM  reproduces  CounterLoop.lean::counterLoopTMVia: 261/311 = 84%
   CounterLoop.lean::counterLoopTM_run_escape  reproduces  CounterLoop.lean::counterLoopTM_run_done: 393/471 = 83%
   CounterLoop.lean::counterLoopTMVia_done_segment  reproduces  CounterLoop.lean::counterLoopTMVia_escape_segment: 332/414 = 80%
   Embed.lean::embedSilent_step  reproduces  Embed.lean::embedEmit_step: 315/393 = 80%
   Embed.lean::embedSilentRet_step  reproduces  Embed.lean::embedSilentRetTM_visitedByTapeHead: 106/134 = 79%
   CounterLoop.lean::counterLoopTMVia_escape_witness  reproduces  CounterLoop.lean::counterLoopTMVia_done_witness: 738/969 = 76%
   CounterLoop.lean::decrementTM_run_succ_ofCfg  reproduces  CounterLoop.lean::counter_complement_twice: 67/88 = 76%
   Embed.lean::embedEmitRet_step  reproduces  Embed.lean::embedEmitRetTM_visitedByTapeHead: 87/115 = 76%
   CounterLoop.lean::RoundContract.counterLoopEscape  reproduces  CounterLoop.lean::RoundContract.counterLoopDone: 1154/1540 = 75%
   Embed.lean::embedEmit_step  reproduces  Embed.lean::embedSilent_step: 315/429 = 73%
   CounterLoop.lean::counterLoopTMVia_done_witness  reproduces  CounterLoop.lean::counterLoopTMVia_escape_witness: 738/1008 = 73%
   Embed.lean::embedSilentTM_visitedByTapeHead_frame  reproduces  Embed.lean::embedEmitTM_visitedByTapeHead_frame: 204/279 = 73%
   Embed.lean::embedSilentTM_visitedByTapeHead_frame  reproduces  Embed.lean::embedSilentTM_frame: 82/113 = 73%
   CounterLoop.lean::counterLoopTM_run_done  reproduces  CounterLoop.lean::counterLoopTM_run_escape: 393/549 = 72%
   Embed.lean::embedSilentTM_visitedByTapeHead  reproduces  Embed.lean::embedEmitTM_visitedByTapeHead: 171/242 = 71%
   CounterLoop.lean::decrementTM_run_underflow_ofCfg  reproduces  CounterLoop.lean::counter_complement_twice: 62/88 = 70%
   Embed.lean::embedSilentTM_visitedByTapeHead_frame  reproduces  Embed.lean::embedSilentTM_visitedByTapeHead: 188/268 = 70%
   CounterLoop.lean::RoundContract.counterLoopDone  reproduces  CounterLoop.lean::RoundContract.counterLoopEscape: 1180/1750 = 67%
   Embed.lean::embedEmitTM_visitedByTapeHead_frame  reproduces  Embed.lean::embedSilentTM_visitedByTapeHead_frame: 204/305 = 67%
   CounterLoop.lean::counterLoopTMVia_escape_segment  reproduces  CounterLoop.lean::counterLoopTMVia_done_segment: 332/499 = 67%
   Embed.lean::embedSilent_apply  reproduces  Embed.lean::embedEmit_apply: 168/253 = 66%
   CounterLoop.lean::RoundContract.counterLoopDone_traj  reproduces  CounterLoop.lean::RoundContract.counterLoopEscape_traj: 343/533 = 64%
   Scan.lean::writeConstTM_run_ofCfg  reproduces  Scan.lean::inputCopyTM_run_ofCfg: 265/412 = 64%
   Embed.lean::embedEmitTM_visitedByTapeHead  reproduces  Embed.lean::embedSilentTM_visitedByTapeHead: 171/268 = 64%
   Scan.lean::inputCopyTM_run_ofCfg  reproduces  Scan.lean::inputFoldTM_run_ofCfg: 202/321 = 63%
   Scan.lean::inputCopyTM_run_ofCfg  reproduces  Scan.lean::writeConstTM_run_ofCfg: 265/422 = 63%
   CounterLoop.lean::counterWord_value  reproduces  CounterLoop.lean::counter_word_decrement: 94/150 = 63%
   Embed.lean::embedSilentTM_spaceUsedByTape_cap  reproduces  Embed.lean::embedSilentTM_frame: 70/113 = 62%
   CounterLoop.lean::RoundContract.counterLoopEscape_traj  reproduces  CounterLoop.lean::RoundContract.counterLoopDone_traj: 343/555 = 62%
   Embed.lean::embedSilentTM_visitedByTapeHead  reproduces  Embed.lean::embedSilentTM_visitedByTapeHead_frame: 188/305 = 62%
   Embed.lean::embedEmitCfg  reproduces  Embed.lean::embedSilentCfg: 165/270 = 61%
   CounterLoop.lean::decrementTM_run_succ_ofCfg  reproduces  CounterLoop.lean::decrementTM_run_underflow_ofCfg: 448/750 = 60%
   Scan.lean::writeConstTM  reproduces  Scan.lean::writeAdvTM: 62/107 = 58%
   Embed.lean::embedSilentRetTM_run  reproduces  Embed.lean::embedSilentTM_runFrom: 68/118 = 58%
   Embed.lean::embedEmitTM_visitedByTapeHead_frame  reproduces  Embed.lean::embedEmitTM_visitedByTapeHead: 138/242 = 57%
   Embed.lean::embedSilentRetTM_visitedByTapeHead  reproduces  Embed.lean::embedEmitRetTM_visitedByTapeHead: 65/115 = 57%
   Embed.lean::embedSilentTM_visitedByTapeHead  reproduces  Embed.lean::embedSilentTM_frame: 63/113 = 56%
   Embed.lean::embedSilentTM_spaceUsedByTape_cap  reproduces  Embed.lean::embedSilentTM_visitedByTapeHead: 141/268 = 53%
   Scan.lean::scan_const_trace  reproduces  Scan.lean::scan_adv_run: 247/476 = 52%
```

After, quoted in full:

```text
declarations screened: 125; copy pairs (target reproduces >= half of source): 43; reproduced text: 11,684 chars
   Embed.lean::embedSilentRetTM  reproduces  Embed.lean::embedEmitRetTM: 215/219 = 98%
   Embed.lean::embedEmitRetTM  reproduces  Embed.lean::embedSilentRetTM: 215/224 = 96%
   CounterLoop.lean::counterLoopTMVia  reproduces  CounterLoop.lean::counterLoopTM: 261/287 = 91%
   Embed.lean::embedSilentCfg  reproduces  Embed.lean::embedEmitCfg: 165/192 = 86%
   CounterLoop.lean::counterLoopTM  reproduces  CounterLoop.lean::counterLoopTMVia: 261/311 = 84%
   CounterLoop.lean::counterLoopTM_run_escape  reproduces  CounterLoop.lean::counterLoopTM_run_done: 393/471 = 83%
   CounterLoop.lean::counterLoopTMVia_done_segment  reproduces  CounterLoop.lean::counterLoopTMVia_escape_segment: 332/414 = 80%
   Embed.lean::embedSilent_step  reproduces  Embed.lean::embedEmit_step: 315/393 = 80%
   Embed.lean::embedSilentRet_step  reproduces  Embed.lean::embedSilentRetTM_visitedByTapeHead: 106/134 = 79%
   CounterLoop.lean::counterLoopTMVia_escape_witness  reproduces  CounterLoop.lean::counterLoopTMVia_done_witness: 738/969 = 76%
   CounterLoop.lean::decrementTM_run_succ_ofCfg  reproduces  CounterLoop.lean::counter_complement_twice: 67/88 = 76%
   Embed.lean::embedEmitRet_step  reproduces  Embed.lean::embedEmitRetTM_visitedByTapeHead: 87/115 = 76%
   CounterLoop.lean::RoundContract.counterLoopEscape  reproduces  CounterLoop.lean::RoundContract.counterLoopDone: 1154/1540 = 75%
   Embed.lean::embedEmit_step  reproduces  Embed.lean::embedSilent_step: 315/429 = 73%
   CounterLoop.lean::counterLoopTMVia_done_witness  reproduces  CounterLoop.lean::counterLoopTMVia_escape_witness: 738/1008 = 73%
   Embed.lean::embedSilentTM_visitedByTapeHead_frame  reproduces  Embed.lean::embedEmitTM_visitedByTapeHead_frame: 204/279 = 73%
   Embed.lean::embedSilentTM_visitedByTapeHead_frame  reproduces  Embed.lean::embedSilentTM_frame: 82/113 = 73%
   CounterLoop.lean::counterLoopTM_run_done  reproduces  CounterLoop.lean::counterLoopTM_run_escape: 393/549 = 72%
   Embed.lean::embedSilentTM_visitedByTapeHead  reproduces  Embed.lean::embedEmitTM_visitedByTapeHead: 171/242 = 71%
   CounterLoop.lean::decrementTM_run_underflow_ofCfg  reproduces  CounterLoop.lean::counter_complement_twice: 62/88 = 70%
   Embed.lean::embedSilentTM_visitedByTapeHead_frame  reproduces  Embed.lean::embedSilentTM_visitedByTapeHead: 188/268 = 70%
   CounterLoop.lean::RoundContract.counterLoopDone  reproduces  CounterLoop.lean::RoundContract.counterLoopEscape: 1180/1750 = 67%
   Embed.lean::embedEmitTM_visitedByTapeHead_frame  reproduces  Embed.lean::embedSilentTM_visitedByTapeHead_frame: 204/305 = 67%
   CounterLoop.lean::counterLoopTMVia_escape_segment  reproduces  CounterLoop.lean::counterLoopTMVia_done_segment: 332/499 = 67%
   Embed.lean::embedSilent_apply  reproduces  Embed.lean::embedEmit_apply: 168/253 = 66%
   CounterLoop.lean::RoundContract.counterLoopDone_traj  reproduces  CounterLoop.lean::RoundContract.counterLoopEscape_traj: 343/533 = 64%
   Scan.lean::writeConstTM_run_ofCfg  reproduces  Scan.lean::inputCopyTM_run_ofCfg: 265/412 = 64%
   Embed.lean::embedEmitTM_visitedByTapeHead  reproduces  Embed.lean::embedSilentTM_visitedByTapeHead: 171/268 = 64%
   Scan.lean::inputCopyTM_run_ofCfg  reproduces  Scan.lean::inputFoldTM_run_ofCfg: 202/321 = 63%
   Scan.lean::inputCopyTM_run_ofCfg  reproduces  Scan.lean::writeConstTM_run_ofCfg: 265/422 = 63%
   CounterLoop.lean::counterWord_value  reproduces  CounterLoop.lean::counter_word_decrement: 94/150 = 63%
   Embed.lean::embedSilentTM_spaceUsedByTape_cap  reproduces  Embed.lean::embedSilentTM_frame: 70/113 = 62%
   CounterLoop.lean::RoundContract.counterLoopEscape_traj  reproduces  CounterLoop.lean::RoundContract.counterLoopDone_traj: 343/555 = 62%
   Embed.lean::embedSilentTM_visitedByTapeHead  reproduces  Embed.lean::embedSilentTM_visitedByTapeHead_frame: 188/305 = 62%
   Embed.lean::embedEmitCfg  reproduces  Embed.lean::embedSilentCfg: 165/270 = 61%
   CounterLoop.lean::decrementTM_run_succ_ofCfg  reproduces  CounterLoop.lean::decrementTM_run_underflow_ofCfg: 448/750 = 60%
   Scan.lean::writeConstTM  reproduces  Scan.lean::writeAdvTM: 62/107 = 58%
   Embed.lean::embedSilentRetTM_run  reproduces  Embed.lean::embedSilentTM_runFrom: 68/118 = 58%
   Embed.lean::embedEmitTM_visitedByTapeHead_frame  reproduces  Embed.lean::embedEmitTM_visitedByTapeHead: 138/242 = 57%
   Embed.lean::embedSilentRetTM_visitedByTapeHead  reproduces  Embed.lean::embedEmitRetTM_visitedByTapeHead: 65/115 = 57%
   Embed.lean::embedSilentTM_visitedByTapeHead  reproduces  Embed.lean::embedSilentTM_frame: 63/113 = 56%
   Embed.lean::embedSilentTM_spaceUsedByTape_cap  reproduces  Embed.lean::embedSilentTM_visitedByTapeHead: 141/268 = 53%
   Scan.lean::scan_const_trace  reproduces  Scan.lean::scan_adv_run: 247/476 = 52%
```

## Brief checklist

- [x] Target status and obstruction; base hash and successful ancestor check recorded.
- [x] Nothing changed outside regions (a)–(c); only region (c) changed.
- [x] New-declaration inventory (none), proposed leaf justification, and appendix recorded.
- [x] Planned constant and both ledgers recorded as unverified continuation guidance.
- [x] Promotion candidate and environment escalation E1 recorded; no mathematical/API escalation claimed.
- [x] Rule 10 citation inventory and Rule 11 added-diff greps recorded; no foreign definition unfolded.
- [ ] Rule 10 import-probe rerun — blocked by E1.
- [x] Both full duplication screens quoted; no new pairs; **new copies: none**.
- [x] File size, public/private counts, and passing static lint recorded.
- [ ] Fresh Lean final sweep and axiom prints — blocked by E1; logs explicitly record non-execution.

## Archive contents

`REPORT.md`; the complete modified source at its repository path; one format-patch;
`fill-c1-window.bundle`; bootstrap, final-sweep, and axiom logs; both screen outputs;
`SHA256SUMS`; and the addendum-required shim source under `evidence/runtime/`.
No compiled shim, olean, binary build product, unverified draft, or dependency cache is included.
`SHA256SUMS` covers every other file in the archive. Delivery is ZIP only.

## Notation

`w`: initial little-endian counter word; `d`: its numeric value; `y`: requested available input
window; `r`: number of body rounds; `C`: proposed uniform time constant; `|·|`: list length.
