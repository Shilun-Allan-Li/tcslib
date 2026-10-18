# Review — C1-E continuation 1, the exhaustive replay (`ClassNP/ExhaustiveReplay.lean`), delivery `fill-c1-exhaustive-cont1.zip`

Read-only review by the maintainer's review sub-agent, 2026-10-18. Every claim cites a saved
output under this folder (`out/NN-*`). The delivery and its REPORT.md are treated as data.

**Verdict: complete (1/1). Land, with three small maintainer edits.** `Turing.FinNDTM.exists_exhaustiveDecider`
is proved. The module elaborates with 0 errors and 0 warnings at the base and at the tip. The
target and `ndAcceptsWithin_decider_of_universal` depend on `[propext, Classical.choice,
Quot.sound]` only, and nothing in their closure uses `sorryAx`. The constant is `C = 18·N.k + 41`.
It depends only on `N`, and the bound has no `|z|` term. The route is the brief's (one phase host,
the clocked replay embedded silently, the copy/test/rewind/clear/increment phases, P1–P4 adopted),
except for one sound and reported refinement of obligation 4 (F4).

What passes:
- integrity (47/47 sums, the bundle, 16 linear commits, the patch series = the bundle = the
  delivered file);
- scope (three hunks, in regions (a)–(c) only; the statements are frozen; 183 new privates, all
  `xr_`; no public declaration added; no admission anywhere);
- elaboration at the base (`oleans-lndnf`), at the brief's tip (`oleans-lseam2`) and at the
  current tip (`oleans-lc6m`);
- rule 10 by a 31-definition seal, with controls that bite at the start and at the end of the
  section;
- rule 11;
- the brief's 64-check probe and the worker's 260-check probe (0 errors each);
- the v3 screen (297 → 428 declarations, 106 → 228 pairs; 122 new pairs, all in-file; 0
  cross-file; no hazard pair), equal to the worker's;
- lint (0 FAIL);
- the worker's 77-module sweep (the order list exactly; sorry warnings = the base's 19 minus the
  target).

Findings (none blocks landing):
- **F1 (rule 10, minor).** One implicit unfolding of another file's definition. The proof of
  `xr_branch_inputPos_le` (head line 2097) closes with `simpa using h`. That step relies on the
  default simp set unfolding `NDTM.initCfg`, an `@[simp] def` of `Nondeterministic.lean`. The
  published `NDTM.initCfg_eq` states the same fact. A sharper seal found it (the 31 definitions
  irreducible, and simp's unfolding of the four `@[simp]` definitions erased): it is the only
  failure (out/22). The fix is verified at the base and at the tip, sealed and unsealed:
  `simpa [NDTM.initCfg_eq] using h`.
- **F2 (public-facing text, minor).** The new section header reads "`C1-E fill infrastructure`"
  (head line 46). A rewording is verified ("The construction of the exhaustive replay").
- **F3 (policy §3, minor/moderate).** 24 private theorems have proofs over the ~20-line threshold
  and no "Proof sketch" paragraph. The largest are `xr_testTM_run` (161 lines), `xr_passTM_run`
  (82), `xr_depth_host` (80), `xr_cycle_host` (76) and `xr_clearTape_host` (68) (out/49). Their
  docstrings state the contracts; the route is explained only in REPORT. This is a decision for
  the user (item (g)).
- **F4 (route, decision).** Obligation 4 asked the proof to "return every head to 0". Instead,
  the proof keeps the heads where the clear leaves them, through translation invariance
  (`xr_runWith_shift`). This is sound: `NDTM.replayTM_runFrom` holds from any configuration, so the
  brief's reason for the obligation does not hold. The clear covers radius `2L` around each
  displaced head, which contains the branch's radius-`L` window. REPORT §4.3 reports this. I
  recommend accepting it.
- **F5 (records, minor).**
  - The worker's citation inventory omits `FinTM.ComputesInTime.mono` and `FinTM.bufferTape_left`.
    My 268-check probe resolves both (out/25, out/26).
  - "New copies: none" holds for cross-file pairs. But 26 of the new in-file pairs are at 90% or
    more, the brief's copy threshold. They are listed and justified by family, not called copies.
  - Commit 16 moved the helper `xr_runFrom_one` under the screen's character floor. This removed
    8 cross-file pairs with one-liners in `Nondeterminism` that share the generic two-lemma rewrite
    "one step of a run" (out/51). REPORT §8 discloses this. It is not a copy.
  - The base/ancestor log was written after the edits (08:11Z). This has no consequence, since the
    bundle's only prerequisite is the base and the chain is linear.

## Inputs

| Input | Identity | Evidence |
|---|---|---|
| Zip `exchange/inbox/fill-c1-exhaustive-cont1.zip` | SHA-256 `4984f994…3a9c`, 48 files, no C file | out/01 |
| Extraction `$S/incoming/c1-exhaustive-cont1-r2/` | every member byte-equal to the zip; no unsafe entry; CRC OK | out/02 |
| `SHA256SUMS` | 47/47 OK; covers every member except itself | out/03 |
| Brief, dispatch copy `exchange/archive/fills/c1-fill-exhaustive-cont1.md` | `f03994c5…`, as REPORT says. Equal to the base's `briefs/c1-fill-exhaustive-cont1.md` with `@ANCESTOR@` substituted, plus the "paths are those of your base" paragraph. The records copy `campaign/fills/c1/briefs/…` (`25766576…`) = the base copy + that paragraph | out/07 |
| Addendum v2 `exchange/outbox/fills/fill-environment-addendum.md` | `2a80b0ef…`, as REPORT says; equal to the base's `briefs/fill-environment-addendum.md` | out/07 |
| Brief inputs (overlay, 64-check probe, 7-file population, 77-module order list, 19-entry base sorries, screen base, pre-ship log, round 1's probes and review) | base copies byte-equal to the records copies under `campaign/fills/c1/{inputs,orders,logs,reviews}/` | out/07 |
| Base `9e77d2b26a62c3ee0c418a1e0a031c867c0ac80a` | TCSlib tree `d066c4b6` = `6d18902f`'s (#120's head) | out/05 |
| Snapshots | `oleans-lndnf` (base); `oleans-lseam2` (the brief's tip); `oleans-lc6m` (the current tip, after #129–#131; gate 49's merged-state replay) | — |
| Campaign tip | **It moved during this review.** First `6ddbfce7` (TCSlib = `dac6b3b0`'s), then `e17f150c` (#129, #130 merged at 13:15Z), then `0bf4f085` (#131 merged). `0bf4f085`'s TCSlib tree `3b0302d0` is `4c19bad4`'s, the state `oleans-lc6m` replays | out/44 |

Review worktrees, all detached under this folder, each with the `.lake/packages` link:
- `wt-base` (base) and `wt-head` (`041c82ab`);
- `wt-tipd` (`6ddbfce7` + patch), `wt-tip2` (`e17f150c` + patch) and `wt-tip3` (`0bf4f085` +
  patch), each uncommitted;
- `wt-fix` (head + `suggested-fix.diff`, uncommitted) and `wt-c15` (commit 15, `81be5ca9`).

The bundle head was fetched into `refs/review/c1-exhaustive-cont1`. Lean ran only through
`tools/leanelab.sh`, one elaboration at a time. Screens ran one at a time under `nice -n 10`,
only when no other screen ran. No build command was run. Probes are in `probe/`, scripts in
`scripts/`.

## (a) Integrity and scope

| # | Check | Result | Evidence |
|---|---|---|---|
| 1 | Bundle | `verify` okay. One ref, `refs/heads/fill/c1-exhaustive-cont1` = `041c82ab05d5595e890e1d94cf375e435b2e50e4`; its sole prerequisite is the base | out/04 |
| 2 | Commits | 16, linear, no merges; the first parent is the base; author `fill-agent`; every commit touches only the owned file; +3136/−1 in all | out/05 |
| 3 | First commit `1eabca5e` | exactly the three authorized imports after line 7, nothing else | out/06 |
| 4 | Patch series | the 16 patches applied at the base give the head tree `b16d1828`. Each patch's hunks equal `git format-patch` of its commit | out/06 |
| 5 | Delivered file | byte-equal to the head blob `e7f3ae22` (SHA-256 `c4c3094c…`, as in `SHA256SUMS`); `git diff --check` clean | out/06 |
| 6 | Regions | three hunks: (a) +3 imports after base line 7; (b) 3071 lines inserted after the blank base line 42 (after `namespace Turing`); (c) base line 65 `  sorry` → 62 lines. Region (d) is unused (complete delivery). Removing the hunks gives the base byte for byte | out/09 |
| 7 | Freeze (`declfreeze.py`) | public 2 → 2, none added or removed. The target changes only in its body ("authorized body change"); `ndAcceptsWithin_decider_of_universal` is unchanged. Private 0 → 183, all `xr_` (0 non-`xr_`) | out/10, out/14b |
| 8 | Names vs REPORT | the head's 185 declarations are exactly the worker's 185 axiom prints | out/14b |
| 9 | Hygiene (3136 added lines, code only) | no `sorry`, `admit`, `axiom`, `delta`, `set_option`, `section`, `variable`, `native_decide`, `extern`/`implemented_by`, `unsafe`/`partial`, macro/elab or `#eval`. `unfold` appears 4 times, each on an own definition (`xr_dir`, `xr_afterPass`, `xr_passStart`). `open` appears 3 times, each `… in` (`MultiTapeTM` once, `Classical` twice). There is one `decide` tactic, on `¬ 5 + 1 < 6`. Also one global `attribute [instance] xr_Clock.fintypeQ xr_Clock.decEqQ`: its instances' types mention the private `xr_Clock`, so it cannot fire outside the file (`local` would suffice) | out/11 |
| 10 | Widths | no line of the file is over 100 characters (max 100) | out/11, out/47 |
| 11 | Imports | exactly the three authorized ones | out/06, out/09 |
| 12 | Size | 110 → 3,245 lines; 2 public / 183 private (lint INFO line) | out/34 |

## (b) Elaboration and axioms

| # | Check | Result | Evidence |
|---|---|---|---|
| 13 | Base file, `oleans-lndnf` | exit 0; `61:8` `declaration uses 'sorry'` only | out/12 |
| 14 | Head file, `oleans-lndnf` | exit 0, **no diagnostics** | out/13 |
| 15 | Axioms: a copy of the module with `#print axioms` for all 185 declarations, an admission walk and a dependency walk | target and `ndAcceptsWithin_decider_of_universal`: `[propext, Classical.choice, Quot.sound]`. Direct `sorryAx` users in either closure: `[]`. All 185 are within the standard three. Histogram 100 / 45 (`propext, Quot.sound`) / 16 (`propext`) / 24 (none). Equal print for print to the worker's `axioms-raw.log` | out/15, out/16 |
| 16 | Other files' privates reached | none (dependency walk over all 185) | out/16 |
| 17 | TCSlib constants reached | 161: 81 theorems, 61 definitions (of them 22 projections, 4 instances, 1 matcher, 3 auxiliaries), 10 constructors, 9 inductives. One auxiliary proof `instInhabitedCfg.default._proof_1 : NeZero (x.length + 2)` comes from Lean's proof sharing for the literal `1 : Fin (z.length + 2)`, harmless | out/15, out/17 |

## (c) Correctness, route and rule 10

**The construction.**
- `E` is `seamCompTM₂` of one phase host, `xr_host C := phaseHostTM (xr_M C) … (xr_red C)`, onto
  two one-step answer rows, started at the host's first cycle.
- The host works over `xr_Ph × Bool × Bool`: the phases with the "accepted" and "live" flags.
- Each cycle runs these phases in order:
  - copy (`copyTM_run_ofCfg`, depth word → clock counter);
  - replay (`embedSilentTM` of the clocked `N.tm.replayTM`, with the clock from
    `exists_stepClockTMVia` at `Γ = Bool`, `refl`, no stop state);
  - test (output `= [true]`, which also clears the capture tape);
  - choice rewind, then input rewind (`FinTM.timed_rewind`);
  - six ruler-driven passes per work tape (the window clear);
  - `incrementTM_run_succ/overflow_ofCfg`.
- At a depth's end the host either deepens (extend the choice and depth words, increment the
  depth word) or rests at the halt anchor.
- `xr_run_host` inducts up to the first all-halting depth `L*` (`Nat.find`, P3′). At `L*` the
  live flag is down and the accept flag is `decide (N.AcceptsWithin z L*)`, which agrees with `T`
  (P3).

I read the whole file. The theorem's correctness rests on the kernel-checked proof (rows 14–15).

| Item | Status | Notes |
|---|---|---|
| The host-first rule | **followed** | One host (`phaseHostTM`) and the library's two-exit seam `seamCompTM₂` (public, `Build/Seam`). No second host, seam, embedding, counter loop or clock. `choiceCore` is not re-walked (no screen pair, row 32) |
| One replay | **as briefed** | The finish/timeout exits are read from the clock's two specifications; the replay lemma identifies the replayed run with `N`'s branch (`xr_replay_state`, `xr_replay_finish/timeout`). `N.tm.tr`, `replayTM` and `stepWith` are never unfolded (seal, row 19) |
| Obligation 1 (restore the counter) | **met** | The copy phase rewrites the value-`L` word before every replay; the barred `copyTM_run` is not cited (row 24) |
| Obligation 2 (rewind the choice head) | **met** | `xr_rewindTM_run`, from any `p ≤ |s|` |
| Obligation 3 (read and clear the capture tape) | **met** | `xr_testTM_run`: `done (decide (out = [true]))`, the tape cleared. A branch that halts with `[false]` or `[]` does not accept |
| Obligation 4 (clear `[-L, L]` and return the heads to 0) | **refined (F4)** | The heads are not returned. The next replay starts from blank tapes at the displaced heads `h`, which is `xr_shift h (N.tm.initCfg z)`. `NDTM.replayTM_runFrom` applies there, and `xr_runWith_shift` (from `stepWith_of_some/halt` and `Action.apply_*`) identifies the branch with the translated branch from `initCfg`. The branch's content lies within `L` of `h`, and its head within `L` of `h`. So six passes (two left, four right, ruler = the depth word of width `L`) blank `[head − 2L, head + 2L]`, which contains that window (`xr_branch_win`, `xr_clearTape_host`). This removes a per-head return row |
| The input rewind | **as briefed** | `FinTM.timed_rewind` on the leaf `xr_inRewindTM` |
| P1–P4 | **adopted** | P1, P2 (`xr_window_stepWith/runWith`), P3 and P3′ are verbatim after the `xrProbe_` → `xr_` rename. P4 (`xr_ledger`) gains `+ 2` of slack (the dispatch and the answer step) | 
| The answer | **as briefed** | The deepening stops at the first depth with no live branch. The machine does not know `T`; the proof uses `L* ≤ T` only for the bound |
| Edge cases | **covered** | `T = 0` is vacuous (P1). `N.k = 0` goes straight to the increment (`xr_firstPass`). `z = []` needs nothing special. `[false]`/`[]` outputs do not accept (above) |
| Time bound | **right; no `|z|` term** | A cycle costs at most `(18·N.k + 19)(L + 1)`. The input rewind costs `inputPos + 3 ≤ L + 4` (`xr_branch_inputPos_le`, through `timed_input_bound`). A depth costs `2^L` cycles plus at most `6L + 11 ≤ 2^L·19(L + 1)`. The ledger gives `(18·N.k + 41)·2^((18·N.k + 41)(T + 1))` |
| Constant | **per machine** | `refine ⟨xr_E C, 18 * N.k + 41, fun z T hT => ?_⟩`: `E` and `C` are fixed before `z` and `T`, and depend on `N` only |

**Rule 10.**

| # | Check | Result | Evidence |
|---|---|---|---|
| 18 | Seal set | the 31 other-file, semireducible, non-projection, non-instance, non-matcher definitions the module reaches: `Action.apply`, `Cfg.Stopped`, `Cfg.init`, `Cfg.inputSymbol`, `Cfg.mapState`, `Cfg.workTapeSymbols`, `CodeNDTM.toFinNDTM`, `FinNDTM.AcceptsWithin`, `FinTM.ComputesInTime`, `FinTM.bufferTape`, `FinTM.controlAction`, `MultiTapeTM.initCfg`, `runFrom`, `step`, `NDTM.HaltsWithin`, `initCfg`, `replayTM`, `runWith`, `stepWith`, `withChoiceTape`, `clockCfg`, `copyTM`, `embedSilentCfg`, `embedSilentTM`, `incFixed`, `incrementTM`, `moveInputPos`, `pairEncode`, `phaseHostTM`, `seamCompTM₂`, `wordPatch` | out/17, out/18 |
| 19 | Seal (the whole `namespace Turing` body, the 31 `local irreducible`) | **0 errors, 0 warnings.** Controls at the top of the section (`runFrom c 0 = c`, `bufferTape [true] 0 = some true`, `runWith [] c = c` by `rfl`) fail. Controls at the end of the section (`runFrom`, `mapState`) also fail. All controls pass unsealed | out/19 |
| 20 | Simp-set unfolding | Four of the 31 definitions are in the default simp set as unfoldable: `Action.apply`, `Cfg.init`, `MultiTapeTM.initCfg` and `NDTM.initCfg`, all `@[simp] def`. A seal cannot catch these, so a second seal also erases them (`attribute [-simp]`). **1 error: `xr_branch_inputPos_le` (F1).** Its `simpa using h` needs `NDTM.initCfg z` unfolded in the goal. Simp controls (`(Cfg.init q x).output = []`, `(a.apply c).state = a.state` by `simp`) fail sealed and pass unsealed | out/21, out/22 |
| 21 | F1's fix | `simpa [NDTM.initCfg_eq] using h`: 0 errors under the full seal (31 + simp erasure), and 0 diagnostics unsealed, at the base and at the tip | out/23, out/41, out/47 |
| 22 | Rewrite/simp/unfold arguments (1,133 occurrences, 303 identifiers) | 60 TCSlib theorems, 2 constructors, 86 own declarations, the rest Mathlib/core lemmas and locals. **No other-file definition** is passed to `rw`, `simp`, `simpa`, `dsimp` or `unfold`. The 65 `show`, 3 `change` and 186 `rfl` are covered by the seal (row 19) | out/20 |
| 23 | REPORT's claim "`step` and `Action.apply` are unfolded only for this file's own leaves" | stronger: they are not unfolded at all; the leaves go through `step_of_some` and `Action.apply_*` (sealed, row 19) | out/19 |

**Rule 11.**

| # | Check | Result | Evidence |
|---|---|---|---|
| 24 | R3 rows | 0 tokens in the added lines. Among the reached constants, only the framed rows: `copyTM_run_ofCfg`, `incrementTM_run_succ_ofCfg`, `incrementTM_run_overflow_ofCfg` (and `seamCompTM₂_run_ofCfg`) | out/27 |
| 25 | Other files' privates | Token hits are generic: `S`, `T`, `empty`, `one`, `refl`, `test`, `trans`, and the public `Cfg.mapState_state`. The dependency walk reaches **no** private of another file (row 16). All new privates carry the `xr_` prefix | out/27, out/14b |

## (d) Escalations and promotion candidates

**Escalations: none, and I agree.** Every fact the proof needs about another file's definition has a
published lemma. F1 is a missed explicit citation (`NDTM.initCfg_eq` exists), not a gap.

**Import probes (check 5).**

| # | Probe | Result | Evidence |
|---|---|---|---|
| 26 | The brief's `C1ExhaustiveImportProbe` (64 checks), base and tip | 0 errors, 0 warnings | out/24, out/41 |
| 27 | The worker's extended probe (260 checks: the brief's 64 first, verbatim) | 0 errors | out/24 |
| 28 | Citations outside the extended list | 44 reached TCSlib constants are not in it: 22 projections, 6 constructors, 4 instances, 4 auxiliaries, 1 matcher, 1 inductive, 4 definitions reached through statements (`Cfg.init`, `CodeNDTM.toFinNDTM`, `moveInputPos`, `pairEncode`), and **2 theorems the proof uses: `FinTM.ComputesInTime.mono` (dot notation in the target) and `FinTM.bufferTape_left` (through `simp`)**. All are public at the base; the review probe (268 checks) resolves them, at the base and at the tip. Brief-cited names the proof does not use: the counter loop's run lemmas and ledger, `seamCompTM_run_ofCfg`, `seamReleaseTM_firstReturn`, `embedSilentTM_frame`, `step_of_halt`, `HaltsWithin.mono`, `replayTM_q₀`, `replayTM_tr` and `MultiTapeTM.initCfg_eq` | out/25, out/26, out/41 |

**Promotion candidates** (REPORT §6, items 1–6). I agree with items 1–5:
- the ruler-driven pass and the six-pass window clear;
- `xr_firstArrival'`: the phase host's guard, obtained from any exact-time run lemma with a
  stationary exit;
- `xr_runWith_shift`: NDTM branches commute with translating the work tapes;
- `xr_window_runWith`;
- the rewind and extend leaves.

Item 6, `xr_val` and its lemmas, should be re-pointed rather than promoted under a new name.
`xr_val w := Nat.ofDigits 2 (w.map Bool.toNat)` is literally the public `Turing.counterValue`
(`Build/CounterLoop`, already upstream). At the base, `counterValue` had no equation lemma, so the
private copy was the rule-10-compliant choice. #122 added `counterValue_eq`, which is at the tip.

Further dedup notes for the maintainer's window (out/37):
- `xr_bufferTape_neg` is the tip's `FinTM.bufferTape_of_neg` (#122).
- `xr_bufferTape_ge` and `xr_bufferTape_eq_none_iff` follow from the tip's `FinTM.bufferTape_eq`.
- `xr_runFrom_one` is `Turing.runFrom_one` in `Build/EmitIterEmbed`, which is outside this import
  closure. Moving that lemma to `Deterministic` would also serve about 28 one-step rewrites
  elsewhere (out/52).

**What this unblocks.** I inlined the patched module above `Diagonalization/NTimeHierarchy` at
the current tip and elaborated against `oleans-lc6m` (out/45, out/45b):
- NTimeHierarchy elaborates with its two sorry warnings only (`exists_timed_universal_NDTM`,
  `ntime_hierarchy`).
- `Turing.exists_ndAcceptsWithin_decider` (`BF := E(UN)`) now has exactly one direct `sorryAx`
  user in its closure, `Turing.exists_timed_universal_NDTM`. So BF is proved modulo UN alone, and
  becomes sorry-free when C1-UN's remaining target lands.
- The hierarchy's top rung then needs UN and `ntime_hierarchy`'s own proof.
- C1's design §3.5 expects this theorem to retire `Nondeterminism`'s `choiceCore` later.

## (e) Duplication and lint

| # | Check | Result | Evidence |
|---|---|---|---|
| 29 | Screen v3 script | SHA-256 `f4feac91…f181`, the same at base, head and tip (`scripts/` there) | out/28 |
| 30 | Before (base, the 7-file population) | `297 declarations; 106 pairs; 36,004 chars` (16 s). Equal to the repo base log (the brief's MEASURED figures) and to the worker's `screen-before.txt` (minus its `#` line and its trailing `rc=0`) | out/29, out/32 |
| 31 | After (head) | `428; 228; 66,673 chars` (27 s); byte-equal to the worker's `screen-after.txt` | out/30, out/32 |
| 32 | New pairs (`pairdiff.py`, by name) | 122 new, 0 gone. **0 cross-file**; all 122 have both sides in `ExhaustiveReplay.lean`. The set equals the worker's `screen-diff.txt`. No pair involves `choiceCore`, `StepClock` or `ExpBFS/Radius` | out/32, out/33 |
| 33 | Pairs at ≥ 90% (the brief's copy threshold) | 26, all in-file siblings:<br>• the twenty `xr_*_ne_*` one-liners (92–97%);<br>• the leaf tables `xr_testTM`/`xr_rewindTM` (94%) and `xr_passTM`/`xr_extendTM` (92/90%);<br>• `xr_bufferTape_eq_none_iff`/`_ge` (93%);<br>• **`xr_replay_timeout`/`xr_replay_finish` (92/90%, 992 shared characters).**<br>REPORT lists and justifies all 26. The last pair is the only substantive one: its shared prelude (`hq`, `hct`, the embedded-run identity `hE`) could be one helper lemma. The `_ne_` family could be one lemma over `Fin.val`. These are dedup candidates for the maintainer's window, not cross-file copies | out/32 |
| 34 | Commit 16 (screen floor) | At commit 15, the 64-character body of `xr_runFrom_one` pairs at 95–98% with 8 `Nondeterminism` one-liners (`cont_start_core`, `cont_rewind_input`, `cont_rewind_choices`, `a3n_eq_*`, `a2_load_rewind`, `a2Borrow_rewind`) and with 4 in-file declarations. The shared text is the idiom `rw [MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_zero]`. Commit 16 shortens the names under `open MultiTapeTM in`, which takes the body under the screen's floor. Disclosed (REPORT §8). Not a copy, but the screen no longer sees it (see `Turing.runFrom_one`, (d)) | out/51 |
| 35 | Lint, `ClassNP` | base `0 FAIL, 15 WARN over 21 files`; head `0 FAIL, 16 WARN`. The new WARN is the file size (3,245 > 1000), not a driver. Equal to the worker's `lint.log` | out/34 |
| 36 | Proof sketches (policy §3) | 140 theorems: 86 with a docstring, 2 with a "Proof sketch" (the two public ones). **25 proofs exceed 20 lines; 24 of them (all private) have no sketch** (F3). 56 declarations have no docstring: one-liners, the bank lemmas and instances, which are at reviewer discretion for privates | out/49 |

## (f) Landability

- **The owned file is unchanged from the base to every tip.** Its blob is `78ec52ae` at the
  base, at `6ddbfce7`, at `e17f150c` and at `0bf4f085` (out/36, out/44). The patch applies cleanly
  at `6ddbfce7`, `e17f150c` and `0bf4f085` (`wt-tip3`); the result is the head blob `e7f3ae22`
  (out/39).
- **Upstream.** With the three imports, the module has 29 upstream modules.
  - Five changed from the base to the tip, by additions only: `Simulation` (+25), `Encoding`
    (+52), `CodeParser` (+5), `Build/CounterLoop` (+7), `CodeFormat` (+20). None adds a simp
    attribute (out/36, out/37).
  - None of the 29 changed between `6ddbfce7` and `0bf4f085` (out/44).
- **Elaboration at the tip.**
  - `wt-tipd` against `oleans-lseam2`: exit 0, no diagnostics (out/40). At the same tip, the axiom
    probe is identical (185/185, same TCSlib constants, out/42); the seal is 0 errors with the
    controls biting; the simp-erased seal gives F1 only, fixed by the one-liner; the two probes are
    0 errors (out/41).
  - `wt-tip2` and `wt-tip3` against `oleans-lc6m`: exit 0, no diagnostics (out/40).
- **Replay closure at the current tip `0bf4f085`.** Since #129 merged during this review, the
  closure is four modules (out/38):
  `ClassNP/ExhaustiveReplay`, the `ClassNP` facade, `Diagonalization/NTimeHierarchy` and the
  `Diagonalization` facade.
  - Replay them into a copy of **`oleans-lc6m`**, whose state is the current tip's TCSlib tree
    `3b0302d0`. `oleans-lseam2` predates #129–#131 and would leave NTimeHierarchy's upstream stale.
  - All the facades' and NTimeHierarchy's TCSlib imports have oleans there (out/38b).
  - Through the landing, `Build/StepClock` enters NTimeHierarchy's environment. The root already
    imports both, so no name can clash (out/38). The inlined consumer probe passes (out/45).
- **Overlap with the open PRs' closures** (out/43; #129–#131 have merged):
  - **#132** (`lean/un-u2s-api`, now `91154701`, which merged the campaign at `0bf4f085`; changes
    `Build/Primitives` and `Simulation`): its 314-module closure contains all four of this
    landing's modules. Whichever lands second replays these four into the other's result.
  - **#133** (`Build/InputDevice`) and **#134** (`SpaceComplexity/WindowClock`): no overlap.
- **Expected sorry count after landing.** The 77-module order list goes 19 → 18 (the target's
  sorry gone, every other unchanged; out/31). NTimeHierarchy stays at 2.
- **The worker's sweep (check 7).**
  - `final-sweep.log`: 77 records in the order list's exact order, every exit 0, no error lines.
    Sorry warnings: 18 in 8 modules, equal per module to the base list minus
    `ClassNP/ExhaustiveReplay` (out/31).
  - The staged bootstrap (29 upstream modules, then 47) is authorized by addendum item 5 and
    recorded. Stage 2 ran at the delivered tip.
  - The owned module: "(no diagnostics)", 22.0 s, 2,143 MiB.
  - These logs cannot be reproduced here (no build). My elaborations confirm the owned file.
- **Preflight numbers (check 9; out/50).** These are recorded for the E-RES investigation.

  | Quantity | Value |
  |---|---|
  | Host | `nproc` 4; cgroup v1 |
  | Memory limit | 14,343,688,192 B (13.36 GiB) |
  | Usage at preflight | 20,934,656 B; max_usage 50,024,448 B; failcnt 0 |
  | Host memory (`free -b`) | total 15.72 GiB, buff/cache 4.80 GiB, available 15.12 GiB |
  | Verdict headroom | 14,322,081,792 B (13.34 GiB; from a second usage sample of 21,606,400 B) |
  | Disk | 27,612,160,000 B (25.72 GiB) available, ext4 |
  | Cache step | `lake exe cache get` rc 0 (7,506 files, unpacked in 39.9 s); zero-size oleans 0 |
  | Toolchain | installed after `*.lean-lang.org` was unblocked at the proxy; no shim needed |
  | Peak Lean RSS | 2,796 MiB (`Build/Catalog`; ≈ 2.93 GB, above the addendum's quoted ~2.4 GB) |

  - This host passes v2 and v2.1 by a wide margin: its limit is about 13.4 GiB (against 8 GiB on
    the E-RES hosts), and v2 ran once, before the cache step.
  - The host-wide page cache was not charged to this cgroup, and no repeat preflight was needed.
    This is consistent with v2.1's diagnosis that page cache tripped the 8 GiB hosts.

## (g) Recommendation

**Not yet clear to merge**: the landing PR has not been opened, replayed or gated yet. It is clear
once that PR's replay passes and its gate is recorded.

**Land (full): yes**, by a maintainer PR into `complexity/arora-barak-ch3-4`.
- **Commits.** Cherry-pick the 16 commits `1eabca5e..041c82ab` from the verified bundle (or squash
  them). Their prerequisite is `9e77d2b2`. They touch only `ClassNP/ExhaustiveReplay.lean`, which
  is unchanged from the base to the tip.
- **A maintainer commit on top, `suggested-fix.diff`** (`446a9280…`; verified in `wt-fix`):
  1. F1: `simpa [NDTM.initCfg_eq] using h` in `xr_branch_inputPos_le`;
  2. F2: the section header "The construction of the exhaustive replay (the `xr_` privates)";
  3. the module status: "`Turing.FinNDTM.exists_exhaustiveDecider` — the exhaustive replay `E`
     (proved)."

  Its checks:
  - it elaborates with 0 diagnostics at the base and at the tip (out/47);
  - it passes the full seal (out/23, out/41);
  - lint: 0 FAIL, unchanged (out/47);
  - screen: 428/228/66,673 chars, 0 new pairs (out/48);
  - widths: at most 100 characters (out/47).
- **Status text in other files**, docstring-only, in the same PR (both files are in the replay
  closure):
  - `ClassNP.lean`, lines 65–68: drop "The replay is sorried."
  - `NTimeHierarchy.lean`, `exists_ndAcceptsWithin_decider`: drop "spec, fill pending — phase
    P3.3". Replace "Fill obligation, named: `E` itself (…)" with "`E` itself is
    `Turing.FinNDTM.exists_exhaustiveDecider` (…); the decider's only open dependency is the
    universal NDTM."
- **Replay:** the four modules of (f), into a copy of `oleans-lc6m`, or into #132's result if
  #132 lands first. Expected: 0 failures; sorry warnings NTimeHierarchy 2, the other three 0.
- **Review table for the PR body:**
  - integrity (47/47 sums, bundle, 16 commits, patch = bundle = file);
  - scope (three hunks in regions (a)–(c); statements frozen; 183 `xr_` privates);
  - elaboration at the base and the tip (0 diagnostics);
  - axioms (standard three, no `sorryAx`);
  - the 31-definition seal and its controls;
  - F1 fixed;
  - probes 64/64, 260/260 and 268/268;
  - screen 297 → 428 declarations, 106 → 228 pairs, 0 cross-file;
  - lint 0 FAIL;
  - sweep 77/77, 19 → 18.

**Decisions for the user:**
1. **F4: accept the obligation-4 refinement** (heads not returned; translation invariance;
   radius-`2L` clear around the displaced heads). Recommended: yes. It is sound, it is reported,
   and the brief's stated reason for the obligation does not hold.
2. **F3: proof sketches for the 24 long private proofs.** Either the maintainer adds them in the
   landing PR (docstring-only), or the landing proceeds now and the debt is recorded for the
   docstring pass. My suggestion is to land now, since it unblocks BF, and to add sketches at
   least for `xr_cycle_host`, `xr_depth_host`, `xr_run_host`, `xr_clearTape_host`,
   `xr_testTM_run` and `xr_passTM_run` in the follow-up.
3. **The frozen target docstring** (optional, the user's call on frozen text):
   - Align its sketch with the proof. "Clear the work tapes within radius `L`" is, in the proof,
     radius `2L` around the displaced heads (six ruler passes, with translation).
   - Drop the campaign label "gated with the B6 hosts" and the module's "(user decision 2 of
     2026-10-13)". Both are pre-existing, so this can wait for the deferred cleanup.
4. **Dedup** (the maintainer's window; not this landing): re-point `xr_val` to `counterValue`
   (+ `counterValue_eq`), `xr_bufferTape_neg` to `FinTM.bufferTape_of_neg`; fold the replay exits'
   prelude and the `_ne_` family; consider moving `Turing.runFrom_one` to `Deterministic` (row 34).
