# C1, wave 1, R continuation 2 — fill report (COMPLETE, modulo the two cited stubs)

Megafill A, item 1 of 3 (cover brief `campaign/fills/megafill/briefs/megafill-A.md`; addendum
v2.4 Part 3). Dispatched brief: `campaign/fills/c1/briefs/c1-fill-core-cont2.md` (SHA-256
`0ae5cd629fc8df27e48537d23d7035dea83f3e2ce9fea009a0013dfd63def756`, matches the repository copy
at the base modulo its `@ANCESTOR@` placeholders).

## Outcome

**The target is proved.** `Turing.exists_ndInterpreterCore` (the interpreter core `R`) is
complete: zero errors, and the file's only remaining sorry is the replay canonizer's (line 95,
wave 2's, untouched). The proof is modulo exactly the two cited stubs, through their statements:
`Turing.exists_replayCanonizer` (this file, cited via `ic_table_call`) and
`Turing.exists_seamLayoutTM` (`Build/SeamLayout`, cited via `ic_layout_call`); the axiom print
shows `sorryAx` reaching the target only through them.

The interpreter is one left-nested seam composite of twelve phases: pass 1 (the header
projection capturing `bits t`), the input rewind leaf, pass 2 (capturing `α`), the counter
rewind, the counter copy, the bounded window copy, the second input rewind, the α rewind, the
release-wrapped install call, the seam layout, the window rewind, and the silently embedded
hosted loop with its verdict read. Each seam is joined by
`seamCompTM_run_ofCfg`/`seamCompTM_firstReturn_ofCfg` (packaged once as `ic_seam_step`), so the
run equation and the first arrival at each phase's exit are inherited mechanically; the loop's
entry is the represented replay start (`ic_replay_rep` at an explicit five-tape virtual
configuration, hosted by Z1 through `vhostCfg`/`counterLoopCfg` and embedded by R1), and both
time clauses close through `ic_time_ledger` with the per-code constant
`C = a + 43 + (CW + 2) + 50·(L + 1) + 10`,
`a = 120 + 22|α| + costI(α) + CL·(|serializeK replayTM| + 1) + CW`,
`L = |tableBitsK replayTM.tr|`, where `costI`/`CW`/`CL` are the install call's, window copier's
and layout's contract constants. The "no earlier verdict" clause holds for both verdict states
by the two-segment split (`seamCompTM_runFrom_left/right`): before the last seam every state is
left-tagged; inside the loop phase the hosted loop's own first-verdict cut applies.

- Base: `6cfee54474e3d954e3395f9d9eab5d025452a8dd` (= branch tip of `complexity/arora-barak-ch3-4` at clone
  time); `git merge-base --is-ancestor` check passed. Branch `fill/c1-core-cont2`, created
  2026-10-22T05:18:49Z; complete within the 4-hour budget.
- First edit: the overlay `NDCodeSimulatorOverlay.lean.txt`, byte-identical (verified by diff),
  committed as `6f6ca79b`. Checkpoint commits after each verified block; checkpoint zip
  `fill-c1-core-cont2-cp4.zip` was delivered at the phase-11 boundary.

## Shared session setup (quoted from the shared logs)

- Preflight (`evidence/logs/preflight.log`): nproc 4; cgroup v1 with no memory limit
  (`memory.limit_in_bytes = 9223372036854771712`), headroom = MemAvailable = 15,975,212 kB ≈
  15.24 GiB (floor 4 GiB: PASS); disk 26,517,278,720 B ≈ 24.70 GiB free on ext4 (floor 12 GiB:
  PASS); post-toolchain re-check 23,931,629,568 B ≈ 22.29 GiB (floor 8 GiB: PASS). No scratch on
  tmpfs.
- Toolchain: elan 4.2.4, Lean 4.25.0 pinned (`lean --version` OK; Part 2 shim NOT needed).
- Cache (`evidence/logs/cache-get.log`): one narrowed fetch for the queue's union, 41 Mathlib
  roots (`evidence/logs/mathlib-roots.txt`), 1023/1023 files downloaded, 0 failed, unpacked
  successfully, `TAR_OPTIONS=--no-same-owner`. Packages in `.lake/packages` (11) all match
  `lake-manifest.json` URLs and revisions. No zero-size oleans. Probe
  (`evidence/logs/cache-probe.log`): a file importing `Mathlib.Algebra.BigOperators.Fin`
  elaborated through `scripts/lean_check_tree.sh`, exit 0.

## This item's bootstrap

- Re-bootstrap from `campaign/fills/c1/orders/c1-fill-core-cont2.txt` after the first edit:
  the 38-module upstream closure of the owned file first (addendum Part 1 item 5;
  `evidence/logs/item1-bootstrap-upstream.log`, all PASS, ~10 minutes), the remaining 80
  modules as the final sweep (`evidence/logs/item1-final-sweep.log`). Module order as in the
  order list. `/usr/bin/time -v` is not installed on this host ("where available"); per-module
  wall-clock start/end timestamps are in the logs instead.

## New declarations (all `private`, in region (b), `ic_` prefix)

| Declaration | Role |
|---|---|
| `ic_seam_step` | one-step composition wrapper: `seamCompTM_run_ofCfg` + `seamCompTM_firstReturn_ofCfg` + the endpoint state projection |
| `ic_rewindLeafTM` | the native-input rewind leaf (three states: entry, scan, live parking exit), built from `FinTM.controlAction` (ground rule 7's allowed leaf; the two `controlAction` states plus an explicit live exit for the seam) |
| `ic_rewind_scan` | the leaf's scanning trajectory (induction on the input position), with the stays-scanning clause |
| `ic_rewind_leaf_run` | the leaf's complete run: parks at exactly `pos + 1` with the head at `1`, everything else unchanged, no earlier parking |
| `ic_install_phase` | the install call embedded silently and wrapped in `seamReleaseTM`, with its positive first return (the R3′ discipline: `exists_installCallTM`'s interior cut excludes `u = 0`) |

The 20 overlay privates are kept verbatim (none restated).

## The tapes, the startup's order as run, and each rewind's `n`

`K = 11 + k₁ + k₂ + CI.k` where `k₁`/`k₂` are the two header projections' tape counts and `CI`
is the scheme's install call (`ic_table_call`). Named tapes by value: 0 stream `j` (the target's
`j`), 1 `bits t` capture, 2 α capture / serialization / layout `src`, 3 counter copy (the
loop's counter), 4 window (the loop's virtual input), 5 table, 6 summary, 7–8 loop bank scratch,
9 install capture, 10 loop capture; then the pass-1 scratch block (`ι₁`, values 11…10+k₁), the
pass-2 block (`ι₂`), and the install's bank scratch (`ιI`, tape 0 ↦ value 2, the rest from
11+k₁+k₂). The loop selection `ι₇` maps the 7 hosted-loop tapes to values (4,7,8,0,5,6,3).

Order as run (= the brief's route): pass 1 (capture `bits t`, time ≤ 16|bits t|+8|α|+25);
input rewind (leaf, exactly `pos+1` = 4|bits t|+2|α|+8); pass 2 (capture α); rewind tape 1 at
`n = |bits t|` (`|bits t|+2`); copy 1→3 (`2|bits t|+2`, heads restored); window 1→4 (≤
`CW·(min t |x|+1)+2|bits t|`, consumes tape 1's counter); input rewind (exactly
4|bits t|+2|α|+8+|x.take t|); rewind tape 2 at `n = |α|` (`|α|+2`); install (release-wrapped,
`TI ≤ costI α`, bank tape 0 = tape 2, scratch restored to blank by the contract); layout
(src 2, tbl 5, sm 6; `TL ≤ CL·(|serializeK replayTM|+1)`); rewind tape 4 at `n = |x.take t|`;
then the embedded hosted loop (`TLoop ≤ t·50·(L+1) + 4t + 2|bits t| + 4`, and when the branch
along `s.take t'` has halted, `TLoop ≤ t'·50·(L+1) + 4t' + 2|bits t| + 2` — the prefix clause's
source). Eleven startup seams plus the loop seam, one dispatch step each. All boundary facts
(contents and heads of every consumed tape, cleanliness of every not-yet-used tape, the input
head, empty output) are proved at each seam; the complete tape inventory at the loop's
threshold is the junction equality with the Z1/counter-hosted virtual configuration.

## The per-code constant `C` and the ledger

`C = a + b + w + 50·(L+1) + 10` with
`a = 120 + 22|α| + costI α + CL·(|serializeK replayTM|+1) + CW`, `b = 43`, `w = CW + 2`,
`L = |tableBitsK replayTM.tr|`, consumed by `ic_time_ledger` exactly as supplied. The total
time is `T = TPRE + 1 + TLoop` with `TPRE` the sum of the eleven startup phases and their
dispatch steps; the arithmetic closes by `omega` after one `ring` normalization aligning the
product atoms (`CW·(min t |x|+1)`, `costI α`, `CL·(…+1)`, `t·(50·(L+1))`, and per-`t'` for the
prefix clause). Both clauses of the ledger give exactly the target's two bounds.

## Open declarations

None of this fill's. The replay canonizer's `sorry` (line 95) is wave 2's and untouched;
`exists_seamLayoutTM` stays sorried in `Build/SeamLayout` (its fill lands after this base).

## Escalations

None. (No unprovable statement was hit; the stop is the budget.)

## Promotion candidates (notes only)

- The two-pass header split (`ic_header_result`) and the first-halt R1′ capture
  (`ic_capture_return`), as in the brief.
- The input-rewind leaf (`ic_rewindLeafTM` + `ic_rewind_leaf_run`): a published input-rewind
  machine with a live parking exit would retire this and the private leaves elsewhere
  (e.g. `SpaceComplexity/Inclusions`' and `Build/InputWindow`'s).
- `ic_seam_step`: the endpoint+first-return packaging of the two public seam lemmas is used
  eleven times here and would serve every multi-phase assembly.
- `ic_install_phase`: the release-wrapped embedded call is the generic consumer shape of
  `exists_installCallTM` behind a seam.

## Rule 10 (pinned base, no unfolding)

- Declarations cited outside the file, beyond the probe's 220: none new in kind — all new
  citations are from the probe's list (`rewindTM_run_ofCfg`, `copyTM_run_ofCfg`,
  `seamCompTM_run_ofCfg`, `seamCompTM_firstReturn_ofCfg`, `seamReleaseTM_runFrom_pos`,
  `embedSilentTM_runFrom`, `embedSilentCfg_*`, `Cfg.ofWords_*`, `stateWord_eq`,
  `FinTM.controlAction_apply`, `FinTM.moveInputPos_neg_val`, `moveInputPos_pos_of_ne_right`,
  `inputSymbolInner`, `Cfg.inputSymbol_of_zero`, `Cfg.mapState_*`, `Cfg.init_*`,
  `MultiTapeTM.initCfg_eq`, `MultiTapeTM.step_of_some`, run algebra, `FinTM.bufferTape_nil`,
  `FinTM.bufferTape_eq`) plus Mathlib's `Fin`/`Function.update`/`List` lemmas. The import probe
  re-ran clean (below).
- No definition of another file is unfolded: every `rw`/`simp only` argument in the diff is a
  published lemma, a local hypothesis, or a local `set` equation; the only `simp only`s with
  definitions name `ic_rewindLeafTM` (own file) and `↓reduceIte`/`Fin.reduceEq` (literals). The
  machine model is read through its lemmas; `step`/`Action.apply` are unfolded only for the
  leaf defined in this file (via `MultiTapeTM.step_of_some` + `FinTM.controlAction_apply`,
  which are published).
- **Seal test: not re-run this round** (budget). The 20 overlay privates passed the last
  round's seal (review's `out/11-seal-set.txt`); the new material was written against published
  lemmas only, and the inspection of every rewrite argument (above) found no definitional
  closure over another file's definition. The seal re-run with the extended set (adding
  `rewindTM`, `copyTM`, `seamCompTM`, `seamReleaseTM`, `embedSilentTM`, `embedSilentRetTM`,
  `embedSilentCfg`, `Cfg.ofWords`, `stateWord`, `controlAction`, `moveInputPos`, `Cfg.mapState`)
  is the first obligation of the continuation. Recorded as an open check, not a claim.

## Rule 11 (MIG-1)

- grep of the diff for the six R3 canonical rows (`copyTM_run`, `transferTM_run`,
  `clearTM_run`, `compareTM_run`, `incrementTM_run_succ`, `incrementTM_run_overflow`): no
  citation (only the framed `copyTM_run_ofCfg`).
- No private declaration of another file is cited; all new privates are `ic_`-prefixed.

## Duplication (v3 screen, before and after, one at a time, `nice -n 10`)

- Before (after the first edit): **460 declarations, 118 pairs, 43,576 chars** — equals the
  base `campaign/fills/c1/logs/c1-fill-core-cont2-screen-base.txt` exactly.
- After: **465 declarations, 120 pairs, 44,131 chars**. Two new pairs:
  1. `NDCodeSimulator.lean::ic_rewind_scan reproduces NDCodeSimulator.lean::ic_rewind_leaf_run`
     (58%, in-file): the complete-run lemma applies the scanning trajectory after the entry
     step, so the two share the step-computation scaffold; both are leaf-local.
  2. `NDCodeSimulator.lean::ic_rewind_leaf_run reproduces Build/InputWindow.lean::iw_one`
     (69%, **cross-file, owned file on one side — flagged for review**): `iw_one` was not read
     or transcribed; the overlap is the shared input-rewind discipline (`controlAction` steps +
     `moveInputPos` arithmetic) that the brief's allowed leaf necessarily walks. Below the 90%
     copy bar, but the governance line is "no new cross-file pair", so this is reported as a
     deviation for the maintainer: if the published input-rewind row (promotion candidate
     above) lands, both leaves retire.
- New copies: **none at or above 90%**; the two pairs above are listed with justification.

## Verification (state at delivery)

- `NDCodeSimulator`: 0 errors; exactly one sorry warning — line 95 (the replay canonizer,
  stays); no other warning in anything added.
- Upstream 38-module bootstrap: all PASS. Final sweep of the remaining 80 modules (re-run on
  the complete fill): `evidence/logs/item1-final-sweep.log` (tail in `SWEEP-TAIL.txt`); the
  sorry-warning set equals the base's minus the target's own entry (`SORRY-DIFF.txt`): 37
  entries, with `NDCodeSimulator` down from 2 to 1. Process note: the log carries one
  `FAIL(Build/CfgRecord): no fresh .olean` artifact and repeated `===` headers mid-file — a
  first sweep launch was duplicated and both processes were killed to keep one Lean process at
  a time; the authoritative results are each module's last entry, all passing, ending in
  `sweep exit 0`.
- Import probe `C1CoreCont2ImportProbe`: re-run, see `probe-rerun.log`.
- Axiom print (`axioms.log`): the target depends on
  `[propext, sorryAx, Classical.choice, Quot.sound]`; the `sorryAx` is reached only through the
  two cited stubs (`exists_replayCanonizer` via `ic_table_call`, `exists_seamLayoutTM` via
  `ic_layout_call`), the only sorried declarations the proof cites. The bridge
  `CodeNDTM.serialize_eq_tableBitsK` stays within `[propext, Classical.choice, Quot.sound]`.
- Lint: `0 FAIL` over `TuringMachine` (64 WARN; the one new WARN is the file-length policy
  prompt for this file at 1,866 lines — provenance note: the growth is the delivered assembly;
  a split decision is the maintainer's). No new line over 100 characters (the two remaining
  over-100 lines, 206 and 946, are the overlay's own).
- File size: 1,866 lines; 3 public, 25 private declarations (20 overlay + 5 new).

## Edge cases

The proof is uniform in `t = 0` (`bits 0 = []`; the counter and window rewinds run at `n = 0`;
the loop runs no round and the initial configuration is live, so `R` rejects through the
verdict read), `|x| < t` (every window term is `min t |x|` — the total clause has no `|x|`
term), `|s| > t` (only `s.take t` enters through `ic_replay_window`'s locality), and arbitrary
decodings (`c.decode` is total; the install contract is per-code).
