# B6 F3, continuation 2: the configuration-count runner — fill report

**Brief:** `campaign/fills/b6/briefs/b6-fill-configclock-cont2.md` (attachment SHA-256
`f0294fbab53706f8328cef63e057603744365716d8316face3d0f1ce0d96c66d`, verified; the repository copy
matches the attachment except for its two `@ANCESTOR@` placeholder lines, `diff` in
`evidence/logs/brief-diff.log`).
**Addendum:** `fill-environment-addendum.md` v2.5 (attachment SHA-256
`90851511cf164dfa84ac9264cb5ba7acd54b7f551c823ae5d1000e43e233abf0`, verified; byte-equal to the
base's `campaign/standards/fill-environment-addendum.md`).
**Delivery:** `fill-b6-configclock-cont2.zip`, by zip (no PR, no push to the campaign repository);
checkpoint zips `fill-b6-configclock-cont2-cp1.zip` … `-cp5.zip`.

## 1. Outcome

- [x] **1/1: the target is proved.** `Turing.exists_configWindowRunnerTM`
  (`TCSlib/Complexity/SpaceComplexity/WindowClock.lean`, now line 1507) has no `sorry`. The
  module elaborates with **0 errors and 0 warnings**; the target's axioms are
  `[propext, Classical.choice, Quot.sound]` (no `sorryAx`). Checkpoint reached: **6 of 6**.
- [x] **Base and ancestor check** (`evidence/logs/base-and-ancestor.log`). Clone of
  `https://github.com/Shilun-Allan-Li/tcslib`, branch `complexity/arora-barak-ch3-4` (tip
  `6e761018546499de7f4ab600ca20afddb1761ba8` at clone time).
  `git merge-base --is-ancestor 968d7b2bfbcd9635d8a763673731c89f1a125eda HEAD` exited 0.
  `git checkout -b fill/b6-configclock-cont2 968d7b2b…` then `git rev-parse HEAD` printed
  **`968d7b2bfbcd9635d8a763673731c89f1a125eda`: the base.** No rebase, merge or cherry-pick onto
  anything else.
- **Constant:** `c = C₂ + |Q| + 8` passes (`C₂` F2's runner constant), clock width
  `W = c · F ≤ c · L`; the statement's constant is
  `C = (14c + 13) + 4c + 0 + 10 + C₂ · (c + 1) + c + 2` (§6).
- **Checkpoint zips.** One commit per checkpoint, each elaborating with only the target's
  `sorry` warning (checkpoints 1–5) or none (6); each has its zip (§11).

Commits on `fill/b6-configclock-cont2` (base excluded), each touching only `WindowClock.lean`:

```
475ecdd0bf118a9eed92d2051ff18b31d21f6cbf WindowClock: the writer's host and one field's round (F3 cont2, checkpoint 1)
4619561316f94dd9c62c8179ef369549a7e33957 WindowClock: one pass over the record's fields (F3 cont2, checkpoint 2)
0ea338d0671254867ef8132c4235302efbe64e1b WindowClock: the c passes with the record's rewind (F3 cont2, checkpoint 3)
a468d65d9c7c19a050472a5b2a94be5829369b70 WindowClock: the clock head's rewind (F3 cont2, checkpoint 4)
aaf09900e3016a6b88d0846be79019972ea41cb8 WindowClock: the clock writer's contract (F3 cont2, checkpoint 5)
ebca0bc53382464f7ff674909e8ac3aa5fb673e6 WindowClock: prove exists_configWindowRunnerTM (F3 cont2, checkpoint 6)
```

```
TCSlib/Complexity/SpaceComplexity/WindowClock.lean | 1304 +++++++++++++++++++-
 1 file changed, 1263 insertions(+), 41 deletions(-)
```

**History note.** The six checkpoint commits were created three times on this local branch
before delivery, always at the base and never rebased onto anything: the first set's checkpoint
commits relied, in four phase lemmas, on `exact` closing a goal by unfolding `Cfg.mapState`,
which the seal test (§8) caught; the second set had campaign labels ("checkpoint") in five
docstrings. Each time the branch was reset to the base and the corrected pieces recommitted in
the same checkpoint order. Only the final set is delivered (the bundle, the patches, the zips).

## 2. Preflight, toolchain and cache (addendum v2.5, Part 1)

`evidence/logs/preflight.log` (2026-10-23T23:29:34Z, before any cache or Lean work):

| item | value |
|---|---|
| `nproc` | 4 |
| cgroup | v1 (`memory:/process_api/…/claude-code-bash`); `memory.max`/`memory.current`/`memory.events` absent |
| `memory.limit_in_bytes` | 14,341,881,856 B |
| `memory.usage_in_bytes` / `total_cache` / `total_shmem` | 646,053,888 / 605,478,912 / 0 B |
| memory in use (`usage − total_cache + total_shmem`) | 40,574,976 B |
| **headroom** (limit − in use) | **14,301,306,880 B = 13.32 GiB ≥ 4 GiB: PASS** |
| `failcnt`, OOM | 0, none |
| `df -B1` of the clone `/home/user/tcslib` (also `/home/user`, the scratchpad, `/tmp`) | `/dev/vda`, 26,314,911,744 B available = **24.51 GiB ≥ 12 GiB: PASS** |
| `df -T` | `ext4` for all; `/dev/shm` (tmpfs) unused |

No E-RES. **Toolchain** (`evidence/logs/toolchain.log`): elan 4.2.4, `leanprover/lean4:v4.25.0`
(Lean 4.25.0, commit `cdd38ac5…`; Lake 5.0.0), installed with `TAR_OPTIONS=--no-same-owner`.
Lean started normally: **Part 2 (the `readlink` shim) was not needed and not used.**
**Re-check before the cache** (`evidence/logs/preflight-recheck.log`, the 8 GiB floor): headroom
13.23 GiB, 23,729,311,744 B = 22.10 GiB free: PASS.

**Cache store, logged first** (`evidence/logs/cache-store.log`): `/root/.cache/mathlib` did not
exist (0 files, 0 bytes). **Roots:** the order list's direct Mathlib imports,
`evidence/logs/mathlib-roots.txt`: **54 roots**, as the brief says.
**Fetch** (`evidence/logs/cache-get.log`):
`TAR_OPTIONS=--no-same-owner lake exe cache get <54 roots>` — the cache tool compiled itself and
installed `leantar 0.1.16`; "Attempting to download **1025** file(s)", "Decompressing 1025
file(s)", "Completed successfully!", exit 0, **no failed download**, no retry. `M − N = 0`: no
archive came from a pre-existing store. Never the unfiltered `lake exe cache get`.

**Checks before the bootstrap** (item 3):
- packages against the manifest (`evidence/logs/packages-manifest-check.log`): the 11 present
  packages (`PFR`, `mathlib`, `Cli`, `LeanAPAP`, `plausible`, `LeanSearchClient`,
  `importGraph`, `proofwidgets`, `aesop`, `Qq`, `batteries`) have the manifest's URL and
  revision; **ABSENT** (not cloned by the narrowed fetch): `doc-gen4`, `UnicodeBasic`,
  `BibtexQuery`, `MD4Lean`; no module of the order list imports them. Last line:
  `present packages match the manifest: PASS; absent: «doc-gen4», UnicodeBasic, BibtexQuery, MD4Lean`.
- `find .lake/packages -name '*.olean' -size 0`: nothing (`evidence/logs/zero-oleans-check.log`).
- cache probe `import Mathlib.Algebra.BigOperators.Fin` (the first root) through
  `scripts/lean_check_tree.sh`: rc 0 (`evidence/logs/cache-probe.log`).

One clone, one cache; no dependency tree copied, moved or deduplicated; nothing on a tmpfs;
**`lake build` never run** (only the cache tool's own internal validation).

**Bootstrap** (item 5; `evidence/logs/bootstrap-stage{1,2}.{txt,log}`), at the unchanged base:
stage 1 = the **60** modules of the order list that `WindowClock` imports (directly or not), in
the list's order; stage 2 = the remaining **122**, in order. **182/182 rc 0**. Each module's start,
end, wall time and child max RSS are logged (`/usr/bin/time` is absent; the wrapper
`evidence/tools/check_mod.py` reads `getrusage(RUSAGE_CHILDREN)` around
`scripts/lean_check_tree.sh`). Peak RSS 2,890 MiB (`Build/CfgRecord`); nothing stalled. Sorry
warnings at the base: **28 in 11 modules**, equal per module to
`campaign/fills/b6/logs/b6-fill-configclock-cont2-base-sorries.txt`
(`evidence/logs/base-sorry-count.txt`). One Lean process at a time throughout.

## 3. What changed, by region (ground rules 1–3, 6)

Only `TCSlib/Complexity/SpaceComplexity/WindowClock.lean` (`evidence/logs/regions.log`: every
removed line and insertion point lies in region (a), (b) or (c); 0 outside). Imports unchanged.
The target's statement is byte-identical to the base's (`evidence/logs/statement-freeze.log`);
the module header, the three proved bridges and the target's docstring before (c) are
untouched.

- **(a) the home**: 55 new `private cw_` declarations (§4) and two restated helpers:
  - `cw_copy_constant` now states its endpoint as the constant patch
    `wordPatch (d.workTapes dst) (d.workTapePos dst) (List.replicate |w| e)` on the destination
    (instead of the `if` on the interval) and also exports the framed copy's cut and head
    envelope (the second and third clauses of `copyMapTM_run_ofCfg`, verbatim);
  - `cw_clear_patch` also exports the clear's cut and head envelope (the second and third
    clauses of `clearTM_run_ofCfg`).
  The other nine `cw_` lemmas are unchanged.
- **(b) the body**: the `sorry` replaced by the proof (§6).
- **(c) the Implementation status paragraph**, rewritten for the final state:

```
**Implementation status.** Proved, by Route A with the clock over field cells. The record's
fields are separated by blank cells and a mapped copy reads one blank-delimited word, so the
all-true clock word has width `W = c · F ≤ c · L`, where `F` counts the field cells, and it is
written field by field: in each of `c = C + |Q| + 8` passes (`C` the windowed runner's
constant), each field is copied onto the clock through the constant map, the two heads skip past
it and the clock head steps back onto the clock's delimiter; after each pass the record head
skips back over the fields, and after the last the clock head returns to the clock's first cell.
The word's value suffices for every round up to `configBound + 1` (`cw_record_clock`). One phase
host (`cw_hostTM`) runs the writer, `Turing.exists_windowRunnerTM` on the word, the clear of the
clock after a `halted` or `left` exit, and the exits. The writer and the clear take `O(L)` steps
and cells and the runner at most `5 · (2^W - 1) + 2W + 3` steps (`cw_time_bound`); the head
bound adds the runner's (`cw_head_bound`), silence follows from the endpoint, and the space
bound from the head bound. The construction over the whole layout sketched above
(`W := c_M · L`) is not used.

```

## 4. New declarations (all `private`, prefix `cw_`)

**Promotion candidates** (notes only): the clock writer — `cw_writer` with its host
`cw_hostTM`/`cw_rows`/`cw_red` and the configuration family `cw_cfg` — as a public "write the
all-`e` word of width `c · F` at the clock head" row; and the generic `cw_seg_row` (a framed
one-head row as a phase-host segment), which any phase host over catalog rows could share.

| declaration | role |
|---|---|
| `cw_patch_rep` | a constant `wordPatch` read cell by cell (`if` on the interval) |
| `cw_buffer_rep` | `FinTM.bufferTape` of a constant word, cell by cell (through `bufferTape_nat`/`_of_neg`) |
| `cw_join` | the join: two adjacent constant patches are one, by `Turing.wordPatch_append` |
| `cw_Idx` | the host's phase index: per pass `p` and field `j` the four round phases (`copy`, `skipS`, `skipC (some (p, j))`, `left`) and the record's skip back (`back`); the clock's return (`skipC none`, `clockBack`); `run`, `clear b`, `stop` |
| `cw_Ctrl`, `cw_Ctrl_fintype`, `cw_Ctrl_decidableEq` | each phase's controls (its row's, the runner's `P`, `WindowExit` for the exits), finite with decidable equality |
| `cw_rows` | the phase machines: `copyMapTM` (constant map), `skipTM`, `skipBackTM`, `cw_leftTM` on tape `0` or the clock `Fin.last (K + 1)`, the runner `R`, `clearTM`, and the stationary exit leaf |
| `cw_next`, `cw_prev`, `cw_afterSkip` | the phase after a round, after a skip back, after the clock skip |
| `cw_red` | the redirect table |
| `cw_hostTM` | the machine: `phaseHostTM cw_rows _ cw_red` |
| `cw_cfg` | the writer's configurations: start `d`, record head moved by `a`, clock head by `b`, `n` cells of `e` patched at the clock's start |
| `cw_zero_ne_last` | tape `0` ≠ the clock tape |
| `cw_cfg_clockTape`, `cw_cfg_clock`, `cw_cfg_tape`, `cw_cfg_pos₀`, `cw_cfg_posL`, `cw_cfg_pos` | the fields of `cw_cfg` |
| `cw_mapState_pos`, `cw_mapState_tapes`, `cw_mapState_io` | `Cfg.mapState`'s field equations as function equalities |
| `cw_cfg_mapState`, `cw_cfg_pos_zero`, `cw_cfg_zero` | renaming a writer configuration's control; zero offsets; with nothing written it is `d` |
| `cw_cfg_move₀`, `cw_cfg_moveL` | a framed row's endpoint (one head moved, control renamed) as a writer configuration |
| `cw_box`, `cw_box_of`, `cw_box_row`, `cw_cfg_box` | the head box `|pos j − d j| ≤ r` and its derivation from a row's head ranges |
| `cw_guard` | a phase redirected only at its anchor is not redirected before it |
| `cw_seg` | **one phase as a host segment** (`phaseHostTM_run`), avoiding the exits, with its head relation |
| `cw_seg_row` | a framed row moving one head, as a host segment (`cw_seg` + `cw_guard` + `cw_box_row`) |
| `cw_seg_copy` | the constant copy of a field onto the clock (`cw_copy_constant`, joined by `cw_join`) |
| `cw_seg_skipS` | the skip past a field on the record tape (`skipTM_run_ofCfg`) |
| `cw_skip_word` | the clock word under the clock head, the premise of the clock skips |
| `cw_seg_skipC` | the skip past the written cells on the clock (after a field), or past the clock's right delimiter (after the last pass) |
| `cw_seg_left` | the one-cell move back onto the clock's delimiter (`cw_left_run`) |
| `cw_seg_time` | restating a segment's length |
| `cw_field` | field `i` of a record is a delimited word at its offset (`recordAt_iff`, `fieldsTape_field`) |
| `cw_round` | **checkpoint 1**: one field's round |
| `cw_pass` | **checkpoint 2**: one pass, by induction on the fields left |
| `cw_seg_back`, `cw_rewind`, `cw_pass_rewind`, `cw_passes` | **checkpoint 3**: the skip back over a field, the record's rewind, a pass with its rewind, all `c` passes |
| `cw_seg_clockBack` | **checkpoint 4**: the skip back over the clock word (`skipBackTM_run_ofCfg`), then the runner's entry; with `cw_seg_skipC none` the clock head's return |
| `cw_silence` | an endpoint that keeps the output kept it throughout (`MultiTapeTM.output_prefix`) |
| `cw_writer` | **checkpoint 5**: the writer's contract (below) |
| `cw_seg_run` | the windowed runner as a phase, from its entry to its exit |
| `cw_seg_clear` | the clear after a `halted`/`left` exit, from the runner's endpoint to the stopped configuration |
| `cw_finish` | the target's run-time clauses (no earlier exit, heads, silence, space) from a segment |

**The writer's contract, as restated** (`cw_writer`): for the host
`cw_hostTM e R en ex c m` (`c, m > 0`), a record `fs` with `fs.length = m` at the head of tape `0`
(`RecordAt d 0 fs`), a blank clock tape and `d` at the first copy's control, and any
`r ≥ c · (|joinFields fs| + 1) + 2`:

```
∃ t ≤ 13 · c · fieldOffset fs |fs| + c · F + 6,
  Segment host {exits} (cw_box d.workTapePos r) d (cw_cfg e d ⟨run, en⟩ 0 (c · F) 0) t ∧
  ∀ u ≤ t, (host.runFrom d u).output = d.output
```

with `F = (fs.map List.length).sum` and `fieldOffset fs |fs| = |joinFields fs| + 1 = L + 1`:
the all-`e` word of width `c · F` patched at the clock's start, both heads returned, the
runner's control, silently, every head within `r` of its start, no exit on the way. It refines
continuation 1's stub: the time bound is explicit, and the endpoint is the runner's entry
configuration itself.

## 5. The construction and its refinements of the route

- **One phase host for everything** (`phaseHostTM`, read only through `phaseHostTM_run`, via
  `cw_seg`). The brief's checkpoint 1 names the round "by `seamCompTM`"; here the round's four
  rows are four consecutive phases of the host, which the passes need anyway (the redirect
  table carries the pass and field indices). This avoids a second layer (a seam composite
  inside each phase) and its lockstep bookkeeping; no seam, host, loop or transport is written.
  Every phase is one framed catalog row (`copyMapTM_run_ofCfg`, `skipTM_run_ofCfg`,
  `skipBackTM_run_ofCfg`, `clearTM_run_ofCfg`), the landed leaf `cw_leftTM`, F2's runner, or the
  stationary exit leaf (the "one-step exit dispatch" the brief allows; `phaseHostTM_run` needs
  every finished phase redirected, so the three exits are a `stop` phase).
- **The round** (field `j` of length `l`, `n` cells written, the clock head at `n`): constant copy
  (`2l + 2` steps; the clock gains the patch of `l` copies of `e` at its head, joined to the
  earlier patch by `wordPatch_append`), skip on the record tape (`l + 1`; head to the next
  field), skip on the clock (`l + 1`; head one past the new delimiter), one-cell move (`1`; head
  on the delimiter, where the next copy continues), each followed by its dispatch: `4l + 9`.
- **The clock's blank suffix** is carried explicitly: every clock cell at or after the write
  position is blank because the clock was blank at the start and every configuration's clock is
  the patch over the start's clock (`cw_cfg`).
- **The record's rewind** after each pass: `m` skips back from `fieldOffset fs m` to `0`
  (`l + 4` each).
- **The clock's rewind**: `cw_seg_skipC none` (the skip over the empty word at the clock's right
  delimiter, the route's step 4) and `cw_seg_clockBack`. The step past the delimiter is the same
  row as the round's clock skip (`skipTM` on the clock), so it is the same phase kind
  (`skipC none`).
- **Then the runner** at its entry on the word `List.replicate W true` (its clock premise is
  `cw_skip_word`, its record premise the unchanged tape `0`); at `halted`/`left` the clear
  (`cw_clear_patch`, whose blank-exterior hypothesis comes from the writer's blank exterior and
  F2's `w'.length = w.length`, as the brief says); at `exhausted` straight to the exit.
- **Certification** comes from F2's own `N` (its last clause) and from `cw_record_clock`'s
  bound for every `N ≤ configBound + 1`; `Turing.windowRun_stop_unique` was not needed.

## 6. The constant `c` and the ledger, step by step

Notation: `L = recordLength M.k |x| s = |joinFields fs|`, `fs = cfgRecord s c τ`, `m = k + 3`
fields, `F = k(2s + 1) + posWidth |x| + 2` field cells (`cw_field_total`),
`fieldOffset fs m = L + 1 = F + m` (`length_joinFields_add_one`, `joinFields_length`),
`c = C₂ + |Q| + 8`, `W = c · F ≤ c · L` (`cw_record_clock`).

1. **Writer** (`cw_writer`): a round costs `4l + 9 ≤ 9(l + 1)` steps, a pass `≤ 9(L + 1)`; the
   rewind `l + 4 ≤ 4(l + 1)` per field, `≤ 4(L + 1)`; `c` passes `≤ 13c(L + 1)`; the clock's
   rewind `(0 + 1 + 1) + (W + 3 + 1)`. Total `T_w ≤ 13c(L + 1) + W + 6`.
2. **Runner**: F2 gives `t₂ ≤ 5 · Nat.ofDigits 2 (W trues) + 2W + 3 = 5(2^W − 1) + 2W + 3`
   (`cw_true_value`), then one dispatch.
3. **Clear** (`halted`/`left`): `2W + 2`, then one dispatch into the exit. At `exhausted`: none.
4. **Total**: `t ≤ T_w + (t₂ + 1) + (2W + 3)`. With `A = 14c + 13` and `D = 0`,
   `A(L + 1) ≥ 13c(L + 1) + W + 13` (as `W ≤ cL`), so
   `t ≤ A(L + 1) + (5(2^W − 1) + 2W + 3) + (2W + 2) + D ≤ (A + 4c + D + 10) · 2^((A + 4c + D + 10)(L + 1))`
   by `cw_time_bound`, and `≤ C · 2^(C(L + 1))` since `A + 4c + 10 ≤ C`.
5. **Heads**, with `r = C(L + 1)`: the writer keeps the record head in `[−1, L + 1]` and the
   clock head in `[−1, W + 1]` (`r ≥ (c + 2)(L + 1) ≥ c(L + 1) + 2`); the runner keeps every head
   within `C₂(L + W + 1) ≤ C₂(c + 1)(L + 1)` (`cw_head_bound`) `≤ C(L + 1)`; the clear keeps the
   clock head within `[−1, W]`; nothing else moves.
6. **Silence**: the final configuration's output is `d.output`, so by
   `MultiTapeTM.output_prefix` at `0` and at `t` it is `d.output` throughout (`cw_silence`).
7. **Space**: `MultiTapeTM.spaceUsed_le_of_abs_le` at `r = C(L + 1)` gives
   `(K + 2)(2C(L + 1) + 1)`, the statement's form after `mul_assoc`.
8. **Certification**: `cw_record_clock` gives `C₂ · N · (L + |x| + 1) ≤ 2^W − 1` for every
   `N ≤ configBound + 1`, F2's hypothesis for that `N`.
9. **The constant**: `C = A + 4c + 0 + 10 + C₂(c + 1) + c + 2` dominates the time constant
   (`A + 4c + D + 10`), the head constant (`C₂(c + 1)`) and the writer's `c + 2` at once.

## 7. Escalations

**None.** No item stopped; Route B was not used.

## 8. Rule 10 (the pinned base, no unfolding)

**Declarations cited outside the file** (computed from the elaborated constants of every `cw_`
declaration and the target, `evidence/probes/DefsUsed.lean`, output
`evidence/logs/defs-used.log`): 99 TCSlib names, all public at the base; the probe's 102
`#check`s plus 43 more (types, constructors, structure fields and instances reached
through cited statements, `Turing.Segment`, `Turing.Segment.trans`, `Turing.segment_iff`,
`Turing.FinTM.bufferTape_of_neg`) form `evidence/probes/F3C2ImportProbe.lean`
(145 `#check`s): **0 errors, 0 warnings** (`evidence/logs/import-probe.log`). All of
them — lemmas, definitions, types, constructors, structure fields and instances:

`Turing.Action`, `Turing.Action.mk`, `Turing.Cfg`, `Turing.Cfg.InWindow`, `Turing.Cfg.ext`, `Turing.Cfg.inputPos`, `Turing.Cfg.inputSymbol`, `Turing.Cfg.mapState`, `Turing.Cfg.mapState_inputPos`, `Turing.Cfg.mapState_output`, `Turing.Cfg.mapState_state`, `Turing.Cfg.mapState_workTapePos`, `Turing.Cfg.mapState_workTapes`, `Turing.Cfg.mk`, `Turing.Cfg.output`, `Turing.Cfg.state`, `Turing.Cfg.workTapePos`, `Turing.Cfg.workTapeSymbols`, `Turing.Cfg.workTapes`, `Turing.FinTM`, `Turing.FinTM.State`, `Turing.FinTM.bufferTape`, `Turing.FinTM.bufferTape_left`, `Turing.FinTM.bufferTape_nat`, `Turing.FinTM.bufferTape_of_neg`, `Turing.FinTM.configBound`, `Turing.FinTM.fintypeState`, `Turing.FinTM.k`, `Turing.FinTM.tm`, `Turing.MultiTapeTM`, `Turing.MultiTapeTM.mk`, `Turing.MultiTapeTM.output_prefix`, `Turing.MultiTapeTM.runFrom`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.MultiTapeTM.runFrom_zero`, `Turing.MultiTapeTM.spaceUsed`, `Turing.MultiTapeTM.spaceUsed_le_of_abs_le`, `Turing.MultiTapeTM.step`, `Turing.MultiTapeTM.tr`, `Turing.RecSym`, `Turing.RecSym.digitEmb`, `Turing.RecordAt`, `Turing.SeekPhase`, `Turing.SeekPhase.done`, `Turing.SeekPhase.run`, `Turing.Segment`, `Turing.Segment.trans`, `Turing.SweepPhase`, `Turing.SweepPhase.done`, `Turing.SweepPhase.sweep`, `Turing.WindowExit`, `Turing.WindowExit.casesOn`, `Turing.WindowExit.ctorIdx`, `Turing.WindowExit.exhausted`, `Turing.WindowExit.halted`, `Turing.WindowExit.left`, `Turing.cfgRecord`, `Turing.cfgRecord_length`, `Turing.clearTM`, `Turing.clearTM_run_ofCfg`, `Turing.copyMapTM`, `Turing.copyMapTM_run_ofCfg`, `Turing.exists_windowRunnerTM`, `Turing.fieldOffset`, `Turing.fieldOffset_add_length_le`, `Turing.fieldOffset_succ`, `Turing.fieldOffset_zero`, `Turing.fieldsTape`, `Turing.fieldsTape_field`, `Turing.instDecidableEqSeekPhase`, `Turing.instDecidableEqSweepPhase`, `Turing.instDecidableEqWindowExit`, `Turing.instFintypeSeekPhase`, `Turing.instFintypeSweepPhase`, `Turing.joinFields`, `Turing.joinFields_cfgRecord_length`, `Turing.joinFields_length`, `Turing.length_joinFields_add_one`, `Turing.moveInputPos`, `Turing.moveInputPos_zero`, `Turing.phaseHostTM`, `Turing.phaseHostTM_run`, `Turing.posWidth`, `Turing.recordAt_iff`, `Turing.recordLength`, `Turing.recordLength_eq`, `Turing.record_pos_lt`, `Turing.segment_iff`, `Turing.skipBackTM`, `Turing.skipBackTM_run_ofCfg`, `Turing.skipTM`, `Turing.skipTM_run_ofCfg`, `Turing.step_of_tapeAction_move`, `Turing.tapeAction`, `Turing.windowRun`, `Turing.wordPatch`, `Turing.wordPatch_append`, `Turing.wordPatch_of_mem`, `Turing.wordPatch_of_not_mem`

**Probes re-run at the delivery** (all against this tree's oleans):
- import probe, extended: 0 errors, 0 warnings;
- consumer probe `F3ConsumerProbe.lean.txt` (unchanged): 0 errors, 0 warnings
  (`evidence/logs/consumer-probe.log`);
- the join probe as published at gate 56 (`F3C2JoinProbe-published.lean.txt`): exactly its two
  bare controls fail (lines 48 and 50, the same as the gate's
  `F3C2JoinProbe-published.out`), nothing else (`evidence/logs/join-probe.log`).

**Seal test** (`evidence/tools/mkseal.py`, `evidence/probes/WindowClockSeal.lean`,
`evidence/logs/seal-test.log`): a scratch copy of the module whose whole runner home, from
`/-! ### The runner -/` to the end, the target included, sits in a section with
`attribute [local irreducible]` on **32** other-file TCSlib definitions — continuation 1's 17
(`Cfg.inputSymbol`, `Cfg.workTapeSymbols`, `FinTM.bufferTape`, `FinTM.configBound`,
`MultiTapeTM.runFrom`, `MultiTapeTM.step`, `cfgRecord`, `clearTM`, `copyMapTM`, `joinFields`,
`moveInputPos`, `posWidth`, `recordLength`, `tapeAction`, `wordPatch`, `fieldsTape`,
`RecordAt`) and 15 more (`Cfg.InWindow`, `Cfg.mapState`, `MultiTapeTM.spaceUsed`,
`MultiTapeTM.spaceUsedByTape`, `MultiTapeTM.visitedByTapeHead`, `RecSym.digitEmb`, `Segment`,
`fieldOffset`, `phaseHostTM`, `skipBackTM`, `skipTM`, `windowRun`, and the derived
`instDecidableEqSeekPhase`, `instDecidableEqSweepPhase`, `instDecidableEqWindowExit`): **exit 0,
no diagnostic at all**. `FinTM.fintypeState` is `@[reducible]` and cannot be sealed locally; the
derived `instFintypeSweepPhase`/`instFintypeSeekPhase` were dropped from the set because their
controls do not bite (below). The census also lists `WindowExit.casesOn` and `WindowExit.ctorIdx`,
the inductive's generated eliminator and constructor index, which `cases` and `simp`'s
constructor discrimination produce; `ctorIdx` is generated `@[reducible]` and cannot be sealed
either (the attempt is refused, as for `fintypeState`). The frozen bridge `FinTM.configBound_le_two_pow` stays outside the
seal, as the brief says.

**Controls** (`evidence/probes/SealControls.lean`, `evidence/logs/seal-controls.log`): for each of
the 31 sealed definitions other than `windowRun`, `isDefEq (const) (its value)` at default
transparency — the `rfl` that unfolds it — succeeds with nothing sealed (31 × "unfolds") and
fails under the same seal (31 × "sealed"). `windowRun` (structural recursion, which this check
cannot see through) and `FinTM.bufferTape` have concrete `rfl` controls,
`windowRun M s upd 0 c τ = (.exhausted, c, τ)` and `bufferTape w (−1) = none`: both close
unsealed and both fail sealed (the file's only two errors, lines 97 and 100, as intended).

**Inspection** of every `rw`/`simp`/`simpa`/`dsimp`/`unfold` argument in the diff
(`evidence/logs/rw-simp-args.log`): lemmas only (TCSlib public lemmas, core and Mathlib
lemmas such as `if_pos`, `List.length_replicate`, `Function.update_self`), local hypotheses,
the let-bound start configurations `a₀`, and this file's own definitions `cw_cfg`, `cw_Ctrl`,
`cw_hostTM`, `cw_next`, `cw_prev`, `cw_red`. No other file's definition and no core or Mathlib
definition is passed to `rw`, `simp` or `unfold`. Bare `simp` (no lemma list) closes only
constructor disequalities (`cw_Idx`, `WindowExit`) and the three-element `Finset` membership of
the exits; `decide` is used only on core `Nat`/`Option Bool` facts (the landed `cw_left_run`,
`Nat.pow_le_pow_right (by decide)`). `rfl` steps reduce only this file's definitions and core
ones (`Option.map`, `Function.comp`, `Nat.sub`).

**Rule 11** (`evidence/logs/rule11.log`, the cont1 review's `rule11.py`): **R3-row hits: none**
(`copyTM_run`, `transferTM_run`, `clearTM_run`, `compareTM_run`, `incrementTM_run_succ`,
`incrementTM_run_overflow`). The other-file private-name token hits are not citations: `S`, `T`
(type variables), `one`, `part` (prose), `sum` (`List.sum`), `trans` (`.trans`), and
`mapState_state`, which occurs only as the public simps lemma `Cfg.mapState_state`
(Contract/Seam's private `mapState_state` is a different declaration). The elaborated-constant
census above confirms that no private declaration of another file is reached.

## 9. Duplication (the v3 screen)

Population: continuation 1's 21 files (`screen-population.txt`), screen
`scripts/copy-text-screen-v3.py` (SHA-256 `f4feac91d3a1ec036f3bbcaafde83e6855a1bf1a62d31dac31a40a40d878f181`), one run at a time under
`nice -n 10`.

- **Before** (base worktree, `evidence/logs/screen-before.txt`): `declarations screened: 1058;
  copy pairs: 513; reproduced text: 149,070 chars` — byte-equal, after its comment lines, to
  `campaign/fills/b6/logs/b6-fill-configclock-cont2-screen-base.txt`.
- **After** (final commit, `evidence/logs/screen-after.txt`): `declarations screened: 1102; copy pairs (target reproduces >= half of source): 521; reproduced text: 150,388 chars`.
- **Diff** (`evidence/logs/screen-diff.txt`, by label): 8 new pairs (8 in-file, 8 involving `WindowClock.lean`); **0 new cross-file pairs**; 0 pairs removed; 0 pairs with changed figures; the highest new share 88%.

**No new cross-file pair** has a `WindowClock` declaration on either side; the only cross-file
pair with `WindowClock` is the base's (`ConfigCount::ComputesInTime.of_spaceUsed_le` reproduces
the frozen bridge `FinTM.inWindow_of_spaceUsed_le`, 67%). **New in-file pairs** (none at 90% or
more), each justified:

| pair (target reproduces source) | share | justification |
|---|---|---|
| `cw_seg_back` ⟶ `cw_seg_skipS`, and back | 88% / 73% | the two record-tape rows (skip, skip back): each feeds its framed row's three clauses to the one shared argument `cw_seg_row`; what they share is that call's argument list and the record-tape premise's rewrite |
| `cw_seg_clockBack` ⟶ `cw_seg_skipC` | 79% | the two clock rows (skip back over the word, skip past the written cells): the same `cw_seg_row` call with the clock word premise from `cw_skip_word` |
| `cw_cfg_moveL` ⟶ `cw_cfg_move₀` | 69% | one endpoint conversion (a framed row's `Function.update` of one head into a writer configuration) for the clock head and for the record head: mirror-image case splits |
| `cw_cfg_box` ⟶ `cw_cfg_pos_zero`; `cw_cfg_moveL` ⟶ `cw_cfg_pos_zero` | 68%; 52% | the same three-way case split on a head (record, clock, other) through `cw_cfg_pos₀`/`cw_cfg_posL`/`cw_cfg_pos`, towards three different conclusions |
| `cw_prev` ⟶ `cw_next`; `cw_red` ⟶ `cw_next` | 62%; 61% | the successor definitions share the dependent-pair syntax `⟨.phase …, (SeekPhase.run : SeekPhase)⟩` |

**new copies: none.**

## 10. File size, final sweep, axioms, lint

- **Size**: 458 → 1680 lines; **4 public / 66 private** declarations (base 4 / 11; lint's
  INFO line). The lint's size WARN (`> 1000 lines`) is recorded here as the justification the
  policy asks for: ground rule 8 sets no cap and this brief owns only this file.
- **Final sweep** (`evidence/logs/final-sweep.log`, the 182 modules of the order list in order, at
  the final commit): 182/182 modules rc 0 in the order list's order (2026-10-24T00:43:31Z – 01:07:41Z), 0 errors; `WindowClock` (00:56:47–00:57:00Z, 13.5 s, 2,084 MiB) with no diagnostic at all; **27 sorry warnings in 10 modules**, equal per module to the base's 28 minus the target's (`evidence/logs/final-sweep-sorries.txt`); peak RSS 2,813 MiB. Tail: `=== TCSlib/Complexity/SpaceComplexity end 2026-10-24T01:07:41Z rc=0 wall=1.8s maxrss_children=2025MiB`, `SWEEP DONE`.
- **Axioms** (`evidence/logs/axioms.log`, `evidence/probes/WindowClockAxioms.lean`: a scratch copy
  of the module with a `#print axioms` for the 4 public and all 66 private declarations): the
  target `[propext, Classical.choice, Quot.sound]`; every private within
  `[propext, Classical.choice, Quot.sound]`; no `sorryAx` anywhere.
- **Lint**: `python3 -I scripts/campaign_style_lint.py TCSlib/Complexity/SpaceComplexity`:
  `style_lint: 0 FAIL, 82 WARN over 107 files` (base: `0 FAIL, 81 WARN over 107 files`; the one new WARN is the size line
  above). No line over 100 characters (`evidence/logs/line-widths.log`).

## 11. Checkpoint zips

| zip | commit | state |
|---|---|---|
| `fill-b6-configclock-cont2-cp1.zip` | `475ecdd0bf118a9eed92d2051ff18b31d21f6cbf` | checkpoint 1: only the target open |
| `fill-b6-configclock-cont2-cp2.zip` | `4619561316f94dd9c62c8179ef369549a7e33957` | checkpoint 2: only the target open |
| `fill-b6-configclock-cont2-cp3.zip` | `0ea338d0671254867ef8132c4235302efbe64e1b` | checkpoint 3: only the target open |
| `fill-b6-configclock-cont2-cp4.zip` | `a468d65d9c7c19a050472a5b2a94be5829369b70` | checkpoint 4: only the target open |
| `fill-b6-configclock-cont2-cp5.zip` | `aaf09900e3016a6b88d0846be79019972ea41cb8` | checkpoint 5: only the target open |
| `fill-b6-configclock-cont2.zip` | `ebca0bc53382464f7ff674909e8ac3aa5fb673e6` | checkpoint 6: the target proved (this zip) |

Each checkpoint zip holds that commit's `WindowClock.lean`, its patch series and bundle
(prerequisite: the base), its module check (the brief allows the module's check as the final
sweep of a checkpoint), its axiom prints and seal test, both screens, the shared environment
logs, a checkpoint `REPORT.md` (the open declaration, the target, with its literal
"Proof sketch", and its axiom walk), and `SHA256SUMS`.

## 12. Files in this zip

- `REPORT.md` — this report.
- `source/TCSlib/Complexity/SpaceComplexity/WindowClock.lean` — the full modified source at the
  final commit.
- `patches/0001-…` to `0006-…` — `git format-patch` of the six commits against the base.
- `fill-b6-configclock-cont2.bundle` — `git bundle create … fill/b6-configclock-cont2 ^968d7b2b`;
  its only prerequisite is the base (`evidence/logs/bundle-verify.log`).
- `evidence/logs/` — preflight (`preflight.log`, `preflight-recheck.log`), `toolchain.log`,
  `cache-store.log`, `mathlib-roots.txt`, `cache-get.log`, `packages-manifest-check.log`,
  `zero-oleans-check.log`, `cache-probe.log`, `base-and-ancestor.log`, `brief-diff.log`, the
  bootstrap (`bootstrap-stage{1,2}.{txt,log}`, `base-sorry-count.txt`,
  `base-windowclock-check.log`), the final sweep (`final-sweep.log`, `final-sweep-order.txt`,
  `final-sweep-summary.txt`, `final-sweep-sorries.txt`), `axioms.log`, `seal-test.log`,
  `seal-controls.log`, `defs-used.log`, `import-probe.log`, `consumer-probe.log`,
  `join-probe.log`, `rw-simp-args.log`, `rule11.log`, `regions.log`, `statement-freeze.log`,
  `line-widths.log`, `lint.log`, `lint-base.log`, both screens (`screen-before.txt`,
  `screen-after.txt`) and their difference (`screen-diff.txt`, `screen-diff-summary.txt`),
  `bundle-verify.log`, and under `cp/` each checkpoint's module check (and, where run, its
  axiom prints, seal test and screen).
- `evidence/probes/` — the probe sources run here: `F3C2ImportProbe.lean` (the brief's probe plus
  the added names), `F3ConsumerProbe.lean`, `F3C2JoinProbePublished.lean`, `DefsUsed.lean`,
  `WindowClockAxioms.lean`, `WindowClockSeal.lean`, `SealControls.lean`, `MathlibProbe.lean`.
- `evidence/tools/` — the scripts used: `preflight.sh`, `check_mod.py`, `sweep.sh`,
  `mkseal.py`, `mkaxioms.py`, `regions.py`, `screen-owned-only.py` (a quick variant of the v3
  screen restricted to pairs with a `WindowClock` declaration, used only while writing; every
  reported screen is the official script's), `build_zip.py`.
- `SHA256SUMS` — every member except itself.
