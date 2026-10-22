# C1-E continuation 1: the exhaustive replay `E` — fill report

**Brief:** `campaign/fills/c1/briefs/c1-fill-exhaustive-cont1.md`
(SHA-256 `f03994c526c07540c654044decc21027f33017a5307f09b1c639e7875981ab04`, verified against the
attachment; the tip's copy matches the attachment except for the `@ANCESTOR@` placeholders).
**Addendum:** `briefs/fill-environment-addendum.md` v2
(SHA-256 `2a80b0ef8da202cc5faf4c1513b2f34ed7437c5aef2cb3ed815355934b54ad2b`).
**Delivery:** `fill-c1-exhaustive-cont1.zip` (this report, the modified source, the patch series,
the bundle, the logs, the axiom log, both screens, `SHA256SUMS`). By zip, not PR or push.

## 1. Outcome

- [x] **The target is proved in full.** `Turing.FinNDTM.exists_exhaustiveDecider`
  (`TCSlib/Complexity/ClassNP/ExhaustiveReplay.lean`) has no `sorry`; the module elaborates with
  zero errors and zero warnings; its axioms are `[propext, Classical.choice, Quot.sound]`, with no
  `sorryAx`. `ndAcceptsWithin_decider_of_universal` (the base's consumer of the target) now has
  the same axiom set. Phase reached: 4 of 4 (no partial, no appendix needed).
- [x] **Base and ancestor check.** Base `9e77d2b26a62c3ee0c418a1e0a031c867c0ac80a`; branch
  `fill/c1-exhaustive-cont1` created at exactly that commit
  (`git rev-parse HEAD` printed it before the first edit). The ancestor check
  `git merge-base --is-ancestor 9e77d2b2… complexity/arora-barak-ch3-4` exited 0 (the clone's
  tip of `complexity/arora-barak-ch3-4` was `519c3a248a67770967f62cdf85b28b18935f7ad1`). No
  rebase, merge or cherry-pick. Log: `evidence/logs/base-and-ancestor.log`.
- **Constant:** `C = 18·N.k + 41`. **Time bound:** `E` halts within
  `(18·N.k + 41)·2^((18·N.k + 41)·(T + 1))` steps on every `z` with `N.tm.HaltsWithin z T`; there
  is no `|z|` term (§5).

Commits on `fill/c1-exhaustive-cont1` (base excluded; the first is the imports alone):

```
1eabca5e ExhaustiveReplay: the three authorized imports (C1-E cont1, region (a))
4dae0d2d ExhaustiveReplay: adopted review probes P1-P4 as xr_ privates, tape translation, first arrival at a stationary anchor
e29ecc28 ExhaustiveReplay: leaf-row scaffolding, the return pass and forward scan, the rewind and extend rows
e6f0c8c3 ExhaustiveReplay: the pass, capture test, input rewind and answer rows with their run lemmas; buffer-tape facts
14a27c15 ExhaustiveReplay: the clock over the replay machine, the tape-bank layout, and one replay's two exits
78f1eed7 ExhaustiveReplay: host infrastructure (anchors, banks, counter values, phases, redirect table, E, one-phase step)
807e6a64 ExhaustiveReplay: the patch lemma over a shorter stored word
3484eb38 ExhaustiveReplay: one cycle's phases on the host (copy, replay, capture test, rewinds, increment)
a45b88da ExhaustiveReplay: reflow lines over 100 characters
4eecd8b3 ExhaustiveReplay: the window clear on the host (one pass, one tape, all tapes)
2ac42a81 ExhaustiveReplay: the host's halt phase, and one cycle on the host
a1aa022e ExhaustiveReplay: one depth and the depth change on the host
77c580ea ExhaustiveReplay: the whole run, the machine E, and the exhaustive decider
c86fc6a3 ExhaustiveReplay: drop three unused private lemmas
81be5ca9 ExhaustiveReplay: read one and two steps of a run through two helpers (screen hygiene)
041c82ab ExhaustiveReplay: scope the one-step helper's proof under open MultiTapeTM
```

```
TCSlib/Complexity/ClassNP/ExhaustiveReplay.lean | 3137 ++++++++++++++++++++++-
 1 file changed, 3136 insertions(+), 1 deletion(-)
```

## 2. Preflight (addendum v2, Part 1) — `evidence/logs/preflight.log`

Recorded at 2026-10-18T05:50:12Z, before any cache or Lean work:

| item | value |
|---|---|
| `nproc` | 4 |
| cgroup (v1) `memory.limit_in_bytes` | 14,343,688,192 B |
| cgroup `memory.usage_in_bytes` at preflight | 20,934,656 B (`max_usage` 50,024,448 B, `failcnt` 0) |
| `memory.max` / `memory.current` / `memory.events` (v2) | not present (cgroup v1 host); `free -b`: total 16,874,930,176 B, available 16,236,531,712 B |
| memory headroom (limit − use) | 14,322,081,792 B ≥ 4 GiB: **yes** |
| `df -B1` of the clone (`/home/user/tcslib`), the staging dir and the scratchpad (all on `/dev/vda`) | 270,553,174,016 B total, 14,211,698,688 B used, **27,612,160,000 B available** ≥ 12 GiB: **yes** |
| `df -T` filesystem type | `ext4` (no clone, cache, olean tree or `TMPDIR` on a tmpfs; `/dev/shm` unused) |

Verdict: both thresholds met; no E-RES.

**One checkout, one cache.** A single clone (`/home/user/tcslib`), `lake exe cache get` once into
its own `.lake/packages` (`evidence/logs/cache-get.log`: rc 0, 7506 files decompressed;
`lake build --no-build proofwidgets:release` is the cache tool's own validation). **Packages
against the manifest** (`evidence/logs/packages-manifest-check.log`): the 11 fetched packages
all have the manifest's URL and revision; the manifest's other 4 entries (`doc-gen4` and its
three inherited dependencies `UnicodeBasic`, `BibtexQuery`, `MD4Lean`) are absent because the
lakefile requires `doc-gen4` only under `env = "dev"`, so the cache tool never fetched them —
nothing differs, nothing was re-cloned or updated, no E-RES condition.
`find .lake/packages -name '*.olean' -size 0` printed nothing
(`evidence/logs/zero-oleans-check.log`). The Mathlib probe (`probes/MathlibProbe.lean`, `import Mathlib.Algebra.BigOperators.Group.Finset.Basic`
only) elaborated through `scripts/lean_check_tree.sh` (`evidence/logs/cache-probe.log`; a first
attempt with a stray `#check` is kept as `cache-probe-attempt1-badprobe.log` — a probe error, not
a cache failure). No dependency tree was copied, moved or deduplicated; no `lake build`.

**Toolchain** (`evidence/logs/toolchain.log`): elan 4.2.4 installed `leanprover/lean4:v4.25.0`
(Lean 4.25.0, Lake 5.0.0). The host's proxy initially blocked `release.lean-lang.org` /
`releases.lean-lang.org`; the user unblocked `*.lean-lang.org` and the install then succeeded.
Lean started normally: **Part 2 of the addendum (the `readlink` shim) was not needed and not
used.**

**Bootstrap** (addendum item 5, recorded): stage 1 = the 29 modules of the order list that the
owned file imports (directly or not), in the list's order (`evidence/logs/bootstrap-split.txt`,
`bootstrap-stage1.log`); the owned file was then checked against them after every chunk. Stage 2
= the remaining 47 modules, in order (`bootstrap-stage2.log`), then the final sweep over all 77
(`final-sweep.log`), both at the delivered tip. No timeouts were wrapped around any check; each
module's start and end time and the child's maximum RSS are logged
(`/usr/bin/time` is not installed on this host, so `/home/user/fill-tools/check_mod.py` wraps
`scripts/lean_check_tree.sh` and reads `getrusage(RUSAGE_CHILDREN)`). Peak RSS over all checks
was 2,796 MiB (`Build/Catalog`, stage 1; the addendum's measured figure is about 2.4 GB); the
owned module peaks at about 2.1 GB; nothing stalled.

## 3. Edits by region (ground rules 1–3, 6)

Only `TCSlib/Complexity/ClassNP/ExhaustiveReplay.lean` changed (the diff stat above is one file).

- [x] **(a) Imports, the first edit** (commit `1eabca5e`): exactly the three authorized imports
  `TCSlib.Complexity.TuringMachine.ChoiceReplay`, `TCSlib.Complexity.TuringMachine.Build.StepClock`,
  `TCSlib.Complexity.TuringMachine.Build.Seam`; no other import.
- [x] **(b) The privates' home** (the blank line after `namespace Turing`): every new declaration
  is `private` with the `xr_` prefix (183 privates; §9). Two carry a scoped `open … in`
  (`open Classical in` for the redirect table and the depth-run lemma, whose statements use
  `decide`; `open MultiTapeTM in` for a one-line helper).
- [x] **(c) The body** of `FinNDTM.exists_exhaustiveDecider`: the `sorry` replaced by the proof
  (§4–5). The statement is byte-identical; so is `ndAcceptsWithin_decider_of_universal`
  (statement and proof); the diff deletes exactly one line, the `sorry`.
- [x] **(d) No appendix:** the delivery is complete, so the target's docstring is unchanged.
  The route refinements against its proof sketch are reported here (§4.3), not in the file.
- No new public declaration (lint: 2 public declarations, the base's two).

## 4. The construction

### 4.1 Route binding (as the brief fixed it)

- **The host** is `Turing.phaseHostTM` (`xr_host C`), the only host; every phase is a published
  row or a leaf defined in this file; the redirect table is `xr_red`.
- **One replay** is `N.tm.replayTM` under the step clock `Turing.exists_stepClockTMVia`
  (`Γ = Bool`, the identity embedding, no stop state), packed as the private structure
  `xr_Clock N` (the clock's control `Q`, machine `H` on `N.k + 2` tapes, the injection of the
  replay's states, the two exit families `finish`/`timeout` and their two specifications read off
  the existential), run **silently** through `Turing.embedSilentTM` with the output captured on
  the capture tape (`xr_replayTM C := embedSilentTM (xr_ι N.k) (xr_cap N.k) C.H`).
- **The counter word** of value `L` on the clock's last tape is copied from the depth tape at
  the start of every cycle by `Turing.copyTM` (`copyTM_run_ofCfg`; the barred `copyTM_run` is
  not cited), which also restores the clock's counter after either exit (obligation 1).
- **The answer** is the two-exit seam `Turing.seamCompTM₂` of the host onto two one-step answer
  rows at the host's two halt anchors (§4.4). No second host, seam, embedding, counter loop or
  clock is written; `Nondeterminism`'s `choiceCore` is not re-walked.

### 4.2 The tape bank, the phases, one cycle

`E` has `N.k + 2 + 2` work tapes: `N`'s `N.k` tapes (`xr_work k j`), the choice tape
(`xr_choice`), the clock's counter (`xr_ctr`) — the clocked replay's `N.k + 2` tapes, embedded
by `xr_ι = Fin.castAddEmb 2` — then the capture tape (`xr_cap`) and the depth tape (`xr_dep`).
`xr_tapes`/`xr_heads` build a bank from its five parts (`Fin.addCases`, `Fin.lastCases`), with
projection and one-bank-update lemmas and the extensionality lemma `xr_bank_ext`.

The phase index is `xr_I = xr_Ph N.k × Bool × Bool`: a phase and the two flags **"some branch
accepted"** and **"some branch is live"**. The phases (`xr_Ph`) and their machines (`xr_M`):

| phase | machine | control | effect (host lemma, bound) |
|---|---|---|---|
| `copy` | `copyTM _ (xr_dep) (xr_ctr)` | `SweepPhase` | depth word → counter: the clock's budget `L` (`xr_copy_host`, exactly `2L + 3`) |
| `replay` | `xr_replayTM C` | `C.Q` | the branch along the choice word `s`, up to `L` steps, silently; exit `finish` (halted) or `timeout` (live, raises the live flag) (`xr_replay_host`, `≤ 5L + 2L + 3`) |
| `test` | `xr_testTM _ (xr_cap)` | `xr_St` | reads whether the captured output is `[true]` (raises the accept flag) and clears the capture tape (`xr_test_host`, `≤ |out| + 3`) — obligation 3 |
| `crewind` | `xr_rewindTM _ (xr_choice)` | `xr_St` | choice head back to `0` (`xr_crewind_host`, `≤ p + 3`) — obligation 2 |
| `irewind` | `xr_inRewindTM` | `xr_St` | input head back to `1` (`xr_irewind_host`, `≤ inputPos + 3`) — obligation 4 |
| `pass j n` (`j < N.k`, `n < 6`) | `xr_passTM _ (xr_work j) (xr_dep) (xr_dir n)` | `xr_St` | the window clear: pass `n` of tape `j`, the depth word as the ruler (`xr_pass_host`, `≤ 2L + 3`; six passes per tape, `xr_clearTape_host`; all tapes, `xr_clear_host`) |
| `inc` | `incrementTM _ (xr_choice)` | `FlagPhase` | next choice word (`xr_inc_host_succ`, `≤ 2L + 3`), or at the overflow the depth's end (`xr_inc_host_overflow`) |
| `extC` | `xr_extendTM _ (xr_choice)` | `xr_St` | depth change: the choice word becomes the all-`false` word of length `L + 1` (`xr_extC_host`) |
| `extD` | `xr_extendTM _ (xr_dep)` | `xr_St` | depth change: the depth word gets one more cell (`xr_extD_host`) |
| `incD` | `incrementTM _ (xr_dep)` | `FlagPhase` | depth change: the depth word's value becomes `L + 1` (`xr_incD_host`) |
| `halt` | `xr_idleTM` | `xr_St` | a stationary anchor, self-redirected (`xr_halt_fixed`); the accept flag is the answer |

A **cycle** at depth `L` (`xr_cycle C z a l wL s u h`: the copy phase with flags `a l`, the depth
word `wL` of width and value `L`, the choice word `s` of length `L`, some counter word `u` of
width at most `L`, the capture tape blank, `N`'s tapes blank with their heads at `h`, the input
head at `1`) runs copy → replay → test → crewind → irewind → the `6·N.k` passes → inc, within
`(18·N.k + 19)(L + 1)` steps (`xr_cycle_host`), folding the branch's verdicts into the flags
(`[true]` output → accept flag; live after `L` steps → live flag) and restoring the tapes: a
successor word starts the next cycle, the overflow reaches the depth's end `xr_depthEnd`. A
**depth** (`xr_depth_host`, by induction on `2^L − val s`) runs the `2^L` words; its flags are
characterized as iffs over the words of value at least `val s`. The **depth change**
(`xr_deepen_host`, `≤ 6L + 11`) lowers both flags and starts depth `L + 1` with the all-`false`
word and a depth word of width and value `L + 1`.

**The whole run** (`xr_run_host`, by induction on the number of depths left before `L*`): let
`L*` be the first all-halting depth (`xr_first_depth`: it exists, is positive, is at most `T`,
and `AcceptsWithin z L* ↔ AcceptsWithin z T` by `xr_accepts_iff_of_halts`). Below `L*` some
branch of length `L` is live (`¬ HaltsWithin z L`, through `NDTM.haltsWithin_iff`), so the live
flag is up at the depth's end and the host deepens. At `L*` every branch of length `L*` has
halted, so the live flag is down and the accept flag is `decide (N.AcceptsWithin z L*)`
(`FinNDTM.acceptsWithin_iff` both ways). The host then sits at
`xr_anchor C (decide (N.AcceptsWithin z L*))`, which is stationary.

### 4.3 Route refinements against the target's proof sketch (reported, not in the file)

1. **Translation invariance instead of returning the heads.** `N`'s work heads are never
   returned to their origins. The invariant carries their current positions `h`;
   `xr_runWith_shift` (a branch commutes with translating the work tapes, through
   `xr_stepWith_shift`/`xr_apply_shift`) identifies the replay from translated blank tapes with
   `N`'s branch from `N.tm.initCfg z`, read through `NDTM.replayTM_runFrom` and the
   `withChoiceTape` field lemmas. The window clear therefore blanks radius `2L` around the
   displaced heads (`xr_branch_win`: after `L` steps from the translated origin the content is
   within radius `L` of it, hence within `2L` of the head; `xr_window_runWith` is round 1's P2).
   This removes a "return each head to its origin" row, which would need a marker or a counter
   per head.
2. **The window clear is six ruler-driven passes per tape** (`xr_passTM`): the depth word is the
   ruler; a pass moves head `j` by `L` cells along its direction, blanks the `L + 1` cells it
   visits, and returns the ruler head (`xr_passTM_run`, exactly `2L + 2` steps). Two passes left
   then four right blank `[h − 2L, h + 2L]` and leave the head `2L` cells to the right, which
   translation invariance tolerates.
3. **The phase host's guard from exact-time run lemmas.** Every leaf row stops at a stationary
   `done b` anchor, so the first arrival at the anchor is at most the exact time and no earlier
   state is redirected (`xr_firstArrival`, `xr_firstArrival'`, with `xr_runFrom_fixed`). The
   catalog rows' `_ofCfg` contracts already carry their no-earlier-exit cuts.
4. **The flags live in the phase index**, not on a tape (`xr_I`), so a redirect carries them.
5. **The depth word does double duty:** its value `L` is the clock's budget (copied every cycle)
   and its width `L` is the ruler of the passes.
6. **The halt phase is a stationary, self-redirecting phase**; the seam's cut is the first visit
   to one of the two anchors (`xr_firstArrival'` over the predicate "is one of the two
   anchors"), then one dispatch step and one answer step (`xr_answerTM`, `xr_answer_tail`).

### 4.4 The machine `E`

`xr_E C : FinTM Bool` has `N.k + 2 + 2` tapes and control `((Σ i, xr_PhSt C i) ⊕ xr_St) ⊕ xr_St`;
its table is `xr_seam C = seamCompTM₂ (xr_host C) (xr_anchor C true) (xr_anchor C false)
(xr_answerTM _ true) .start (xr_answerTM _ false) .start`, started at the host's first cycle
through the `{ tm with q₀ := … }` idiom (`MultiTapeTM.runFrom_with_q₀`,
`MultiTapeTM.initCfg_with_q₀`; `xr_E_initCfg` identifies `E`'s initial configuration with
`xr_cycle C z false false [] [] [] 0`, read in the seam's states). `seamCompTM₂_run_ofCfg` then
gives, at the anchor with the accept flag `b`, the answer row's run one dispatch step later;
`xr_answer_tail` reads its halt and output `[b]`; `FinTM.computesInTime_iff` and
`FinTM.ComputesInTime.mono` close the target with `decide_eq_true`/`decide_eq_false` on
`AcceptsWithin z L* ↔ AcceptsWithin z T`.

## 5. The constant `C` and the ledger

Per cycle at depth `L`: copy `2L + 3`, replay `≤ 7L + 3`, test `≤ L + 3`, choice rewind `≤ L + 3`,
input rewind `≤ L + 4`, the `6·N.k` passes `≤ 6·N.k·(2L + 3)`, increment `≤ 2L + 3`; in total
`≤ (18·N.k + 19)(L + 1)` (`xr_cycle_host`). Per depth: `2^L` cycles plus the depth change
`≤ 6L + 11 ≤ 2^L·19·(L + 1)`, so `≤ 2^L·(18·N.k + 38)(L + 1)` (`xr_run_host`, with
`A := 18·N.k + 38`). The ledger `xr_ledger A L*`:

```
Σ_{L ≤ L*} 2^L · A·(L + 1) + 2 ≤ (A + 3) · 2^((A + 3)(L* + 1))
```

(the `+ 2` pays the seam's dispatch and the answer step), and `L* ≤ T` gives
`E.ComputesInTime z [b] ((18·N.k + 41) · 2^((18·N.k + 41)(T + 1)))`. So `C = 18·N.k + 41`, and
there is no `|z|` term: each replay touches at most `L + 1` input cells
(`MultiTapeTM.timed_input_bound`, in `xr_branch_inputPos_le`), and the input rewind costs
`inputPos + 3 ≤ L + 4`.

## 6. The window clear and the promotion candidates

**Why no row serves the clear.** `clearTM_run_ofCfg` clears a word delimited by blanks at
relative `−1` and `|w|`; after a replay the work tape holds an arbitrary pattern of symbols and
blanks within radius `L` of the translated origin, with the head displaced inside it — there is
no delimited word and no known head offset. The new leaf `xr_passTM` (one tape, one ruler, one
direction) blanks exactly the cells its head visits and returns the ruler head, so six passes
blank a radius-`2L` window around the head without a marker, a counter per head or a return to
the origin.

**Promotion candidates** (private here; each is a self-contained statement with an exact-time
contract):
1. `xr_passTM` / `xr_passTM_run` — the ruler-driven pass (blank `L + 1` cells along a direction,
   return the ruler head), and `xr_clearTape_host`'s six-pass window clear.
2. `xr_firstArrival'` (and `xr_firstArrival`, `xr_runFrom_fixed`) — the first arrival at a set of
   stationary anchors: the phase host's guard from any exact-time run lemma whose exit is
   stationary.
3. `xr_runWith_shift` (with `xr_shift`, `xr_apply_shift`, `xr_stepWith_shift`) — branches of an
   NDTM commute with translating the work tapes.
4. `xr_window_runWith` (round 1's P2) — the radius-`|w|` window of a branch.
5. `xr_extendTM`/`xr_extendTM_run` and `xr_rewindTM`/`xr_rewindTM_run` — append one `false` to a
   buffered word; rewind a head to a word's origin.
6. `xr_val_*`/`xr_incFixed_*` — the little-endian value of a word and `incFixed` as its successor
   (`xr_incFixed_val`, `xr_incFixed_none_max`, `xr_val_inj`), completing `Convention`'s
   `incFixed` lemmas.

**Escalations: none.** No statement was unprovable as stated; no fact about another file's
definition lacked a published lemma.

## 7. Rule 10 (the pinned base, no unfolding) and rule 11 (MIG-1 compatibility)

- Every definition of another file is read through its published lemmas: the machine model's
  primitives through `MultiTapeTM.runFrom_*`, `step_of_some`, `Action.apply_*`,
  `Cfg.mapState_*`, `Cfg.init_*`, `Cfg.workTapeSymbols_eq`, `inputSymbolInner`,
  `moveInputPos_zero`; the replay through `replayTM_runFrom`, `replayTM_tr`,
  `withChoiceTape_*`; the clock through `exists_stepClockTMVia` and `clockCfg`/`wordPatch`'s
  lemmas; the silent embedding through `embedSilentTM_runFrom`/`embedSilentCfg_*`; the hosts
  through `phaseHostTM_run` and `seamCompTM₂_run_ofCfg`; the rows through `copyTM_run_ofCfg`,
  `incrementTM_run_succ_ofCfg`, `incrementTM_run_overflow_ofCfg`, `FinTM.timed_rewind`,
  `FinTM.controlAction`, `MultiTapeTM.timed_input_bound`; the buffer tape through
  `FinTM.bufferTape_*`. `step` and `Action.apply` are unfolded only for this file's own leaves
  (`xr_act_apply`, `xr_mv1_apply`, `xr_mv2_apply`, `xr_stay_step`, the leaf tables).
- **The import probe re-run** (`evidence/probes/C1ExhaustiveImportProbeExtended.lean.txt`):
  the brief's 64 `#check`s plus 196 more for every other declaration the proof cites (the
  TCSlib names under `Turing`, then the Mathlib/core names), 260 in all, **0 errors**
  (`evidence/logs/import-probe.log`). The extra TCSlib names:

```
Action Action.apply Cfg Cfg.ext Cfg.inputSymbol Cfg.inputSymbol_of_end Cfg.inputSymbol_of_zero
Cfg.workTapeSymbols Cfg.workTapeSymbols_eq Cfg.Stopped Cfg.mapState inputSymbolInner
moveInputPos_zero FinTM FinTM.ComputesInTime FinTM.bufferTape FinTM.bufferTape_append
FinTM.bufferTape_nat FinTM.bufferTape_nil FinTM.controlAction MultiTapeTM MultiTapeTM.initCfg
MultiTapeTM.step MultiTapeTM.runFrom MultiTapeTM.initCfg_with_q₀
MultiTapeTM.runFrom_succ_eq_step MultiTapeTM.runFrom_succ_eq_step' MultiTapeTM.runFrom_with_q₀
MultiTapeTM.runFrom_zero MultiTapeTM.timed_input_bound NDTM NDTM.withChoiceTape NDTM.runWith
NDTM.stepWith NDTM.HaltsWithin NDTM.initCfg NDTM.replayTM FinNDTM FinNDTM.AcceptsWithin copyTM
copyTM_run_ofCfg incrementTM incFixed incFixed_eq_none_iff_replicate incFixed_false_cons
incFixed_length incFixed_nil incFixed_true_cons embedSilentCfg embedSilentCfg_inputPos
embedSilentCfg_output embedSilentCfg_state clockCfg wordPatch wordPatch_of_mem
wordPatch_of_not_mem seamCompTM₂ seamCompTM₂_run_ofCfg SweepPhase SweepPhase.done
SweepPhase.sweep FlagPhase FlagPhase.done FlagPhase.run
```

  and the Mathlib/core names:

```
Bool.eq_iff_iff Bool.false_ne_true Bool.or_eq_true Bool.or_false Bool.or_true Bool.toNat
Bool.toNat_false Bool.toNat_true Fin.addCases Fin.addCases_left Fin.addCases_right Fin.castAdd
Fin.castAddEmb Fin.castAddEmb_apply Fin.ext Fin.last Fin.lastCases Fin.lastCases_castSucc
Fin.lastCases_last Fin.natAdd Finset.card_range Finset.mem_range Finset.range Finset.sum_congr
Finset.sum_const Finset.sum_le_sum Finset.sum_range_one Finset.sum_range_succ'
Function.Embedding.coe_refl Function.Embedding.refl Function.update Function.update_eq_self
Function.update_eq_self_iff Function.update_idem Function.update_of_ne Function.update_self
List.append_inj_right' List.append_nil List.concat_eq_append List.eq_nil_or_concat
List.getElem?_eq_getElem List.getElem?_eq_none_iff List.length_append List.length_cons
List.length_nil List.length_replicate List.length_singleton List.length_take List.map_id
List.mem_map List.nil_append List.replicate List.replicate_succ List.replicate_succ'
List.replicate_zero List.reverseRecOn List.takeWhile_sublist List.take_append_drop
List.take_length Nat.add_assoc Nat.add_comm Nat.add_le_add_right Nat.add_sub_cancel'
Nat.add_zero Nat.cast_zero Nat.eq_zero_or_pos Nat.find Nat.find_min Nat.find_min' Nat.find_spec
Nat.le_mul_of_pos_left Nat.le_succ Nat.lt_or_eq_of_le Nat.lt_or_ge Nat.lt_succ_iff_lt_or_eq
Nat.lt_two_pow_self Nat.mul_le_mul Nat.mul_le_mul_left Nat.mul_le_mul_right Nat.not_lt_zero
Nat.ofDigits Nat.ofDigits_append Nat.ofDigits_cons Nat.ofDigits_lt_base_pow_length
Nat.one_le_two_pow Nat.pow_le_pow_right Nat.sub_self Nat.sub_zero Nat.two_pow_pos Nat.zero_add
Nat.zero_le Ne.symm Option.getD_none Option.getD_some Option.isSome_iff_ne_none
Option.isSome_none Option.map_eq_some_iff Option.ne_none_iff_exists' Option.some.injEq
Option.some_ne_none Set.range SignType SignType.coe_zero SignType.neg SignType.pos abs_le
add_neg_cancel_right add_sub_cancel_right add_zero decide_eq_false decide_eq_false_iff_not
decide_eq_true decide_eq_true_eq decide_eq_true_iff dif_neg dif_pos if_neg if_pos ite_self
ite_true le_or_gt lt_irrefl ne_eq not_le pow_add pow_succ sub_zero zero_add Sigma.mk Sum.inl
Sum.inr Nonempty
```

- **Rule 11 greps** over the added lines of the diff (`evidence/logs/rule11-greps.log`): the six
  R3 canonical rows `transferTM_run`, `copyTM_run`, `clearTM_run`, `compareTM_run`,
  `incrementTM_run_succ`, `incrementTM_run_overflow`: **0 hits each** (the framed `_ofCfg` rows
  cited: `copyTM_run_ofCfg` 1 line, `incrementTM_run_succ_ofCfg` 2, `incrementTM_run_overflow_ofCfg`
  1). Private declarations of other files (5,088 names collected from the other 246 `.lean`
  files): **no token of the added lines equals one** (the loose suffix matches listed in the log
  are generic names — `.trans`, `test`, `one`, `empty`, `refl`, `S`, `T` — and
  `Cfg.mapState_state`, which is `StateRenaming`'s public simps lemma). All new privates carry
  the `xr_` prefix.

## 8. Duplication (the copy-text screen v3)

Both runs under `nice -n 10`, one at a time, over the brief's 7-file population:

- before (at the base, `evidence/logs/screen-before.txt`): `declarations screened: 297; copy pairs (target reproduces >= half of source): 106; reproduced text: 36,004 chars` — the brief's
  MEASURED base (297 declarations, 106 pairs, 36,004 characters) reproduced exactly;
- after (at the delivered tip, `evidence/logs/screen-after.txt`): `declarations screened: 428; copy pairs (target reproduces >= half of source): 228; reproduced text: 66,673 chars`.

**New cross-file pairs with an owned-file declaration on one side: none. New copies: none.**
Two intermediate runs showed spurious cross-file pairs with `Nondeterminism.lean` (first
`xr_back_run`/`xr_testTM_run` against `b2_unary_run`, then the helper `xr_runFrom_one` against
seven one-line rewinds): the shared text was the idiom
`rw [MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_zero]`, not a transcription. The
final text reads one and two steps of a run through the helpers `xr_runFrom_one`/`xr_runFrom_two`
(commits `81be5ca9`, `041c82ab`); the final screen has no cross-file pair involving the owned
file, and no pair of the population disappeared (`gone: 0`). The hazards (`choiceCore` and its
run lemmas; the step clock's private round induction) pair with nothing of this file.

**New in-file pairs: 122**, all between sibling declarations of this file, listed in full
below by family with the justification per family (`evidence/logs/screen-diff.txt`). They are the
mechanical siblings one bank of five tapes produces: the twenty one-line distinctness facts
`xr_*_ne_*`, the nine one-bank update lemmas (one `Function.update_self` case and four
`Function.update_of_ne` cases each), the leaf tables that differ in one transition, the two exits
of the replay read from the clock's two symmetric specifications, and the per-phase host lemmas,
which all instantiate the same four steps (row contract, first arrival, `xr_phase_step`, one bank
update). The 26 pairs at 90% or more are among these one-liners and sibling pairs
(listed at the end of the section). A generic "update one bank" lemma would fold the largest
family (59 pairs); it is left as it is because the nine lemmas are what `rw` needs to read a bank
literal, and a maintainer can fold them in one pass if wanted.

```
# copy-text screen v3: pair diff (after minus before)
before: # screen-before 2026-10-18T05:54:10Z at 9e77d2b26a62c3ee0c418a1e0a031c867c0ac80a
after:  declarations screened: 428; copy pairs (target reproduces >= half of source): 228; reproduced text: 66,673 chars
pairs before: 106; after: 228; gone: 0; new: 122
new cross-file pairs (any files): 0; new pairs with ExhaustiveReplay.lean on exactly one side: 0
new pairs not involving ExhaustiveReplay.lean: 0
## new in-file pairs of ExhaustiveReplay.lean, by family (target reproduces source: shared/source = %)
### bank distinctness one-liners (`xr_*_ne_*`: each is `Fin.ne_of_val_ne` on two `xr_*_val` facts): 20 pair(s)
    xr_cap_ne_dep reproduces xr_ctr_ne_dep: 67/69 = 97%
    xr_choice_ne_cap reproduces xr_ctr_ne_cap: 67/69 = 97%
    xr_choice_ne_dep reproduces xr_cap_ne_dep: 67/69 = 97%
    xr_choice_ne_dep reproduces xr_ctr_ne_dep: 67/69 = 97%
    xr_ctr_ne_dep reproduces xr_cap_ne_dep: 67/69 = 97%
    xr_work_ne_cap reproduces xr_ctr_ne_cap: 66/69 = 96%
    xr_work_ne_dep reproduces xr_cap_ne_dep: 66/69 = 96%
    xr_work_ne_dep reproduces xr_ctr_ne_dep: 66/69 = 96%
    xr_cap_ne_dep reproduces xr_work_ne_dep: 66/70 = 94%
    xr_choice_ne_cap reproduces xr_work_ne_cap: 66/70 = 94%
    xr_choice_ne_ctr reproduces xr_work_ne_ctr: 66/70 = 94%
    xr_choice_ne_dep reproduces xr_work_ne_dep: 66/70 = 94%
    xr_ctr_ne_cap reproduces xr_work_ne_cap: 66/70 = 94%
    xr_ctr_ne_dep reproduces xr_work_ne_dep: 66/70 = 94%
    xr_cap_ne_dep reproduces xr_choice_ne_dep: 67/72 = 93%
    xr_ctr_ne_cap reproduces xr_choice_ne_cap: 67/72 = 93%
    xr_ctr_ne_dep reproduces xr_choice_ne_dep: 67/72 = 93%
    xr_work_ne_cap reproduces xr_choice_ne_cap: 66/72 = 92%
    xr_work_ne_ctr reproduces xr_choice_ne_ctr: 66/72 = 92%
    xr_work_ne_dep reproduces xr_choice_ne_dep: 66/72 = 92%
### leaf row tables (`xr_*TM`: `xr_mv1`/`xr_stay` cases on the five control states): 4 pair(s)
    xr_testTM reproduces xr_rewindTM: 209/222 = 94%
    xr_extendTM reproduces xr_rewindTM: 167/222 = 75%
    xr_testTM reproduces xr_extendTM: 199/298 = 67%
    xr_rewindTM reproduces xr_extendTM: 167/298 = 56%
### buffer-tape facts (`xr_bufferTape_*`): 1 pair(s)
    xr_bufferTape_eq_none_iff reproduces xr_bufferTape_ge: 91/98 = 93%
### the window clear's pass (`xr_pass_*`: the two directions of one ruler-driven pass): 7 pair(s)
    xr_passTM reproduces xr_extendTM: 273/298 = 92%
    xr_extendTM reproduces xr_passTM: 273/303 = 90%
    xr_pass_left reproduces xr_pass_right: 180/228 = 79%
    xr_pass_right reproduces xr_pass_left: 180/231 = 78%
    xr_passTM reproduces xr_rewindTM: 167/222 = 75%
    xr_rewindTM reproduces xr_passTM: 167/303 = 55%
    xr_passTM_run reproduces xr_pass_fwd: 856/1571 = 54%
### the replay's two exits (`xr_replay_finish`/`xr_replay_timeout`: the clock's two specs read the same way): 4 pair(s)
    xr_replay_timeout reproduces xr_replay_finish: 992/1084 = 92%
    xr_replay_finish reproduces xr_replay_timeout: 992/1101 = 90%
    xr_replay_timeout reproduces xr_replay_state: 81/131 = 62%
    xr_replay_finish reproduces xr_replay_state: 80/131 = 61%
### per-phase host lemmas (`xr_*_host`: the row's run lemma, `xr_firstArrival'`, `xr_phase_step`, one bank update; the shared text is this four-step pattern): 7 pair(s)
    xr_extC_host reproduces xr_extD_host: 573/650 = 88%
    xr_extD_host reproduces xr_extC_host: 573/663 = 86%
    xr_test_host reproduces xr_crewind_host: 371/588 = 63%
    xr_crewind_host reproduces xr_test_host: 371/623 = 60%
    xr_extC_host reproduces xr_crewind_host: 335/588 = 57%
    xr_pass_host reproduces xr_extD_host: 355/650 = 55%
    xr_crewind_host reproduces xr_extC_host: 335/663 = 51%
### one-bank update lemmas (`xr_tapes_upd_*`, `xr_heads_upd_*`: `xr_bank_ext` with one `Function.update_self` and four `Function.update_of_ne` cases): 59 pair(s)
    xr_tapes_upd_ctr reproduces xr_tapes_upd_cap: 312/356 = 88%
    xr_tapes_upd_choice reproduces xr_tapes_upd_ctr: 315/365 = 86%
    xr_tapes_upd_cap reproduces xr_tapes_upd_ctr: 312/365 = 85%
    xr_tapes_upd_work reproduces xr_tapes_upd_ctr: 306/365 = 84%
    xr_heads_upd_cap reproduces xr_heads_upd_dep: 289/347 = 83%
    xr_heads_upd_choice reproduces xr_heads_upd_cap: 294/356 = 83%
    xr_heads_upd_work reproduces xr_heads_upd_cap: 294/356 = 83%
    xr_tapes_upd_cap reproduces xr_tapes_upd_dep: 289/347 = 83%
    xr_tapes_upd_choice reproduces xr_tapes_upd_cap: 294/356 = 83%
    xr_tapes_upd_ctr reproduces xr_tapes_upd_choice: 315/380 = 83%
    xr_tapes_upd_work reproduces xr_tapes_upd_cap: 294/356 = 83%
    xr_heads_upd_work reproduces xr_tapes_upd_work: 439/538 = 82%
    xr_tapes_upd_work reproduces xr_heads_upd_work: 439/538 = 82%
    xr_heads_upd_dep reproduces xr_heads_upd_cap: 289/356 = 81%
    xr_tapes_upd_dep reproduces xr_tapes_upd_cap: 289/356 = 81%
    xr_heads_upd_choice reproduces xr_tapes_upd_choice: 301/380 = 79%
    xr_tapes_upd_choice reproduces xr_heads_upd_choice: 301/380 = 79%
    xr_tapes_upd_ctr reproduces xr_tapes_upd_dep: 275/347 = 79%
    xr_heads_upd_cap reproduces xr_heads_upd_choice: 294/380 = 77%
    xr_heads_upd_cap reproduces xr_tapes_upd_cap: 274/356 = 77%
    xr_heads_upd_work reproduces xr_heads_upd_choice: 294/380 = 77%
    xr_heads_upd_work reproduces xr_heads_upd_dep: 268/347 = 77%
    xr_tapes_upd_cap reproduces xr_heads_upd_cap: 274/356 = 77%
    xr_tapes_upd_cap reproduces xr_tapes_upd_choice: 294/380 = 77%
    xr_tapes_upd_work reproduces xr_tapes_upd_choice: 294/380 = 77%
    xr_tapes_upd_work reproduces xr_tapes_upd_dep: 268/347 = 77%
    xr_heads_upd_dep reproduces xr_tapes_upd_dep: 265/347 = 76%
    xr_tapes_upd_dep reproduces xr_heads_upd_dep: 265/347 = 76%
    xr_tapes_upd_dep reproduces xr_tapes_upd_ctr: 275/365 = 75%
    xr_heads_upd_choice reproduces xr_heads_upd_dep: 258/347 = 74%
    xr_tapes_upd_choice reproduces xr_tapes_upd_dep: 258/347 = 74%
    xr_heads_upd_dep reproduces xr_heads_upd_choice: 258/380 = 68%
    xr_tapes_upd_dep reproduces xr_tapes_upd_choice: 258/380 = 68%
    xr_heads_upd_cap reproduces xr_tapes_upd_dep: 209/347 = 60%
    xr_tapes_upd_cap reproduces xr_heads_upd_dep: 209/347 = 60%
    xr_heads_upd_dep reproduces xr_tapes_upd_cap: 209/356 = 59%
    xr_tapes_upd_ctr reproduces xr_heads_upd_cap: 209/356 = 59%
    xr_tapes_upd_dep reproduces xr_heads_upd_cap: 209/356 = 59%
    xr_heads_upd_cap reproduces xr_tapes_upd_ctr: 209/365 = 57%
    xr_heads_upd_choice reproduces xr_tapes_upd_ctr: 207/365 = 57%
    xr_tapes_upd_ctr reproduces xr_tapes_upd_work: 306/538 = 57%
    xr_heads_upd_choice reproduces xr_tapes_upd_cap: 198/356 = 56%
    xr_tapes_upd_choice reproduces xr_heads_upd_cap: 198/356 = 56%
    xr_tapes_upd_ctr reproduces xr_heads_upd_dep: 195/347 = 56%
    xr_heads_upd_cap reproduces xr_heads_upd_work: 294/538 = 55%
    xr_heads_upd_choice reproduces xr_heads_upd_work: 294/538 = 55%
    xr_heads_upd_work reproduces xr_tapes_upd_choice: 209/380 = 55%
    xr_tapes_upd_cap reproduces xr_tapes_upd_work: 294/538 = 55%
    xr_tapes_upd_choice reproduces xr_tapes_upd_work: 294/538 = 55%
    xr_tapes_upd_work reproduces xr_heads_upd_choice: 209/380 = 55%
    xr_tapes_upd_ctr reproduces xr_heads_upd_choice: 207/380 = 54%
    xr_heads_upd_choice reproduces xr_tapes_upd_dep: 185/347 = 53%
    xr_heads_upd_dep reproduces xr_tapes_upd_ctr: 195/365 = 53%
    xr_heads_upd_work reproduces xr_tapes_upd_ctr: 192/365 = 53%
    xr_tapes_upd_choice reproduces xr_heads_upd_dep: 185/347 = 53%
    xr_heads_upd_cap reproduces xr_tapes_upd_choice: 198/380 = 52%
    xr_tapes_upd_cap reproduces xr_heads_upd_choice: 198/380 = 52%
    xr_heads_upd_work reproduces xr_tapes_upd_cap: 182/356 = 51%
    xr_tapes_upd_work reproduces xr_heads_upd_cap: 182/356 = 51%
### the two instances on the phase controls (eleven `inferInstanceAs` cases each): 2 pair(s)
    xr_PhSt_decEq reproduces xr_PhSt_fintype: 410/493 = 83%
    xr_PhSt_fintype reproduces xr_PhSt_decEq: 410/537 = 76%
### increment readers (`xr_inc_host_*`, `xr_incFixed_*`): 6 pair(s)
    xr_inc_host_succ reproduces xr_incD_host: 576/709 = 81%
    xr_incD_host reproduces xr_inc_host_succ: 576/731 = 79%
    xr_inc_host_overflow reproduces xr_inc_host_succ: 539/731 = 74%
    xr_inc_host_succ reproduces xr_inc_host_overflow: 539/747 = 72%
    xr_inc_host_overflow reproduces xr_incD_host: 414/709 = 58%
    xr_incD_host reproduces xr_inc_host_overflow: 414/747 = 55%
### first arrival at an anchor, for one anchor and for a predicate (`xr_firstArrival`, `xr_firstArrival'`: `Nat.find` and `xr_runFrom_fixed`): 2 pair(s)
    xr_firstArrival' reproduces xr_firstArrival: 320/405 = 79%
    xr_firstArrival reproduces xr_firstArrival': 320/480 = 67%
### the configurations between phases (`xr_cycle`, `xr_depthEnd`, `xr_replayStart`: one bank literal each): 5 pair(s)
    xr_depthEnd reproduces xr_cycle: 119/155 = 77%
    xr_cycle reproduces xr_replayStart: 99/139 = 71%
    xr_replayStart reproduces xr_cycle: 99/155 = 64%
    xr_depthEnd reproduces xr_replayStart: 81/139 = 58%
    xr_cycle reproduces xr_depthEnd: 119/219 = 54%
### other: 3 pair(s)
    xr_embed_eq reproduces xr_bank_ext: 160/208 = 77%
    xr_halt_fixed reproduces xr_phase_step: 437/693 = 63%
    xr_branch_inputPos_le reproduces xr_replay_state: 76/131 = 58%
### leaf action readers (`xr_act_apply`, `xr_mv1_apply*`, `xr_mv2_apply`): 1 pair(s)
    xr_answerTM_run reproduces xr_act_apply: 152/250 = 61%
### redirect-table readers (`xr_red_*`: `rfl`/`simp` on `xr_red`): 1 pair(s)
    xr_red_replay_timeout reproduces xr_red_replay_none: 74/135 = 55%
## new pairs at 90% or more: 26
    ExhaustiveReplay.lean::xr_cap_ne_dep reproduces ExhaustiveReplay.lean::xr_ctr_ne_dep: 67/69 = 97%
    ExhaustiveReplay.lean::xr_choice_ne_cap reproduces ExhaustiveReplay.lean::xr_ctr_ne_cap: 67/69 = 97%
    ExhaustiveReplay.lean::xr_choice_ne_dep reproduces ExhaustiveReplay.lean::xr_cap_ne_dep: 67/69 = 97%
    ExhaustiveReplay.lean::xr_choice_ne_dep reproduces ExhaustiveReplay.lean::xr_ctr_ne_dep: 67/69 = 97%
    ExhaustiveReplay.lean::xr_ctr_ne_dep reproduces ExhaustiveReplay.lean::xr_cap_ne_dep: 67/69 = 97%
    ExhaustiveReplay.lean::xr_work_ne_cap reproduces ExhaustiveReplay.lean::xr_ctr_ne_cap: 66/69 = 96%
    ExhaustiveReplay.lean::xr_work_ne_dep reproduces ExhaustiveReplay.lean::xr_cap_ne_dep: 66/69 = 96%
    ExhaustiveReplay.lean::xr_work_ne_dep reproduces ExhaustiveReplay.lean::xr_ctr_ne_dep: 66/69 = 96%
    ExhaustiveReplay.lean::xr_cap_ne_dep reproduces ExhaustiveReplay.lean::xr_work_ne_dep: 66/70 = 94%
    ExhaustiveReplay.lean::xr_choice_ne_cap reproduces ExhaustiveReplay.lean::xr_work_ne_cap: 66/70 = 94%
    ExhaustiveReplay.lean::xr_choice_ne_ctr reproduces ExhaustiveReplay.lean::xr_work_ne_ctr: 66/70 = 94%
    ExhaustiveReplay.lean::xr_choice_ne_dep reproduces ExhaustiveReplay.lean::xr_work_ne_dep: 66/70 = 94%
    ExhaustiveReplay.lean::xr_ctr_ne_cap reproduces ExhaustiveReplay.lean::xr_work_ne_cap: 66/70 = 94%
    ExhaustiveReplay.lean::xr_ctr_ne_dep reproduces ExhaustiveReplay.lean::xr_work_ne_dep: 66/70 = 94%
    ExhaustiveReplay.lean::xr_testTM reproduces ExhaustiveReplay.lean::xr_rewindTM: 209/222 = 94%
    ExhaustiveReplay.lean::xr_bufferTape_eq_none_iff reproduces ExhaustiveReplay.lean::xr_bufferTape_ge: 91/98 = 93%
    ExhaustiveReplay.lean::xr_cap_ne_dep reproduces ExhaustiveReplay.lean::xr_choice_ne_dep: 67/72 = 93%
    ExhaustiveReplay.lean::xr_ctr_ne_cap reproduces ExhaustiveReplay.lean::xr_choice_ne_cap: 67/72 = 93%
    ExhaustiveReplay.lean::xr_ctr_ne_dep reproduces ExhaustiveReplay.lean::xr_choice_ne_dep: 67/72 = 93%
    ExhaustiveReplay.lean::xr_passTM reproduces ExhaustiveReplay.lean::xr_extendTM: 273/298 = 92%
    ExhaustiveReplay.lean::xr_replay_timeout reproduces ExhaustiveReplay.lean::xr_replay_finish: 992/1084 = 92%
    ExhaustiveReplay.lean::xr_work_ne_cap reproduces ExhaustiveReplay.lean::xr_choice_ne_cap: 66/72 = 92%
    ExhaustiveReplay.lean::xr_work_ne_ctr reproduces ExhaustiveReplay.lean::xr_choice_ne_ctr: 66/72 = 92%
    ExhaustiveReplay.lean::xr_work_ne_dep reproduces ExhaustiveReplay.lean::xr_choice_ne_dep: 66/72 = 92%
    ExhaustiveReplay.lean::xr_extendTM reproduces ExhaustiveReplay.lean::xr_passTM: 273/303 = 90%
    ExhaustiveReplay.lean::xr_replay_finish reproduces ExhaustiveReplay.lean::xr_replay_timeout: 992/1101 = 90%
## pairs gone (before, not after): 0
```

## 9. Size, sweep, axioms, lint

- **File size:** 3,245 lines (base 110); 2 public declarations (the base's) and 183 private
  (`style_lint`'s INFO line). The lint's size WARN (`> 1000 lines`) is expected under ground
  rule 8 (no cap); the brief asks for the counts, recorded here.
- **The owned module** (`evidence/logs/final-sweep.log`, also `evidence/logs/owned-final-check.log`):
  zero errors, no sorry warning, no other warning:

```
(no diagnostics)
### TCSlib/Complexity/ClassNP/ExhaustiveReplay: start 2026-10-18T08:40:31Z end 2026-10-18T08:40:53Z wall 22.0s maxrss 2143 MiB exit 0
```

- **Stage 2 of the bootstrap** (the 47 downstream modules, `evidence/logs/bootstrap-stage2.log`):

```
# stage 2 (the 47 remaining modules of briefs/orders/c1-fill-exhaustive-cont1.txt) start 2026-10-18T08:11:49Z at 041c82ab05d5595e890e1d94cf375e435b2e50e4
…
### TCSlib/Complexity/CookLevin/Hardness: start 2026-10-18T08:19:13Z end 2026-10-18T08:29:00Z wall 587.0s maxrss 2692 MiB exit 0
### TCSlib/Complexity/ClassNP/Tautology: start 2026-10-18T08:29:00Z end 2026-10-18T08:29:10Z wall 10.0s maxrss 1917 MiB exit 0
### TCSlib/Complexity/ClassNP: start 2026-10-18T08:29:10Z end 2026-10-18T08:29:12Z wall 2.7s maxrss 1865 MiB exit 0
# stage 2 end 2026-10-18T08:29:12Z
```

- **The final sweep** over all 77 modules of `briefs/orders/c1-fill-exhaustive-cont1.txt`, in
  order, at the delivered tip (`evidence/logs/final-sweep.log`; every module exit 0; tail):

```
# final sweep (all 77 modules of briefs/orders/c1-fill-exhaustive-cont1.txt, in order) start 2026-10-18T08:29:12Z at 041c82ab05d5595e890e1d94cf375e435b2e50e4
…

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
### TCSlib/Complexity/CookLevin/Hardness: start 2026-10-18T08:44:21Z end 2026-10-18T08:53:57Z wall 576.3s maxrss 2716 MiB exit 0
### TCSlib/Complexity/ClassNP/Tautology: start 2026-10-18T08:53:57Z end 2026-10-18T08:54:07Z wall 10.2s maxrss 1914 MiB exit 0
### TCSlib/Complexity/ClassNP: start 2026-10-18T08:54:07Z end 2026-10-18T08:54:10Z wall 2.8s maxrss 1867 MiB exit 0
# final sweep end 2026-10-18T08:54:10Z
```

  Sorry warnings in the sweep against the base list
  (`audits/logs/c1-fill-exhaustive-cont1-base-sorries.txt`, 19 entries in 9 modules, recorded
  by name before the bootstrap): **exactly the base's minus `ClassNP/ExhaustiveReplay: FinNDTM.exists_exhaustiveDecider`** (18 entries in 8 modules; set equality checked by the assembler). Per module
  (`evidence/logs/final-sweep-sorries.txt`):

```
TuringMachine/Simulation: 1: branchTM_spaceUsed
TuringMachine/Composition: 3: idTM_computes, ifEqTM_computes, condTM_computes_iff
TuringMachine/Build/Wrappers: 2: timedCondTM_computes, timedCondTM_spaceUsed
TuringMachine/Build/Loop: 5: loopHostTM_contracts, loopHostTM_decides, loopHostTM_finds, loopHostTM_spaceUsed_le_budget, emitLoopTM_computes
TuringMachine/Encoding: 1: pairDiagTM_computes
ClassP/TimeConstructible: 2: _root_.Turing.FinTM.lengthBitsTM_computes, _root_.Turing.FinTM.lengthBitsTM_spaceUsed
TuringMachine/Build/Primitives: 3: polyUnaryTM_spaceUsed, unaryTokenTM_computes, appendBitTM_computes
ClassNP/NDNormalForm: 1: exists_codeNDTM_accepts_linear
TOTAL 18
```

  Other warnings in the sweep are the base's own linter notes in other modules
  (`unnecessarySeqFocus`, `unusedTactic` in `Configuration`, `ObliviousCandidate`,
  `ObliviousSetup`, …); none is in the owned module.

- **Axiom prints** (`evidence/logs/axioms.log`; the probe is the delivered file plus
  `#print axioms` for the two public declarations and every new private,
  `evidence/probes/ExhaustiveReplayAxioms-appendix.lean.txt`):

```
# axiom prints: probes/ExhaustiveReplayAxioms.lean is the delivered owned file plus `#print axioms` for the two
# public declarations and every new private (before `end Turing`), run through scripts/lean_check_tree.sh;
# private names print under the probe copy's `_private.probes.ExhaustiveReplayAxioms.0.Turing.` prefix.
# requested 185, printed 185, missing []; outside [propext, Classical.choice, Quot.sound]: 0 []; sorryAx present: no
# axiom-set histogram: {'propext, Classical.choice, Quot.sound': 100, 'propext, Quot.sound': 45, 'propext': 16, '(none)': 24}
# lean_check_tree verdict: ### probes/ExhaustiveReplayAxioms: start 2026-10-18T08:13:02Z end 2026-10-18T08:13:40Z wall 38.4s maxrss 2139 MiB exit 0; error lines: 0
'Turing.FinNDTM.exists_exhaustiveDecider' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.ndAcceptsWithin_decider_of_universal' depends on axioms: [propext, Classical.choice, Quot.sound]
```

- **Lint:** `python3 -I scripts/campaign_style_lint.py TCSlib/Complexity/ClassNP` →
  `style_lint: 0 FAIL, 16 WARN over 21 files` (base: 0 FAIL, 15 WARN; the one new WARN is this file's size, above). No line
  over 100 characters (measured in characters, `evidence/logs/line-widths.log`).

## 10. Every new declaration, with its role

# Declarations of `TCSlib/Complexity/ClassNP/ExhaustiveReplay.lean` at the delivered tip (185 total; the two public ones are the base's)

| line | kind | name | role (first sentence of the docstring) |
|---|---|---|---|
| 57 | private theorem | `xr_not_haltsWithin_zero` | No branch of length `0` has halted: `Cfg.init` is live. |
| 66 | private theorem | `xr_window_stepWith` | One step from the radius-`s` window stays in the radius-`s + 1` window, with the output growing by at most one symbol. |
| 103 | private theorem | `xr_window_runWith` | After a branch of length `\|w\|` from the initial configuration, every work head lies within `\|w\|` of its origin, every cell beyond radius `\|w\|` is blank, and the output has length at most `\|w\|`: the window the cle |
| 134 | private theorem | `xr_accepts_iff_of_halts` | At an all-halting depth `L ≤ T`, acceptance within `L` and within `T` agree: one direction is monotonicity, the other truncates an accepting word of length `T` at `L`. |
| 149 | private theorem | `xr_first_depth` | The first all-halting depth exists below any all-halting bound, is positive, and answers as the bound does: the deepening terminates by depth `T`, never at depth `0`. |
| 164 | private theorem | `xr_ledger` | The ledger's shape, with two steps of slack for the dispatch and the answer: `Σ_{L ≤ T} 2^L · A(L + 1) + 2 ≤ (A + 3)·2^{(A + 3)(T + 1)}`. |
| 194 | private def | `xr_shift` | The configuration `c` with work tape `i` translated by `δ i`: cell `p` holds what cell `p - δ i` held, and the head moves by `δ i`; the state, input head and output are `c`'s. |
| 200 | private theorem | `xr_inputSymbol_congr` | Two configurations with the same input head read the same input symbol. |
| 220 | private theorem | `xr_workTapeSymbols_shift` | A translated configuration reads the same work symbols. |
| 228 | private theorem | `xr_apply_shift` | Applying an action commutes with translation. |
| 255 | private theorem | `xr_stepWith_shift` | One nondeterministic step commutes with translation. |
| 268 | private theorem | `xr_runWith_shift` | A branch commutes with translation: the branch along `w` from a translated configuration is the translated branch. |
| 278 | private theorem | `xr_runFrom_fixed` | A configuration fixed by one step is fixed by every run. |
| 286 | private theorem | `xr_runFrom_one` | One step of a run. |
| 291 | private theorem | `xr_runFrom_two` | Two steps of a run. |
| 298 | private theorem | `xr_firstArrival` | **The first arrival at a stationary anchor.** If a run reaches `c'` in state `a` at time `T` and `a` is stationary, the first time the state is `a` is at most `T`, reaches `c'` too, and no earlier state is `a`: the phase |
| 319 | private inductive | `xr_St` | The control of the leaf rows. |
| 328 | private def | `xr_act` | A silent action: no input move and no emission. |
| 332 | private def | `xr_mv1` | Write `wr` and move `m` on tape `r` only. |
| 337 | private def | `xr_mv2` | Write `wr` and move `m` on tape `j`, move `m'` on tape `r`. |
| 342 | private def | `xr_stay` | The stationary action at `q`. |
| 345 | private theorem | `xr_cast_pos` | (no docstring: a one-line helper) |
| 346 | private theorem | `xr_cast_neg` | (no docstring: a one-line helper) |
| 349 | private theorem | `xr_act_apply` | A silent action's effect: the state, the writes under the heads, the head moves. |
| 367 | private theorem | `xr_mv1_apply` | A one-tape write-and-move. |
| 388 | private theorem | `xr_mv1_apply_none` | A one-tape move without a write. |
| 398 | private theorem | `xr_mv2_apply` | A two-tape move: a write-and-move on `j`, a move on `r`. |
| 426 | private theorem | `xr_stay_step` | A state whose table is the stationary action fixes every configuration in that state. |
| 442 | private theorem | `xr_back_run` | **The return pass** of the leaf rows. |
| 515 | private theorem | `xr_fwd_run` | **The forward scan** of the leaf rows: from `run` with the head at `o` and `m` non-blank cells ahead, `m` steps move the head to `o + m` and change nothing else. |
| 562 | private def | `xr_rewindTM` | **The rewind**: one step left, then left while reading a symbol, then one step right at the blank. |
| 575 | private theorem | `xr_rewindTM_run` | From any head position `p₀ ≤ \|u\|` on the word `u` at the origin, the rewind returns the head to `0` in `p₀ + 2` steps, changes nothing else, and stops at `done true`. |
| 608 | private def | `xr_extendTM` | **The extension**: right while reading a symbol, write `false` at the blank and turn, return to the origin: the word grows by one `false`. |
| 624 | private theorem | `xr_extendTM_run` | From the origin of the word `u`, the extension writes `u ++ [false]` in `2\|u\| + 2` steps, returns the head to `0`, changes nothing else, and stops at `done true`. |
| 689 | private theorem | `xr_bufferTape_neg` | A stored word is blank at every negative cell. |
| 698 | private theorem | `xr_bufferTape_ge` | A stored word is blank at and beyond its length. |
| 705 | private theorem | `xr_bufferTape_eq_none_iff` | A stored word is blank exactly off `[0, \|v\|)`. |
| 719 | private theorem | `xr_bufferTape_ne_none` | A stored word is non-blank on `[0, \|v\|)`. |
| 725 | private theorem | `xr_bufferTape_pop` | Blanking the last symbol of a stored word stores its prefix. |
| 732 | private theorem | `xr_clear_fun` | The return pass over a stored word with the blanking write clears it entirely. |
| 746 | private def | `xr_passTM` | **The pass** (the window clear's engine). |
| 762 | private theorem | `xr_pass_fwd` | The pass's forward phase: after `m ≤ \|u\|` steps, head `j` has moved `m` cells along `dir`, blanking the cells it left, and the ruler head is at `m`. |
| 839 | private theorem | `xr_passTM_run` | **The pass's contract.** From the origin of the ruler word `u`, `2\|u\| + 2` steps move head `j` by `\|u\|` cells along `dir`, blank the `\|u\| + 1` cells it visited, return the ruler head to `0`, change nothing else, an |
| 936 | private def | `xr_testTM` | **The capture test.** From the end of the captured output, step left and read the last symbol: blank (an empty output) exits `done false`; `true` steps left once more and exits `done true` at a blank there (the output wa |
| 958 | private theorem | `xr_test_tail` | The test's clearing tail: from `back false` at the end of the stored word `v`, `\|v\| + 1` steps blank it, return the head to `0`, and stop at `done false`. |
| 973 | private theorem | `xr_testTM_run` | **The capture test's contract.** With the output `out` stored at the origin and the head at its end, `\|out\| + 2` steps clear it, return the head to `0`, change nothing else, and stop at `done true` exactly when `out =  |
| 1144 | private def | `xr_inRewindTM` | **The input rewind**: a left step, then left while the input head reads a symbol, then one step right at the left blank. |
| 1156 | private def | `xr_answerTM` | **The answer**: emit `b` and halt. |
| 1161 | private theorem | `xr_answerTM_run` | The answer's contract: one step from any live state emits `b` and halts. |
| 1188 | private structure | `xr_Clock` | **The step clock over the replay machine.** The control `Q`, the clocked machine `H` on `N.k + 2` tapes (the counter last), the injection of the replay's states, the two exit families, and the clock's two exits: `finish  |
| 1224 | private theorem | `xr_stopped_iff` | With no stop state, a body configuration is stopped exactly when it is halted. |
| 1231 | private theorem | `xr_Clock.exists` | The clock exists: `Turing.exists_stepClockTMVia` at `Γ = Bool`, the identity embedding and no stop state, with its two exits read. |
| 1262 | private def | `xr_ι` | The clocked replay's bank, as the first `k + 2` tapes. |
| 1265 | private def | `xr_cap` | The capture tape. |
| 1268 | private def | `xr_dep` | The depth tape. |
| 1271 | private def | `xr_work` | `N`'s work tape `j`. |
| 1274 | private def | `xr_choice` | The choice tape. |
| 1277 | private def | `xr_ctr` | The clock's counter tape. |
| 1280 | private def | `xr_tapes` | `E`'s work tapes from their five banks. |
| 1286 | private def | `xr_heads` | `E`'s work heads from their five banks. |
| 1290 | private theorem | `xr_tapes_work` | (no docstring: a one-line helper) |
| 1294 | private theorem | `xr_tapes_choice` | (no docstring: a one-line helper) |
| 1298 | private theorem | `xr_tapes_ctr` | (no docstring: a one-line helper) |
| 1302 | private theorem | `xr_tapes_cap` | (no docstring: a one-line helper) |
| 1306 | private theorem | `xr_tapes_dep` | (no docstring: a one-line helper) |
| 1310 | private theorem | `xr_heads_work` | (no docstring: a one-line helper) |
| 1314 | private theorem | `xr_heads_choice` | (no docstring: a one-line helper) |
| 1318 | private theorem | `xr_heads_ctr` | (no docstring: a one-line helper) |
| 1322 | private theorem | `xr_heads_cap` | (no docstring: a one-line helper) |
| 1326 | private theorem | `xr_heads_dep` | (no docstring: a one-line helper) |
| 1331 | private theorem | `xr_cap_not_mem` | The capture tape is outside the clocked replay's bank. |
| 1338 | private theorem | `xr_dep_not_mem` | The depth tape is outside the clocked replay's bank. |
| 1344 | private theorem | `xr_dep_ne_cap` | (no docstring: a one-line helper) |
| 1350 | private theorem | `xr_addCases_split` | Every index of `Fin (m + n)` is a left or a right index. |
| 1357 | private theorem | `xr_lastCases_split` | Every index of `Fin (n + 1)` is the last one or a cast. |
| 1362 | private theorem | `xr_fin2` | (no docstring: a one-line helper) |
| 1368 | private theorem | `xr_embed_eq` | **The embedded clocked configuration, by banks**: the clocked replay configuration over `N`'s configuration `c`, the choice tape and the counter, embedded silently with the capture tape and the depth tape, is the explici |
| 1430 | private theorem | `xr_wordPatch_buffer` | Patching a same-width word over a stored word at the origin stores the new word. |
| 1441 | private def | `xr_replayTM` | **The replay phase**: the clocked replay, embedded silently with the capture tape. |
| 1448 | private def | `xr_replayStart` | `E` at the start of a replay of the choice word `s` under the budget word `w`: the clock at the replay's initial state, `N`'s tapes blank with their heads at `h`, the input head at `1`, the capture tape blank, the depth  |
| 1457 | private theorem | `xr_replayStart_eq` | The replay's start is the embedded clocked configuration over the translated initial configuration of `N`. |
| 1487 | private theorem | `xr_replay_state` | The replay's body states along the choice word are `N`'s branch states. |
| 1502 | private theorem | `xr_replay_finish` | **One replay, the `finish` exit.** If the branch along `s` first halts at `τ ≤ \|s\|`, and the budget word `w` has value `\|s\|`, the replay phase reaches, within `5τ + 2\|w\| + 2` steps and with no earlier exit, the exi |
| 1547 | private theorem | `xr_replay_timeout` | **One replay, the `timeout` exit.** If the branch along `s` is still live after `\|s\|` steps (and so at every earlier time), and the budget word `w` has value `\|s\|`, the replay phase reaches, within `7\|s\| + 2\|w\| + |
| 1600 | private theorem | `xr_firstArrival'` | **The first arrival at a stationary anchor, over a family of anchors.** If every state in `A` is stationary and a run reaches `c'` in a state of `A` at time `T`, the first time the state is in `A` is at most `T`, reaches |
| 1619 | private theorem | `xr_done_stationary` | Every `done` anchor of a leaf row whose table is stationary there is stationary. |
| 1627 | private theorem | `xr_work_val` | (no docstring: a one-line helper) |
| 1629 | private theorem | `xr_choice_val` | (no docstring: a one-line helper) |
| 1631 | private theorem | `xr_ctr_val` | (no docstring: a one-line helper) |
| 1633 | private theorem | `xr_cap_val` | (no docstring: a one-line helper) |
| 1635 | private theorem | `xr_dep_val` | (no docstring: a one-line helper) |
| 1638 | private theorem | `xr_work_ne_choice` | (no docstring: a one-line helper) |
| 1640 | private theorem | `xr_work_ne_ctr` | (no docstring: a one-line helper) |
| 1642 | private theorem | `xr_work_ne_cap` | (no docstring: a one-line helper) |
| 1644 | private theorem | `xr_work_ne_dep` | (no docstring: a one-line helper) |
| 1646 | private theorem | `xr_choice_ne_ctr` | (no docstring: a one-line helper) |
| 1648 | private theorem | `xr_choice_ne_cap` | (no docstring: a one-line helper) |
| 1650 | private theorem | `xr_choice_ne_dep` | (no docstring: a one-line helper) |
| 1652 | private theorem | `xr_ctr_ne_cap` | (no docstring: a one-line helper) |
| 1654 | private theorem | `xr_ctr_ne_dep` | (no docstring: a one-line helper) |
| 1656 | private theorem | `xr_cap_ne_dep` | (no docstring: a one-line helper) |
| 1658 | private theorem | `xr_work_injective` | (no docstring: a one-line helper) |
| 1665 | private theorem | `xr_bank_ext` | Two functions on `E`'s tape indices agree when they agree on every bank. |
| 1682 | private theorem | `xr_tapes_upd_work` | (no docstring: a one-line helper) |
| 1697 | private theorem | `xr_tapes_upd_choice` | (no docstring: a one-line helper) |
| 1707 | private theorem | `xr_tapes_upd_ctr` | (no docstring: a one-line helper) |
| 1717 | private theorem | `xr_tapes_upd_cap` | (no docstring: a one-line helper) |
| 1727 | private theorem | `xr_tapes_upd_dep` | (no docstring: a one-line helper) |
| 1737 | private theorem | `xr_heads_upd_work` | (no docstring: a one-line helper) |
| 1752 | private theorem | `xr_heads_upd_choice` | (no docstring: a one-line helper) |
| 1762 | private theorem | `xr_heads_upd_cap` | (no docstring: a one-line helper) |
| 1771 | private theorem | `xr_heads_upd_dep` | (no docstring: a one-line helper) |
| 1782 | private theorem | `xr_patch_eq` | **The catalog rows' result tape.** A row that rewrites the cells `[0, \|w\|)` of a bank holding the word `w` at the origin with a same-width word `v` leaves that bank holding `v`. |
| 1801 | private def | `xr_val` | The value of a binary word, little-endian. |
| 1803 | private theorem | `xr_val_nil` | (no docstring: a one-line helper) |
| 1806 | private theorem | `xr_val_cons` | (no docstring: a one-line helper) |
| 1810 | private theorem | `xr_val_lt` | (no docstring: a one-line helper) |
| 1815 | private theorem | `xr_val_inj` | (no docstring: a one-line helper) |
| 1828 | private theorem | `xr_val_append_false` | (no docstring: a one-line helper) |
| 1831 | private theorem | `xr_val_replicate_false` | (no docstring: a one-line helper) |
| 1836 | private theorem | `xr_val_replicate_true` | (no docstring: a one-line helper) |
| 1842 | private theorem | `xr_incFixed_val` | The increment adds one to the value. |
| 1858 | private theorem | `xr_incFixed_none_max` | At the overflow the word is all `true`, so every same-length word has a value at most its. |
| 1868 | private theorem | `xr_incFixed_append_false` | A word not entirely `true` increments. |
| 1881 | private inductive | `xr_Ph` | The phases of the exhaustive replay. |
| 1907 | private abbrev | `xr_I` | The phase index: a phase with the two flags "some branch accepted" and "some branch is live". |
| 1910 | private def | `xr_PhSt` | Each phase's control. |
| 1923 | private instance | `xr_PhSt_fintype` | (no docstring: a one-line helper) |
| 1937 | private instance | `xr_PhSt_decEq` | (no docstring: a one-line helper) |
| 1952 | private def | `xr_dir` | The direction of pass `n`: the first two passes move left, the last four right. |
| 1955 | private def | `xr_idleTM` | The idle row: stationary everywhere (the `halt` phase, which the host never steps). |
| 1960 | private def | `xr_M` | The phase machines. |
| 1975 | private def | `xr_firstPass` | The first phase of the window clear (the increment when `N` has no work tape). |
| 1979 | private def | `xr_afterPass` | The phase after pass `n` of tape `j`: the next pass, the next tape, or the increment. |
| 1987 | private def | `xr_redDone` | The redirect of a leaf row's anchor `done b` at phase `i`, when the phase redirects on a `done` state at all. |
| 2000 | private def | `xr_red` | The redirect table. |
| 2024 | private def | `xr_host` | **The host of the exhaustive replay**: the phase host over the phases above, starting at the copy with both flags down. |
| 2032 | private theorem | `xr_phase_step` | **One phase of the host.** If phase `i`, started at `s₀` over the tapes `tp` and heads `hd`, reaches `c'` in `T` steps, `c'` is in a state `s'` that the table redirects to `q'`, and no earlier state is redirected, then t |
| 2072 | private def | `xr_cycle` | `E` at the start of a cycle at depth `\|s\|`: the copy phase with the flags `a` and `l`, the depth word `wL` on the depth tape, the choice word `s`, some word `u` on the counter, the capture tape blank, `N`'s tapes blank |
| 2081 | private def | `xr_depthEnd` | `E` at the end of a depth, after the choice word's overflow: the deepening when some branch was live, else the answer; the choice tape holds the all-`false` word again. |
| 2090 | private theorem | `xr_branch_inputPos_le` | A branch of length `\|s\|` moves the input head at most `\|s\|` cells from its start at `1` (through the replay machine and `Turing.MultiTapeTM.timed_input_bound`). |
| 2101 | private theorem | `xr_red_copy_done` | (no docstring: a one-line helper) |
| 2105 | private theorem | `xr_red_copy_none` | (no docstring: a one-line helper) |
| 2109 | private theorem | `xr_red_replay_finish` | (no docstring: a one-line helper) |
| 2115 | private theorem | `xr_red_replay_timeout` | (no docstring: a one-line helper) |
| 2122 | private theorem | `xr_red_replay_none` | (no docstring: a one-line helper) |
| 2128 | private theorem | `xr_red_leaf_none` | The phases run by a leaf row redirect only at a `done` anchor. |
| 2144 | private theorem | `xr_copy_host` | **The copy phase on the host.** From the start of a cycle, `2\|wL\| + 3` steps copy the depth word onto the counter and dispatch to the replay. |
| 2173 | private theorem | `xr_replay_host` | **The replay phase on the host.** From the copy's end, the clocked replay of the choice word `s` runs, within `5\|s\| + 2\|wL\| + 3` steps, to the capture test, raising the live flag exactly when the branch along `s` is  |
| 2231 | private theorem | `xr_test_host` | **The capture test on the host.** With the output `out` captured, within `\|out\| + 3` steps the host clears it, returns the capture head, raises the accept flag exactly when `out = [true]`, and dispatches to the choice  |
| 2256 | private theorem | `xr_crewind_host` | **The choice rewind on the host.** With the choice head at `p ≤ \|s\|`, within `p + 3` steps the host returns it to the origin and dispatches to the input rewind. |
| 2281 | private theorem | `xr_irewind_host` | **The input rewind on the host.** Within `inputPos + 3` steps the host returns the input head to `1` and dispatches to the window clear (or to the increment when `N` has no work tape). |
| 2303 | private theorem | `xr_inc_host_succ` | **The increment on the host, a successor.** When `incFixed s = some s'`, within `2\|s\| + 3` steps the host writes `s'` on the choice tape and dispatches to the next cycle. |
| 2330 | private theorem | `xr_inc_host_overflow` | **The increment on the host, the overflow.** When `incFixed s = none`, `2\|s\| + 3` steps leave the all-`false` word on the choice tape and dispatch to the depth's end. |
| 2358 | private def | `xr_Win` | Content within radius `R` of the cell `a`. |
| 2362 | private def | `xr_Blank` | Blank on `[lo, hi]`. |
| 2365 | private theorem | `xr_dir_cast` | (no docstring: a one-line helper) |
| 2371 | private def | `xr_passStart` | The phase at which the window clear of tape `m` starts (the increment when `m = N.k`). |
| 2375 | private theorem | `xr_firstPass_eq` | (no docstring: a one-line helper) |
| 2378 | private theorem | `xr_afterPass_last` | (no docstring: a one-line helper) |
| 2386 | private theorem | `xr_pass_host` | **One pass on the host.** From the start of pass `n` of tape `j`, within `2\|wL\| + 3` steps head `j` moves `\|wL\|` cells along the pass's direction, the cells between its start and its end are blanked, the ruler head r |
| 2421 | private theorem | `xr_pass_left` | A leftward pass: head `j` moves `\|wL\|` cells left and `[hk j - \|wL\|, hk j]` is blanked. |
| 2440 | private theorem | `xr_pass_right` | A rightward pass: head `j` moves `\|wL\|` cells right and `[hk j, hk j + \|wL\|]` is blanked. |
| 2459 | private theorem | `xr_Blank_mono` | Blank cells stay blank under a pass. |
| 2467 | private theorem | `xr_none_mono` | A blank cell stays blank under a pass. |
| 2477 | private theorem | `xr_clearTape_host` | **The window clear of one tape on the host.** From the start of pass `0` of tape `j`, whose content lies within radius `2\|wL\|` of its head, within `6(2\|wL\| + 3)` steps the six passes blank the tape and move its head  |
| 2559 | private theorem | `xr_clear_host` | **The window clear on the host, from tape `N.k - m` on.** The tapes `N.k - m, …, N.k - 1`, each with its content within radius `2\|wL\|` of its head, are blanked within `m·6(2\|wL\| + 3)` steps, after which the host is a |
| 2630 | private theorem | `xr_branch_win` | The branch along `s` keeps `N`'s tapes within radius `2\|s\|` of its translated heads. |
| 2650 | private theorem | `xr_cycle_host` | **One cycle on the host.** From the start of a cycle at depth `L = \|s\|` (the depth word has value `L` and width `L`, the counter width at most `L`), within `(18 N.k + 19)(L + 1)` steps the host replays the choice word  |
| 2747 | private theorem | `xr_depth_host` | **One depth on the host.** From the cycle at the word `s`, with `m = 2^L - val s` words of depth `L` left to replay, the host runs through them to the depth's end within `m·(18 N.k + 19)(L + 1)` steps; the accept flag en |
| 2841 | private theorem | `xr_extC_host` | **The choice word's extension on the host**: within `2\|s\| + 3` steps a `false` is appended to the choice word and the host dispatches to the depth word's extension. |
| 2867 | private theorem | `xr_extD_host` | **The depth word's extension on the host**: within `2\|wL\| + 3` steps a `false` is appended to the depth word and the host dispatches to its increment. |
| 2893 | private theorem | `xr_incD_host` | **The depth word's increment on the host**: with `incFixed w = some w'`, within `2\|w\| + 3` steps the depth tape holds `w'` and the host dispatches to the next depth's first cycle. |
| 2923 | private theorem | `xr_deepen_host` | **The depth change on the host.** From a depth's end with the live flag up, within `6L + 11` steps the host extends the choice word to the all-`false` word of length `L + 1`, extends and increments the depth word to a wo |
| 2946 | private theorem | `xr_halt_fixed` | The halt phase's `start` is stationary on the host: the table redirects it to itself. |
| 2983 | private theorem | `xr_run_host` | **The depths on the host.** With `L*` the first all-halting depth, from the first cycle at a depth `L ≤ L*` (the depth word of width and value `L`, the choice word all `false`, the counter word of width at most `L`, both |
| 3054 | private theorem | `xr_tapes_blank` | The blank tape bank. |
| 3061 | private theorem | `xr_heads_zero` | The heads at the origin. |
| 3066 | private def | `xr_anchor` | The host's halt anchor with the accept flag `b`. |
| 3071 | private def | `xr_seam` | The two-exit seam of the host onto the two one-step answers: at the anchor with the accept flag up, the answer `[true]`; at the anchor with it down, the answer `[false]`. |
| 3077 | private def | `xr_E` | **The exhaustive replay's machine `E`**: the seam, started at the host's first cycle. |
| 3083 | private theorem | `xr_E_initCfg` | `E`'s initial configuration on `z` is the host's first cycle at depth `0`, in the seam's states. |
| 3104 | private theorem | `xr_answer_tail` | **The answer's tail.** From a live configuration with empty output, one step of the answer row halts with the output `[b]`, read in any renaming of the states. |
| 3135 | public theorem | `FinNDTM.exists_exhaustiveDecider` | **The exhaustive replay `E`.** For every bundled binary NDTM `N` there is a deterministic machine `E` and a constant `C` such that, on every input `z` on which every branch of `N` of length `T` has halted (any `T`, which |
| 3214 | public theorem | `ndAcceptsWithin_decider_of_universal` | **The exponential decider from the universal NDTM**, `BF := E(UN)`: if `UN` is a timed universal NDTM for the scheme `c` (the statement of `Turing.exists_timed_universal_NDTM`), then there is a deterministic machine `BF` |

## 11. Contents of the zip

- `REPORT.md` (this file); `source/TCSlib/Complexity/ClassNP/ExhaustiveReplay.lean` (the full
  modified source at the tip).
- `patches/` — `git format-patch` series against the base (`16` patches);
  `fill-c1-exhaustive-cont1.bundle` — a git bundle of `fill/c1-exhaustive-cont1` whose only
  prerequisite is the base `9e77d2b2…` (`git bundle verify` output in `evidence/logs/bundle-verify.log`).
- `evidence/logs/` — `preflight.log`, `toolchain.log`, `cache-get.log`, `cache-probe*.log`,
  `bootstrap-split.txt`, `bootstrap-stage1.log`, `bootstrap-stage2.log`, `final-sweep.log`,
  `owned-final-check.log`, `axioms-raw.log`, `axioms.log`, `import-probe.log`, `lint.log`,
  `line-widths.log`, `screen-before.txt`, `screen-after.txt`, `screen-diff.txt`,
  `rule11-greps.log`, `base-and-ancestor.log`, `bundle-verify.log`, `check-chunk1.log`.
- `evidence/probes/` — the extended import probe and the axiom probe's appendix.
- `evidence/declarations.md` — the declaration table of §10.
- `SHA256SUMS` — over every file of the zip.
