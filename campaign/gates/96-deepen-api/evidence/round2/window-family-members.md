# The window family: candidate members across the campaign tip and every ref

The user acknowledged on 2026-11-05, by kind, the family **"every proof that one action keeps a
configuration in a window, and window monotonicity"** (gate 96, finding 2). This file enumerates
its candidate members. Candidate enumeration plus inspection, not an exhaustive search.

**Ruled after this enumeration (the user, 2026-11-05):** the family is **widened by kind** to every
proof that one step keeps a configuration within a window of any shape, so section B's members
belong to it, and the tape half becomes a third canonical statement, to be published in the 12.2c
window (`campaign/duplication-ledger.md`, WS-1). Run by a sub-agent of the cloud maintainer
session and reviewed by the maintainer.

**Canonical statements** (PR #196, repaired head `f2616fee`, `TuringMachine/Build/CfgRecord.lean`):
- `Turing.Cfg.InWindow.mono` (118): `c.InWindow s → s ≤ s' → c.InWindow s'`;
- `Turing.Cfg.InWindow.apply_iff` (130): for `c.InWindow s`, `(a.apply c).InWindow s ↔ ∀ i,
  ¬(c.workTapePos i = -s ∧ (a.workTapes i).2 = -1) ∧ ¬(c.workTapePos i = s ∧ (a.workTapes i).2 =
  1)` (the harvested `recordStep_window`);
- their corollary `Turing.Cfg.InWindow.apply_of_lt` (5717): heads strictly inside `[-s', s']`,
  `s ≤ s'` ⇒ `(a.apply C).InWindow s'`.

`Cfg.InWindow s c` is `(∀ i, |c.workTapePos i| ≤ s) ∧ ∀ i z, s < |z| → c.workTapes i z = none`. A
proof of the kind has a **head half** (a head moves at most one cell, so it stays inside unless it
crosses a boundary) and a **tape half** (the write lands under the old head, inside the window, so
every cell outside stays blank: `Action.apply_workTapes` and `Function.update_of_ne`).

## Commands

Every command was run as `. /home/user/tcslib-scratch/env.sh; …`, from `/home/user/tcslib`.
`S` is `$TCSLIB_SCRATCH/agents/sweeps`. The index `$S/raw/ref-blobs.tsv` (340 refs, 2,119 distinct
`.lean` blobs) and `shape_grep.py` are those of `gate96-shape-search.md`.

```sh
# 1. window-named definitions and theorems, every ref
python3 -I $S/shape_grep.py $S/raw/ref-blobs.tsv $S/raw/pat-window-defs.tsv \
  f2616fee=f2616fee1d41f75600bc9070db149d32a0c69acc > $S/raw/out-window-defs.txt
#    pat-window-defs.tsv:
#    defs-window       ^\s*(private |protected |noncomputable )*(def|abbrev|structure|inductive|class)\s+\S*([Ww]indow|[Ww]in[A-Z]|inWin)
#    thm-names-window  ^\s*(private |protected )*(theorem|lemma)\s+\S*([Ww]indow|inWin|[Ww]in[A-Z_]|boundary)
# 2. declarations mentioning a window predicate (InWindow / InWin / inWin_ / the two clauses
#    written out) together with an action or step expansion, or a radius growth
python3 -I $S/window_decls.py $S/raw/ref-blobs.tsv f2616fee=f2616fee1d41f75600bc9070db149d32a0c69acc \
  10c01517=10c015177fde0f9f2b020c010cf44f0f3b3dd37f > $S/raw/out-window-decls.tsv        # 38 rows
python3 -I $S/window_decls_wide.py $S/raw/ref-blobs.tsv f2616fee=f2616fee1d41f75600bc9070db149d32a0c69acc \
  10c01517=10c015177fde0f9f2b020c010cf44f0f3b3dd37f > $S/raw/out-window-decls-wide.tsv   # 82 rows
#    (wide: also `step_le`, `step_eq_of_ne`, `workTapes_step`, `stepWith`, `.step …`, `runFrom_succ`,
#     `((n + 1 : ℕ) : ℤ)`, `≤ |z| →` blank clauses)
# 3. the tape half by declaration: an action's write + `update_of_ne` + `= none` + a head bound
python3 -I $S/tapehalf_decls.py $S/raw/ref-blobs.tsv > $S/raw/out-tapehalf.tsv            # 8 rows
# 4. radius and interval windows written out, and their step lemmas, every ref
python3 -I $S/shape_grep.py $S/raw/ref-blobs.tsv $S/raw/pat-radius.tsv \
  f2616fee=f2616fee1d41f75600bc9070db149d32a0c69acc > $S/raw/out-radius.txt
python3 -I $S/shape_grep.py $S/raw/ref-blobs.tsv $S/raw/pat-radius2.tsv \
  f2616fee=f2616fee1d41f75600bc9070db149d32a0c69acc > $S/raw/out-radius2.txt
#    pat-radius.tsv:
#    R1-blank-outside        (<|≤) \|[a-z]\| → [^\n]*workTapes[^\n]*= none|(<|≤) \|[a-z]\| → [^\n]*= none
#    R2-step-radius-names    step_radius|runFrom_radius|runWith_radius|headBlank|apply_workTapes_eq_of_ne|workTapes_step_eq_of_ne|workTapePos_step_le|stepWith_radius
#    pat-radius2.tsv:
#    R3-blank-outside-interval  z < -\(?[\w ]+(: ℤ\))? ∨ [^\n]*< z|< z ∨ z < -|natAbs[^\n]*→[^\n]*= none|\| > [^\n]*→[^\n]*= none
#    R4-step-blank-inline       Function\.update_of_ne hne\]?$|update_of_ne hzp|update_of_ne hzhead|update_of_ne hz'?\]?$
# 5. tip declarations that combine a head-move fact with a blank cell
T=origin/complexity/arora-barak-ch3-4
for f in $(git grep -l -E 'workTapePos_step_le|workTapePos_apply_le|apply_workTapes_eq_of_ne|workTapes_step_eq_of_ne' $T -- 'TCSlib/*.lean' | sed "s#^$T:##"); do
  git show $T:$f | python3 -I -c '
import sys,re
f=sys.argv[1]; L=sys.stdin.read().split("\n")
H=re.compile(r"^\s*(?:@\[[^\]]*\]\s*)?(?:private |protected |noncomputable )*(theorem|lemma|def)\s+(\S+)")
st=[(i,m.group(2)) for i,l in enumerate(L) for m in [H.match(l)] if m]
for n,(i,nm) in enumerate(st):
  j=st[n+1][0] if n+1<len(st) else len(L)
  b="\n".join(L[i:j])
  if re.search(r"workTapePos_step_le|workTapePos_apply_le|apply_workTapes_eq_of_ne|workTapes_step_eq_of_ne",b) and re.search(r"= none",b):
    print(f"{f}:{i+1}\t{nm}")
' $f; done
#    -> ExhaustiveReplay 67 xr_window_stepWith, Loop 3383 emCall_track_run, Oracle 346 step_radius,
#       Oracle 417 queryString_eq_of_cells, Sweep 359 source_bounds
# 6. which member files can cite CfgRecord (text-only import closure at the tip)
python3 -I - "$T" <<'EOF'
import sys,subprocess,re
T=sys.argv[1]
def imports(mod):
    r=subprocess.run(['git','show',f'{T}:'+mod.replace('.','/')+'.lean'],capture_output=True,text=True)
    return None if r.returncode else [m.group(1) for m in re.finditer(r'^import\s+(\S+)',r.stdout,re.M)]
def closure(root):
    seen=set(); st=[root]
    while st:
        m=st.pop()
        if m in seen: continue
        seen.add(m); im=imports(m)
        if im: st.extend(i for i in im if i.startswith('TCSlib'))
    return seen
tgt='TCSlib.Complexity.TuringMachine.Build.CfgRecord'
for f in ['ClassNP.ExhaustiveReplay','ClassPSPACE.TQBF','TuringMachine.Sweep','TuringMachine.Oracle',
          'TuringMachine.Robustness.SingleTape','TuringMachine.Build.Loop',
          'SpaceComplexity.ExpBFS.Radius','SpaceComplexity.Codec.Step']:
    c=closure('TCSlib.Complexity.'+f); print(f, tgt in c, len(c))
EOF
#    -> CfgRecord is in the closure of TQBF, Radius and Codec/Step only
# 7. ref counts of the member headers (remote refs only)
python3 -I $S/shape_grep.py $S/raw/ref-blobs.tsv $S/raw/pat-members.tsv
#    pat-members.tsv: M-headers  (theorem|lemma) (inWin_mono|inWin_stepWith|boundary_iff|recordStep_window|codec_step_blank|xr_window_stepWith|source_bounds|step_radius|dgWindow_step|emCall_track_support|emCall_track_extent|apply_workTapes_eq_of_ne)\b
```

The S1 (monotonicity) and S2 (action keeps a window) shape patterns of `gate96-shape-search.md`
were also used. Every flagged declaration was read at the tip (or on the ref named). Ref counts in the tables count remote refs holding the declaration's header line (step 7); `gate96-shape-search.md`'s counts also include the local `f2616fee` tree, hence one more.

## A. Members on `Cfg.InWindow` itself

| # | Declaration (tip line) | Owner | Refs | What it proves | Against the canonical statements |
|---|---|---|---|---|---|
| A1 | `Complexity.ExpBFS.inWin_mono` (`SpaceComplexity/ExpBFS/Radius.lean`:63) | Hydroxyi | tip, 207 | window monotonicity, for `FinNDTM` configurations | `Cfg.InWindow.mono` verbatim (same proof text). **Named by the auditor** |
| A2 | `Complexity.ExpBFS.inWin_stepWith` (Radius:70) | Hydroxyi | tip, 207 | one choice step from window `s` lands in window `s + 1` (halted: `inWin_mono`; live: `workTapePos_apply_le` and `abs_le` for heads, `simp only [Action.apply]` and `update_of_ne` for cells) | corollary of `apply_of_lt` at `s' = s + 1` (live) and `mono` (halted). **Named** |
| A3 | `Complexity.Codec.boundary_iff`, window half (`SpaceComplexity/Codec/Step.lean`:195–244) | Hydroxyi | tip, 207 | `(∀ i, move = .neg → pos ≠ -s) ∧ (∀ i, move = .pos → pos ≠ s) ↔ InWindow s (a.apply C)`, re-proved by `simp only [Action.apply]`, `abs_le`, `update_of_ne` | `apply_iff` up to the form of the boundary condition. **Named** |
| A4 | `Turing.recordStep_window` (private, `TuringMachine/Build/CfgRecord.lean`:677) | campaign | tip, 289 | `apply_iff` for `Bool` configurations | the source of the harvest; deleted by #196 (`f2616fee`), its use (3635) re-pointed. Retires when #196 lands |
| A5 | `codec_step_blank` (private, `ClassPSPACE/TQBF.lean`:1505) | campaign (Seyoon Ragavan) | tip, 281 | the **tape half** at the same radius for one deterministic step: `c.InWindow s → ∀ i z, s < \|z\| → (M.tm.step c).workTapes i z = none` (halted: `hc.2`; live: `z ≠ head`, `simp [Function.update, …]`). Its caller `codecObserve_step_iff` (1526) supplies the head half from the observation | **new, not named by the auditor.** Not a corollary of `apply_iff` as stated (the iff needs the boundary condition, and the tape half holds without it); it is `apply_iff`'s off-head branch. `TQBF` imports `CfgRecord` |
| A6 | `xr_window_stepWith` (private, `ClassNP/ExhaustiveReplay.lean`:67) | campaign (Seyoon Ragavan) | tip, 122 | one choice step from `Cfg.InWindow s`'s two clauses (written out as `hpos`, `hblank`) to the same clauses at `s + 1`, for any `NDTM k Bool S`, plus `output.length ≤ s + 1`; the halted branch (77–78) is inline monotonicity | **new, not named.** The window part is `inWin_stepWith` for general machines (a corollary of `apply_of_lt` + `mono`); the output bound is outside the kind. `ExhaustiveReplay`'s import closure (31 modules) does not contain `CfgRecord` |

## B. The same kind over other window predicates

Each proves that one step keeps a configuration in a window of another shape: a per-tape radius
(`|head| ≤ n`, blank at `n ≤ |z|`), the interval `[-t, t]`, or a data-dependent interval. They
cannot cite `apply_iff` without a translation between window predicates. **Scope question for the
maintainer and the user:** the ruling says "a window"; reading it by kind, these are members.

| # | Declaration (tip line) | Owner | Refs | Window and step | Note |
|---|---|---|---|---|---|
| B1 | `Turing.FinTM.source_bounds` (public, `TuringMachine/Sweep.lean`:359) | campaign | tip, 336 | interval window `[-t, t]` of an initialized deterministic run (heads, and blank for `z < -t ∨ t < z`); the induction step is one step from window `t` to `t + 1`, inline (`workTapePos_step_le`, `abs_le`; `unfold MultiTapeTM.step`, `Action.apply`, `update_of_ne hne`) | inline step inside a run lemma; consumers `ObliviousCandidate.sourcePayload_support` (655), `Oblivious` |
| B2 | `Turing.OracleTM.step_radius` (public, `TuringMachine/Oracle.lean`:346) | campaign | tip, 287 | per-tape radius window, one oracle step, `n → n + 1` (`workTapePos_step_le`; `workTapes_step_eq_of_ne`, which rests on the private `apply_workTapes_eq_of_ne`, 304: an action changes a cell only at the old head) | the shared form for oracle machines, factored at the wave-1 statement gate (round 1, finding 2); consumers `runFrom_radius` (369), `runFrom_workTapes_invariant` (384), `OracleNDTM`'s `runWith_headBlank` (`OracleNondeterministic`:348), `Build/OracleSim` (169, 2006). A member by kind; also the canonical of its own window form |
| B3 | `dgWindow_step` (private, `TuringMachine/Robustness/SingleTape.lean`:1933) | campaign | tip, 322 | a grown interval window `[a - left, a + n + right)` of the source run (heads by the move case split with boundary-crossing flags, the same logic as `apply_iff`; cells by `Action.apply` and `update_of_ne hne`), plus visited, history and size fields | the window part is of the kind; the other fields are not |
| B4 | `emCall_track_support` (private, `TuringMachine/Build/Loop.lean`:3316), with `emCall_track_extent` (3294) | campaign | tip, 334 | the visited interval `[lo_t, hi_t]` of the source run: the tape half inline (`unfold MultiTapeTM.step`, `Action.apply`, `update_of_ne hne`), the head half by `workTapePos_step_le` | inline step inside run lemmas |

## C. Older revisions on refs other than the tip (same members)

| Revision | Refs | Note |
|---|---|---|
| `ExpBFS/Radius` 72–79 and `Codec/Step` 194 ff. over `InWin N s C` (A1–A3 before `Cfg.InWindow` was relocated) | 27 (`complexity/arm-extensions`, `lean/arm-minor-fixes`, `lean/b5a-canon-cont3`, `lean/b6-f2-windowrun`, `lean/b6-hosts`, …) | superseded at the tip |
| `TuringMachine/Oracle.lean` `runFrom_workTapes_invariant` with the step inline (256, 354) | 49 (`pr/1`, `pr/10`, `fill/epoch3-B`, …) | before B2 was factored |
| `TuringMachine/OracleNondeterministic.lean` `runWith_headBlank` with the step inline (359, 372) | 31 (`pr/17`–`pr/20`, …) | before B2 was factored |
| `TuringMachine/Build/Primitives.lean` `emitter_track_extent`/`emitter_track_support` (about 5198, 5221) | 11 (`pr/10`–`pr/12`, `cryptography/pass-shelat-ch2-4-base-repair`, …) | the earlier home of B4 |
| `campaign/fills/c1/reviews/exhaustive-cont1/probe/XR*.lean` (10 files) | 109–110, tip included | record copies of A6, not library code |

## D. Consumers (cite a member or a canonical statement; not members)

`ExpBFS.WinRun.mono` (Radius 110), `ExpBFS.winRun_of_card_eq` (258), `ExpBFS.card_rset_succ_of_le`
(327); `Codec.slide_step_iff` (Step 254), `Codec.sDone_step` (476), `Codec.stepChk_iff`
(Checks 335); `codecObserve_step_iff` (TQBF 1526); `xr_window_runWith` (ExhaustiveReplay 104);
`OracleTM.runFrom_radius`, `runFrom_workTapes_invariant`, `OracleNDTM`'s `runWith_headBlank`,
`Build/OracleSim` 169 and 2006; `sourcePayload_support` (ObliviousCandidate 655) and
`dataCfg_simulates` (Oblivious 443, which assumes both windows); `recordStep_observed_action`
(CfgRecord 3597, citing `apply_iff` at 3635 on #196); `SavitchARM.mem_iff_reach_of_noEdge` (#196,
citing `apply_of_lt`).

## E. Inspected and excluded (other kinds)

- **Head bounds only, no blank-outside half** (`workTapePos_step_le`/`workTapePos_apply_le` along a
  run): `PSubsetPPolyConfigStep.abs_workTapePos_le` (190), `SpaceAmplifyRun.abs_workTapePos_le`
  (339), `Build/Catalog` (2801, 10262, …), `Build/Loop` (3060–3110, the interval clear), `StepBlock`
  (1808–1907), `Finite` (395–479), `Machines/Clean` (203), `Robustness/AlphabetReduction` (794,
  847), `ConfigCount.abs_pos_lt_card_visited` (253).
- **A space bound gives a window** (no step argument): `ConfigGraph.runWith_take_inWindow` (411),
  `ExpBFS.inWin_runWith_of_decides` (305), `BPLInP.inWin_run` (BPLInPCount 101),
  `Reach.inWin` (SpaceAmplifyPolyCode 127), `FinTM.inWindow_of_spaceUsed_le` (WindowClock 68), and
  the older `Codec/Bridge` `inWin_runWith_take` (27 refs).
- **Window by vertex, core bounds, initial window:** `NDTM.inWindow_of_coreSum_eq` (ConfigGraph
  436), `Cfg.InWindow.core_bounds` (247; older private `TQBF.codec_core_window`, 74 refs),
  `Cfg.inWindow_init` (CfgRecord 5687), `ExpBFS.inWin_init`; the older `ConfigGraph` private
  `InWindow` with `s1b_record*` (61–111 refs).
- **Visited sets and cell rules:** `ConfigCount.mem_image_workTapePos_of_ne_none` (211),
  `Codec.cellOf_apply` (Step 151), `PSubsetPPolyConfigStep.cell_step` (219),
  `CfgRecord.recordStep_cell_write` (1286), `recordStep_tape_word`/`_tape_run`/`_apply_run` (1368,
  3630, 4097), `exists_recordStepTM` (4682), `MultiTapeTM.liftSymbols_step_over` (SymbolLift),
  `Oblivious.prepInvariant_step` (663).
- **"Window" in another sense:** `StepBlock` `RoundWindow`/`roundData_window`/`roundWindow_frame`
  (heads at the round's start or end) and its older copy `CodeSimulator.h1RoundWindow` (11 refs),
  `Zone` windows (133 non-tip refs), `InputWindow`, `InputDevice.rd_test_window`, `WindowRun` and
  `WindowClock` runners, `RecordTable` `rt_*Window*`, `UniversalInterpreter.universalStateWindow*`,
  `CookLevin/Hardness.clWindowBit`, `TQBFHardVerifier.winBlk`, `DualHardSample.xWindow_*`.

## Census (members per file, tip)

| File | Members | Declarations | Share |
|---|---|---|---|
| `SpaceComplexity/ExpBFS/Radius` | A1, A2 | 25 | 8.0% |
| `SpaceComplexity/Codec/Step` | A3 (half of `boundary_iff`) | 30 | 3.3% |
| `TuringMachine/Build/CfgRecord` | A4 (retired by #196) | 136 (138 at `f2616fee`) | 0.7% → 0 |
| `ClassPSPACE/TQBF` | A5 | 190 | 0.5% |
| `ClassNP/ExhaustiveReplay` | A6 | 184 | 0.5% |
| `TuringMachine/Sweep` | B1 | 22 | 4.5% |
| `TuringMachine/Oracle` | B2 (+ helper `apply_workTapes_eq_of_ne`) | 44 | 2.3% (4.5%) |
| `TuringMachine/Robustness/SingleTape` | B3 | 101 | 1.0% |
| `TuringMachine/Build/Loop` | B4 (two lemmas) | 205 | 1.0% |

Declarations counted by `grep -cE '^\s*(@\[[^]]*\]\s*)?(private |protected |noncomputable )*(theorem|lemma|def|abbrev|instance|structure|inductive) '`
on each tip file. No file crosses one fifth.

## Summary for the ledger

- **Named by the auditor:** A1 `inWin_mono`, A2 `inWin_stepWith`, A3 `boundary_iff`'s window half
  (all Hydroxyi's: the user's dedup window, FYI only).
- **Found here on `Cfg.InWindow`:** A5 `TQBF`'s `codec_step_blank` and A6 `ExhaustiveReplay`'s
  `xr_window_stepWith` (both campaign files). Under a by-kind acknowledgment they are accounting
  minors, not majors. A4 retires with #196.
- **Same kind, other window predicates:** B1 `FinTM.source_bounds`, B2 `OracleTM.step_radius`,
  B3 `dgWindow_step`, B4 `emCall_track_support`/`_extent` (all campaign files). Whether "a window"
  covers them is the scope question above; recording them now avoids a later major.
- **Common core.** Eight of the ten members (A2, A3, A5, A6, B1–B4) re-prove the same tape half:
  "the write of one action lands under the old head, so a cell outside a window containing the
  heads keeps its contents". `apply_iff` contains it only as its off-head branch. Harvesting that
  branch as its own public lemma beside `Cfg.InWindow` (and one head-move bound) would give the
  12.2c window a citation target for A5 and for the B members' tape halves.
