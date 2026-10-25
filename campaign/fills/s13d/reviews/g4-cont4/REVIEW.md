# Review — §13d G4, continuation 4: the zone rows (`Turing.exists_zoneExtendTM`, `Turing.exists_zoneRebalanceTM`, `Build/ZoneRebalance.lean`), delivery `fill-s13d-g4-cont4.zip`

Read-only review by the maintainer's review sub-agent, 2026-10-25 (UTC). Every claim cites a saved
output under this folder (`out/NN-*`). The zip, its REPORT.md, logs, probes and tools are data:
nothing from it was run except the worker's import probe (`#check` lines and one `import` only,
scanned first, copied into my worktree as `probe/G4C4RevW_ImportProbe.lean`). Lean ran only
through `tools/leanelab.sh` (`scripts/elab.sh`), one elaboration at a time; no build or cache
command was run; the screen ran once, niced, under `locks/screen.lock` (`scripts/screen.sh`).

**Verdict: complete (2/2), with no admission. Land, by a maintainer PR, with one mechanical
re-point (F1, drafted and tested) and the status-text edits (F4, drafted and tested), after the
user's rulings on the private round iteration (F2) and the route refinements (F5). Not yet clear
to merge** (no PR, replay or gate yet). Nothing blocks the mathematics:
- The delivered file elaborates with **0 errors and no diagnostic at all** at the base (against
  `oleans-lphl2`, out/11), at the review-start tip `5cade0b8` (against `oleans-lrcan3`, out/12)
  and at the current tip `cfaaf75a`, after #161 merged during this review (against
  `oleans-lu2api`, out/37). The landing candidate (the delivered file with the drafted edits)
  elaborates with no diagnostic at both tips too (out/40, out/37b).
- Both targets depend on `[propext, Classical.choice, Quot.sound]`; their sorry-source walks are
  empty; all 872 declarations are within the standard three, name for name the worker's
  `axioms-cp7.log` (out/14, out/15).
- The constants are `C = 135` (extension) and `C = 2300` (rebalance), as REPORT says; the proofs
  carry no hypothesis beyond the frozen statements, so `ℓ = 0`, `i₀ = 0`, the short escape and both
  directions are all instances of what the kernel checked.

What passes:
- integrity: 128/128 internal sums; the bundle's only prerequisite is the base; 37 linear commits,
  each touching only the owned file; the 37 patches reproduce the delivered file (blob
  `7e42db77…`) at the base and at both tips;
- scope: every hunk in regions (a)–(c); imports unchanged; 18 → 18 public declarations at source,
  no statement changed; 783 new `zr_` privates, 2 removed, 36 restated or re-proved (all in the
  home, which the brief opens to them); new public constants only compiler auxiliaries;
- rule 10: my 82-definition seal with `[-simp] Turing.Action.apply` (the worker's omitted it):
  the body has 0 errors; 81 of 82 `rfl` controls bite, alone and together; the 82nd
  (`Contract._sizeOf_inst`) is shown not to matter. No TCSlib, core or Mathlib definition is a
  `rw`/`simp`/`unfold` rule; the core simproc `reduceCtorEq` is (8×), which I accept. Rule 11:
  no R3 row, no other file's private;
- probes: the brief's 448-check probe (equal to the pre-ship output) and the worker's 501-check
  probe, standalone: 0 errors, 0 warnings;
- lint 0 FAIL at both scopes, as at the base; widths ≤ 100; every new declaration documented;
  no campaign label in any new Lean text;
- the sweeps: bootstrap 27 sorries = the base set; final 25 = the base set minus the targets, by
  name; 96/96 in list order, exit 0;
- the v3 screen: 847 → 1,391 declarations, 477 → 970 pairs; 500 new, all in-file, none ≥ 90%
  (top 88%), no cross-file pair; identical to the worker's after-screen.

Findings (none blocks the mathematics):
- **F1 (major, failure mode 5; fixed by a tested mechanical edit).** `zr_contents_ext` is a
  private copy of the published `Turing.ZoneContents.ext'` (same statement, re-proved by `cases`),
  used 4 times. The text screen cannot see it. Edit C1 deletes it and cites `ZoneContents.ext'`.
- **F2 (major, failure mode 5 / ground rule 7; decision).** `zr_pinLoop` iterates rounds by its
  own induction (`Round.segment` chained by `Segment.trans`), the proof of `Turing.Round.iterate`
  re-done for an orbit indexed by the pass index. It carries all seven passes. No published
  statement covers that form, so it is a private generalization of a registry routine.
- **F3 (minor, policy §3).** 83 of the 103 new or changed proofs over 20 lines lack a literal
  "Proof sketch" (49 lemmas, 34 definitions; e.g. `zr_inSeg` 591 lines, `zr_outSeg` 768,
  `zr_pinLoop`, `zr_mir_step`). The lint does not check this.
- **F4 (landing edit, minor).** The module's **Status** paragraph and "Main results" entry and the
  `TuringMachine` facade's module list still call the rows sorried. Drafted and checked (A1–A3).
- **F5 (route refinements; decision, accept recommended).** Checkpoint 1.4 subsumed (no
  zero-level branch); the column moves cut the scratch copies by one-cell blanks instead of
  re-packing by `scanTM_contract` (a row the route names); `dir = false` by a mirrored machine
  through `Turing.Contract.lockstep` and `Turing.zoneRebalance_false`. The frozen fill-plan
  sketches now describe steps the proofs do not take (optional B1, B2).
- **F6 (rule-10 records, note).** The worker's seal starts after the first new declaration, does
  not erase `Action.apply`'s `@[simp]` (a local `irreducible` does not stop `simp` from unfolding
  it: my control 83), and three of its `isDefEq` controls do not bite. Mine covers all three; no
  violation is found.
- **F7 (records, minor).** Checkpoint zips not in the inbox; 173 in-file pairs justified only by
  class in reports that were not delivered; commit subjects carry campaign labels; REPORT does not
  say how each of the 36 inherited privates changed; noisy manifest-check tail;
  `synthInstance.maxSize` up to 1024, once inside a target's body.
- **F8 (environment note).** The module peaks at 4.4–4.5 GiB at `-j4` on the fill host, above the
  addendum's measured 2.8 GiB and its 4 GiB headroom floor.
- **F9 (landing order; decision).** #161 merged during this review (`5bbef333`; tip `cfaaf75a`,
  Lean content = `oleans-lu2api`'s tree); #162's merged-tree replay `lkit` (5/5) passed on it. This
  landing's replay is the same 2 modules in every order; only the snapshot differs.

## Inputs

| Input | Identity | Evidence |
|---|---|---|
| Zip `exchange/inbox/fill-s13d-g4-cont4.zip` | SHA-256 `4d1667b7…cfce7` (as given); 1,026,064 B; 142 entries (129 files); CRC OK; no unsafe name or symlink; copied to `delivery/` and extracted there; every member byte-equal to the extraction | out/01 |
| `SHA256SUMS` | 128/128 OK; covers every file except itself | out/01 |
| Brief (dispatch copy) `exchange/outbox/fills/s13d-fill-g4-cont4.md` | SHA-256 `852265b0…6052c` (as given and as REPORT says); equal to `campaign/fills/s13d/briefs/s13d-fill-g4-cont4.md` with its three `@ANCESTOR@` replaced by the base; the same at the base and at the tip | out/05 |
| Addendum | v2.5, SHA-256 `90851511…3abf0` at base and tip, as REPORT says | out/05 |
| Brief inputs | `inputs/s13d-fill-g4-cont4/` (import probe 448/437, return probe, population): base = tip = `drafts/…/preship-21d53053/`; order list (96), base sorries (27, in `logs/`), screen base (847/477/136,473) | out/05, out/31, out/43 |
| Base `f89c5c8da79997f4fb73bbfce04ed7f671afe206` | its Lean content = #156's round-2 head `0e5f210b` (0 Lean files differ); owned blob `1abbb871` | out/04, out/13 |
| Head `374337b0697bc0fb9fb3f6795e214d441be83482` | the bundle's only ref, `refs/heads/deliver/fill-s13d-g4-cont4`; equal to the local `deliver/fill-s13d-g4-cont4-in` | out/02 |
| Tips | `5cade0b8` (the records worktree's; Lean = #160's `1cc8ab39`, 0 files differ) at the start; **`cfaaf75a` from 04:42Z** (#161 merged as `5bbef333`, then records and `Build/README.md`); owned blob `1abbb871` at both | out/13, out/38 |
| Snapshots | `oleans-lphl2` (base), `oleans-lrcan3` (`5cade0b8`), `oleans-lu2api` (#161's tree = `cfaaf75a`'s Lean, 325/325), `oleans-lkit` (#162 on `lu2api`, 5/5) | out/11, 12, 37 |

Review worktrees, all detached under this folder, each with the `.lake/packages` link (checked
absent first): `wt-base` (base), `wt-head` (head; the screen and lint ran here, nothing else
touched it), `wt-work` (head; probe copies only), `wt-tip` (`5cade0b8` + the delivered file),
`wt-land` (`5cade0b8` + the landing candidate), `wt-tip2` (`cfaaf75a` + the delivered file).
A first attempt under zsh, whose `set --` does not split words, created four worktrees at
mistaken paths (the main checkout's HEAD); nothing was copied or elaborated in them, and they
were removed cleanly with `git worktree remove` (out/00-worktrees-mistake.txt).

## (a) Integrity and scope

| # | Check | Result | Evidence |
|---|---|---|---|
| 1 | Bundle | `verify` okay; one ref = `374337b0`; sole prerequisite the base `f89c5c8d`; equal to the worker's `bundle-verify.txt` | out/02 |
| 2 | Commits | 37, linear, first parent the base; author `Claude <noreply@anthropic.com>`; 2026-10-24T07:09:13Z – 2026-10-25T00:13:52Z; each touches only the owned file. REPORT's checkpoint table (`b5247d00`, `478124e9`, `7fbf3c2e`, `604d9404`, `f771d4ff`, `06872fff`, `374337b0`) and its other hashes (`4f8a01e5`, `61e33ef2`, `a6cf08df`) are all in the series | out/03 |
| 3 | Patches | the 37 apply in order at the base and reproduce the delivered file byte for byte (blob `7e42db77`, SHA-256 `76a108a4…`); each equals `git format-patch` of its commit up to the git-version trailer; the same at `cfaaf75a`, whose owned blob is the base's | out/03, out/38 |
| 4 | Delivered file | = the head blob `7e42db77` | out/04 |
| 5 | Regions | 118 hunks, **0 outside** (a) 127–1350, (b) 1391–1395 and 1408, (c) 1431–1438 and 1449; lines 1–126 identical; the rows section changes only at base 1391–1395 → head 14643–14656, 1408 → 14669–14675, 1431–1438 → 14698–14708, 1449 → 14719–14764 | out/07 |
| 6 | Freeze (`declfreeze`) | public 18 → 18, none added or removed, **no statement changed**; the targets change only in body and status paragraph (authorized; without the authorization those two are the only changes reported) | out/06 |
| 7 | Privates (`declfreeze`, `privstmt`) | 73 → 854: **783 added** (all `zr_`), **2 removed** (`zr_RightData`, `zr_left_two_walks`), **36 changed**: 25 restated, 11 body or docstring only. REPORT's "38 changed" are these 36 and the two targets. All 36 are inherited home helpers, which region (a) lets the worker "adjust … or remove" (report each change): re-indexed from `zr_RightData` (ℓ = n + 1) to `ZoneData` at every level, the ruler step and adjusted walk parametrized by direction (the brief's ask), the second seek's precondition by two local facts (gate 44 note 9), the bounds' constants | out/06, out/08b |
| 8 | Code lines (`stmtcheck`, `codeonly`) | 722 of 1,111 base code lines not found in order, all inside the home and the two `sorry` bodies; code differs (expected) | out/06 |
| 9 | Imports | unchanged (lines 6–9) | out/07 |
| 10 | Public constants (workflow.md §4) | 40 → 47 non-private names: new only compiler auxiliaries (`exists_zoneExtendTM._proof_1_1…3`, `zoneRowLo.eq_1`, `zoneRowHi.eq_1`, renumbered `zoneRebalancePost_frames._proof_1_5`/`_simp_1_1`, and the realized `Contract.branch.congr_simp`, `Contract.lockstep.congr_simp`); no `deriving`, so no derived instance | out/14b |
| 11 | Hygiene (13,541 added lines, 11,342 code lines) | no `sorry`, `admit`, `axiom`, `native_decide`, `delta`, `change`, macro, `#` command, `section`, `namespace`, `variable`, `attribute`, `instance`, `@[simp]`; 15 `unfold`, all of own definitions; 3 `open Classical in` (declaration-scoped); 10 `set_option synthInstance.maxSize … in` (256 ×5, 512, 1024 ×4, one inside `exists_zoneExtendTM`'s body; F7) | out/08 |
| 12 | Rule 11 | R3 rows: 0. Other files' 5,494 private names as identifiers: only `S`, `T` (type variables) and `mapState_state` (the public `Cfg.mapState_state`); no external private in any elaborated closure (872/872, row 18); all new privates `zr_` | out/22, out/14 |
| 13 | Size | 1,572 → 14,887 lines; 18 public / 854 private (lint INFO; REPORT agrees). Size alone is no driver | out/28 |

## (b) Elaboration and axioms

| # | Check | Result | Evidence |
|---|---|---|---|
| 14 | Head at the base, `oleans-lphl2` | exit 0, **no diagnostic**; 204 s, 3.4 GB | out/11 |
| 15 | At the tip `5cade0b8`, `oleans-lrcan3` (only `Build/Seam` changed upstream: #159's two equations) | exit 0, **no diagnostic**; 191 s | out/12, out/13 |
| 16 | At the tip `cfaaf75a` (#161 merged; `Deterministic` changed upstream), `oleans-lu2api` | exit 0, **no diagnostic**; 174 s. The landing candidate (A1, A2, C1) likewise, 175 s | out/37 |
| 17 | The six checkpoint commits (`b5247d00` … `06872fff`), `oleans-lphl2` | each exit 0, 0 errors; only the open targets' `sorry` warnings (two through `478124e9`, then only the rebalance row's): the series is bisectable at its checkpoints | out/30 |
| 18 | Axioms: an in-module copy with 872 prints, sorry-source walks, an external-dependency walk per declaration, a public-constant listing | targets `[propext, Classical.choice, Quot.sound]`; walks empty; tally 561 all three (targets included) / 83 `propext, Quot.sound` / 195 `propext` / 4 `Quot.sound` / 29 none; **no `sorryAx`**; no external private; the external-equation filter flags only `Nat.eq_zero_or_pos` (a core theorem; name pattern). At the base both targets are `[propext, sorryAx, …]`, each its own only source | out/14, out/15, out/13 |
| 19 | Against the worker | the 872 prints equal `axioms-cp7.log` name for name, set for set | out/15 |
| 20 | TCSlib constants reached from the 821 new or changed declarations | 291: 94 definitions, 177 theorems, 8 inductives, 12 constructors; `@[simp]` among the definitions: only `Turing.Action.apply` | out/16 |

**Downstream consumers.** No Lean declaration anywhere uses either target or any of the module's
public rows, at either tip or on #161, #162 or #135's branches; only docstrings mention the
module, and the facade imports it. Neither the brief ("proved modulo: none") nor REPORT claims
that a downstream admission goes away (out/26).

## (c) Correctness, route, rules 10 and 11

I read the targets' bodies, the host and pinned-loop layers, the row assembly and the mirror in
full, and the rest by sampling. Correctness rests on the kernel check (rows 14–18).

**What is proved.**
- **Extension** (`C = 135`): `zr_machineOf (zr_extendContract [])`, four contracts through
  stationary seams (right pass, return home, left pass, final return), assembled by
  `Contract.ofSegment` at exactly `zoneRowPre`, `zoneExtendPost done`, `zoneRowLo`/`zoneRowHi` at
  `ℓ`; time `≤ 135 · (2^ℓ + 1)` (`zr_extend_time_le`). The left pass ends at `−8` at `ℓ = 1`
  (`zr_leftPass_one`); the displacement is the brief's second option, `2 · 2^ℓ + 1`
  (`zr_left_reach`). The return home's seam has the explicit `DecidableEq` (`zr_decEqRP`), the
  real `link` and a proved `hlink` (`zr_rightReturn_link`).
- **Rebalance** (`C = 2300`): one state type for both directions, with `Fintype`/`DecidableEq`
  built part by part (`zr_rowInst`); `done ≠ short` by `Sum.inl_ne_inr`. `dir = true`:
  `zr_rowR`, a branch on the scan's two escapes (found: the found path, `≤ 1000 · 2^(i₀+1) + 200`,
  then the count's clear; short: the return home and the clear), time `≤ 2300 · (2^i₀ + 1)`
  (`zr_rowC_time`), box `zoneStart (i₀ + 1)` and scratch `q − 1 … q + 18 · 2^i₀ + i₀ + 13`.
  `dir = false`: `zr_rowLeft`, the rightward contract transported along `zr_mir_lockstep` by the
  published `Contract.lockstep`, at the swapped data and the mirrored start, the endpoint
  identified by `zoneRebalance_false`, the time the rightward one's (cost 1 per step).
- **Boundary cases.** The frozen statements quantify over all `ℓ`, data and directions, and the
  proofs add no hypothesis, so each case is an instance: `ℓ = 0` (the extension's ruler is the
  home field, `zr_rightWord ⟨0, z⟩`; the rebalance index is then `≥ ℓ`, the short path); `i₀ = 0`
  (the found path starts at field `i₀ + 1 = 1`, `zr_rowP0_valid`; its passes' level-zero rounds act
  by the identity shifts `zr_shiftIn_zero`, `zr_shiftOut_zero`); the short escape (`zr_short_eq`:
  index = ℓ, data unchanged by `zoneRebalance_of_le`); both directions (`cases dir`). No private
  lemma on the way to either target carries a hypothesis the statements lack (`2300 ≤ C` is
  discharged by `le_rfl`).
- **REPORT's constants and bounds** match the statements of `zr_extend_time_le`,
  `zr_fpSeg_time`, `zr_rowC_time`, `zr_rowL`/`zr_rowU`, and both status paragraphs.

| Item (the brief's route) | Status | Notes |
|---|---|---|
| 1.2 the return home | as briefed | `skipTM` over the outer half, then the phase-host loop of `skipBackTM` rounds built by `round_iff`, iterated by **`Round.iterate`** (`zr_loop_segment`) |
| 1.3 the left pass | as briefed | the second displacement option; per-stage `time`/`lo`/`hi` lemmas; ℓ = 1 in Lean |
| 1.4 the ℓ = 0 branch | **subsumed (F5a)** | every phase is uniform in ℓ; the brief names the one-cell leaf for this branch |
| 1.5–1.6 cleanup, assembly | as briefed | `clearTM_contract`; `Contract.ofSegment` in the `HeadBox` |
| 2.1 the scan with `short` | as briefed | rounds by `round_iff` with two escapes, iterated by **`Round.iterate`** (`zr_scanLoop_segment`); a unary zone count on scratch (the recommended form) |
| 2.2 one level's column move | **refined (F5b)** | copy with `extract := zoneSlotOf t`, cut the copy by one-cell blanks at offset `2^(i−1)` (the leaf's one-cell write; the walk over field `i − 1` as the ruler), copy the pieces back with `merge := zoneSlotSet t`; no `scanTM_contract` |
| 2.3 the passes and the home move | as briefed, **one host deviation (F2)** | the passes are phase-host loops whose rounds are pinned steps; their iteration is `zr_pinLoop`'s own induction, not `Round.iterate`; the order is `zr_cascade_passes`' |
| 2.4 the mirror | **refined (F5c)** | `zr_mirTM` (tape 0's moves negated), `zr_mir_step` through `MultiTapeTM.step_of_some`/`_of_halt` and `Action.apply_*`, a `Turing.Lockstep` instance of cost 1, `Contract.lockstep` |
| 2.5–2.6 cleanup, assembly | as briefed | the count's clear; `Contract.ofSegment` |
| Hosts | instances only | `zr_hostTM` is `phaseHostTM (zr_hostMachines MB) ⟨false, some false⟩ (zr_hostRed e back)`: no machine of its own; its phases are the anchor leaf and the body |

**Rule 10.**

| # | Check | Result | Evidence |
|---|---|---|---|
| 21 | Seal set | **82 definitions**: the 71 semireducible non-projection TCSlib definitions reached (row 20), the worker's four extras (`Cfg.SameOutside`, `Contract._sizeOf_inst`, `framedContract`, `sweepContract`), and seven reached one level deeper (`Action.mapState`, `Contract._sizeOf_1`, `SeekPhase.enumList`, `SweepPhase.enumList`, `zoneBase`, `zoneCascadeLeft`, `zoneMoveLeft`); plus **`attribute [-simp] Turing.Action.apply`**. Not sealed: 12 TCSlib matchers, reachable only through their sealed parents | out/16, out/17-seal-walk.out, out/17-seal-summary.txt |
| 22 | Controls alone | unsealed: 83/83 close (82 `rfl` and a default-`simp` control); all sealed: 82 errors, one each, all but control 9 (`Contract._sizeOf_inst`); each under its own definition's seal only: 81/82 fail, one error each, again all but control 9 | out/17-seal-G4C4RevCtl{Unsealed,Sealed,Each}.out |
| 23 | The module sealed (section from line 127, the first new declaration, through `exists_zoneExtendTM`; controls at its top) | **exactly 82 errors, all in the controls; 0 in the body**; both targets `[propext, Classical.choice, Quot.sound]` under the seal | out/17-seal-G4C4RevSeal.out |
| 24 | `Contract._sizeOf_inst` | cannot matter: in the module only the structure compiler's `zr_PinSeg.mk.sizeOf_spec` and `zr_PinSeg._sizeOf_1` mention it, and no proof uses them; no `termination_by`, `decreasing_by` or `sizeOf` in the file | out/17-seal-G4C4RevSeal.out (USERS) |
| 25 | `instFintypeSeekPhase`, `instFintypeSweepPhase` | the concrete controls `(Finset.univ : Finset SeekPhase).card = 4 := rfl` (and `= 3`) bite, alone and together; the body passes with both sealed | out/17 |
| 26 | `[-simp]` | without it, `by simp` still unfolds `Action.apply` under the irreducible seal (control 83 closes); with it, the control fails and the body still passes | out/17-seal-G4C4RevSimpIrredOnly.out |
| 27 | `rw`/`rwa`/`simp`/`simpa`/`dsimp`/`unfold`/`show`/`change` on the added lines | 3,016 calls (1,364 `rw`, 921 `show`, 542 `simp only`, 67 `norm_num`, 55 `simp`, 21 `simpa only`, 15 `rwa`, 15 `unfold`, 10 `simpa`, 6 `dsimp only`); 5,981 rule elements, each head classified by Lean name resolution in the module's context: 1,389 TCSlib theorems, 1,989 core or Mathlib theorems, 1,532 own declarations, 1,063 locals, **8 the core simproc `reduceCtorEq`**. **No TCSlib, core or Mathlib definition is a rule.** Other-file definitions occur only in `show` terms or term arguments (`zonedTape` 52, `zoneStart` 31, `zoneCapacity` 5, `Action.apply` 5, `fieldOffset` 4, `zoneShiftIndex` 3, `joinFields` 2, `zoneShiftIn`, `zoneShiftOut`, `zoneRebalance`, `zoneCells` 1 each); core `Function.update` 37, `min`/`max` 12 each: all covered by the seal. The 55 bare `simp`, 10 `simpa` and 67 `norm_num` close side goals (list lengths, arithmetic); row 26 shows none relies on a `@[simp]` definition. Agrees with the worker's `inspection-definitions-cp7.tsv` | out/20, out/21 |
| 28 | `reduceCtorEq` | a core simproc that decides equalities of distinct constructors: no definition is unfolded, and the scope bullet's object (core definitions passed to `simp`) does not cover it. **Allowed**, in my judgment | out/21 |

## (d) Escalations, probes and promotion candidates

**Escalations: none, and I agree.**

| # | Probe | Result | Evidence |
|---|---|---|---|
| 29 | The brief's import probe (448 checks of 437 names), standalone, `oleans-lphl2` | 0 errors, 0 warnings; output equal to the pre-ship's `G4C4ImportProbe.out` (paths aside) | out/25 |
| 30 | The worker's probe (501 checks of 490 names: the brief's 448 first, in order, then 53), standalone | 0 errors, 0 warnings; equal to its `probe-cp7.out` but for that file's trailing `exit 0` | out/25 |
| 31 | Coverage | of the 291 TCSlib constants reached (row 20), 289 are in the worker's probe; the other two are compiler auxiliaries inside published equations' statements (`Contract.lockstep._proof_2`, `zoneShiftInW._proof_1`), not citations | out/42 |
| 32 | Scan of the delivered Lean before use | the worker's probe has only `#check` lines and its import | out/25 |

**Promotion candidates** (REPORT's seven; my assessment):
- the mirror lockstep (`zr_mir`, `zr_mirTM`, `zr_mir_step`, `zr_mir_lockstep`) is fully generic
  (any two-tape machine, any state type) and the strongest: a public "reflect tape `j`" machine
  transformer with its `Lockstep` instance;
- `zr_round_of_body` (a dispatch step and a contract make a `Round`) and a sequence form of
  `Round.iterate` (F2) belong in `Build/Contract/Basic`;
- the contract adapters (`zr_reindexContract`, `zr_exitsContract`, `zr_singletonContract`) beside
  `Contract.ofSegment`, as `def`s with non-`simp` `simps` fields;
- the field-layout library (`zr_joinFields_append`, `zr_fieldsTape_snoc′`, `zr_fieldsTape_cut`,
  `zr_fieldOffset_append`) beside `Build/Catalog`'s layout API;
- the pinned-step frame and the count stack are this file's bookkeeping; promote only with a
  second consumer.

## (e) Duplication and lint

| # | Check | Result | Evidence |
|---|---|---|---|
| 33 | Screen v3 script | SHA-256 `f4feac91…f878f181` in `wt-head`, `wt-tip` and the main checkout | out/27.status, out/43 |
| 34 | Before | the worker's `screen-before.txt` equals the recorded base `s13d-fill-g4-cont4-screen-base.txt` (847; 477; 136,473), comment lines aside | out/43 |
| 35 | After (my one run at the head, `wt-head`, the brief's 10-file population) | `declarations screened: 1391; copy pairs …: 970; reproduced text: 353,746 chars`; exit 0; 539 s; niced; under the lock (acquired 04:38:22Z, released 04:47:21Z by the script's trap); the worktree unchanged before and after | out/27 |
| 36 | New pairs (`pairdiff.py`, against the recorded base) | **500 new, 7 gone; all in-file; no cross-file pair; none ≥ 90%** (top: `zr_fp8` ⟶ `zr_fp6` 88%, `zr_out2Test_step` ⟶ `zr_out1Test_step` 87%, `zr_scan_fields` ⟶ `zr_return_post` 87%); distribution 232 in 50s, 155 in 60s, 80 in 70s, 33 in 80s. Between the two directions the top pair is `zr_rowR_spec`/`zr_rowLeft_spec` at 69%; within the mirror `zr_mir_post` ⟶ `zr_mir_mir` 85%. The 7 gone are inherited pairs among the factored ruler composites (51–67%) | out/43, out/43b |
| 37 | Against the worker | my after-screen equals its `screen-after-cp7.txt` line for line; all 500 new pairs are in its cumulative `screen-pairs-since-base-cp7.md`, 327 with a line of their own, 173 (zips 1–3, up to 84%) only "justified by class" in reports not delivered (F7) | out/43 |
| 38 | Hazards | no pair with `Build/RecordTable` (`rt_copyMachine`, `exists_fieldsCopyTM`), `Build/Zone`'s cascade family, `Build/Seam`'s host or `Contract/Basic`'s rounds | out/43 |
| 39 | **Semantic re-derivations** (the text screen cannot see them) | **two**: `zr_contents_ext` = `ZoneContents.ext'` (F1); `zr_pinLoop`'s induction = `Round.iterate`'s, generalized (F2). Table below | out/34 |
| 40 | Lint | `TuringMachine`: 0 FAIL, 68 WARN over 83 files; `Build` (the brief's scope): 0 FAIL, 33 WARN over 40; both as at the base; only the size WARN and INFO lines change; `Build` equal to the worker's `lint-cp7.txt` | out/28 |
| 41 | Widths, whitespace | widest line 100; no trailing whitespace, tab or double blank line | out/29 |
| 42 | Docstrings and sketches | all 821 new or changed declarations have a docstring; of the 103 proofs over 20 lines, 20 carry a literal "Proof sketch" and **83 do not** (F3) | out/29, out/29b |
| 43 | Public-facing text | no campaign label, path, date or session narrative in any new docstring or in the two status paragraphs (the only label hits, "§13d G4" and "Deviation", are frozen text); both paragraphs are headed `**Implementation.**` and describe the phases and the rows they compose, as region (b)/(c) asks | out/29, out/29c |

**Semantic-duplication table** (exact? over the module's own imports, so that only published
declarations are found: out/34-dup-exact.out, out/34-dup-exact2.out; greps over both tips and the
three branches; the full list is out/34-semantic-dup.txt).

| Private (new) | Published candidate | Verdict |
|---|---|---|
| `zr_contents_ext` | `Turing.ZoneContents.ext'` (`Build/ZoneTape`, in the closure; already cited at head line 648) | **re-derivation** of the same statement; exact? returns `ZoneContents.ext' h1 h2 h3` (F1) |
| `zr_pinLoop` (`hseg`) | `Turing.Round.iterate` | **re-derives its induction** for an index-driven orbit; no published statement of that form (exact? on the sequence form: none) (F2) |
| `zr_map_pair` | Mathlib `Set.image_pair` | an instance (exact? returns it); a one-line `simp only`; note only |
| `zr_host_dispatch_run` | `Turing.phaseHostTM_run` at `T = 0` | near: the same step, reached through the published `Contract.inPhase`; note only |
| `zr_bufferTape_map` | `FinTM.bufferTape_map` (`SymbolLift`, embeddings only) | outside the import closure and narrower; none |
| `zr_bindState_eq` | `Cfg.ext` | exact? closes it only definitionally (through `Cfg.bindState`); the worker's proof reads `Cfg.bindState_*`; a compliant adapter |
| `zr_shiftIn_zero`, `zr_shiftOut_zero` | — | exact? closes them only by `rfl` (unfolding `Build/Zone`); no lemma; the worker's proofs read the `simps` equations |
| `zr_sum_*_eq`, `zr_time_desc`/`_asc` | `zoneCascade_cost_le` | its fixed budget `4·(2^(i+1)+i+2)` does not meet the rounds' bounds (up to `95·2^i + 170`); none |
| `zr_round_of_body`, `zr_inputSymbol_congr`, `zr_slot_track`, `zr_zonedTape_inr`, `zr_slotSet_slotSet`, `zr_zonedTape_update(_same)`, `zr_joinFields_append`, `zr_fieldsTape_end`, `zr_fieldsTape_snoc′`, `zr_fieldOffset_append`, `zr_bufferTape_reverse`, `zr_getElem?_mid`, `zr_iterate_pred`/`_succ` | — | no published statement (exact?: none); built on the published API |
| adapters, host instance, pinned frame, count stack, mirror, endpoint `Cfg.ext` lemmas, cascade folds | `Contract.ofSegment`, `phaseHostTM`, `Contract.inPhase`/`seq`/`branch`, `Contract.lockstep`, `ZoneContents.swap`/`zoneRebalance_false`, the field equations, `zr_cascade_passes` | uses of the published API; no re-proof (out/34) |

## (f) Environment (addendum v2.5, Part 1)

| Item | Recorded | Evidence |
|---|---|---|
| Preflight (2026-10-24T06:17:12Z) | `nproc` 4; cgroup v1 without an effective limit, so the headroom is `MemAvailable` 15,906,124 kB ≥ 4 GiB; in use 221,253,632 B; `failcnt` 0, `oom_kill` 0; clone ext4, 26,303,459,328 B free ≥ 12 GiB; no tmpfs used. Re-check before the cache 23,717,871,616 B ≥ 8 GiB. **PASS** | `preflight.log`, out/33 |
| Store, roots, fetch | store absent before (`cache-store.log`), 1,004 files after; **40 roots, byte-equal to my extraction from the order list and to the pre-ship's `roots.txt`**; "Attempting to download 1002", "Decompressing 1002", "Completed successfully!", exit 0; `M − N = 0`; the cache tool's own build only | out/33, out/33-roots-mine.txt |
| Manifest | 11 present packages match URL and revision; absent exactly `doc-gen4`, `UnicodeBasic`, `BibtexQuery`, `MD4Lean`; no order-list module imports them (my grep). Its trailing import list is noisy (F7) | out/33 |
| Cache checks, bans | no zero-size olean; cache probe exit 0; no `lake build`, no unfiltered fetch | out/33 |
| Bootstrap (06:20:56–06:43:14Z) | 96/96 in the list's exact order, exit 0, 0 errors; **27 sorry warnings = the base set** by module (the owned file's at 1396 and 1439, the pre-ship's lines); the worker's by-name list equals `s13d-fill-g4-cont4-base-sorries.txt` | out/31 |
| Final sweep (2026-10-25T00:41:14–01:16:50Z, at `374337b0`, fresh olean directory) | 96/96 in order, exit 0, 0 errors; **25 = the base set minus the two targets**; `Build/ZoneRebalance` no diagnostic (622.7 s, 4,506 MiB); the 398 diagnostics outside it identical to the bootstrap's | out/31 |
| Memory logging | each module's start, end, wall and max RSS; bootstrap peak 2,900 MiB (`Build/CfgRecord`); final peak 4,506 MiB (the owned module; F8) | out/31, out/33 |
| Checkpoint zips | seven named in REPORT (and an earlier final zip at `f771d4ff`); **none is in the inbox**, only the final zip; moot for a complete delivery; the six checkpoint commits elaborate (row 17) | out/30 |

## (g) Landability

- **The patches apply at the current tip.** `cfaaf75a`'s owned blob is the base's (`1abbb871`),
  so the 37 patches give the delivered blob there (out/38).
- **Downstream closure** (`mkdownmulti.py` at the tip): `Build/ZoneRebalance`, then the facade
  `TCSlib/Complexity/TuringMachine`, **2 modules**; the root is not listed (out/35).
- **#161** (merged during this review, `5bbef333`; Lean = `oleans-lu2api`'s tree): its
  325-module closure contains both of this landing's modules (`Deterministic` is upstream of
  `Build/ZoneRebalance`), but its replay elaborated the old `ZoneRebalance`. #161 adds one
  theorem to `Deterministic` and changes two files outside this closure; the delivered file and the
  landing candidate elaborate against `oleans-lu2api` with no diagnostic (row 16, out/37b).
- **#162** (open, head `e984516b`, its merged-tree replay `lkit` 5/5 on `lu2api`): it meets this
  landing only at the facade (it adds an import and a module-list entry; A3 edits another entry
  of the same list: no textual conflict). That is the facade-only rule: no re-replay of #162.
- **#135** (chapter 7, into `main`) is not on this branch's path.
- **Expected sorry count after landing:** the order list 27 → 25; `Build/ZoneRebalance` 2 → 0.

## Findings

**F1 (major, failure mode 5; resolution drafted and tested).**
- *Claim:* `zr_contents_ext` (head 6411–6419) states exactly `Turing.ZoneContents.ext'`
  (`Build/ZoneTape:471`, public at the base and in the import closure, already cited by the
  inherited code at head line 648) and re-proves it by `cases`. It is used by `zr_shiftIn_off`,
  `zr_shiftOut_off`, `zr_shiftIn_zero`, `zr_shiftOut_zero`. Ground rule 5: "Cite proved material;
  never re-prove it." The text screen pairs it with nothing.
- *Evidence:* out/34-dup-exact.out (P1: `exact ZoneContents.ext' h1 h2 h3`); the head file.
- *Resolution:* edit C1 (`scripts/landedits.py`, every replacement asserted): delete the lemma and
  write `ZoneContents.ext'` at the four uses (the hypotheses are in the same order). Checked on
  `wt-land`: no diagnostic at the tip (out/40) and at `cfaaf75a` (out/37b); `declfreeze`/
  `privstmt`: `zr_contents_ext` removed, the four users' bodies changed, no statement changed;
  lint, widths unchanged (out/40-land-checks.txt). With C1 the debt is gone, so no
  acknowledgment is needed.

**F2 (major, failure mode 5 / ground rule 7; decision).**
- *Claim:* the brief's hosts rule (binding) puts iteration over levels, zones and marks on
  `Turing.Round.iterate` or `RoundContract`, and ground rule 7 says "Never write a second … round
  iteration". `zr_pinLoop` (head 8085–8148) iterates the pinned rounds by its own induction
  (`hseg`: `Round.segment`, then `Segment.trans`), which is `Round.iterate`'s proof, over the
  orbit `nxt^[m] j₀` of the pass index instead of `roundOrbit M τ c`. All seven passes go through
  it (`zr_passContract`). The return loop and the scan do use `Round.iterate`. REPORT lists the
  pinned loop as a promotion candidate but not as a deviation.
- *Why it was written:* `Round.iterate` needs the round time as a function of the configuration;
  the pinned rounds' times are given per index, and recovering the index from a configuration
  needs either a level read off the head (as the scan does) or a first-return uniqueness argument.
  No published statement has the sequence form (P18: exact? finds nothing).
- *Resolution (decision 2):* (a) accept and ledger it now, and add the sequence form
  (`Round.iterate` for any sequence of round starts) to `Build/Contract/Basic` by an API PR, with
  `Round.iterate` as its corollary and `zr_pinLoop` re-pointed (recommended); (b) a continuation
  re-routes the passes through `Round.iterate` with a configuration-read time; (c) accept as a
  private generalization with no follow-up.

**F3 (minor, policy §3).**
- *Claim:* 83 of the 103 new or changed proofs over 20 lines carry no literal "Proof sketch"
  (49 lemmas, 34 definitions whose bodies are long contract terms), among them `zr_inSeg` (591
  lines), `zr_outSeg` (768), `zr_hmGat` (279), `zr_hmSc2` (282), `zr_prSeg` (147), `zr_rowR` (62),
  `zr_pinLoop` (39), `zr_mir_step` (54). Their docstrings state what they prove; the lint checks
  sketches only before a `sorry`.
- *Evidence:* out/29b-sketches.txt (the list), out/29.
- *Resolution:* a docstring-only follow-up commit (the maintainer's or a short continuation's);
  not needed for the mathematics. For later briefs: ask for the sketch on every proof over 20
  lines, definitions included, and check it mechanically.

**F4 (landing edit, minor).**
- *Claim:* outside the worker's regions, the module docstring says "**Status: statements.** The
  two rows are sorried …" (head 31–33) and "the rows (sorried)" (head 54), and the facade's module
  list says "sorried for the G4 fill" (`TuringMachine.lean` 165–166).
- *Resolution:* A1–A3 (`scripts/landedits.py`; diffs out/39-landedits-*.diff):
  - A1: "**Status: proved.** Every declaration is proved, both rows included; their machines and
    contracts are private to this module. These rows replace the retired binary rows
    `exists_zoneShiftInTM` and `exists_zoneShiftOutTM` of `Build/Zone`."
  - A2: "…: the rows (proved)."
  - A3: "* `Build/ZoneRebalance` — the rebalance and extension rows (§13d, G4), as contracts.
    Proved."

  Checked with C1 on `wt-land`: the module and the facade elaborate with no diagnostic
  (out/40, out/40-land-facade-elab.out); landed blob `b5a31166`, SHA-256 `5c46f25f…`.

**F5 (route refinements; decision, accept recommended).**
- *Claim:* three departures, all disclosed in REPORT:
  - (a) checkpoint 1.4 is subsumed: every phase is uniform in ℓ (at ℓ = 0 the ruler is the home
    field), so there is no zero-level branch; the brief named the one-cell leaf for it;
  - (b) the column moves never re-pack: they cut the scratch copies by one-cell blanks (the leaf's
    one-cell write, which the brief lists among its uses) and copy the pieces back, so
    `scanTM_contract`, which the route and the hosts list name for re-packing, is not used. No
    re-packer is written;
  - (c) `dir = false` is a mirrored machine (`zr_mirTM`, tape 0's moves negated) with a
    `Lockstep` instance, transported by the published `Contract.lockstep`, and the data side through
    `ZoneContents.swap`, `zr_mirror_tape` and `zoneRebalance_false` (the brief: "through
    `zoneCascadeLeft_eq` and `zr_mirror_tape`, or by a direction parameter"). It is no second copy
    of the passes (the highest cross-direction pair is 69%), and no new transport.
- *Consequence:* the targets' frozen fill-plan sketches now describe steps the proofs do not take
  ("re-packs it there by scans", "a scratch ruler of the distance to home", "at ℓ = 0 finite
  control writes the two cells", "through a ruler of the distance"), while the new
  `**Implementation.**` paragraphs are accurate.
- *Resolution:* accept all three (decision 1); optionally bring the sketches in line (B1, B2,
  comment-only, `scripts/landedits_optional.py`, diff out/39b-landedits-optional.diff; code
  identical, widths ≤ 100).

**F6 (rule-10 records, note).**
- *Claim:* the worker's seal (`seal/ZRSeal-cp7.lean`, 75 names) opens after `zr_exitsContract`, so
  the first new declaration is outside it; it does not erase `Action.apply`'s `@[simp]`, and a
  local `irreducible` alone leaves `simp` free to unfold it (my control 83 closes under the
  irreducible seal); and its `isDefEq` controls pass inside for `instFintypeSeekPhase`,
  `instFintypeSweepPhase` and `Contract._sizeOf_inst`.
- *Resolution:* none needed: my seal (row 21–26) covers all three and finds nothing. For later
  briefs: require `[-simp]` on every `@[simp]` definition sealed, the seal from the first owned
  line, and concrete `rfl` controls.

**F7 (records and cosmetics, minor).**
- (a) The checkpoint zips are not in the inbox (moot; row 17).
- (b) 173 of the 500 new in-file pairs (up to 84%) are "justified by class" in the zip 1–3
  reports, which were not delivered; REPORT gives the classes (the `Cfg.ext` branches, the
  `seq_time`/`seq_lo` openings, the `zoneRowPre` readings). My sample of the top ones agrees.
- (c) The commit subjects carry campaign labels ("G4 cont4 checkpoint 1.2: …", "s13d g4 cont4:
  …"); the author is `Claude <noreply@anthropic.com>`. Not Lean text (decision 3).
- (d) REPORT lists the 36 changed inherited privates with their roles but not what changed in
  each, as region (a) asks; out/08b records it (re-indexing to `ZoneData`, the direction
  parameter, the local-fact seek precondition, the bounds).
- (e) `manifest-check.log`'s trailing list of "non-Mathlib non-TCSlib imports" holds package
  directory names and two docstring words; the check itself is clean.
- (f) `set_option synthInstance.maxSize` reaches 1024 (four times, once inside
  `exists_zoneExtendTM`'s body); the brief suggested 256 on the declaration. It only bounds
  instance search; each is declaration- or tactic-scoped.
- (g) The rebalance row's status paragraph uses this file's private vocabulary ("pinned
  branch", "pinned segment", "loop host"); fine to keep.

**F8 (environment note).**
- *Claim:* the owned module peaks at 4,496–4,506 MiB at `-j4` on the fill host (sweep-cp7, final
  sweep), above the addendum's measured 2.8 GiB and above its 4 GiB headroom floor; here it peaked
  at 3.2–3.6 GiB (rows 14–16).
- *Resolution:* update the addendum's measured needs and size replay hosts for ≥ 5 GiB headroom
  for this module.

**F9 (landing order; decision).**
- *Claim:* section (g). #161 merged during this review; #162's `lkit` passed on #161's tree and
  its gate 74 is open.
- *Resolution:* decision 4.

## Decisions for the user

1. **F5: the route refinements** (no zero-level branch; cut copies instead of `scanTM_contract`;
   the mirrored machine with `Contract.lockstep`).
   - (a) **Recommended:** accept all three and record them. Each uses fewer rows than the route
     allows and adds no public name, host or admission.
   - (b) Accept, and also apply B1/B2 so the frozen fill-plan sketches match the proofs (comment
     only).
2. **F2: the private round iteration.**
   - (a) **Recommended:** land with a ledger entry, and schedule an API PR adding the sequence form
     of `Round.iterate` to `Build/Contract/Basic` (its corollary `Round.iterate`), then re-point
     `zr_pinLoop` (a one-lemma maintainer PR, its own gate).
   - (b) Hold the landing for a short continuation that re-routes the seven passes through
     `Round.iterate` with a time read off the configuration.
   - (c) Accept as a private generalization, no follow-up.
3. **Commit form.**
   - (a) **Recommended:** `git am -3` the 37 patches as delivered (authorship kept; each checkpoint
     commit elaborates), then one maintainer commit with A1–A3 and C1 (and B1/B2 if chosen).
   - (b) The same with the subjects' campaign labels dropped.
   - (c) One squashed commit with a public-facing subject, e.g. "ZoneRebalance: the extension and
     rebalance rows proved".
4. **F9: the order against #162.**
   - (a) **Recommended: #162 first** (its replay passed; gate 74 pending), then this PR with its
     2-module replay chained from a copy of `oleans-lkit`.
   - (b) This first: the 2-module replay from a copy of `oleans-lu2api` (the current tip's exact
     tree); #162 then needs no re-replay (facade only).
   In both: never compose snapshots; never append the root `TCSlib` to a replay list.
5. **F3:** whether the missing sketches are a follow-up commit before or after landing.

## Landing

**Not yet clear to merge**: no PR is open, no replay has run, and decisions 1–4 are pending. It
becomes clear once they are ruled, the PR's base is the campaign branch, its replay has passed and
its fill gate is recorded.

**Land (full): yes**, by a maintainer PR into `complexity/arora-barak-ch3-4` (base `cfaaf75a`, or
the tip after #162).

**Commits** (from the verified bundle, prerequisite `f89c5c8da79997f4fb73bbfce04ed7f671afe206`,
ref `deliver/fill-s13d-g4-cont4-in` = `374337b0697bc0fb9fb3f6795e214d441be83482`; or `git am -3`
of the 37 patches, which apply at `cfaaf75a` unchanged, out/38): the series `f89c5c8d..374337b0`
(out/03 lists all 37 with full hashes). Then **the maintainer's edit commit**: A1–A3 and C1 from
`scripts/landedits.py` (blob `b5a31166c2c49330f543b4b419f17a587d45c18f` for the module; facade blob
`c4917d8e8faa7200a3bb467a8667c787de83bd04` at `cfaaf75a`/`5cade0b8`), optionally B1/B2 from
`scripts/landedits_optional.py`. After it: re-run the v3 screen on the edited file (expected: the
pair set unchanged but for the four users' text; `zr_contents_ext` pairs with nothing).

**Replay** (link `.lake/packages` in the PR worktree; precheck that the Lean diff from the
snapshot's tree to the PR head is exactly `Build/ZoneRebalance.lean` and `TuringMachine.lean`):
- list: `TCSlib/Complexity/TuringMachine/Build/ZoneRebalance`, then `TCSlib/Complexity/TuringMachine`
  (out/35); never the root `TCSlib`;
- from a copy of `oleans-lkit` if #162 lands first, or of `oleans-lu2api` if this lands first;
- expected: 0 failures; `Build/ZoneRebalance` no diagnostic (about 10 minutes and 4.5 GiB on a
  fill host); the facade no diagnostic; the order list 27 → 25.

**Review table for the PR body:**
- integrity: 128/128 sums; bundle (sole prerequisite the base); 37 linear commits, owned file only;
  patches = bundle = file (blob `7e42db77`);
- scope: regions (a)–(c) only; imports unchanged; 18 → 18 public declarations at source, no
  statement changed; 783 new `zr_` privates, 2 removed, 36 restated or re-proved; new public
  constants only auxiliaries;
- elaboration: no diagnostic at the base, at `5cade0b8` and at `cfaaf75a`; checkpoints bisectable;
- axioms: both targets and all 872 within `[propext, Classical.choice, Quot.sound]`, no `sorryAx`;
- rule 10: 82-definition seal with `[-simp] Action.apply`, 81/82 controls biting (the 82nd moot);
  no definition passed to `rw`/`simp`/`unfold`; `reduceCtorEq` accepted; rule 11 clean;
- probes: 448 (brief) and 501 (worker) checks, 0 errors;
- lint 0 FAIL (68/33 WARN, as at the base);
- v3 screen: 847 → 1,391 declarations, 477 → 970 pairs; 500 new in-file (≤ 88%), 0 cross-file;
  semantic: `zr_contents_ext` re-pointed (C1), `zr_pinLoop` ruled (decision 2);
- sweep 27 → 25.
