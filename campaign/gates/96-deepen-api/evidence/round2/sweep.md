# Gate 96 (PR #196, the deepening API): the inline-step sweep over the lines the PR adds

Evidence (run by a sub-agent of the cloud maintainer session, reviewed by the maintainer) for
findings 2 and 6 of `campaign/gates/96-deepen-api/findings.md`. Text-only (no build). Candidate
enumeration plus inspection, not an exhaustive search.

- **Repaired head** (local): `f2616fee1d41f75600bc9070db149d32a0c69acc` ("gate 96's repairs:
  noEdge_iff, the window step harvested, the head-form walk equation, attribution"), one commit on
  top of `origin/pr/196` = `origin/lean/deepen-window-api` = `89f4ebbc6b0d007c981f907e3353d72fa84fa787`.
- **Base:** `origin/complexity/arora-barak-ch3-4`. The three-dot diff runs from the merge base
  `4ef99963b8839877c843adc8a8b09da64ef1d8b6`. The campaign tip moved during this run (records only:
  `b325c1ef` → `db5d6a1335b5595b0fca70d32691c978aaf48648`); `git diff --stat 4ef99963 db5d6a13 --
  'TCSlib/*.lean'` is empty, so the base's Lean tree is the tip's.
- The PR's Lean diff: 10 files, +395 −36 (`SpaceComplexity.lean` facade, `Codec/Bridge`,
  `ExpBFS/Radius`, `Logspace/PathWalk`, `SavitchARM/{Reach,Recursion,Search,Setup,Window}`,
  `Build/CfgRecord`).

## Commands

Every command was run as `. /home/user/tcslib-scratch/env.sh; …`. `S` is
`$TCSLIB_SCRATCH/agents/sweeps`.

```sh
cd /home/user/tcslib
B=origin/complexity/arora-barak-ch3-4; H=f2616fee1d41f75600bc9070db149d32a0c69acc
git merge-base $B $H                      # 4ef99963…
git diff --stat $B...$H -- '*.lean'
git diff $B...$H -- '*.lean' > $S/raw/pr196-f2616fee.diff
# added lines with their new-file line numbers (file, line, text)
python3 -I - $S/raw/pr196-f2616fee.diff > $S/raw/pr196-added-lines.tsv <<'EOF'
import sys,re
cur=None; n=0
for raw in open(sys.argv[1],encoding='utf-8'):
    l=raw.rstrip('\n')
    if l.startswith('+++ '): cur=l[6:]; continue
    if l.startswith('--- '): continue
    m=re.match(r'^@@ -\d+(?:,\d+)? \+(\d+)(?:,\d+)? @@',l)
    if m: n=int(m.group(1)); continue
    if l.startswith('+'): print(f"{cur}\t{n}\t{l[1:]}"); n+=1
    elif not l.startswith('-'): n+=1
EOF
cd $S/raw
for p in 'bufferTape_eq' 'bufferTape_nat' 'List\.getElem\?_' \
  'getElem\?_append|getElem_append|getElem\?_drop|getElem_drop|getElem\?_take|getElem_take|take_concat|take_succ|drop_append|take_append' \
  'Nat\.exists_eq_add_of_le' 'runFrom_add' 'runFrom_of_halt' 'runWith_append' 'runWith_of_halt' \
  'lt_trichotomy' 'Nat\.find' 'Cfg\.ext' 'obtain ⟨\w+, rfl⟩ : ∃' \
  'Action\.apply_workTapes' 'Action\.apply_workTapePos' 'workTapePos_apply_le' \
  'Function\.update_of_ne' 'InWindow' 'inWin_' 'abs_le' 'abs_lt'; do
  printf '%-60s %s\n' "$p" "$(cut -f3 pr196-added-lines.tsv | grep -cP "$p")"; done
grep -P 'getElem\?_append|getElem_append|take_concat|take_succ|runWith_append|Action\.apply_workTape|workTapePos_apply_le|Function\.update_of_ne|InWindow|inWin_|abs_le|abs_lt' \
  pr196-added-lines.tsv
# the harvest against its source, and the pre-repair corollary
cd /home/user/tcslib
git show $B:TCSlib/Complexity/TuringMachine/Build/CfgRecord.lean | sed -n 670,705p     # recordStep_window
git show $H:TCSlib/Complexity/TuringMachine/Build/CfgRecord.lean | sed -n 113,158p     # mono, apply_iff
git show $H:TCSlib/Complexity/TuringMachine/Build/CfgRecord.lean | sed -n 5704,5724p   # apply_of_lt
git show 89f4ebbc:TCSlib/Complexity/TuringMachine/Build/CfgRecord.lean | sed -n 5694,5722p
git show $B:TCSlib/Complexity/SpaceComplexity/ExpBFS/Radius.lean | sed -n 60,92p      # inWin_mono, inWin_stepWith
```

## Counts (added lines only, 395)

| Sign | Hits | Sign | Hits |
|---|---|---|---|
| `bufferTape_eq`, `bufferTape_nat` | 0, 0 | `Cfg.ext` | 0 |
| `List.getElem?_*` | 0 | `obtain ⟨v, rfl⟩ : ∃ …` time splits | 0 |
| append/drop/take indexing (incl. `take_concat`, `take_succ`) | 1 | `Action.apply_workTapes` | 1 |
| `Nat.exists_eq_add_of_le` | 0 | `Action.apply_workTapePos` | 2 |
| `runFrom_add`, `runFrom_of_halt` | 0, 0 | `workTapePos_apply_le` | 0 |
| `runWith_append` | 1 | `Function.update_of_ne` | 1 |
| `runWith_of_halt` | 0 | `InWindow` | 20 (13 in code, 7 in docstrings) |
| `lt_trichotomy`, `Nat.find` | 0, 0 | `inWin_` | 3 |
| | | `abs_le`, `abs_lt` | 1, 1 |

## Hits and dispositions

Line numbers are those of `f2616fee`.

| File:line | Declaration | Text | Disposition |
|---|---|---|---|
| `Build/CfgRecord.lean`:118–122 | `Turing.Cfg.InWindow.mono` (new public) | `⟨fun i => (hc.1 i).trans (by exact_mod_cast hs), fun i z hz => hc.2 i z (lt_of_le_of_lt (by exact_mod_cast hs) hz)⟩` | **the canonical home** of window monotonicity, beside `Cfg.InWindow` (finding 2's (2)). Its text is `ExpBFS.inWin_mono`'s (Radius 63–67, Hydroxyi), the older member of the acknowledged window family, which the 12.2c window re-points. Not a new copy |
| `Build/CfgRecord.lean`:130–157 (139 `abs_le`; 144, 148 `Action.apply_workTapePos`; 156 `Action.apply_workTapes, Function.update_of_ne hne`) | `Turing.Cfg.InWindow.apply_iff` (new public) | the two-sided boundary condition, the `heads` case split, the off-head cell | **the harvest** of the private `recordStep_window` (tip `CfgRecord.lean` 677–704), deleted by the same commit: the body is moved unchanged; the signature is generalized (`Cfg k Bool Q x` → `Cfg k Symbol State x`, `s` and `c` implicit). Finding 2's (1). Canonical |
| `Build/CfgRecord.lean`:3635 | `recordStep_observed_action` | `rw [← step, hc.apply_iff]` | the old use of `recordStep_window s c hc` re-pointed (finding 2's (4)); citation |
| `Build/CfgRecord.lean`:5717–5723 (5721 `abs_lt`) | `Turing.Cfg.InWindow.apply_of_lt` | `((hC.mono hs).apply_iff a).mpr fun i => …` with `abs_lt.mp (hlt i)` and `omega` | **now a corollary** of `mono` and `apply_iff` (finding 2's (3)); `abs_lt` is Mathlib. The inline window step of the pre-repair version (`origin/pr/196` = `89f4ebbc`, CfgRecord 5706–5720: `workTapePos_apply_le`, `Action.apply_workTapes`, `Function.update_of_ne hzp`, `hC.2 i z (lt_of_le_of_lt (by exact_mod_cast hs) hz)`) is gone. Resolved |
| `SavitchARM/Window.lean`:115–117 | `noEdge_of_lt` | `NDTM.inWindow_of_coreSum_eq`, `ExpBFS.inWin_runWith_of_decides`, `Cfg.InWindow.core_bounds` | citations of published lemmas |
| `SavitchARM/Window.lean`:151, 153 | `mem_iff_reach_of_noEdge` (`key`, `j = 0`) | `ExpBFS.winRun_iff.mpr`, `ExpBFS.inWin_init s` | citations (`inWin_init` wraps `Cfg.inWindow_init`) |
| `SavitchARM/Window.lean`:160 | same (`hlt`) | `rcases lt_or_eq_of_le ((Cfg.InWindow.core_bounds hW.last) i).1` | a head strictly inside, or on the edge (then `NoEdge` is contradicted); Mathlib order lemma; idiom |
| `SavitchARM/Window.lean`:166–167 | same (`hstep`) | `(List.take_concat_get' wd j (by omega)).symm` | core list lemma for the prefix of length `j + 1`; idiom |
| `SavitchARM/Window.lean`:168–171 | same (`hnext`) | `rw [NDTM.runWith_append, NDTM.runWith_cons, NDTM.runWith_nil, stepWith_eq_apply]; exact hW.last.apply_of_lt hlt le_rfl _` | one more choice bit (the composition used in at least ten files; no published `runWith_concat`), then `Codec.stepWith_eq_apply` and the new corollary. This is the step `ExpBFS.inWin_stepWith` makes at `s + 1`, made here at `s` with strict heads, **by citation**; idiom |
| `ExpBFS/Radius.lean`:97–103 | `winRun_iff` (new public) | statement, `Iff.rfl` | n/a |
| docstrings: `ExpBFS/Radius.lean`:100; `SavitchARM/Window.lean`:103–104, 132; `Build/CfgRecord.lean`:73, 76, 5715–5716 | — | text | n/a |

Not on the sign list but inspected: `SavitchARM/Reach.lean` `chain_of_walkLe` (117–150) shifts
chain indices with `Nat.add_sub_cancel`, `Nat.sub_add_cancel`, `Nat.eq_zero_or_pos` (core), and
`reach_of_reflTransGen` (162–175) uses Mathlib's `Relation.ReflTransGen.cases_tail` and `.mono`;
both cite `walkLe_zero_iff`, `walkLe_succ_iff_head`, `reach_iff_walkLe` and `reach_of_chain`. No
re-derivation.

## Result

- **No added line re-derives a published lemma.** The window step is now stated once, as
  `Cfg.InWindow.apply_iff` (the harvested `recordStep_window`) with `Cfg.InWindow.mono`, and
  `apply_of_lt` and the window module reach it by citation.
- The older copies of the same facts (`ExpBFS.inWin_mono`, `ExpBFS.inWin_stepWith`, the window half
  of `Codec.boundary_iff`) are untouched by the PR and belong to the acknowledged family; the
  family's full candidate list is `window-family-members.md`.
- The pre-repair text of `apply_of_lt` is still on `origin/pr/196` until the repair is pushed; the
  shape search (`gate96-shape-search.md`) reports it on the PR's two refs.
