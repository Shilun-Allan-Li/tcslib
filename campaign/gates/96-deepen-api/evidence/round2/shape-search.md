# Gate 96 (PR #196): the statement-shape search over every ref

Evidence (run by a sub-agent of the cloud maintainer session, reviewed by the maintainer) for
finding 6 of `campaign/gates/96-deepen-api/findings.md` (and the family scope of finding 2). For
each new public statement of #196 at the repaired head `f2616fee`, its key subterms were grepped
over the `.lean` files of every fetched ref, then every candidate was read and given a disposition.
Candidate enumeration plus inspection, not an exhaustive search. Shapes, not names: the patterns
match subterms (`InWindow s'`, `.apply … ).InWindow`, `|… workTapePos …| ≤` or `<`,
`WalkLe … (j + 1)`, `StepRel … ↔`, `).toV =`, `edgeLang`, `x ∈ L ↔ ∃ u < 2 ^ w`, …) and the inline
forms that would re-derive them (`simp only [WalkLe]`, `rw [StepRel, …]`,
`lt_of_le_of_lt (by exact_mod_cast hs)`, `update_of_ne` beside a blank-outside clause).

**Population.** 340 remote refs (`refs/remotes/origin/*`; no `origin/HEAD`), 339 of which carry
`.lean` files: 261,209 (ref, file) pairs, **2,119 distinct blobs**, about 84 MB. Each distinct blob
is grepped once and every hit is reported with the number of refs holding that (path, line text),
whether the campaign tip holds it, and sample refs. The local repaired head `f2616fee` (not on any
remote ref) is added as an extra tree, and the ref counts below include it as one tree (so a line
held by the tip and by `f2616fee` on 207 remote refs shows 208). The campaign tip moved during the run by records commits
only (`b325c1ef` → `db5d6a13`, no `.lean` file changed), so the index is valid for `db5d6a13`.
`.lean` files under `campaign/` (probe and draft copies in review folders) are record copies, not
library code; their hits are listed once at the end.

## Commands

Every command was run as `. /home/user/tcslib-scratch/env.sh; …`, from `/home/user/tcslib`.
`S` is `$TCSLIB_SCRATCH/agents/sweeps`; the scripts are `$S/shape_grep.py`,
`$S/window_decls.py`, `$S/window_decls_wide.py`, `$S/tapehalf_decls.py` (read-only: they read blobs
with `git cat-file --batch`).

```sh
git for-each-ref --format='%(refname)' refs/remotes/origin | grep -v 'origin/HEAD$' > $S/raw/refs.txt
while read r; do git ls-tree -r "$r" | awk '$4 ~ /\.lean$/ {print $3"\t"$4}' | sed "s#^#$r\t#"; done \
  < $S/raw/refs.txt > $S/raw/ref-blobs.tsv                  # 261,209 rows, 2,119 distinct blobs
python3 -I $S/shape_grep.py $S/raw/ref-blobs.tsv $S/raw/pat-shapes.tsv \
  f2616fee=f2616fee1d41f75600bc9070db149d32a0c69acc > $S/raw/out-shapes.txt
python3 -I $S/shape_grep.py $S/raw/ref-blobs.tsv $S/raw/pat-strict.tsv \
  f2616fee=f2616fee1d41f75600bc9070db149d32a0c69acc > $S/raw/out-strict.txt
python3 -I $S/shape_grep.py $S/raw/ref-blobs.tsv $S/raw/pat-tov.tsv \
  f2616fee=f2616fee1d41f75600bc9070db149d32a0c69acc
python3 -I $S/shape_grep.py $S/raw/ref-blobs.tsv $S/raw/pat-window-defs.tsv \
  f2616fee=f2616fee1d41f75600bc9070db149d32a0c69acc > $S/raw/out-window-defs.txt
# non-tip hits, to find candidates only on PR heads or old branches
for f in out-shapes.txt out-window-defs.txt; do awk '/^===/{lab=$2} /^[^ =].*\trefs=/{line=$0; getline s; if (line ~ /\t-\t/) print lab"\t"line"\t"s}' $S/raw/$f; done
```

`$S/raw/pat-shapes.tsv` (label, Python regex, one line each, matched line by line):

```
S1a-mono-grown-radius	InWindow (s'|\(s \+ 1\)|\(\w+ \+ \w+\)|\(max )|InWin \w+ (s'|\(s \+ 1\))
S1b-mono-inline	lt_of_le_of_lt \(by exact_mod_cast|\.trans \(by exact_mod_cast|\(by push_cast; omega\), fun i p hp => hblank
S1c-mono-names	(theorem|lemma)\s+\S*(mono|_le_of_le|_of_le)\b.*([Ww]indow|InWin|inWin)|([Ww]indow|InWin|inWin)\S*mono
S2a-apply-window	(\.apply [^\n]*\)\)?\.InWindow|InWindow[^\n]*\.apply\b|InWin [^\n]*\.apply\b|InWindow[^\n]*stepWith|InWin [^\n]*stepWith|InWindow[^\n]*\.step\b|InWindow[^\n]*\+\+ \[)
S2b-head-cross	workTapePos [a-z] = -\(?s|workTapePos [a-z] = \(?s|\.2 = -1|\.2 = 1\)|= \.neg → |= \.pos → 
S2c-apply-fields	workTapePos_apply_le|Action\.apply_workTapePos|Action\.apply_workTapes
S3-abs-head	\|[^|\n]*workTapePos[^|\n]*\| (<|≤)
S4-walk-zero	WalkLe [^\n]* 0 [a-z(]|walkLe_zero|unfold WalkLe|\[WalkLe\]|simp only \[WalkLe
S5-walk-succ	WalkLe [^\n]*\(\w+ \+ 1\)|walkLe_succ|∃ v, v < n ∧ E c v
S6-steprel	StepRel [^\n]*↔|unfold StepRel|\[StepRel[\],]|stepRel_iff|StepRel[^\n]*stepLang|stepLang[^\n]*StepRel
S7-winrun	WinRun[^\n]*↔|unfold WinRun|\[WinRun[\],]|winRun_iff
S8-rcode	RCode[^\n]*ReflTransGen|unfold RCode|\[RCode[\],]|rcode_iff
S9-reach-rtg	ReflTransGen[^\n]*Reach |Reach [^\n]*ReflTransGen|reach_of_reflTransGen|reach_iff_walkLe|walkLe_short|exists_walkLe|mem_ball_iff_rcode|reach_of_chain
S10-rel	Rel orc[^\n]*↔|unfold Rel\b|\[Rel[\],]|rel_iff_orc|orc 3 \(pairEncode
S11-initacc	(InitO|AccO)[^\n]*↔|unfold (InitO|AccO)|\[(InitO|AccO)[\],]|(initO|accO)_iff|orc [12] \(pairEncode
S12-setst	setSt [^\n]*\)\.toV|toV[^\n]*setSt|St\.upd_[swK]\b|St\.toV_zero|setSt_toV
S13-outerst	outerSt [^\n]*\)\.toV|St\.upd_[UVM]\b|outerSt_toV
S14-edge	edgeLang|NoEdge|noEdge
S15-beyond	sp x\.length < s|sp \|x\| < s|card_rset_succ_of_le|inWin_runWith_of_decides
S16-exact	x ∈ L ↔ ∃ u < 2 \^ w|acceptLang N ∧|mem_iff_reach\b|mem_iff_of_card_eq|winRun_of_card_eq|WinRun\.snoc
```

`pat-strict.tsv`: `S3b-strict-head	\|[^|\n]*workTapePos[^|\n]*\| <`. `pat-tov.tsv`:
`S12b-toV-eq	\)\.toV =|toV = Function\.update|\.toV = fun`. `pat-window-defs.tsv`: window-named
definitions and theorems (see `window-family-members.md`). Hit totals (distinct (path, text)):
S1a 9, S1b 31, S1c 8, S2a 13, S2b 17, S2c 159, S3 286, S3b 2, S4 12, S5 16, S6 13, S7 4, S8 29,
S9 36, S10 18, S11 22, S12 21, S12b 3, S13 12, S14 59, S15 19, S16 32. The large S2c and S3 sets
(action field equations and head bounds in every machine construction) were narrowed by
declaration, by the family enumerators of `window-family-members.md`; the rest were read one by
one.

**Refs of the PR itself.** Every hit on the new statements and their in-PR uses sits on exactly
`origin/lean/deepen-window-api` and `origin/pr/196` (both `89f4ebbc`, the pre-repair head) and
the local `f2616fee`; the repair-only statements (`mono`, `apply_iff`, `walkLe_succ_iff_head`,
`noEdge_iff`) are on `f2616fee` alone. Those rows are not repeated below. Paths are under
`TCSlib/Complexity/`; "tip" means the campaign tip holds the line (with the ref count).

## 1. `Turing.Cfg.InWindow.mono` — window monotonicity (S1a, S1b, S1c)

| Site | Refs | Disposition |
|---|---|---|
| `SpaceComplexity/ExpBFS/Radius.lean`:63–67 `ExpBFS.inWin_mono` | tip, 208 | same statement for `FinNDTM` configurations, same proof text; **member of the acknowledged window family** (named by the auditor); 12.2c re-point |
| same file, older revision (`InWin N s C`), lines 72–74 | 27 (`complexity/arm-extensions`, `lean/arm-minor-fixes`, `lean/b5a-canon-cont3`, `lean/b6-f2-windowrun`, …) | the same member before `Cfg.InWindow` was relocated; superseded at the tip |
| `ClassNP/ExhaustiveReplay.lean`:77–78, halted branch of `xr_window_stepWith` | tip, 123 | inline `s → s + 1` monotonicity on `Cfg.InWindow`'s two clauses written out; **family member** (not named by the auditor), see `window-family-members.md` |
| `ExpBFS/Radius.lean`:110 `WinRun.mono`, 74 (`exact inWin_mono h (by omega)`), 336 (`card_rset_succ_of_le`) | tip, 235 | cite `inWin_mono`; consumers |
| `.trans (by exact_mod_cast …)` elsewhere: `BooleanAnalysis/…/Tensorization` 523, `Randomized/ErrorReduction` 400, `ExpectedTime` 259, `ZPPHosts` 186, `Logspace/InputAccess` (8 sites), `Logspace/PreimageHost` 301/517, `Machines/ARMProof` 133, `Machines/Clean` 436, `Cryptography/Foundations/Negligible` 141 (20 non-tip refs) | — | monotone numeric bounds, no window; unrelated |

## 2. `Turing.Cfg.InWindow.apply_iff` — one action keeps a window iff no head crosses (S2a, S2b, S2c)

| Site | Refs | Disposition |
|---|---|---|
| `TuringMachine/Build/CfgRecord.lean`:677–704 `recordStep_window` (private) | tip, 290 | **the source of the harvest**: moved verbatim into `apply_iff`, deleted at `f2616fee` |
| `SpaceComplexity/Codec/Step.lean`:195–244 `Codec.boundary_iff`, the window half (after `rw [left, right]`: `(∀ i, move = .neg → pos ≠ -s) ∧ (∀ i, move = .pos → pos ≠ s) ↔ InWindow s (a.apply C)`) | tip, 208; older `InWin N` revision from 194 on 27 refs | `apply_iff` up to the form of the boundary condition, re-proved by `simp only [Action.apply]`; **family member** (named by the auditor) |
| `SpaceComplexity/ExpBFS/Radius.lean`:70–92 `ExpBFS.inWin_stepWith` | tip, 208; `InWin N` revision 78 on 27 refs | the `s → s + 1` instance; **family member** (named) |
| `Codec/Step.lean`:254 `slide_step_iff`, 476 `sDone_step`; `Codec/Checks.lean`:335 `stepChk_iff`, 308 `aI_cfgWord` | tip | cite `boundary_iff`; consumers |
| `ClassPSPACE/TQBF.lean`:1505 `codec_step_blank` (private) | tip, 282 | the tape half at the same radius; **family member** (not named), see the family file |
| `TuringMachine/Build/CfgRecord.lean`:1043–1060 (`recordStepOutside`), 964–1205 and 1840–2215 (`decide (c.workTapePos i = ±s)` edge flags) | tip | the record machine's computable boundary test and its field encodings (definitions); joined to `apply_iff` by `recordStep_observed_action` (3618, now citing it); not re-derivations |
| `SpaceComplexity/Codec/Checks.lean`:486, 493 (`decide (C.workTapePos i = ±s)`) | tip, 16 | the edge check behind `edgeLang`; definition-level; not a re-derivation |
| `SpaceComplexity/ConfigGraph.lean`:575–641 (`∃ c b, c.InWindow s ∧ (tm.stepWith b c).InWindow s ∧ …`, `s1b_recordEdge`) | 61 non-tip refs (`audits/b5b-r2`, `dedup/ch34-d4`, `integrate/fills-6`, …) | an older edge relation; window transferred through `inWindow_of_coreSum_eq`, no window step proved; superseded |
| `SpaceComplexity/SavitchARM/Window.lean`:168–171 | #196 | cites `apply_of_lt` |

## 3. `Turing.Cfg.InWindow.apply_of_lt` — strict heads, a step stays in the window (S3b, S2a)

| Site | Refs | Disposition |
|---|---|---|
| strict head bound `\|… workTapePos …\| <` anywhere | only #196 (`CfgRecord` 5718, `Window` 158) | no other statement of this shape on any ref |
| `ExpBFS/Radius.lean`:70 `inWin_stepWith` | tip | the `s' = s + 1` case (every window head is strictly inside `s + 1`); family member, row 2 |
| `CfgRecord.lean`:5706–5720 at `89f4ebbc` | `origin/pr/196`, `origin/lean/deepen-window-api` | the pre-repair inline proof (finding 2); replaced at `f2616fee` by the corollary |

## 4–5. `Complexity.walkLe_zero_iff`, `Complexity.walkLe_succ_iff_head` (S4, S5)

| Site | Refs | Disposition |
|---|---|---|
| `SpaceComplexity/Logspace/ISCountMath.lean`:120 `ISCount.walkLe_succ_iff` | tip, 235 | the **last-edge** form `WalkLe R K (j+1) c t ↔ WalkLe R K j c t ∨ ∃ w, WalkLe R K j c w ∧ R w t ∧ t < K`, proved by induction (its `j = 0` case by `simp only [WalkLe]`, 124); a different equation from the head form (finding 3); not a copy |
| `Logspace/ISCountGenWalk.lean`:83–105 (`simp only [WalkLe, he, …]` at `dd = 0` and `dd + 1`) | tip, 235 | inline unfoldings of `WalkLe`'s two clauses in a colleague's file (cross-file unfolding); nothing re-stated; consumers the two new equations serve (12.2c re-point candidates) |
| `Logspace/PathWalkMachine.lean`:429–439 (same) | tip, 235 | same as above |
| `Logspace/PathWalk.lean`:65–67 (definition), 76 `walkLe_succ` (monotone in `j`), 133 `key` inside `walkLe_short` | tip, 235 | the definition's home; in-home reads; `walkLe_succ` is a different fact |
| `SavitchARM/Reach.lean`:129 `ISCount.walkLe_succ_iff` use, with the `ISCountMath` import | `origin/pr/196` (`89f4ebbc`) | the pre-repair route; at `f2616fee` it cites `walkLe_succ_iff_head` and the import is gone |

## 6. `Complexity.Codec.stepRel_iff_mem` (S6)

| Site | Refs | Disposition |
|---|---|---|
| `SpaceComplexity/ExpBFS/Radius.lean`:167 `rw [StepRel, mem_stepLang]` (in `rcode_iff`) | tip, 235 | cross-file unfolding of `Codec.StepRel`; the use the equation serves; not a re-derivation |
| `SpaceComplexity/Logspace/PathHard.lean`:232 `simpa [StepRel] using …` (`open Codec`) | tip, 235 | same |
| `Randomized/BPLInPCount.lean`:112 `BPLInP.stepRel_iff` | tip, 57 | a different statement (the coin-`b` successor code from a reachable code); reads `StepRel` by defeq into `mem_stepLang` (119); the name clash the PR avoided |
| `Logspace/ISCountGenRadius.lean`:80, 121 | tip | `StepRel` inside ball statements; not the equation |

## 7. `Complexity.ExpBFS.winRun_iff` (S7)

No site outside the PR. `WinRun` is read by application in its home (`Radius`: `WinRun.snoc`,
`.mono`, `.last`) and through those lemmas elsewhere (`ISCountGenRadius` 151).

## 8. `rcode_iff_reflTransGen` (S8)

| Site | Refs | Disposition |
|---|---|---|
| `SpaceComplexity/ExpBFS/Main.lean`:98–104 (`∀ w, ExpBFS.RCode N x r w → ReflTransGen …`, then `induction hw`) | tip, 235 | reads `RCode` as its `ReflTransGen` body by defeq in a colleague's file; the use the equation serves; not a re-derivation |
| `Logspace/ISCountGenRadius.lean`:88–92 (`hpath`, same) | tip, 235 | same |
| `ExpBFS/Radius.lean`:142 `rcode_iff` and its uses (176–352) | tip, 235 | a different statement (reachable codes are codes of window runs); in-home |

## 9. `reach_of_reflTransGen` (S9)

| Site | Refs | Disposition |
|---|---|---|
| `Logspace/ISCountGenRadius.lean`:79 `ISGen.mem_ball_iff_rcode` | tip, 235 | a ball of the walk relation is the reachable codes; shares the one shortening argument (`exists_walkLe`, `walkLe_short`), not a copy (finding 10) |
| `SavitchARM/Reach.lean`:213 `mem_iff_reach` (chain cut by `reach_of_chain` 225) | tip, 235 | shortens runs (`mem_iff_codeChain`), not paths; not a copy (finding 10) |
| `Logspace/PathWalk.lean`:102 `exists_walkLe`, 119 `walkLe_short`, 184 `reach_iff_walkLe`, 401–423 | tip, 235 | the cited sources and their in-home uses |

## 10–11. `rel_iff_orc`, `initO_iff_orc`, `accO_iff_orc` (S10, S11)

| Site | Refs | Disposition |
|---|---|---|
| `SpaceComplexity/SavitchARM/Correct.lean`:55–71 `rel_orcN`, `initO_orcN`, `accO_orcN` | tip, 235 | specializations at the concrete oracle `orcN N`, with Codec-level right sides, proved by `simp [Rel/InitO/AccO, orcN, decs, indicator_eq_decide]` (cross-file unfolding inside `SavitchARM`); not re-statements of the defining equations; optional 12.2c re-point through them |
| `SavitchARM/Recursion.lean`:150–163, `SavitchARM/Search.lean`:148–259 (`have hr' : orc 3 (…) := hr`, `ha'`, `hi'`) | tip | defeq reads in the definitions' homes; legal |
| `SpaceComplexity/ExpBFS/Main.lean`:131–192, `ExpBFS/Relax.lean`:61–65, 202, 320 | tip, 235 | the ExpBFS machine's own decider queries (other layouts); not `Rel`/`InitO`/`AccO` |
| `ClassPSPACE/TQBFARM/Machine.lean`:91 | tip, 235 | another machine's oracle; unrelated |

## 12–13. `setSt_toV`, `outerSt_toV` (S12, S12b, S13)

| Site | Refs | Disposition |
|---|---|---|
| any `(…).toV = Function.update …` / `).toV =` statement | only #196's two and `Logspace/ISCountRegs.lean`:135 `ISCount.St.toV_zero` (`zero.toV = fun _ => 0`, another register type) | no other register-file equation of this shape on any ref |
| `SavitchARM/Setup.lean`:139–147 (`setup_run`), `SavitchARM/Search.lean`:108–223 (`outerU_run` …) | tip, 235 | mention `(setSt …).toV` / `(outerSt …).toV` in run statements; consumers |
| `St.upd_*` simp lists in `TQBFARM/Machine` 202–207, `ExpBFS/Machine` 273–289, `ISCountRegs` 291–301, `PathHardRegs` 275–292, `SavitchARM/Machine` 280–287 | tip | each machine's own register simp set; not `toV` equations |
| `Logspace/PathHardRun.lean`:114 `(setSt Y …).toV` | tip, 235 | PathHard's own `setSt` (another definition); consumer in its file |

## 14–15. `NoEdge`, `noEdge_iff` (S14)

| Site | Refs | Disposition |
|---|---|---|
| `SpaceComplexity/Codec/Langs.lean`:95 `edgeLang`, 103 `mem_edgeLang_iff`, 172 `mem_edgeLang`; `Codec/Checks.lean`:512 `edgeLang_iff`; `Codec/Deciders.lean`:760 `edgeLang_mem` | tip, 16 | the language `NoEdge` reads and its published lemmas; no statement of "no reachable edge code" anywhere else |
| `CircuitComplexity/LogspaceUniformAdj*`, `…Canon`, `…Example`, `…Walk` (`DAGCircuitFamily.edgeLang`) | tip, 335 | a circuit's EDGE language; unrelated name |
| the names `NoEdge`, `noEdge` | only #196 | no clash |

## 16. `noEdge_of_lt` (S15)

| Site | Refs | Disposition |
|---|---|---|
| `SpaceComplexity/ExpBFS/Radius.lean`:327 `card_rset_succ_of_le` (and its citations in `ExpBFS/Main`, `ExpTime`, `ISCountGenCorrect`, `ISCountGenMachine`, `ImmermanSzelepcsenyi`) | tip, 235 | counts agree above the space bound; shares only `inWin_runWith_of_decides` (finding 10); not a copy |
| `ExpBFS/Radius.lean`:305 `inWin_runWith_of_decides` | tip, 235 | cited |

## 17. `mem_iff_reach_of_noEdge` (S16)

| Site | Refs | Disposition |
|---|---|---|
| `SavitchARM/Reach.lean`:213 `mem_iff_reach` | tip, 235 | the same right side under `sp \|x\| ≤ s` and a configuration-count bound, proved through code chains; the new lemma drops both hypotheses; not a copy |
| `ExpBFS/Radius.lean`:258 `winRun_of_card_eq`, 284 `mem_iff_of_card_eq` | tip, 235 | the same skeleton (prefix induction with `WinRun.snoc`, then `rcode_iff` and `mem_acceptLang`), closed by equal counts instead of `NoEdge`; a shared pattern (finding 10), not a copy |
| `Codec/Bridge.lean`:146 `mem_of_codePath` | tip, 235 | cited for (⇐) |
| `Logspace/ISCountGenRadius.lean`:140–152 | tip, 235 | consumer of `winRun_of_card_eq` |

## Record copies under `campaign/`

`campaign/fills/c1/reviews/exhaustive-cont1/probe/XR*.lean` (10 files, 109–110 refs) carry copies of
`ExhaustiveReplay`'s `xr_window_stepWith` (S1b, S2c, S3);
`campaign/fills/c1/reviews/window-cont1-r3/out/…InputWindow*.lean` (S2c) and
`campaign/fills/b6/reviews/configclock-cont1/probe/*.lean` (S3) carry review copies of
`InputWindow` and `WindowClock`. They are evidence, not library code, and are not counted.

## Result

- **No candidate on any ref re-derives one of #196's new statements outside the acknowledged
  window family.** The only re-derivations are the window family's members (rows 1–2, and
  `window-family-members.md`).
- The `Iff.rfl` equations have no restatement anywhere; their would-be users are cross-file
  unfoldings or defeq reads in colleagues' files: `WalkLe` (`ISCountGenWalk` 83–105,
  `PathWalkMachine` 429–439, `ISCountMath` 124), `StepRel` (`ExpBFS/Radius` 167, `PathHard` 232,
  `BPLInPCount` 119), `RCode` (`ExpBFS/Main` 98–104, `ISCountGenRadius` 88–92), `Rel`/`InitO`/`AccO`
  (`SavitchARM/Correct` 55–71). These are 12.2c re-point candidates, not duplication.
- No open-PR or archive ref carries a candidate absent from the tip, apart from older revisions of
  tip declarations (the `InWin N` revisions on 27 refs, the older `ConfigGraph` on 61) and #196's
  own two refs.
