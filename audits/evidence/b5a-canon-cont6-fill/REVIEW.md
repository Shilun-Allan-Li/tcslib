# Review — B5a canonizer, continuation 6 (`CodeSimulator.lean`), delivery `fill-b5a-canon-cont6.zip`

**Verdict: partial (phases 1–2 of 4), landable as a partial, preferably with a small re-pointing
(F1).** The stub
`exists_canonGrammarStage` keeps its `sorry`. The delivery adds five checked private lemmas in
the home:
- the fresh-anchor adapter `canonReturnAdapter` (phase 1, as authorized: a composition over
  `phaseHostTM`, two dispatch steps, a positive first-return contract);
- its C2 instance `exists_canonRecordRound`;
- the generic counter-loop link `canonCounterRepeat`, with its parser induction
  `canonRepeat_orbit` and the bridge `canonRepeat_last` (phase 2).

What passes:
- every integrity, ownership, freeze and hygiene check;
- elaboration at the base and at the stack top (`5333b29b`);
- the axiom prints and the headline's admission walk (only the stub);
- the four probes re-run on the delivered module (241/241, 118/118, 15/15, note 50);
- lint;
- the v3 screen: 2,411 → 2,416 declarations, 2,631 pairs before and after, no new pair; my
  after-screen is byte-equal to the worker's.

Three findings:
- **F1 (minor, rule 10).** Two steps of `exists_canonRecordRound` close by definitional
  unfolding of another file's definition, `Cfg.mapState` (`StateRenaming.lean`). This is the same
  class as G4 cont1's F1. The published `Cfg.mapState_workTapes` is fully applied
  (`… .workTapes a a_1 = …`), so `simpa only [c, Cfg.mapState_workTapes] using word` cannot
  rewrite the partial application `(c).workTapes bound`; `simpa`'s closing `exact` unfolds
  `mapState`. A verified re-pointing is below. REPORT's "No foreign TCSlib definition is
  unfolded" is therefore not quite true.
- **F2 (progress).** Phase 3, the stage itself, is not started: C1 is not embedded, there is no
  inner or outer loop machine, no counter initialization, no suffix scan and no ledger. The
  components delivered are on the brief's route and fit the assembly (see (c)).
- **F3 (for the continuation).** The assembly must convert between C1/C2's `counterValue w`, the
  counter loop's `Nat.ofDigits 2 (w.map Bool.toNat)` and the header's `codeBitsNat bits`. At
  this base no published equation states `counterValue` or `codeBitsNat` (only
  `counterValue_bits`, `codeBitsNat_bits` and `foldr_bit_eq_ofDigits`). The stack's #122 adds
  exactly these two equations (`counterValue_eq`, `codeBitsNat_eq`; commit `b6627401`, "C1-R's
  E1"). Continuation 7 should be based after #122 merges. The probe is below.

## Inputs

| Input | Identity |
|---|---|
| Zip | `infra_local/fill-b5a-canon-cont6.zip`, SHA-256 `f63f6cfa…7cf040` (`zip-sha.txt`); 12 entries (`zip-list.txt`) |
| Extraction | `$S/incoming/b5a-canon-cont6/`: every member byte-equal to the zip, no unsafe entry, no symlink, CRC OK (`zip-vs-extracted.txt`, `scripts/zipcmp.py`) |
| Brief | `infra_local/fill-dispatches/b5a-fill-canon-cont6.md`, `4c9f226e…44ef722`; the base's and `wt-hk`'s `briefs/b5a-fill-canon-cont6.md` with both `@ANCESTOR@` → base are byte-equal to it (`brief-check.txt`). REPORT quotes the same hash |
| Addendum | v1, `a25474c5…8d2928`, byte-equal to the base's `briefs/fill-environment-addendum.md` (`brief-check.txt`) |
| Base | `94b986d4db7167ab2a8b20d38d4385f11e60be0e`; TCSlib tree `11fcef24` = `531b98a2`'s (`trees.txt`) |
| Snapshots | `oleans-lbapi4` (base), `oleans-lx2` (stack top) |
| Stack top | `5333b29bf1032ccf8f754b389db303f641d9c59b` (#122–#126 on #121's tip) |
| Review ref and worktrees | `refs/review/b5a-canon-cont6` (fetched from the bundle). Detached worktrees under this folder: `wt-base` (base), `wt-head` (head), `wt-tipd` (stack top plus the delivered patch). Each has the `.lake/packages` link |

Every path below is relative to `$S/review/b5a-canon-cont6-fill/`. Lean ran only through
`tools/leanelab.sh`, one elaboration at a time. The screen ran alone under `nice -n 10`. No build
command was run. The shim `evidence/runtime/executable-path.c` (`985924ad…4fba7`, the addendum's
authorized hash) was neither compiled nor run. Before elaborating, I read the whole diff (outside its
hunks the delivered file is the base's, rows 6–7).

## (a) Integrity and scope

| # | Check | Result | Evidence |
|---|---|---|---|
| 1 | `SHA256SUMS` | PASS: 11/11 OK; covers every member except itself | `sha256sums-check.txt` |
| 2 | Bundle | PASS: `verify` okay; sole prerequisite `94b986d4…`; one ref `fill/b5a-canon-cont6` = `a406c7eeb44998aa54d7a115a4832ba7c4ffd41e` | `bundle-verify.txt` |
| 3 | Head commit | PASS: one commit; sole parent exactly the base; the hash matches REPORT ("`a406c7ee…`"); changes only `TuringMachine/CodeSimulator.lean` (+337/−7) | `head-commit.txt` |
| 4 | Patch | PASS: `0001-…patch` applied to a temporary index at the base reproduces the head tree `5df5250c` | `patch-check.txt` |
| 5 | Delivered file | PASS: byte-equal to the head blob `1e8cffb9` (SHA-256 `f2c09748…f2ce7b`, as REPORT) | `file-agreement.txt` |
| 6 | Owned regions | PASS: 323 lines inserted at the home (before base 4627); the grammar appendix (base 4640–4645) rewritten as "Fill appendix (canonizer continuation 6)"; the headline docstring's last line re-emitted with a flagged cont6 appendix before ` -/`. 0 lines outside | `regions.txt`, `worker.diff` |
| 7 | Code outside the home | PASS: with the home removed, the comment-stripped code is identical to the base (4,125 code lines) | `codeonly.txt`, `stmtcheck.txt` |
| 8 | Freeze (`declfreeze.py`) | PASS: public 12 → 12, none added or removed, no `STATEMENT CHANGED`. Its "UNAUTHORIZED BODY CHANGE: exists_polyCanonizer" is the authorized docstring appendix (row 7: no code change) | `declfreeze.txt` |
| 9 | Private statements (`privstmt.py`) | PASS: `STATEMENT CHANGED: []`; private 144 → 149 (the five new); body/docstring-only changes: the stub (appendix) and the headline (appendix) | `privstmt.txt` |
| 10 | Hygiene (337 added lines) | PASS: no `sorry`/`admit`/`axiom`/`unfold`/`delta`/`set_option`/`native_decide`/`open`/`section`/`variable`/attribute (the one "decide" hit is docstring prose). The one non-`only` `simp` (`simp [redirect, distinct.eq_iff]`) unfolds a local `let`. Every `rfl` closes a local `let` or a core reduction (confirmed by the seal below) | `hygiene.txt` |
| 11 | Rule 11 | PASS: no citation of the six R3 rows; `canonPreserveInstall` untouched (outside the home, row 7) | `hygiene.txt` |
| 12 | Imports | PASS: unchanged | `worker.diff` |
| 13 | Widths | PASS: added lines at most 100 characters; the file's one line over 100 (1145, 102) is the base's | `hygiene.txt` |
| 14 | Rewrite arguments | PASS: every identifier in the added `rw`/`simp`/`simpa` lists is a theorem, a hypothesis, a local `let` (`port`, `redirect`, `initial`, `c`, `T`) or an own-file private (`canonSkipRepeat_add`, `canonRepeat_last`). No definition is passed | `rwargs.txt` |
| 15 | Size | 5,271 → 5,601 lines; 12 public / 144 private → 12 / 149 (REPORT agrees) | `lint-tm-head.out` |

**New private declarations** (head lines, `decl-lines.txt`):

| Declaration | Line | Role | Used by |
|---|---|---|---|
| `canonReturnAdapter` | 4637 | phase 1: generic adapter. From a source `M` with entry and injective Boolean exits it builds `phaseHostTM` over `Option Bool` phases (anchor `⟨some true, entry⟩` dispatches to `⟨some false, entry⟩`; `exit true` ↦ anchor, `exit false` ↦ escape `⟨none, entry⟩`). A first verdict at `t` becomes a round of exactly `t + 2` steps whose endpoint is the source's with the state renamed; every interior state has phase tag `some false`, so C2's own revisits of `entry` never meet either port | `exists_canonRecordRound` |
| `exists_canonRecordRound` | 4718 | C2 wrapped by the adapter: C2's preconditions; verdict `anchor`/`escape` by `codeSkipActionK k (counterValue w)` at the native suffix; output, work tapes and heads restored; suffix address; bound `(a + 2)(|x| + |w| + 1)`; positive time and the interior cut | (the stage, next round) |
| `canonRepeat_last` | 4776 | `codeSkipRepeat r (n + 1) xs = (codeSkipRepeat r n xs).bind r`, from the own `canonSkipRepeat_add` and the public `_succ`/`_zero` | `canonRepeat_orbit` |
| `canonRepeat_orbit` | 4795 | the parser induction over `roundOrbit`: all `n` rounds succeed with the invariant and the right tail, or the first failure at `0 < j ≤ n` is at the escape | `canonCounterRepeat` |
| `canonCounterRepeat` | 4857 | phase 2: generic link. A counter loop over a returning round specification (positive, `≤ B`, interior cut, verdict by `r`, invariant and tail on success) decides `codeSkipRepeat r n`. Exact time `Σ_{i<j} τ + counterOverhead w (j + [success])`, bound `n(B + 4) + 2|w| + 2`, residual counter (all `true` or `counterWord w j`), strict done/escape cut. It applies `counterLoopTM_run_done` or `_run_escape` once, and `counterLoop_time_le`/`counterOverhead_le_of_le` | (the stage) |

All five have docstrings; four carry a "Proof sketch" (`canonRepeat_last`, 10 lines, has none;
under policy §3's threshold). The statements in REPORT ("Adapter statement", "Generic
repetition statement") are verbatim the delivered ones.

**Rule 10 by sealing** (the G4 cont1 method; `scripts/mkseal6.py`, `seal-names.txt`):
- **Method.** The home is wrapped in a section that makes 13 other-file definitions
  `local irreducible`: `Cfg.mapState`, `MultiTapeTM.runFrom`, `MultiTapeTM.step`,
  `phaseHostTM`, `FinTM.bufferTape`, `codeSkipActionK`, `counterValue`, `codeSkipRepeat`,
  `roundOrbit`, `counterLoopCfg`, `counterLoopTM`, `counterOverhead`, `counterWord`. These are
  every non-type, non-abbrev definition the home reaches (`direct-head.out`).
  `counterLoopOrbit` (an `abbrev`, the brief's N3 pitfall) is not sealed.
- **Controls.** Two `rfl` examples inside the sealed section fail as they must
  (`counterValue w = Nat.ofDigits …`, `(d.mapState f).inputPos = d.inputPos`;
  `seal-head-controls.out`).
- **The head.** Exactly two errors, both in `exists_canonRecordRound`, head lines 4749 and 4751
  (`seal-head.out`). Sealing only `Cfg.mapState` reproduces both (`seal-onlyMapState.out`):
  ```lean
      (by simpa only [c, Cfg.mapState_workTapes] using word)
      ...
      (by simpa only [c, Cfg.mapState_workTapes, Cfg.mapState_workTapePos] using blank)
  ```
  The `simps` lemma is `(Cfg.mapState f cfg).workTapes a a_1 = cfg.workTapes a a_1`
  (`simps-statements.out`). It is fully applied, so it does not fire on `.workTapes bound`.
- **Verified fix (F1)** (`suggested-fix.diff`, script `scripts/fix_f1.py`):
  ```lean
      (by funext z; simpa only [c, Cfg.mapState_workTapes] using congrFun word z)
      ...
      (fun j hj => by
        refine ⟨?_, by simpa only [c, Cfg.mapState_workTapePos] using (blank j hj).2⟩
        funext z
        simpa only [c, Cfg.mapState_workTapes] using congrFun (blank j hj).1 z)
  ```
  - Full seal: 0 errors, at the base snapshot and at the stack top (`seal-fix.out`,
    `tipd-C6FixSeal.out`).
  - Unsealed: 0 errors, the two sorry warnings (`elab-fix-unsealed.out`, `tipd-C6Fix.out`).
  - Widths at most 100.
- **Everything else in the home passes the seal.** That includes `canonReturnAdapter`'s
  `cases v <;> rfl` (it compares `mapState` arguments, not unfolded) and every
  `phaseHostTM_run` use.

## (b) Elaboration and axioms

| # | Check | Result | Evidence |
|---|---|---|---|
| 16 | Head against `oleans-lbapi4` | PASS: exit 0, 0 errors; warnings only `:4970:14` (the stub) and `:5589:8` (`exists_uniformSimulator`), `declaration uses 'sorry'` | `elab-head-lbapi4.out` |
| 17 | Base baseline | exit 0; `:4646:14`, `:5259:8` (the same two) | `elab-base-lbapi4.out` |
| 18 | Sorry count, module | 2 → 2, the same declarations; no other warning | 16, 17 |
| 19 | Axioms (in-module copy with `#print axioms`) | PASS: `canonReturnAdapter`, `exists_canonRecordRound`, `canonRepeat_orbit`, `canonCounterRepeat` `[propext, Classical.choice, Quot.sound]`; `canonRepeat_last` `[Quot.sound]`. Equal to REPORT's in-module prints | `ax-head.out` |
| 20 | Admission walks | PASS (partial): `exists_polyCanonizer` and `exists_canonDecider`: the only direct `sorryAx` user is `exists_canonGrammarStage`; `exists_uniformSimulator`: itself | `ax-head.out` |
| 21 | External privates, equation lemmas | none reached from the five (the two "eqn" hits, `Function.Injective.eq_iff` and `List.eq_replicate_or_eq_replicate_append_cons`, are Mathlib theorems caught by the name filter) | `ax-head.out` (`EXT` lines) |
| 22 | Direct citations | 40 TCSlib constants (`direct-head.out`). All are in REPORT's rule-10 list except `Turing.counterLoopOrbit` (the abbreviation; documentation gap only). 22 are outside the 156-name probe; the worker's 84 added `#check`s cover them | `names-vs-probe.txt` |
| 23 | Probes on the delivered module (appended to a copy; imports covered) | PASS, 0 errors, only the module's two sorry warnings: `CanonCont6ImportProbe` + the worker's 84 + `counterLoopOrbit` = **241/241**; `CanonCont3ImportProbe` 118/118; `B5aContPreShip` 15/15 | `probes/P6Import-head.out`, `P3Import-head.out`, `PPreShip-head.out` |
| 24 | Note 50 | pending: the delivered `CanonNote50.lean.txt` is byte-equal to the prescribed file. On the delivered module it gives 0 errors and `'note50_cases' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]`. The walk: `note50_cases` and `exists_polyCanonizer` reach `sorryAx` only through `exists_canonGrammarStage` (REPORT agrees) | `probes/PNote50-head.out`, `PNote50Walk-head.out` |
| 25 | Statements probes | not re-run: `B5aStatementsProbe` and `S1210StatementsProbe` import downstream modules, which need the delivered module's olean. No public statement changed (row 8), and the pre-ship log has them passing at the base. The worker's sweep reports 0 errors with the probe-local admission each | `wt-base/audits/logs/b5a-fill-canon-cont6-preship.log`; REPORT |
| 26 | Worker's sweep log | consistent: all 102 order-list modules checked and passed (`CfgRecord` twice, the disk-space resume). Sorry warnings: 41 in 16 modules, equal per module to `b5a-fill-canon-cont6-base-sorries.txt`; `CodeSimulator` at 4970/5589. Plus the two probe-local warnings. Not reproducible here (no build) | `sweep-summary.txt` |

## (c) Progress (against the brief's phases)

| Phase | State | Notes |
|---|---|---|
| 1: the adapter and its first-return contract | **complete** | `canonReturnAdapter` is exactly the authorized design: `phaseHostTM` over three phases, fresh anchor, separate escape, ledger `t + 2`, positive time, interior avoiding both ports. Its C2 instance is `exists_canonRecordRound` |
| 2: the generic link | **complete (generic)** | `canonCounterRepeat` is stated over a round specification, not directly over `exists_canonRecordRound`. The instance's fields fit it (positive time, a uniform `B`, the cut, verdict by `r`, the preserved bank as `valid`, `tail d := x.drop (d.inputPos.val − 1)`). The `tail` update on success needs `codeSkipActionK`'s suffix, from the public `codeEraseActionK` and `codeReadActionK_sound` |
| 3: `exists_canonGrammarStage` | **open** | no C1 embedding, no inner or outer loop machine, no counter writer, no suffix scan, no ledger (F2). REPORT's "Proof sketch" for the stub is present |
| 4: note 50 | pending | row 24 |

**On route?** Yes, and nothing unfolds another file's definition except at F1:
- the adapter follows `canonEmitVerdict`'s pattern and is not a transcription (screen);
- the link uses the public `counterLoopTM_run_done`/`_run_escape` once each, with no counter
  transition or trace;
- `counterLoopOrbit` is matched through the abbreviation (the brief's N3), and
  `roundOrbit_succ` is rewritten only on `roundOrbit` terms;
- no second loop, host or trace is written.

**For the outer loop.** The inner counter loop (done/escape) is itself a source with an
injective Boolean exit. The same `canonReturnAdapter` therefore gives the outer round's
first-return contract: write the inner counter, then the inner loop through a seam, then the
adapter. So the assembly should need no further generic kit.

**The value bridges (F3), probed** (`probes/ValueBridge.lean.txt`, both definitions sealed):
- **At the stack top** (`wt-tipd`, `oleans-lx2`): 0 errors (`probes/ValueBridge-tip.out`).
  - `counterValue w = Nat.ofDigits 2 (w.map Bool.toNat)` is `rw [counterValue_eq]`.
  - `counterValue w = codeBitsNat w` is `rw [counterValue_eq, ← foldr_bit_eq_ofDigits,
    codeBitsNat_eq]`.
  - `Nat.ofDigits 2 (w.map Bool.toNat) = codeBitsNat w` is `rw [← foldr_bit_eq_ofDigits,
    codeBitsNat_eq]`.
- **At the base** (`oleans-lbapi4`): the first three fail with "Unknown identifier"
  (`probes/ValueBridge-base.out`). Only `counterValue_bits` (canonical words) is available
  there. The seal control above shows that the unfolded form is not available by `rfl` either.
- **So cont7 should be based after #122.** At this base, `counterValue bits` and C1's
  `codeSkipFin (counterValue w + 1)` can be related to `codeBitsNat bits` (the grammar's `n`,
  `canonSkipTable_eq`) only through the canonical header (`bits = (codeBitsNat bits).bits` and
  `counterValue_bits`). The counter loop's `Nat.ofDigits` hypothesis for a header copy would
  still need `codeBitsNat`'s definition.

## (d) Escalations

REPORT raises none ("Requested shared lemmas and escalations: **none**"), and none is needed for
phases 1–2. F3 is a gap the continuation will meet, which #122 already closes. REPORT also asks
for integration wording:
- the `CodeSimulator` header says the two headline contracts retain their original admissions;
- the B5a appendices of `Codes2Tape`/`EXPCOM` say both shared contracts remain admitted.

Both are true observations, carried over from cont5's review: the canonizer is proved modulo one
private stub. They are maintainer text, not part of this fill.

## (e) Duplication and lint

| # | Check | Result | Evidence |
|---|---|---|---|
| 27 | Screen v3 script | SHA-256 `f4feac91…f878f181`, the same at base and head | `screen-script-sha.txt` |
| 28 | Worker's before | byte-equal to `audits/logs/b5a-fill-canon-cont6-screen-base.txt` minus its comments (2,411 / 2,631 / 824,047). Both of REPORT's quoted blocks are byte-equal to the shipped files | `screen-compare.txt` |
| 29 | Worker's after | 2,416 / 2,631 / 824,047; differs from before only in the summary line; `pairdiff`: 0 new, 0 gone | `pairdiff-worker.txt` |
| 30 | Mine, after (head, the 45-file population) | `declarations screened: 2416; copy pairs …: 2631; reproduced text: 824,047 chars` (exit 0, 1,772 s). **Byte-equal to the worker's `screen-after.txt`.** `pairdiff` against the issued base log: 0 new, 0 gone. The five new declarations are screened, and none appears in any pair | `screen-after.txt`, `screen-after.status`, `pairdiff-mine.txt` |
| 31 | Known hazards | no pair names a delivered declaration. In particular there is none with `canonEmitVerdict`, C1's countdown, `MathlibBridge.codeSkipRepeat_iter` or the `StepBlockLoop` loop proofs | same |
| 32 | Lint | `TuringMachine`: `0 FAIL, 67 WARN over 79 files`; `Diagonalization`: `0 FAIL, 1 WARN over 4 files`. Both as at the base; the only change is `CodeSimulator`'s size lines (5,601; 12 / 149) | `lint-*-base.out`, `lint-*-head.out` |

## (f) Landability on the stack top (`5333b29b`)

- **The owned file is unchanged base → stack top** (blob `f267fe7b` at both). The patch applies
  cleanly at `5333b29b`, giving the head blob `1e8cffb9` (`patch-at-tip.txt`).
- **Upstream changes.** `CodeSimulator`'s 28-module upstream closure is the same at both ends
  (`upstream-*.txt`). Eight of those modules changed, all by additions only (`declfreeze`: no
  removal, no statement change; `upstream-changes.txt`):
  - `Convention`: `Cfg.ofWords_*`;
  - `CounterLoop`: `counterValue_eq`;
  - `StepBlock`: 10 equations;
  - `VirtualInput`: 2;
  - `CodeFormat`: `actionBitsK_eq`, `codeSkipActionK_append`;
  - `CodeParser`: `codeBitsNat_eq`;
  - `Encoding`: 12;
  - `Simulation`: 3.
- **Elaboration at the stack top** (`wt-tipd`, against `oleans-lx2`): exit 0, 0 errors, only the
  `:4970`/`:5589` sorry warnings (`elab-tipd-lx2.out`). The axiom, admission and dependency probe
  output is byte-identical to the base-snapshot run (`tipd-C6AxHead.out` vs `ax-head.out`).
- **Replay closure** (`mkdownmulti.py`, the same 9 modules at base and stack top;
  `closure-*.txt`), all under `TCSlib/Complexity/`:
  1. `TuringMachine/CodeSimulator`
  2. `Diagonalization/EXPCOM`
  3. `Diagonalization/Relativization`
  4. `Diagonalization` (facade)
  5. `TuringMachine/Codes2Tape`
  6. `TuringMachine/NDCodeSimulator`
  7. `TuringMachine/UniversalK`
  8. `TuringMachine/SelfUniversal`
  9. `TuringMachine` (facade)

  Replay it into a copy of `oleans-lx2`.
- **Expected after landing:** `CodeSimulator` keeps its 2 sorry warnings. The campaign sorry set
  is unchanged (41 over the order list); this partial removes none and adds none.

## Environment (REPORT "Runtime"; brief)

- **Startup.** Lean failed with "failed to locate application"; the addendum's shim was applied
  as authorized. `TAR_OPTIONS=--no-same-owner` was needed for the cache, and the cache fetch was
  narrowed to the order's 36 Mathlib roots.
- **Interruptions.**
  - A transport disconnect after 68 bootstrap modules (resumed at 69).
  - The scratch volume filled twice. Disposable caches were removed, an identical 530 MB Mathlib
    pack was shared, and the failed attempts were kept and not counted.
  - One status-monitor disconnect.
- **The sweep.** The candidate was installed after 91 modules had passed with the base source,
  and the sweep then continued through `CodeSimulator` and its downstream. Only `CodeSimulator`
  changed, so this is a valid final-state sweep.
- **Census helper.** It mis-parsed the baseline's `TOTAL` line and was fixed (no Lean effect).
- None of this affects the Lean result, which my elaborations confirm for the owned file.

## (g) Recommendation

**Not yet clear to merge**: the landing PR is still to be opened and replayed. Clear once the
PR's replay passes and its gate is recorded.

**Land as a partial: yes**, by a maintainer PR like #113's:
- **Commit.** Cherry-pick `a406c7eeb44998aa54d7a115a4832ba7c4ffd41e` from the verified bundle
  (prerequisite `94b986d4`). It touches only `CodeSimulator.lean`, which is unchanged base →
  stack top.
- **A maintainer commit on top** (recommended, as with G4 cont1's `4ab012d9`): the F1 fix,
  `suggested-fix.diff`. After it, re-elaborate (0 errors, two sorry warnings), re-lint, and
  re-screen (the fix changes one private body). Alternatively, land unchanged and make F1 the
  first item of cont7's re-point list.
- **What it adds:**
  - five private lemmas: the adapter, its C2 round, the generic link, the orbit induction and the
    repetition bridge;
  - no public declaration and no admission;
  - 5,271 → 5,601 lines, 12 public / 149 private.
- **Replay:** the 9 modules above, into a copy of `oleans-lx2`; sorry counts unchanged.
- **Status text at integration:**
  - the module header (lines 46 and 71–77) should say that the canonizer headline is proved
    modulo the grammar stage, and that the stage now has its adapter and loop link;
  - the headline keeps "(spec, fill pending — batch B5a)";
  - REPORT's `Codes2Tape`/`EXPCOM` wording point (d).

**Continuation 7 should:**
1. **Be based after #122 merges** (F3). Cite `counterValue_eq` and `codeBitsNat_eq` for the
   value conversions. Then `counterValue bits = codeBitsNat bits = n` and the counter loop's
   `Nat.ofDigits` hypothesis need no unfolding.
2. **Re-point F1** if it is not fixed at landing. Add "no defeq closure through a partially
   applied field (`Cfg.mapState_workTapes` is fully applied)" to rule 10's pitfalls, and suggest
   the seal test as a self-check.
3. **Build phase 3 in order, each step a checkpoint that may land alone:**
   - instantiate `canonCounterRepeat` at `exists_canonRecordRound` with
     `r := codeSkipActionK k (counterValue bits)`, `valid` = C2's bank preconditions,
     `tail d := x.drop (d.inputPos.val − 1)`, and `B := (a + 2)(|x| + |bits| + 1)`. The tail
     update comes from `codeEraseActionK` and `codeReadActionK_sound`;
   - the inner block: `writeConstTM_run_ofCfg` writes the `3^(k+1)` counter, then the inner loop
     through a seam, then `canonReturnAdapter` again (done ↦ anchor, escape ↦ escape) for the
     outer round's contract;
   - the outer loop over a header copy: a leading block with `codeSkipRepeat_succ`, or
     `incrementTM_run_succ_ofCfg` on a padded copy. `canonSkipTable_eq` and
     `canonSkipRepeat_mul` give the grammar;
   - C1 on `{header, scratch}`, then `canonSuffix_run` at the table's end, with every failure
     forwarded to the rejecting port;
   - the ledger: at most `|x| + 1` records (4k + 5 cells each), `counterOverhead_le_of_le` per
     loop, and `|bits| ≤ |x|`.
4. **List `counterLoopOrbit`** among the cited declarations (row 22).
5. **Keep the inputs:**
   - the base sorry set stays 41 over the order list;
   - the screen base becomes this review's after-screen, plus the F1 re-screen if applied;
   - the probe gains the worker's 84 `#check`s and `counterLoopOrbit`.
