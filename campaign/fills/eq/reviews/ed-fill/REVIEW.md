# Review — E-D, the lazy diagonalizer (`Turing.NTimeDiag.exists_diagonalizer`, `Diagonalization/NTimeDiagonalizer.lean`): `fill-eq-diagonalizer.zip`, branch `refs/deliv/eq-diagonalizer` at `7b1b9353`

**Verdict: land with edits.** The delivery is complete and correct. `exists_diagonalizer` is
proved on `[propext, Classical.choice, Quot.sound]`, and every one of the module's 1,846 constants
is within those three (out/11-audit-head.out). The target's statement and every pre-existing
declaration are unchanged down to the kernel terms (out/11d-hash-compare.txt). The architecture
is the brief's: `D` is `Turing.guessRunTM` over a phase-host setup and a phase-host run, the
uniform `K` is built from the kit's call constants only, and the per-code `C` enters only the
middle's completeness premise and the top's premise. Three re-derivations of published or
ledgered lemmas are new duplication debt (F1–F3). Two of them, and five smaller defects, are
removed by seven tested landing edits E1–E7 (`land/NTimeDiagonalizer.lean.txt`, blob
`fc65a848032abfd935b8d847453e047eabb71d24`). The third, F1, needs the user's acknowledgment.

**Not yet clear to merge.** There is no landing PR, no replay and no fill gate yet. Decisions 1–6
are open, and F1 needs the user's acknowledgment (decision 2).

Severity counts: 0 blockers, 3 majors (F1–F3), 4 minors (F4–F7), 11 notes (F8–F18).

Read-only review by the maintainer's review sub-agent, 2026-11-05 (UTC). Every claim cites a saved
output under this folder (`out/NN-*`).

How the review was done:
- **The zip is data.** I used the maintainer's extraction (`$S/intake/eq-diagonalizer/x/`) and ran
  nothing from it. `REPORT.md`, the logs, the screens and the seal outputs were read as claims to
  check. I elaborated none of the worker's `.lean` files: every probe is my own (`probe/`).
- **Lean** ran only through `tools/leanelab.sh` and `tools/leanelab-o.sh` (`scripts/elab.sh`,
  `compile-head.sh`, `compile-land.sh`, `compile-tip.sh`), never `lake`. I used three
  copy-on-write clones: `oleans-clone` (of `oleans-leqc3`, the base's Lean `711f5444`, for the head),
  `oleans-land` (the same, for the landed file) and `oleans-tipclone` (of `oleans-lsm5`, the tip's
  Lean after #181, for the landing pre-check). All three are deleted at the end.
- **One screen** (the head's), on a frozen copy of the brief's 38-file population, under the
  machine-wide `locks/screen` lock and `nice -n 10` (`scripts/screen.sh`).
- **Python** always ran as `python3 -I`, from `scripts/`, with paths as arguments.
- **Worktrees:** `wt-head` (the delivery), `wt-base` (the base) and `wt-land` (the head with the
  landed file copied in), each with the `.lake/packages` link. All three are removed at the end.
- **Slips, none affecting a result** (the superseded outputs are in `out/superseded/`):
  - `DzAuditR.lean`'s reachability command did not compile (a Lean API name). The rest of that
    probe ran; the reachability is `DzReach.lean` (out/15-*), and the landed audit uses
    `DzAuditR2.lean`, the same probe without that command.
  - My first seal's control code did not parse. Its body result (0 errors in the new code under
    the seal) agrees with the re-run.
  - My first name-collision grep used last components (`K`, `tp`, …) as patterns. It was killed,
    and a stray in-flight `git grep` polluted the hits file. The clean re-run is out/18-rule11.txt.
  - zsh read `$B:c…` as a history modifier once. I redid that step as a bash script
    (`scripts/dispatch.sh`).
  - The maintainer's session restarted while my head screen ran. The screen continued as an
    orphan and finished normally (exit 0); its wrapper released the screen lock
    (out/17-screen-head.meta, out/17b-lock.txt).

## What was delivered, in one paragraph

Region (b) gains 106 private declarations, 3,051 lines between `exists_queryTM`'s proof and the
target's docstring. They are:
- one own leaf, `dzTakeTM`: read a cell, blank it, step right;
- the silent-capture normal form (`dz_silentCfg_eq`, `dz_silent`);
- one generic clocked, hosted run: `DzClockSpec` and `dz_clock_exists`, the step clock over
  `vhostSilentTM M` embedded, used for both the core and `BF`;
- the kit `DzKit` (three input calls, two install calls, the core, the two clocks) and a
  14-named-tape layout with banks from tape 14 on;
- the setup `P = dzSet`, 12 phases;
- the run `Q = dzQ`, 23 phases;
- `D = dzD`: `guessRunTM` bundled as a `FinNDTM`;
- the halting and acceptance lemmas, the middle's two directions and the top.

Region (c) is a 22-line body. Region (d) rewrites one status line and three label-bearing docstring
lines. Region (a) adds the overlay's three imports. Head: 8,505 lines, 22 public and 320 private
declarations (base 5,432 lines, 22 and 214).

## Findings

| # | Severity | Where | Finding | Evidence | Fix |
|---|---|---|---|---|---|
| F1 | **major** (debt, TEMPLATE failure mode 5) | `dz_word_lt` (head 7685) | A new member of BL-1 kind (vi), the word-value bound `bitsVal w < 2 ^ \|w\|`, stated as `Nat.ofDigits 2 (w.map Bool.toNat) < 2 ^ w.length`. The public forms are `Complexity.LogProg.bitsVal_lt_two_pow` (`Machines/Bin:86`) and `Codec/Word:452`'s copy. Neither is in the owned file's closure, and `exact?` finds nothing citable there. REPORT files the declaration only as a promotion request of `ExhaustiveReplay`'s private `xr_val_lt` (the 65% pair). It does not name BL-1 (vi) or the public lemma. By the maintainer's instruction, a new fill declaration of a BL-1 kind is new debt, not covered by the 2026-11-04 scope ruling | out/38-bl1-vi.txt; out/25-dupprobe.out (line 9 fails); out/22-closure.txt (`Machines/Bin` not in the closure) | **Human acknowledgment required** (decision 2): record `dz_word_lt` as a BL-1 (vi) member in `NTimeDiagonalizer`, with the file's other BL-1 members, for the dedup window's one home below both layers. The ledger keeps the `xr_val_lt` promotion request too (F12) |
| F2 | **major** (debt, failure mode 5; removed by E3) | `dz_padded_value` (head 7701–7711) | Its inner `h0` (by induction, the zero tail is worth `0`), with `Nat.ofDigits_append`, `mul_zero` and `add_zero`, re-derives Mathlib's `Nat.ofDigits_append_replicate_zero`, which is in the closure (`Mathlib/Data/Nat/Digits/Defs:220`, `@[simp]`). `exact?` finds it at once | out/25-dupprobe.out (line 13: `exact Nat.ofDigits_append_replicate_zero l`); out/38-bl1-vi.txt | **E3**: `rw [List.map_append, List.map_replicate, Bool.toNat_false, Nat.ofDigits_append_replicate_zero, qy_bits_val]`. Tested (out/32-*, out/33-*, out/34-*) |
| F3 | **major** (debt, failure mode 5, FH-1's kind; removed by E4) | `dz_top_run` (head 7612–7624, 7665) | The decider's first halt is re-derived inline (`Nat.find`, `Nat.find_spec`, `Nat.find_min`, `Nat.find_min'`). That is FH-1's public form `Turing.MultiTapeTM.exists_first_halt` (`TuringMachine/Finite:218`), which is in the closure, and `exact?` finds it. The ledger's FH-1 family records only copies that predate the public form | out/25-dupprobe.out (line 37: `exact MultiTapeTM.exists_first_halt M c h`); ledger lines 208–225 | **E4**: `obtain ⟨τ₀, hτ₀w, hlive0, heq0⟩ := MultiTapeTM.exists_first_halt BF.tm c0 hstw`; minimality from `hlive0`. The docstring cites it. Tested |
| F4 | minor (rule 10) | `dz_test` (head 7181) | `rw [Ne, compare_gt_iff_gt]` passes the core definition `Ne` to `rw`. The brief's rule 10 says core and Mathlib definitions "may reduce in `rfl`, `decide` or `show`, never passed to `simp`, `rw` or `unfold`". `Ne` is `@[reducible]`, so no seal can catch it. It is the only definition in any new `rw`/`simp`/`dsimp`/`unfold` list | out/14b-inspection-table.txt; out/14-origin.out (`Ne def reducible Init.Core`) | **E2**: `rw [ne_eq, compare_gt_iff_gt]`. Tested |
| F5 | minor (public-facing text) | `dz_kit_exists`'s docstring (head 5982) | "of the published prepend row": "published" in the campaign's sense. The scan finds no other campaign vocabulary in the new text: no checkpoint, gate, finding, date, `audits/`, brief, review, pinned, authorized, route probe, rule, ledger, screen or fill labels | out/27-newtext.txt | **E5**: "of the prepend row (`Turing.FinTM.computesFunInTime_prepend`)" |
| F6 | minor (docstring accuracy) | `dz_cell0` (head 7747); `dzLay_tp` (6153), `dzLay_off` (6161), `DzKit.tp_val` (6140), `DzKit.le_K` (6126) | `dz_cell0`'s docstring, "The query's first cell after its flag", is wrong. The lemma is `bufferTape (b :: tail) 0 = some b`, which is the flag's own cell, and it is used for the flag's read. The other four are bare labels ("A layout on a named tape."). Private docstrings are at reviewer discretion under `policy.md` §2. I fix these four because they are theorems stating one equation each | out/27b-short-docstrings.txt; head 7748–7750 | **E7**: each states its equation (text only) |
| F7 | minor (records) | REPORT §"Duplication", `evidence/dedup/semantic-search.md` | The semantic search ran `exact?` on whole statements only, so it misses re-derived sub-steps (F2, F3). It also files F1 without its BL-1 kind. This is the same blind spot as E-Q cont1's review (its F2 and F13 d). REPORT's "new copies" line correctly lists `dz_split_stream` (98%) | semantic-search.md rows 101, 120, 121; out/25-dupprobe.out | Correct the records in the landing PR's description and the ledger (F1–F3, F12). The next fill brief should ask for `exact?` on inline `have` steps of arithmetic and run lemmas |
| F8 | note (landing item) | `qy_call_bound` (head 455–458) | Its `hb` still re-derives `\|bits (f a)\| ≤ f a` (`Nat.size_eq_bits_len`, `Nat.size_le`). That is correct for the delivery: the brief froze E-Q's text and gave the re-point to the landing PR (gate 87's finding 2; BL-1 (iii); NB-1) | head 456–458; brief lines 9–11 | **E1**: `have hb := Turing.length_bits_le_self (f a)`. Tested. The kernel type of `qy_call_bound` is unchanged (out/33b-land-vs-head.txt) |
| F9 | note (docstring sync; decision 4) | the target's frozen `**Proof sketch.**` and "Fill obligations" (head 8419–8457) | The frozen sketch describes the design, not this proof. It names `Turing.NDTM.phaseHostND`, `Turing.ndWriterTM_run_block` and the transfer `Turing.NDTM.runWith_mapState_of_agreeOn_det`; the proof uses `guessRunTM` and its two lemmas and none of those three. It still carries "(C1's design §3.6, the fallback)" and "Fill obligations, named: …". The brief kept these for the deferred cleanup and gave the maintainer the `**Implementation.**` paragraph to land. REPORT's proposed paragraph is accurate against the code and names no private declaration | head 8419–8457; REPORT 273–289; out/28-docnames.out (every qualified name in the new docstrings resolves) | **E6** lands the paragraph, verbatim, after "Fill obligations". Decision 4: resync the sketch in the deferred cleanup (recommended), as for E-Q cont1 |
| F10 | note (public constants) | the module | At source, 22 → 22 public declarations. As constants, 130 → 132. The two new ones are `Turing.NTimeDiag.exists_diagonalizer._proof_1_1`, an auxiliary proof like the file's other `_proof_` constants, and `Turing.walkTM.congr_simp`, a congruence lemma that `simp` realized here for `Build/Catalog`'s `walkTM`. All 106 new declarations are private; the 4 phase-index instances are `private`, with no `deriving` | out/11c-public-diff.txt; out/06-freeze.txt; out/07-hygiene.txt | None. The PR body states "22 → 22 public declarations; 2 generated public constants (`exists_diagonalizer._proof_1_1`, `Turing.walkTM.congr_simp`)" |
| F11 | note (in-file duplication) | `dz_initCfg` (head 7999) against `qy_initCfg` (5043) | The worker's first final screen paired them at 90% (a copy by the 90% rule). The third finishing commit rewrote `dz_initCfg` in term mode, which removed the pair without factoring. The other three removals in that commit are real factorings (`dzClkEmb_eqs`, `dz_seg_read`, `dz_K_bound`). The two lemmas state one fact, "a phase host's initial configuration is the blank seam in normal form", for different machines. Neither can cite the other | evidence/screens/screen-diff-pre.txt against screen-diff.txt; commit `7b1b9353` | None now. Ledger (QF-1's family): one generic lemma over `phaseHostTM_q₀` and `initCfg_ofWords` in the dedup window |
| F12 | note (promotion requests) | `dz_split_stream` (head 8010); `dz_word_lt` | `dz_split_stream` restates `Build/NDHost`'s private `guessRun_split` (98%, a copy by the 90% rule). `dz_word_lt` restates `ClassNP/ExhaustiveReplay`'s private `xr_val_lt` (65%). Governance: keep yours and request a promotion. REPORT does so. `exact?` finds no public `List` form of the split | head screen pairs (§(f)); out/25-dupprobe.out (lines 26, 28) | Ledger: two promotion requests (NDHost's split, or a public `List` lemma; the word-value bound with F1's home) |
| F13 | note (row candidates) | `DzClockSpec`/`dz_clock_exists`, `dz_silentCfg_eq`, `dz_out_le`; `dzTakeTM` (RC-2) | REPORT's promotion candidates are right. `dz_out_le` (`\|F y\| ≤ T \|y\|` for `ComputesFunInTime F T`) has no general public form. The same two-line step is inlined in `SAT` (2702, 894, 3394, 4148, 4167), `Nondeterminism` (3295, 3963), `TMSAT` (610, 1114) and `Loop`'s private `loop_fuel_width` (241); `PolyTime` publishes only its polynomial form | out/21-grep-candidates.txt and the `output_length_le` grep (§(f)) | Ledger RC-3: the clocked hosted run; the silent-transport reconstruction beside `embedEmitCfg_eq`; the output-length bound of a computed function, with its customers |
| F14 | note (scoping) | head 5976 | `attribute [local instance] DzKit.SRf DzKit.SRd DzKit.QRf DzKit.QRd DzKit.QBf DzKit.QBd` is in force to the end of the namespace, which covers the target's proof. It is harmless: the instances fire only on `Fintype`/`DecidableEq` goals for the kit's state types. It is the same pattern as E-Q's `QyKit` line (2281) | out/07-hygiene.txt | None |
| F15 | note (records) | REPORT §"Checkpoints"; `exchange/` | 7 of the 8 abbreviated checkpoint-zip hashes in REPORT end in the wrong characters; 3 of those 7 tails occur nowhere in the full hash. The full hashes are in `evidence/logs/checkpoint-zips.sha256`. The zips themselves are not in the exchange folder: only the final zip is archived. The complete delivery supersedes them | out/19-cp-hashes.txt | None. Quote full hashes only |
| F16 | note (process and timeline) | the session | The logs are consistent (out/36-sweeps.txt, out/04-integrity.txt): preflight 19:45:36Z; bootstrap 19:48–20:00Z (84/84, 19 sorry warnings in 9 modules = the base set); 11 commits 20:29–23:47Z; final sweep at cp8 21:56–22:11Z (84/84, 18 in 8); base screen 21:56–22:46Z beside it (allowed); tail sweep 23:47–23:48Z and seal 23:49–23:51Z, after the last commit; final screen 23:47Z–00:23Z. Unverifiable: the first final screen (its raw output was replaced, and it is not timed in any log), and the step-by-step development. The first checkpoint lands 1,243 lines 29 minutes after the bootstrap ends, and no per-step elaboration log ships. Neither affects the result, which Lean checked here | out/36-sweeps.txt; out/04-integrity.txt (commit times and sizes) | None |
| F17 | note (commit history) | all 11 commits | The subjects carry campaign labels ("E-D checkpoint N: …", "E-D finishing: …"). Two subjects or bodies mention "the exact? probe" and "the screen's". Every body ends with a `Claude-Session:` trailer | out/29-commit-messages.txt | Reword at landing (the table under "Landing plan"). Decision 5 covers the trailers |
| F18 | note (downstream) | `NTimeHierarchy` | After the fill, `Complexity.ntime_hierarchy`, `ntime_hierarchy_of_pos` and `NTIME_linear_ssubset_square` still depend on `sorryAx`. That is expected: `exists_diagonalizer` is now on the standard three, so what remains is NF's `Turing.FinNDTM.exists_codeNDTM_accepts_linear`, which is reviewed separately. At the base all three and the target carried it | out/12-hier-ax-head.out against out/12b-hier-ax-base.out; out/40-tip-hier-ax.out | Check at NF's landing that the three become admission-free (backlog line 4181) |

## What passes

### (a) Integrity and scope

| # | Check | Result | Evidence |
|---|---|---|---|
| 1 | Zip | SHA-256 `9f0aeec1…2c4` as given; 94 members, no unsafe path, no link | out/04-integrity.txt |
| 2 | `SHA256SUMS` | 80/80 OK, no unlisted file | out/04-integrity.txt |
| 3 | Bundle | `verify` okay; `HEAD` and `refs/heads/fill/eq-diagonalizer` = `7b1b9353` = `refs/deliv/eq-diagonalizer`; sole prerequisite the base `c8b07114` | out/04-integrity.txt |
| 4 | Commits | 11 linear commits (no merge), author `Claude`, touching only the owned file (+3078 −5, 5 hunks) | out/04-integrity.txt |
| 5 | Patches | the 11 patch-ids equal the commits' | out/04-integrity.txt |
| 6 | Source | `source/…` = head blob `4b72d525`; base blob `852931eb` as the brief pins | out/04-integrity.txt, out/00-refs.txt |
| 7 | Dispatch | the archived dispatch copy has SHA-256 `959c45ec…20b` = the base's brief with its three `@ANCESTOR@` filled with the base. The record copy differs from it only in the later "Dispatched" status line | out/37-dispatch.txt |
| 8 | Snapshot | `oleans-leqc3` is Lean `711f5444`, the base's `.lean` content exactly, and holds the overlay's three imports | out/01-snapshot-base.txt, out/02-imports-present.txt |
| 9 | Regions | (a) +3 imports after `Build/WordTests`, exactly the overlay's; (d) line 70's "(sorried; C1-E's second fill)" → "(proved)"; (b) the 3,051-line insert after `exists_queryTM` with (d) the target docstring's first two lines; (d) "(the statement gate, finding 1)" removed; (c) `sorry` → the 22-line body. Nothing else | out/04-integrity.txt (hunks), out/05-deleted-lines.txt |
| 10 | Region (d) | The brief lists exactly these labels for rewriting: "(C1-E; …)", "the P3.3 gate's round 2" and "(the statement gate, finding 1)". The new first line cites `[AB09, proof of Theorem 3.2 and Figure 3.1]`, as the module header does. The rewritten sentence keeps the statement gate's content: "its `\|x\|` term (`\|x\| = n + 1`) carries the per-code constant, which the uniform `K` cannot absorb when `g n = n`." | out/05-deleted-lines.txt; head 8397–8452 |
| 11 | Hygiene of the added code | no `sorry`, `admit`, `axiom`, `native_decide`, `implemented_by`, `unsafe`, `@[extern]`, `set_option`, `open`, `section`, `variable`, `deriving`, `macro`/`notation`, `@[simp]` or `@[reducible]`; one `attribute [local instance]` (F14); eight `private instance`s; two `Classical.decEq` instances; `unfold` only of own-file definitions; no line over 100 characters, no double blank line, no trailing space | out/07-hygiene.txt |

### (b) Statements frozen

- `declfreeze`, with the target's body authorized:
  - 22 → 22 public declarations;
  - "authorized body change: exists_diagonalizer";
  - 214 → 320 privates, none removed or changed.

  `privstmt`: no statement changed among the 236 base declarations. `stmtcheck`: the one line
  not found in order is the base's `  sorry` (out/06-freeze.txt).
- **Kernel-level** (stronger): I compared the type and value hashes of all 1,292 constants of the
  base module with the head's. Every type is identical. Every value is identical except
  `exists_diagonalizer`'s. So E-Q's elaborated proofs are unchanged under the three new imports
  (out/11d-hash-compare.txt).
- The 106 new names: `declfreeze`'s "private added" list, all `dz`/`Dz`-prefixed (out/18-newnames.txt).

### (c) Elaboration and axioms

| # | Check | Result | Evidence |
|---|---|---|---|
| 12 | Head file, compiled into `oleans-clone` | exit 0, **no output**: 0 errors, 0 warnings, no sorry warning; 47.9 s, 2.80 GB | out/10-compile-Diagonalization_NTimeDiagonalizer.* |
| 13 | Downstream (import graph: `NTimeHierarchy` and the facade `Diagonalization`; the root `TCSlib` is not replayed) | both exit 0 with no output, so no sorry warning; the base list has none for either | out/03-downstream-head.txt, out/10-compile-*; base sorry list |
| 14 | My audit (olean walk) | module constants 1,846 (132 public); **union of axioms over all of them `[propext, Quot.sound, Classical.choice]`; 0 constants outside the three**. `#print axioms exists_diagonalizer` gives the three. At the base the union had `sorryAx` (1 constant) | out/11-audit-head.out, out/11b-audit-base.out |
| 15 | Reachability | all 106 new declarations are reached from `exists_diagonalizer`. There is no dead code, so every lemma's hypotheses are discharged in the final proof | out/15b-reach-summary.txt |
| 16 | Other files' privates | the 554 new constants mention 1,315 constants, 212 of them other-module TCSlib constants (the worker's 212) and **0 of them another module's private** | out/35-privuse.out |
| 17 | Worker's logs | bootstrap 84/84 with 19 sorry warnings in 9 modules = the base set; final sweep 84/84 with 18 in 8 (the target's gone), the owned file clean; tail sweep after the last commit, 3/3 clean | out/36-sweeps.txt |

### (d) Rule 10

**My seal** (`scripts/mkseal.py`, generator `probe/DzSealGen.lean`), built independently:
- the generator walks the closure's 2,668 TCSlib definitions and seals every one outside the
  module that is semireducible and not private, an instance, a projection, a matcher or an
  internal detail, plus the module's five public definitions (`query`, `budget`, `ladder`, `stage`,
  `stageCode`);
- that is **350 definitions, exactly the worker's 350** (out/16-seal-compare.txt: no difference);
- it includes the brief's whole rule-10 list: the route probe's 11 and the 32 further names
  (out/16-brief-list-check.txt, 47 names checked, none missing);
- it adds `attribute [-simp]` on the environment's four `@[simp]` TCSlib definitions;
- it is placed before the first new section heading (head 5349).

**The new code elaborates sealed with 0 errors** (exit 0; out/24-seal-sealed.*).

**Controls**, each logging one info line, are generated in Lean from the environment:
- for each of the 350, a delta goal `∀ xs, c xs = value xs` and its first equation lemma, each
  tried by `intros; exact rfl`;
- for the four, the delta goal tried by `intros; simp`;
- the results (out/24-seal-summary.txt):
  - **sealed, all 704 `rfl` controls and all 4 `simp` controls fail**;
  - unsealed, 337 pass both;
  - 12 structurally recursive definitions (`pairDecode`, `ladder`, `incFixed`, …) close only
    their equation control, and `StepBlock.summaryEmit` only its delta control;
  - **so every one of the 350 has a control that passes unsealed and fails sealed**, and the four
    `simp` controls pass unsealed and fail sealed.

  This covers far more than the 30 asked, including the hosts and the phase machines:
  `guessRunTM`, `guessRunCfg`, `phaseHostTM`, `embedEmitTM`, `embedSilentTM`, `vhostSilentTM`,
  `seamReleaseTM`, `copyMapTM`, `transferMapTM`, `walkTM`, `skipBackTM`, `rewindTM`,
  `writeConstTM`, `expandTM`, `clearTM` and `clockCfg`.
- The landed file's sealed copy also elaborates with 0 errors, and all its controls fail sealed
  (out/34-land-seal-*).

**My inspection** (`scripts/tacargs.py`, `probe/DzOrigin.lean`): 1,475 rows and 360 identifiers
from the new code's `rw`/`rwa`/`simp`/`simp only`/`dsimp`/`unfold` lists and `show` terms, resolved
in the module's namespace (out/14b-inspection-table.txt, out/14-origin.out):
- **No other-file TCSlib definition** is named in any list. Those lists hold 43 other-file TCSlib
  names, all theorems.
- **One core definition** is in a list: `Ne` (F4).
- `unfold` targets only own definitions: `DzKit.K`, `DzKit.bB`, `DzKit.bR`, `dzAlpha`, `dzBlk`,
  `dzK`, `dzLay`, `dzQB`, `dzSetB` and E-Q's `qyBody`. `dsimp only` lists only `DzPPh`, `DzQPh`
  and `qyC`.
- **`show` steps** name `FinTM.bufferTape` five times, to state goals over the own `qyC`/`dzLay`.
  The seal proves it is never unfolded. The core and Mathlib names in `show` terms are
  `Function.update`, `Fin.castAdd`, `Fin.last`, `Fin.natAdd`, `Option.none`, `SignType.pos` and
  the inductives.
- **The own leaf** `dz_take_run` reads `step` through `MultiTapeTM.step_of_some` and
  `Action.apply` through `Action.apply_state`, `_inputPos`, `_workTapes`, `_workTapePos` and
  `_output`. Neither is unfolded by `show`/`change`/`rfl`, and both are sealed.
- **Published readings** are used as the brief prescribes:
  - `streamStartCfg_*` and `guessRunCfg_*` field equations;
  - `vhostSilentCfg_eq` with `vhostCfg_*`, `vhostCap_eq` and the `embedSilentCfg_*` equations;
  - `Cfg.stopped_iff`, `FinTM.VirtualTag_iff`, `initCfg_ofWords` with `Cfg.ofWords_*`, and
    `phaseHostTM_q₀`;
  - `MultiTapeTM.initCfg_eq` with `Cfg.init_*`;
  - `computesFunInTime_iff`, `computesInTime_iff` and `timeConstructible_iff`.

### (e) Rule 11, the addendum and the process

- **No R3 canonical row** occurs in the added code: `copyTM_run`, `transferTM_run`, `clearTM_run`,
  `compareTM_run` and `incrementTM_run_*` all count 0. Only framed `_ofCfg` rows are used
  (out/20-forbidden.txt).
- **No other file's private** is reached (item 16 above) or named.
- **The names.** No first component of a new name, and no `dz`/`Dz`-prefixed identifier, occurs in
  any `.lean` file of the other 282 ref tips. The control hits the owned file 898 times
  (out/18-rule11.txt).
- **No forbidden route:** `phaseHostND`, `guessRunTM_silent_spec`, `un_setup`,
  `exists_timed_universal_NDTM`, `xr_`/`wr_`/`gr_`, `ndWriterTM`, `prefixCanon_pairExtract_halt`
  and E-Q's `qy_clocked_call`/`QyClockSpec` all count 0 (out/20-forbidden.txt).
- **The addendum and the process:** F16 and out/36-sweeps.txt.

### (f) Duplication

**My head screen** (`scripts/copy-text-screen-v3.py`, SHA-256 `f4feac91…f181`, the campaign's;
the brief's 38-file population, frozen at the head; out/17-*):
- **Counts:** 2,317 declarations, 2,483 pairs, 864,671 characters reproduced. The run took
  4,794 s wall (niced, beside other jobs), 2,514 s user, 3.27 GB peak.
- **Byte-identical to the worker's final screen** (out/17c-screen-analysis.txt). The worker's
  base screen is byte-identical to the campaign's screen base (2,241 / 2,439 / 858,015).
- **Against the base:** 44 new pairs and 0 gone, so E-Q's 133 pairs are unchanged. Every new pair
  has a `NTimeDiagonalizer` declaration on a side.
- **REPORT gives a disposition for every one of the 44**, at the screen's share, with none missing
  and none extra.
- **One new pair is at 90% or more:** `NDHost.lean::guessRun_split` reproduces `dz_split_stream`
  at 98% (F12).
- The lock was released by my wrapper at 05:09:25Z. The present `locks/screen` was created 3 s
  later by the next queued screen, which is running, so I left it in place (out/17b-lock.txt).

The 44 pairs by class, with my assessment of REPORT's dispositions:

| Class | Pairs | Disposition |
|---|---|---|
| `dz_split_stream` against `NDHost`'s private `guessRun_split` | 2 (98%, 65%) | promotion request (F12). REPORT agrees |
| `dz_word_lt` against `ExhaustiveReplay`'s private `xr_val_lt` | 2 (65%, 64%) | promotion request **and BL-1 (vi) debt** (F1). REPORT gives only the first |
| `dzBlk_length`'s `simp only [List.length_append, …]` inside other files' proofs (`clockTM_loop`, `incFixedTM_computes`, `f2_incFixed_computes`, three `sl_` lemmas, `qy_setup_short`) | 7 (73–85%) | idiom: an 85-character length computation. Accept |
| `dz_alpha_eq` against `Nondeterminism`'s `a3n_poly_pair` | 1 (86%) | idiom: the `pairDecode_pairEncode`/`Option.map_some`/`getD_some` chain, with different statements. Accept |
| `dzTakeTM` against `Catalog`'s `clearTM` and `incrementTM` | 2 (61%, 59%) | a one-tape transition table's shape. `dzTakeTM` is the ruled own leaf (RC-2). Accept |
| In-file bank maps and their disjointness facts (`DzKit.bA`/`bB`/`bL`/`bR`, `bR_off`/`bR_j`, `bB_ne`/`bR_ne`, `sR`/`sB`, `dz_zero_bank`/`dz_arg_bank`) | 15 (53–83%) | idiom: `qyBank` at different offsets, as E-Q's `QyKit.b*`. Accept (in-file) |
| In-file readings of rows, hosts and layouts (`dzSetL` against `qySetT5`/`qyTB`; `dz_accepts_iff`/`dz_halts`; `dz_clock_exists`/`qy_clock_start`; `dz_qmid`/`dz_qtop`; `dz_split` against `dz_tail_run`/`qy_wordPatch_ones`; `dz_top_run` against `bB_ne`/`dz_flag`; `qyLocRed`/`dzSetRed`; `qy_main`/`dz_out_le`) | 11 (50–78%) | idiom or the brief's prescribed reading (the clock's clauses stated afresh over `vhostSilentTM`). Accept |
| `dz_tail_run` against `qy_copy`/`qy_copy_over`; `dz_take_run` against `qy_step`/`qy_emit_halt` | 4 (54–62%) | the brief's prescribed off-origin copy (`copyMapTM_run_ofCfg` from cell 1) and the own leaf's step lemma (`qy_step` covers only steps that write nothing). Accept |

The screen cannot see F2, F3 or F11: they are re-derived sub-steps, or a rewrite of the text. So
the semantic search below carries them.

**The semantic search** (my probe `probe/DzDupProbe.lean`, out/25-dupprobe.out; greps
out/21-grep-candidates.txt, out/38-bl1-vi.txt). I restated the new arithmetic, list and reading
lemmas and their inner steps, and ran `exact?` in the closure:

| Statement | `exact?` | Disposition |
|---|---|---|
| `dz_word_lt` (`ofDigits` value `< 2 ^ \|w\|`) and its `counterValue` form | no lemma in the closure | **F1**: BL-1 (vi); the public forms are outside the closure |
| `ofDigits b (l ++ replicate r 0) = ofDigits b l` (inside `dz_padded_value`) | **`Nat.ofDigits_append_replicate_zero`** | **F2**, E3 |
| `dz_padded_value`, `dz_budget_le` (whole) | none | after E3, a citation chain |
| `dz_out_le` | none | F13 (row candidate) |
| `dz_split_stream`, both forms | none | F12 (NDHost's private) |
| `dz_ones_succ`, `dz_cell0` | `rfl` | idiom. `dz_cell0` reads `bufferTape` through `bufferTape_eq`, as rule 10 wants: `rfl` would unfold another file's definition |
| `dz_alpha_eq` | none | the composite's reading, as the brief prescribes |
| first halt (inside `dz_top_run`) | **`MultiTapeTM.exists_first_halt`** | **F3**, E4 |

**By kind**, the brief's and the ledger's hazards:
- **BL-1 (i)–(vi).** The new code cites (iii) `Turing.length_bits_le_self` (7 times) and E-Q's
  ledgered members (ii) `qy_bits_len_mono` and (v) `qy_two_pow_bits_le`. It re-derives no (i)–(v),
  and `Nat.size`/`Nat.log` count 0. It adds (vi) in `dz_word_lt` (F1).
- **`pairEncode` lengths:** `Turing.length_pairEncode` is cited (the worker's commit `c1a7632c`).
- **Run composition:** `Turing.Segment.trans`, `MultiTapeTM.runFrom_add` and `runFrom_of_halt`
  are cited.
- **Configuration retagging:** no `Cfg.mapState` in the new code. The silent transport is
  `embedSilentTM_runFrom`, read through `dz_silentCfg_eq` (F13).
- **First halting:** F3. The core's liveness cites `MultiTapeTM.runFrom_state_ne_none_of_le`.
- **The one-step identity (RO-1):** cited as E-Q's `qy_run_one`, not restated.
- **E-Q's leaves:** cited, never copied. The comparator, the emitter, the word lemma (`dz_core_word`
  is `qy_writer_word` with `W := α ++ [true]`), the calls, the expansions, the rewinds and the
  embeddings all count 0 copies in out/20-forbidden.txt. The pairs with `qy_copy`/`qy_copy_over`
  (`dz_tail_run`) and `qy_step`/`qy_emit_halt` (`dz_take_run`) are the brief's prescribed off-origin
  copy and own leaf step.
- **NTimeHierarchy's guess-then-run setup:** no pair, no citation.

**One fifth.** The largest count is `NTimeDiagonalizer`'s, at about 7 of 342 declarations (2%):
- RO-1's 1;
- the NB-1/BL-1/LS-3 union of 5 (`qy_two_pow_bits_le`, `qy_log_bits`, `qy_bits_len_mono`,
  `qy_lt_two_pow_bits`, `qy_ones_ge`), plus `qy_call_bound`'s inline step until E1;
- `dz_word_lt` (F1);
- `dz_split_stream` (F12).

`NDHost` gains one original-side member (`guessRun_split`) and `ExhaustiveReplay` one
(`xr_val_lt`). **No file crosses one fifth.**

### (g) Brief conformance

| Pin | Delivered | Evidence |
|---|---|---|
| `D = guessRunTM P pexit j Q qentry acc rej`, bundled as a `FinNDTM`; halting by `guessRunTM_haltsWithin`, acceptance by `guessRunTM_accepts_iff` | `dzD` (head 7988); `dz_halts`, `dz_accepts_iff` | head 7988–8195 |
| One guessed block of `g n + 1 + L` cells | `dzBlk G = 1^G ++ [true] ++ bits G` on tape 6; `dz_setup_facts` gives `hblock`, `hend`, `hleft` | head 6337, 8093 |
| `P` as a contract: the query, `g`'s witness and prepend input calls (released); copies; the block by two expansions (the second on `[true]` from `writeConstTM`) and a copy, rewound; the ruler expanded and rewound; the counter `bits (g n)`; `TP ≤ P₀ (g n + 1)` | `dzSetM`'s 12 phases exactly so; `dz_setup` with `dzSetB = (qcA + gcA + pcA + 40)(G + 1)` | head 6294–6589 |
| The own leaf `dzTakeTM` only, its docstring naming the missing row, its own step lemma | yes: "no public row writes a blank at one cell (…`writeConstTM`…`clearTM`…`transferMapTM`…)"; `dz_take_run` by `step_of_some` and `Action.apply_*` | head 5351–5421 |
| `Q`: the flag (`none`/`some true`/`some false`); the tail copied from cell 1 by `copyMapTM_run_ofCfg` directly; the split (`skipBackTM`, `walkTM` over the ruler, `dzTakeTM`, `transferMapTM`, `skipBackTM`); the test (`expandTM`, rewind, `qyCmpTM`, `gt` rejects); the normalization (`lengthBits` install call); `α` by the composite `computesFunInTime_comp pairExtractTM_fst pairExtractTM_snd`; three `qyEmitTM` emissions under `embedSilentTM`; the capture rewound | `dzQM`/`dzQRed` (23 phases), with `dz_flag`, `dz_tail_run`, `dz_split`, `dz_test`, `dz_norm`, `dz_rewrite` | head 6641–6764, 6797–7417 |
| The two runs: one clocked, hosted lemma, generic in the machine and its stop set; the core on tape 6 for its stream, the buffer on 11, the counter on 3; `finish accept` → `acc`, any other `finish` or `timeout` → `rej`; the top's `BF` on the tail's buffer 8, capture rewound, cell 0 taken: `false` → `acc` | `DzClockSpec`/`dz_clock_exists` used for `κ.cR` (stop at `accept`/`reject`) and `κ.cB` (stop at halt); `DzKit.sR`/`sB`; `dz_runR`, `dz_top_run` | head 5608–5865, 6623–6639, 7433–7681 |
| `Q` silent | every segment keeps the output `[]`; `dz_seg_read` reads it at the verdict | head 8018 |
| Time `TP + 2m + T + 11 ≤ K (g n + 1)` | `dz_K_bound`, `K = dzK κ`, built from the kit's constants only | head 7994, 8130 |
| **The uniform `K`** | `dzK` depends on `κ`, so on `f`, `g`, `c` and `BF`, never on `α`. The core's time does not enter it: the clock cuts the core at its allowance `g n`, at physical cost `5G + 2\|bits G\| + 3` (`dz_runR`), whatever the code's constant. Every branch on every input is bounded (`dz_hQ` over all three query shapes) | head 7433–7543, 8038–8152 |
| **The `g n = n` boundary** (the statement gate) | the core's clause in `DzKit.hR` keeps only the total-time `T ≤ C (t + 1)`, the verdict and the cut. `dz_kit_exists` drops the prefix clause (`obtain ⟨T, -, hT, hst, hcut⟩`), so no `\|x\|` term reaches `K` | head 5942–5956, 6100 |
| Per-code `C = max 1 (max C_R C_BF)`; completeness from `C (t' + 1) ≤ g n` (and `t' ≤ g n` from `C ≥ 1`); top from `C 2^{C (T* + 1)} ≤ n ≤ g n` (`κ.hg`, from `timeConstructible_iff`) | the target's body | head 8482–8503 |
| Edge cases | every lemma is general in `G` and the words. Off-stage queries are `[]` and reject at time 2 (`dz_qoff`); `b > g n` hits `gt` (`dz_test`); `b = 0` is general; timeouts reject (`dz_runR`, `dz_top_run`); a `BF` output other than `false :: _` rejects; `g n = 0` gives `dzBlk 0 = [true]` | REPORT's table, checked against the statements |
| Checkpoints 1–8, one commit each, plus three finishing commits | yes (cp1 also carries the leaf, the capture, the clock, the kit and the layout) | out/04-integrity.txt |
| `qy_call_bound` frozen | yes (F8) | head 454–465 |

### (h) The mathematics

The Lean proofs are checked. What remains to read is the docstrings and the architecture.
- **The statements say what they prove.** I read the docstrings of all 106 new declarations
  against their statements.
  - The large lemmas (`dz_setup`, `dz_split`, `dz_test`, `dz_rewrite`, `dz_runR`, `dz_top_run`,
    `dz_qmid`, `dz_qtop`, `dz_hQ`, `dz_halts`, `dz_accepts_iff`, `dz_mid_sound`,
    `dz_mid_complete`, `dz_top_iff`) state their bounds and verdicts as the code has them.
  - One docstring is wrong: `dz_cell0`'s (F6).
  - Every qualified name cited in the new docstrings resolves (out/28-docnames.out). The
    unresolved entries are local variables, state names and the short forms
    `computesFunInTime_lengthBits` and `pairExtractTM_fst`/`_snd`, written after their
    `Turing.FinTM.` context.
- **No vacuous architecture.** Every new lemma is used by the target (item 15). The target's
  hypotheses are its frozen statement's, so nothing can be vacuous beyond the gated statement.
  `hBF` is the `NTimeHierarchy`-supplied decider, and `NTimeHierarchy` discharges it
  (`exists_ndAcceptsWithin_decider`, on the standard three: out/12-hier-ax-head.out).
- **The middle.**
  - Soundness: an accepting stream splits as `s₁ ++ [sp] ++ w` with `|s₁| = g n`. Its first
    verdict is `dz_qmid`'s, so `b = val w ≤ g n`, and the coded machine's branch along
    `s₁.take b` halts with `[true]`. That is `AcceptsWithin (1^{n+1}) b`, then `mono` to `g n`.
  - Completeness: from an accepting word `v₀` (`|v₀| = t'`), the stream `v₀` padded with `false`,
    any separator, and `bits t'` zero-padded to `|bits (g n)|`, worth `t'`. Both directions read
    as the statement requires.
- **The top.** `BF` halts within `C_BF 2^{C_BF (T* + 1)} ≤ g n`, inside the allowance. `D`
  accepts iff the captured output starts with `false`, which by `hBF`'s dichotomy is the
  non-acceptance. Every stream gives the same verdict.

### (i) Public-facing text and policy

- **Campaign vocabulary:** one hit, "published" (F5). The target's remaining "(C1's design §3.6,
  the fallback)" and "Fill obligations" are frozen text left for the deferred cleanup (F9)
  (out/27-newtext.txt).
- **Proof sketches:** every new declaration with a proof over 20 lines has a literal
  `**Proof sketch.**`: 23 of 23, counting `dzClkEmb`'s 75-line injectivity proof. My line
  counter's five misses are four definitions without a proof (`DzClockSpec`, `DzKit`, `dzQM`,
  `dzQRed`) and `dz_split_tape`, whose proof is 17 lines (out/27-newtext.txt).
- **Docstrings:** every new declaration has one (106/106). Short ones are listed in
  out/27b-short-docstrings.txt; F6 covers them.
- **The module header** now reads "(proved)". The target docstring's first line and its
  prefix-clause sentence are public-facing.

### (j) Lint

| | `campaign_style_lint.py TCSlib/Complexity/Diagonalization` | `style_lint.py` on the owned file |
|---|---|---|
| base | 0 FAIL, 3 WARN over 5 files | size only (5,433) |
| head | 0 FAIL, 3 WARN over 5 files, the same three (`EXPCOM`'s check 8, the two sizes) | size only (8,506) |

The only difference is the file's size and declaration counts (out/26-lint-*.txt).

### (k) Process and timeline

F16 gives the timeline. REPORT's other claims check against the logs:
- 34 roots, the same as the campaign's list;
- the bootstrap's 704 s and 2,997 MiB, and the final sweep's 887 s and 2,949 MiB;
- the base screen byte-identical to the campaign's;
- the seal's 350 definitions, 704 delta and equation controls and 4 `simp` controls, with the
  same unsealed exceptions as mine;
- the walk's 212 other-file constants (my out/35-privuse.out).

## Landing plan

**A maintainer PR** onto the campaign tip (`origin/complexity/arora-barak-ch3-4` = `d1ddea26`, after
#181). The merge is clean: the owned file is unchanged at the tip, and `merge-tree` writes no
conflict (out/39-tip.txt).
1. The 11 delivered commits, cherry-picked in order, keeping their authorship, with reworded
   subjects (F17).
2. One maintainer commit applying **E1–E7** (`out/30-landing-edits.diff`; the script
   `scripts/landing_edits.py` asserts each replacement occurs exactly once):
   - **E1**: `qy_call_bound`'s `hb := Turing.length_bits_le_self (f a)`. This is the brief's
     landing item (gate 87's finding 2; F8).
   - **E2**: `rw [ne_eq, …]` (F4).
   - **E3**: `dz_padded_value` cites `Nat.ofDigits_append_replicate_zero` (F2).
   - **E4**: `dz_top_run` cites `MultiTapeTM.exists_first_halt`, and its docstring says so (F3).
   - **E5**: "the published prepend row" → "the prepend row (`…computesFunInTime_prepend`)" (F5).
   - **E6**: the `**Implementation.**` paragraph, REPORT's text verbatim, at the end of the target's
     docstring (F9).
   - **E7**: five private docstrings, text only (F6).

The landed file, `land/NTimeDiagonalizer.lean.txt`, has git blob
**`fc65a848032abfd935b8d847453e047eabb71d24`** and 8,511 lines (out/31-land-setup.txt). Tests:
- **Base snapshot** (a clone of `oleans-leqc3`): the owned file, `NTimeHierarchy` and the facade
  all exit 0 with no output (out/32-*). The audit gives 1,846 constants, 132 public (the head's
  list), the union of axioms within the standard three, and `exists_diagonalizer` on them
  (out/33-land-audit.out).
- **Against the head:** the same constants and public list. No source declaration changes type.
  Values change only in `qy_call_bound`, `dz_test`, `dz_padded_value` and `dz_top_run` (and two of
  `dz_top_run`'s auxiliary proofs) (out/33b-land-vs-head.txt).
- **Sealed:** 0 errors, all 354 controls fail sealed (out/34-land-seal-*).
- **Tip pre-check** (a clone of `oleans-lsm5`, the Lean of #181's head `98912ab2`, which equals the
  tip `d1ddea26` in `.lean` files): the same three modules exit 0 with no output, and
  `exists_diagonalizer` is on the standard three (out/39c-snapshot.txt, out/40-tip-*).

**Replay list** (the downstream closure, never the root `TCSlib`), chained from **`oleans-lsm5`**:
1. `TCSlib/Complexity/Diagonalization/NTimeDiagonalizer`
2. `TCSlib/Complexity/Diagonalization/NTimeHierarchy`
3. `TCSlib/Complexity/Diagonalization`

`oleans-lsm5` is needed because #181 changed `TuringMachine/CodeSimulator`, which is upstream of
the owned file (out/39b-tip-closure.txt).

Expected: 0 errors and no sorry warning in all three. As this review's pre-check found, the three
`NTimeHierarchy` theorems keep `sorryAx` only until NF lands (F18). Link `.lake/packages` in the
PR worktree.

**Commit subjects** (F17; drop "the exact? probe" and "the screen's" from the bodies too):

| Commit | Landed subject |
|---|---|
| `4c15175f` | NTimeDiagonalizer: the overlay's imports; the diagonalizer's setup as a contract |
| `f6b2261f` | NTimeDiagonalizer: the run's phases and dispatch, the handoff, the flag and the tail's copy |
| `2a3e5f71` | NTimeDiagonalizer: the middle's split, the budget's test and its normalization |
| `fdc83fee` | NTimeDiagonalizer: the code α and the core's input |
| `54552c0c` | NTimeDiagonalizer: the two hosted runs and their verdict readers |
| `a2cdad1f` | NTimeDiagonalizer: the run's three cases, D and the uniform time bound |
| `046a6be7` | NTimeDiagonalizer: the middle, both directions, and the top |
| `c1f9a9f6` | NTimeDiagonalizer: exists_diagonalizer proved |
| `d58aef6f` | NTimeDiagonalizer: a proof sketch in dz_setup_facts's docstring |
| `c1a7632c` | NTimeDiagonalizer: cite Turing.length_pairEncode |
| `7b1b9353` | NTimeDiagonalizer: factor in-file near-copies |
| (maintainer) | NTimeDiagonalizer: the diagonalizer's landing edits (qy_call_bound's bound, two citations, ne_eq, docstrings, the Implementation paragraph) |

**The fill gate's pack** should attach:
- `campaign/standards/TEMPLATE.md`, `policy.md`, `workflow.md` and the addendum v2.6;
- the brief, its inputs and its review;
- the delivery's REPORT and evidence;
- this review with `out/`, `probe/` and `scripts/`;
- the landing diff, the duplication ledger and the backlog entries.

It should ask:
1. **Correctness of the architecture:** the uniform `K`, the clock's cut and the `g n = n`
   boundary; the middle in both directions; the top.
2. **Route conformance:** §(g).
3. **Duplication:** F1–F3, F11–F13 and the ledger entries; the screen at the landing head against
   the tip's base.
4. **Rule 10:** the maximal seal (350 definitions, 4 erasures, 704 + 4 controls), the inspection
   and F4. **Rule 11:** F10's public constants.
5. **The public-facing text** after E5–E7; F9.
6. **The replay** (3 modules from `oleans-lsm5`).
7. **Deliverable:** a downloadable `ed-fill-findings.md` with the findings table and the verdict
   line.

## Decisions for the user

1. **The landing edits E1–E7.** Recommended: all seven. E1 is already ruled. E2–E4 change proofs
   and are tested. E5–E7 are text.
2. **F1, `dz_word_lt`, new BL-1 (vi) debt** (major; human acknowledgment required).
   - (a) Acknowledge it as a BL-1 (vi) member of `NTimeDiagonalizer`, for the dedup window's one
     home below both layers (the file cannot reach `Machines/Bin`), and keep the `xr_val_lt`
     promotion request. **Recommended.**
   - (b) Give the file a reachable home now, for example a public word-value bound in
     `Build/CounterLoop` beside `counterValue_eq`, by an API PR before the landing. Not
     recommended: it is one Mathlib step (`Nat.ofDigits_lt_base_pow_length`), and the dedup
     window re-points every (vi) site at once.
3. **F2 and F3 (majors).**
   - (a) Remove them by E3 and E4 in the landing. **Recommended:** tested, and nothing is left to
     acknowledge.
   - (b) Land as delivered and acknowledge both as debt (FH-1 and a Mathlib re-derivation).
4. **The frozen proof sketch (F9).**
   - (a) Resync it in the deferred docstring cleanup, with the target's other campaign references.
     **Recommended:** it is gated text, and E6 describes the real machine.
   - (b) Resync it now, by a maintainer docstring edit in this PR.
5. **The commit history (F17).** Reword the subjects as listed. Keep or drop the
   `Claude-Session:` trailers: the user's call. **Recommended:** reword, keep `Co-Authored-By`.
6. **The ledger entries.**
   - (a) Record them for the dedup window. **Recommended.** They are:
     - F1's BL-1 (vi) member;
     - the two promotion requests (F12);
     - RC-3, the row candidates (F13);
     - F11's in-file factoring, in QF-1's family;
     - F2 and F3, recorded as removed by E3 and E4, so that the ledger shows them caught.
   - (b) Promote `dz_split_stream`'s `List` split by an API PR first. Not recommended: three
     lines, one customer.

**Not yet clear to merge:** no PR, no replay, no fill gate; decisions 1–6 open; F1 awaits the
user's acknowledgment.
