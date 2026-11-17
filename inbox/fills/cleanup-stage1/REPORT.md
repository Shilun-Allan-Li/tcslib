# cleanup-stage1 · final report (Pass–shelat cleanup, Stage 1: promotions, additive only)

Worker: Claude in the cloud, a lead with two sub-agents (A, B). Dates 2026-11-17 UTC. Checkpoint 1 was
delivered at exchange `bc2bf64a0c8449adb61234d957acb0e737fb66d5` (`checkpoint-1/`, kept as delivered).
Every target S1-01 to S1-27 (S1-13 withdrawn) is in the branch exactly as the brief states it,
**69 declarations, proved, no `sorry`, 0 statement changes.** Two questions for Seyoon (CS1-W1, CS1-W2,
§13) and no scope request.

## 1. Revisions

| | |
|---|---|
| Exchange pack | `d929cc21ec817b2518d57a7262e42744728f029a`; `shasum -a 256 -c SHA256SUMS` from its directory: 8/8 OK |
| Records of the issue | `f7308a62c3569c400051e8fe7e25663a94f8db8e`: `briefs/pass-shelat-ch5-8/cleanup-stage1/issued-r1/` byte-equal to the pack; the brief's inputs (cleanup-stages, ledger, deferred work, DW-5 README and evidence ZIP, policy, handoff, decls2, `workflow.md` on `main` `a954201d…`) match the SHA-256s the brief gives |
| Records tip used | `8b5435eb31ffbca51218b2a72a381efd3a0c6141` (fetched by name): a descendant of `8adee3e6…` and `f7308a62…`; **no `.lean`, `lean-toolchain`, `lake-manifest.json` or lakefile change after `f99901fd…`**. Its two later records commits approve the seventh DL-35 change (`ETTGame.dTape`; Stage 2) and log the dispatch |
| Issue base | `daa6e173cdd94cad1475b9a96eca613bce53ba61` (`cleanup/dw5-derand-readers`, fetched by name) |
| Check base | `2081fe57475138297fff6a5144d31b91d7f27706`: the issue base with `f99901fdc98f4c7703cf9485329600311a1ea655` merged (`--no-ff`); tree **`01cc6259480ccc9372181cd4d18d4511c87aa048`** (required value); `SOURCE-SHA256SUMS` 847/847 OK |
| Branch `cleanup/stage1-promotions` (local, never pushed) | head **`c8021348f9bc2d16cfa52ca5e8ff489dc9543592`** |
| Check head | `caad0151d3bc3a29dfd23ed07dcc42ab16395cad` = the check base with the branch merged (`--no-ff`); tree **`985dd3125d8fd588cf2c8faa31ced8dee88407ab`** |
| Merged-tree equality | `git merge-tree --write-tree f99901fdc98f4c7703cf9485329600311a1ea655 c8021348f9bc2d16cfa52ca5e8ff489dc9543592` = `985dd3125d8fd588cf2c8faa31ced8dee88407ab` = the check head's tree: **equal** |

### Commits (on the issue base; `git -c commit.gpgsign=false`; signing `none`)

| # | Commit | Subject | Targets |
|---|---|---|---|
| 1 | `4881cf98a91aa6ed01cf3f80af1b08aa5ae06bf8` | DW-9 view versions of the host control steps | S1-01–03 |
| 2 | `01f6b7e90f97209e59720801bbf4433e9c7a159a` | Games forms of simulation in law, coin tapes and tables (DL-40, DL-41, DL-42) | S1-04, 05, 10, 12, `Games` facade |
| 3 | `7b8a4d975794ab56d8d934ceccdcfd77268d047b` | bit-list, coin, encoding and closeness readers (DL-35, DL-40, DL-41, DL-46, DL-47, DL-48, DL-51) | S1-06–09, 11, 14–17, 22 |
| 4 | `85797b502d7c8ee3a4c97187539d76453e21bff4` | history encoding and the shared machine helpers (DL-38, DL-45, DL-49) | S1-18–21, 26, 27, `ZeroKnowledge` facade |
| 5 | `c8021348f9bc2d16cfa52ca5e8ff489dc9543592` | finite-distribution facts (DL-39) | S1-23–25 |

`patches/`: `git format-patch daa6e173…..c8021348…` (5 patches) and `COMMITS.tsv` (hash, author name,
email, date, committer name, email, date, signing, subject). **Reproduction checked:** in a scratch
clone at the issue base, `git am --committer-date-is-author-date` with committer
`Claude <noreply@anthropic.com>` reproduces all five hashes, and the head tree equals `src/` (§7).
Each file was checked at the check tree on its own before integration (§3); commits 4 and 5 were
re-made once locally (before checkpoint 1) to add the `## Main definitions` line of
`InteractionWords.lean`; the old local commits are kept on `backup/stage1-pre-fix1` and are not
delivered.

## 2. Who wrote what

| Agent | Files | Targets |
|---|---|---|
| Lead | `Games/Tapes.lean` (new), `Games.lean`, `Games/Machines.lean`, `Games/Efficiency/Strings.lean`, `Games/Bridges/Experiments.lean`, `Pseudorandom/Functions/Asymptotic/Defs.lean` | S1-04, S1-05, S1-08, S1-10, S1-12 (24 declarations), `Games` facade; integration, commits, every final check, delivery |
| Sub-agent A | `Foundations/BitLists.lean`, `Asymptotic/Adversary.lean`, `Asymptotic/Sampling.lean`, `Authentication/Encoding.lean`, `ZeroKnowledge/Interaction.lean`, `ZeroKnowledge/InteractionWords.lean` (new), `ZeroKnowledge/EncodingMachines.lean`, `ZeroKnowledge.lean` | S1-06, 07, 09, 11, 15, 18–22, 26, 27 (25 declarations), `ZeroKnowledge` facade |
| Sub-agent B | `Randomized/Build/IterateFindHost.lean`, `Randomized/PPT.lean`, `Encryption/PrivateKey/EnsembleSecurity.lean`, `Encryption/PublicKey/Trapdoor.lean`, `InformationTheory/{FinDist,Samples,Entropy}.lean` | S1-01–03, 14, 16, 17, 23–25 (20 declarations) |

This is the brief's suggested split. Each sub-agent had its own sparse git worktree at the check tree, its own TCSlib
olean tree (seeded only with the lead's bootstrap oleans of modules whose source and every upstream
source were byte-identical to the check base: `tools/wtcheck.py` computes a source-and-imports stamp
per module and copies only on equality; seeding records `subagents/*/seeded.tsv` where present),
`.lake/packages` linked to the lead's, ran Lean only through `tools/wtcheck.py` and the host-wide lock,
and handed its files back as a patch (`subagents/A/A.patch`, `subagents/B/B.patch`): each applies at the
issue base, and every resulting file equals the sub-agent's worktree file byte for byte. Only the lead
ran `lake` (the cache fetch), committed and pushed. Their notes, run logs and probe copies are under
`evidence/subagents/{A,B}/`. The lead fixed one proof line of its own S1-05 after its first check
(`List.length_nil` rewritten twice in the `nil` case).

## 3. Changed files

| File | Lines base → head | Added | Permitted change (Scope) |
|---|---|---|---|
| `TCSlib/Complexity/Randomized/Build/IterateFindHost.lean` | 390 → 450 | 60 | S1-01–03 after `host_halt`; bullet |
| `TCSlib/Complexity/Randomized/PPT.lean` | 486 → 494 | 8 | S1-16 after `Coins`; bullet |
| `TCSlib/Cryptography/Foundations/BitLists.lean` | 192 → 244 | 52 | S1-15, S1-06, S1-07 (new section at the end); two bullets (definitions, results) |
| `TCSlib/Cryptography/Asymptotic/Adversary.lean` | 452 → 482 | 30 | S1-09 after `FunFamily.ofFn_blocks`; bullet |
| `TCSlib/Cryptography/Asymptotic/Sampling.lean` | 936 → 965 | 29 | S1-22 in `section StatClose` after `StatClose.mono`; bullet |
| `TCSlib/Cryptography/Authentication/Encoding.lean` | 47 → 66 | 19 | S1-11 after the `simps` attribute; `## Main results` line |
| `TCSlib/Cryptography/Encryption/PrivateKey/EnsembleSecurity.lean` | 340 → 354 | 14 | S1-14 after `encodeList_nil`; bullet |
| `TCSlib/Cryptography/Encryption/PublicKey/Trapdoor.lean` | 570 → 580 | 10 | S1-17 after `pkPredictor`; bullet |
| `TCSlib/Cryptography/Games/Machines.lean` | 278 → 290 | 12 | S1-12 after `buildComp_costBoundedBy`; bullet |
| `TCSlib/Cryptography/Games/Efficiency/Strings.lean` | 570 → 581 | 11 | S1-05 after `length_encodeLog_le`; bullet |
| `TCSlib/Cryptography/Games/Bridges/Experiments.lean` | 136 → 144 | 8 | S1-10 after `prob_sample_eq_uprob`; bullet |
| `TCSlib/Cryptography/Pseudorandom/Functions/Asymptotic/Defs.lean` | 480 → 501 | 21 | S1-08 after `toOracleAdversary_boundedBy`; bullet |
| `TCSlib/Cryptography/ZeroKnowledge/Interaction.lean` | 565 → 611 | 46 | S1-18–20, S1-26 after `pairFstD_encodeMsgs`; bullets |
| `TCSlib/Cryptography/ZeroKnowledge/EncodingMachines.lean` | 694 → 867 | 173 | S1-27, new section before `end`; bullets |
| `TCSlib/InformationTheory/FinDist.lean` | 200 → 280 | 80 | S1-23 after `FinDist.probTrue_eq` (the last declaration); bullet |
| `TCSlib/InformationTheory/Samples.lean` | 155 → 218 | 63 | S1-24 after `end FinDist`, `section Pushforward`; bullet |
| `TCSlib/InformationTheory/Entropy.lean` | 215 → 263 | 48 | S1-25 after `end FinDist`, `section Mixture`; `## Main definitions` bullet |
| `TCSlib/Cryptography/Games.lean` | 64 → 67 | 3 | import after line 11; `## Contents` entry after line 47 |
| `TCSlib/Cryptography/ZeroKnowledge.lean` | 67 → 69 | 2 | import after line 7; `## Contents` entry after line 41 |
| `TCSlib/Cryptography/Games/Tapes.lean` | new, 346 | 346 | S1-04; imports `Games.Hopping` only |
| `TCSlib/Cryptography/ZeroKnowledge/InteractionWords.lean` | new, 44 | 44 | S1-21; imports `ZeroKnowledge.Interaction` and `Complexity.ClassP.BinaryArith.Words` only |

21 files, **+1,079 lines, 0 deleted** (the brief's estimate was 850–1,050). Facade texts: `Games.lean`
carries the brief's entry verbatim; `ZeroKnowledge.lean` carries the brief's text in the facade's
backtick style, ``* `InteractionWords` — the history encoding as a word list (`BinArith.encWords`).``
(the brief writes it inside a code span).

## 4. The new declarations

Kinds, `protected` flags and full names are the StmtDump's (`statements/StmtDump.log`), equal to the
brief's table. Readers: the published lemmas each proof goes through (Rule 10); own-file definitions
are read directly only in their own file.

| Id | Full name | Home | Kind | P | Readers (proof goes through) |
|---|---|---|---|---|---|
| S1-01 | `Complexity.IterateFind.host_dispatch_view` | IterateFindHost | thm | – | `ModuleHost.hostTMView_step_inl`, `hostCtrl_eq`, `Cfg.ofWords_state`, `Cfg.ofWords_def`, `FinTM.controlAction_apply`, `moveInputPos_zero` |
| S1-02 | `Complexity.IterateFind.host_branch_view` | IterateFindHost | thm | – | as S1-01, plus `Cfg.workTapeSymbols_eq`, `Cfg.ofWords_workTapes`, `Cfg.ofWords_workTapePos`, `stateWord_eq`, `FinTM.bufferTape_eq` |
| S1-03 | `Complexity.IterateFind.host_halt_view` | IterateFindHost | thm | – | `hostTMView_step_inl`, `hostCtrl_eq`, `Cfg.ofWords_state`, `controlAction_apply`, `moveInputPos_zero` |
| S1-04 | `TCSlib.Cryptography.Games.expect_simulate_abs`, `expect_simulate_abs_inv` | Games/Tapes | thm | P | `simulate_pure`, `simulate_query`, `expect_pure`, `expect_bind`, `expect_congr_of_allOutputs`, `OracleComp.costBoundedBy_query` |
| S1-04 | `…Games.freshImpl` (def) + `freshImpl_apply` | Games/Tapes | def, thm | P | reader `freshImpl_apply` (`rfl`, own file) |
| S1-04 | `…Games.extTape` (def) + `extTape_of_lt`, `extTape_of_not_lt`, `extTape_update` | Games/Tapes | def, thm | P | the two case readers (own file); `extTape_update` through them and `Function.update_of_ne` |
| S1-04 | `…Games.tapeImpl` (def) + `tapeImpl_apply`, `simulate_tapeImpl_congr`, `expect_simulate_tapeImpl` | Games/Tapes | def, thm | P | `tapeImpl_apply`, `freshImpl_apply`, `extTape_of_lt`, `extTape_update`, `OracleComp.bind_assoc`, `OracleComp.pure_bind`, `expect_sample_coord`, `expect_expect_sample`, `expect_const` |
| S1-04 | `…Games.ovr` (def) + `ovr_nil`, `ovr_cons`, `ovr_of_not_mem`, `ovr_of_mem`, `ovr_update`, `ovr_append`, `expect_sample_ovr` | Games/Tapes | def, thm | P | `ovr_nil`, `ovr_cons` (the two constructors), `Function.update_*`, `expect_sample_coord` |
| S1-05 | `TCSlib.Cryptography.Games.EffFill.length_le_length_encodeLog` | Games/Efficiency/Strings | thm | P | `MachineCodec.encodeLog_nil`, `MachineCodec.encodeLog_cons`, `length_pairEncode` |
| S1-06 | `TCSlib.Cryptography.zipWith_xor_cancel_right` | Foundations/BitLists | thm | – | core `List.zipWith_cons_cons`; Bool cases |
| S1-07 | `TCSlib.Cryptography.recordBits` (def) + `recordBits_none`, `recordBits_some`, `length_recordBits` | Foundations/BitLists | def, thm | – | the two constructor readers (`rfl`); `length_recordBits` through them |
| S1-08 | `Complexity.NUPPT.eval_toOracleAdversary_padFin` | PRF Asymptotic/Defs | thm | – | `padFin_ofFn` (after `subst`) |
| S1-09 | `TCSlib.Cryptography.FunFamily.ofFn_blocks_symm_eq_flatMap` | Asymptotic/Adversary | thm | – | `FunFamily.blocks_symm_apply`, Mathlib `List.ofFn_mul`, `Fin.coe_divNat`, `Fin.coe_modNat` |
| S1-10 | `TCSlib.Cryptography.Games.Bridge.expect_sample_eq_uexp` | Games/Bridges/Experiments | thm | P | `ProbComp.expect_sample`, `uexp_def` |
| S1-11 | `TCSlib.Cryptography.Authentication.ofFn_splitBits_fst`, `_snd` | Authentication/Encoding | thm | P | `splitBits_fst`, `splitBits_snd`, core `List.ofFn_add`, `List.take_left'`, `List.drop_left'` |
| S1-12 | `TCSlib.Cryptography.Games.OracleComp.exists_eq_pure_of_costBoundedBy_zero` | Games/Machines | thm | – | `OracleComp.costBoundedBy_query` |
| S1-14 | `TCSlib.Cryptography.PrivateKeyScheme.encodeList_eq_flatMap` | EnsembleSecurity | thm | P | `encodeList_nil`, `encodeList_cons`, `pairEncode_eq` |
| S1-15 | `TCSlib.Cryptography.getD_ofFn` | Foundations/BitLists | thm | – | `headD_drop`, `headD_drop_ofFn` (the brief's proof) |
| S1-16 | `Complexity.NUPPT.length_ofFn_coins` | Randomized/PPT | thm | P | `List.length_ofFn`, `coinLen_eq` |
| S1-17 | `TCSlib.Cryptography.pkPredictor_apply` | PublicKey/Trapdoor | thm | – | `rfl` (own file); tag `[PS10, Theorem 104.4, proof]` |
| S1-18 | `TCSlib.Cryptography.Strategy.encodeMsgs_eq` | ZK/Interaction | thm | – | `rfl` (own file; `encodeMsgs`' equation lemma) |
| S1-19 | `TCSlib.Cryptography.Strategy.encodeMsgs_eq_flatMap` | ZK/Interaction | thm | P | `encodeMsgs_nil`, `encodeMsgs_cons`, `pairEncode_eq` |
| S1-20 | `TCSlib.Cryptography.Strategy.iterate_pairSndD_encodeMsgs` | ZK/Interaction | thm | P | `encodeMsgs_nil/cons`, `pairSndD_pairEncode` |
| S1-26 | `TCSlib.Cryptography.Strategy.msgAt_encodeMsgs` | ZK/Interaction | thm | P | `Strategy.iterate_pairSndD_encodeMsgs`, `pairFstD_encodeMsgs`, core `List.head?_drop`, `List.getD_eq_getElem?_getD` |
| S1-21 | `TCSlib.Cryptography.Strategy.encodeMsgs_eq_encWords` | ZK/InteractionWords | thm | P | `Strategy.encodeMsgs_eq_flatMap`, `BinArith.encWords_def` |
| S1-22 | `TCSlib.Cryptography.StatClose.of_uprob_ne` | Asymptotic/Sampling | thm | – | `statClose_iff`, `uprob_mono`, `uprob_or_le`, `OneWay.uprob_congr` |
| S1-23 | `TCSlib.InformationTheory.FinDist.map_uniform_equiv`, `sum_map`, `probTrue_nonneg`, `probTrue_le_one`, `uniform_prod`, `uniform_probTrue` | InformationTheory/FinDist | thm | P | `FinDist.ext`, `map_apply`, `prod_apply`, `uniform_apply`, `probTrue_eq` |
| S1-24 | `…FinDist.expect_map`, `probTrue_map`, `map_apply_expect`, `map_map`, `map_prod_snd` | InformationTheory/Samples | thm | P | `map_apply`, `FinDist.ext`, `FinDist.sum_map`, `expect_eq`, `probTrue_eq_expect`, `expect_prod` |
| S1-25 | `…FinDist.mixture` (def) + `mixture_apply`, `mixture_isSource` | InformationTheory/Entropy | def, thm | P | `mixture_apply` (`rfl`, own file); `hasMinEntropy_iff`, `isSource_iff_hasMinEntropy` |
| S1-27 | `TCSlib.Cryptography.EncodingMachines.flatMap_range_ite`, `polyTimeComputable_flatMap_range`, `iterSnd_poly`, `zeros_poly`, `padTo` (def), `padTo_eq`, `padTo_poly`, `length_padTo`, `getD_padTo`, `padTo_of_length` | ZK/EncodingMachines | def, thm | P | the module's toolkit (`cstep*`, `cbound`, `ltTest_poly`, `unaryLength_poly`, `truncate_poly`, `loopState_*`, `polyTimeComputable_loopState`, `polyTimeComputable_of_getD`), `polyTimeComputable_iterateEmit`, `PolyTimeComputable.output_length_le`, `polyTimeComputable_ite/_const`, `PolyTimeComputable.pairEncode`, `pairFstD_pairEncode`, `pairSndD_pairEncode`, `length_pairEncode`, `PolyExpr.eval_normal`; `padTo` read only through `padTo_eq` |

Totals: **69** (7 definitions: `freshImpl`, `extTape`, `tapeImpl`, `ovr`, `recordBits`, `padTo`,
`mixture`; 62 theorems); **54 protected**, 15 fresh names. Definitions land with their readers
(`freshImpl_apply`; `extTape_of_lt`/`_of_not_lt`; `tapeImpl_apply`; `ovr_nil`/`ovr_cons`;
`recordBits_none`/`_some`; `padTo_eq`; `mixture_apply`); none carries `@[simp]` (no attribute at all).
`iterSnd_poly` is re-proved through `polyTimeComputable_loopState` as the brief requires: that lemma
needs a bound on the update for every input word, which the copies' update does not satisfy, so the
update is the second projection cut to `|s x|` bits (`truncate_poly`), which along the loop changes
nothing (taking the second projection never lengthens a word); the docstring's sketch says so.

## 5. Statement changes

**None.** The header check compares the brief's text of every target with the head source (both
normalized by decls2's own parser): **69/69 equal** (`statements/headercheck.txt`). Two headers are
broken over two lines for the 100-character limit (`length_recordBits`, `EncodingMachines.length_padTo`;
no token changed).

## 6. Builds and admissions (checks 1–2)

All on one host, **one Lean process at a time** through a host-wide `flock` (the brief's rule at the
time; the parallelism ruling relayed later on 2026-11-17 arrived during the head seal phase, which was
not interrupted; afterwards only the base explicit-unfold re-scan, one probe, ran). Pool size 1
throughout; peak RSS of one Lean process 3.6 GiB (`build/pool-and-memory.txt`). Every module through `scripts/lean_check_tree.sh`;
seals, controls and probes through `seal/runner_full.py` (`lean -DmaxErrors=0`, no `-o`). Never
`lake build`; the only `lake` command was the narrowed cache fetch.

- **Environment** (`logs/`): preflight before any cache or Lean work (`preflight.log`): 4 CPUs; cgroup
  v1 limit 14,338,760,704 B, in use (usage − total_cache + total_shmem) 38,490,112 B, **headroom
  13.32 GiB** (floor 4); ext4, **26.12 GiB free** (floor 12). Toolchain `leanprover/lean4:v4.25.0` via
  elan, installed after the preflight (2.5 GB). Cache store `~/.cache/mathlib` absent before the fetch
  (`cache-store.log`): no archive was pre-existing. Roots: the **164** Mathlib modules that `order.txt`
  imports (`mathlib-roots.txt`); the issued `roots.txt` has 166 lines, its two extra lines being core
  `Std.Sat.CNF` (in the toolchain) and the word `the`, from the docstring line
  `import the counter loop.` at `TCSlib/Complexity/TuringMachine/Build/Contract/Counter.lean:19`.
  `TAR_OPTIONS=--no-same-owner lake exe cache get <164 roots>`: "Attempting to download 3246
  file(s)", "Decompressing 3246 file(s)", exit 0, no failed download (`cache-get.log`); `find
  .lake/packages -name '*.olean' -size 0`: nothing; package check (`packages-check.log`): "RESULT: 11
  present, 0 mismatch, absent ['«doc-gen4»', 'UnicodeBasic', 'BibtexQuery', 'MD4Lean']" (no module of
  the order imports an absent package); probe `import Mathlib.Algebra.BigOperators.Field` rc 0
  (`cache-probe.log`). No cleaned retry was needed. No module stalled; max RSS 3.6 GiB.
- **Bootstrap** of `order.txt` (847) at the check base (`build/bootstrap/`, per-module raw logs and
  `results.jsonl` with start, end, seconds, max RSS, rc, both error counts, sorry warnings and the
  source SHA-256 bound to `git show HEAD`): **847/847 rc 0, 0 errors in both forms, all bound**;
  `sorry` warnings **26 in 12 modules = `base-sorries.txt`**; 5,455 s of module time. The runner was
  stopped once, by its own PID, after module 150 (to add a three-second lock yield for the
  sub-agents) and resumed from 151; module 151, which finished unrecorded, was rechecked
  (`NOTES.txt`). Order of the work: the whole list was bootstrapped before any check of a changed
  file at the lead's tree (the sub-agents' checks waited for the bootstrap to pass their upstream
  modules).
- **Base snapshot:** the bootstrap tree was hard-linked (`cp -al`) to a base snapshot before the
  sweep; its object map (`build/base-snapshot-map.txt`, 847 oleans, SHA-256
  `16d6ecf8097558a53b40db13f71c4d71198d1309107ceec66dcb0b5657e687df`) re-checks **847/847 unchanged**
  after the sweep (the check script removes each olean before writing it, so no hard link was
  written through). The base seals run against it.
- **Replay sweep at the check head** (`build/sweep/`): the 493 modules of `closures.txt`'s `DOWN`
  plus the two new modules at their positions (`Games/Tapes` after 477, `InteractionWords` after
  558): **495/495 rc 0, 0 errors in both forms, every source bound to `git show HEAD`**
  (`build/sweep/summary.txt`: module, rc, errors in both forms, sorry warnings, source SHA-256,
  seconds, max RSS); 2,016 s. It ran in two parts in dependency order: first the 129 sweep modules in
  the import closure of the 19 homes and the 2 facades (for checkpoint 1), then the other 366. Every
  module whose source differs from its bootstrap olean (the 19 changed, the 2 new) is in the sweep
  with all its downstream modules. The facades `Games.lean` and `ZeroKnowledge.lean` are in it; the
  root `TCSlib` is not built (as briefed; the maintainer replays it).
- **Admissions** (`admissions/admissions.txt`): at the check head, over the 849 modules (847 + the 2
  new), **26 `sorry` warnings in 12 modules, equal to `base-sorries.txt` module by module**; none in
  any new or changed file (`checks/no-sorry.txt`: 0 `sorry` tokens in the 21 files, comments and
  strings stripped).

## 7. Statements, axioms, insertion and frozen checks (checks 3, 4, 5, 7)

- **decls2** (`statements/decls2.tsv`; the records' tool `fa81981a…`, branch head against the issue
  base, the 21 files): **ADDED 69 = exactly the targets; 0 CHANGED; 0 REMOVED.** `touched.py`
  independently: 48 ADDED + 21 in new files, 0 changed, 0 removed, 551 unchanged.
- **StmtDump** (`statements/StmtDump.lean.txt`, `.log`): rc 0, all 69 constants with full name,
  kind, `protected` flag and type; kinds and `protected` equal the brief's table (0 mismatches).
- **Axioms** (`statements/Axioms.log`, `#print axioms` of all 69 on the head tree): all within
  {`propext`, `Classical.choice`, `Quot.sound`}: 34 all three, 12 `propext`+`Quot.sound`, 6
  `propext`, 4 `Classical.choice`, 13 none; **no `sorryAx`**.
- **Insertion check** (`insertion/`, `tools/insertion_check.py`, anchors `tools/anchors.json`: the
  Scope table's 41 anchors in the 19 changed files): **PASS**: every change is an insertion at its
  declared anchor (each block at its canonical down-slid position, the base line's exact text
  checked), and removing the inserted blocks restores each issue-base file byte for byte; base
  SHA-256s equal the Scope table's. Controls on every file: one character changed in a base line →
  FAIL with exactly one difference; one base line deleted → FAIL with exactly one removal; one extra
  line away from the anchors → FAIL; an inserted block moved → FAIL: **ALL_OK** (19 × 4). With
  decls2's 0 CHANGED, no existing statement, proof or docstring is touched.
- **Frozen files** (`checks/frozen.txt`): `git diff --stat daa6e173… c8021348…` lists exactly the 21
  Scope files (0 outside, 0 Scope file untouched). No forbidden file, `TCSlib.lean`, `blueprint/` or
  reference file is touched; no new import in an existing non-facade file.
- **`src/`** holds the 21 files at the branch head; each equals `git show c8021348…:<path>` and the
  `git am` reproduction's file.

## 8. Rule 10: seals, controls, explicit-unfold scan (check 6; `rule10/`)

Driver `tools/rule10_s1.sh` (adapted from DW-5's `rule10_dw5.sh`/`rule10_b.sh`; DW-5's seal suite
unmodified under `tools/seal/`, except `runner_full.py`'s packages path and lock). Head: the 17
changed owners and the 2 new modules at the check head `caad0151…` on the swept tree; base: the 17
owners at the check base `2081fe57…` on the base snapshot. Canonical whole-file seals with
`-DmaxErrors=0` over each owner's full TCSlib import closure (every ordinary definition, matchers
included), in four variants: strict A (`PolyExpr.eval` notation), strict B (`PolyExpr.eval` sealed),
coe A (strict A with `FinDist`'s `CoeFun` instance treated as notation: **the canonical seal**), coe B.
Every probe has its install and EOF verification records. The facades declare nothing and are not
sealed.

| Owner | Requests sA/sB/cA/cB (head) | Errors base sA/sB/cA/cB | Errors head sA/sB/cA/cB | Install+EOF | Failures in new declarations |
|---|---|---|---|---|---|
| `Complexity.Randomized.Build.IterateFindHost` | 251/251/251/251 | 16/16/16/16 | 16/16/16/16 | yes | none |
| `Complexity.Randomized.PPT` | 543/544/543/544 | 0/1/0/1 | 0/1/0/1 | yes | none |
| `Cryptography.Asymptotic.Adversary` | 587/588/586/587 | 0/0/0/0 | 0/0/0/0 | yes | none |
| `Cryptography.Asymptotic.Sampling` | 18/18/17/17 | 0/0/0/0 | 0/0/0/0 | yes | none |
| `Cryptography.Authentication.Encoding` | 194/194/194/194 | 0/0/0/0 | 0/0/0/0 | yes | none |
| `Cryptography.Encryption.PrivateKey.EnsembleSecurity` | 851/852/850/851 | 0/2/0/2 | 0/2/0/2 | yes | none |
| `Cryptography.Encryption.PublicKey.Trapdoor` | 1636/1637/1635/1636 | 3/3/3/3 | 3/3/3/3 | yes | none |
| `Cryptography.Foundations.BitLists` | 0/0/0/0 | 0/0/0/0 | 0/0/0/0 | yes | none |
| `Cryptography.Games.Bridges.Experiments` | 54/54/53/53 | 0/0/0/0 | 0/0/0/0 | yes | none |
| `Cryptography.Games.Efficiency.Strings` | 1173/1174/1172/1173 | 0/0/0/0 | 0/0/0/0 | yes | none |
| `Cryptography.Games.Machines` | 601/602/601/602 | 0/0/0/0 | 0/0/0/0 | yes | none |
| `Cryptography.Games.Tapes` | 59/59/58/58 | –/–/–/– | 0/0/0/0 | yes | none |
| `Cryptography.Pseudorandom.Functions.Asymptotic.Defs` | 667/668/666/667 | 0/8/0/8 | 0/8/0/8 | yes | none |
| `Cryptography.ZeroKnowledge.EncodingMachines` | 890/891/890/891 | 0/0/0/0 | 0/0/0/0 | yes | none |
| `Cryptography.ZeroKnowledge.Interaction` | 567/568/567/568 | 0/0/0/0 | 0/0/0/0 | yes | none |
| `Cryptography.ZeroKnowledge.InteractionWords` | 748/749/748/749 | –/–/–/– | 0/0/0/0 | yes | none |
| `InformationTheory.Entropy` | 10/10/9/9 | 10/10/5/5 | 15/15/5/5 | yes | sA: mixture, mixture_apply, mixture_isSource; sB: mixture, mixture_apply, mixture_isSource |
| `InformationTheory.FinDist` | 0/0/0/0 | 0/0/0/0 | 0/0/0/0 | yes | none |
| `InformationTheory.Samples` | 10/10/9/9 | 0/0/0/0 | 3/3/0/0 | yes | sA: map_apply_expect, map_map, map_prod_snd; sB: map_apply_expect, map_map, map_prod_snd |

- **Base attribution.** Every base failure reappears at the head in the same declarations with the
  same count (`rule10/compare.md`): `IterateFindHost` **16** in all four variants (DW-5's 16: six in
  the `copy_*` proofs, ten in the statements of `host_dispatch`/`host_branch`/`host_halt`; Stage 2's),
  `Trapdoor` 3, `EnsembleSecurity` 2 (B), `PPT` 1 (B), PRF `Asymptotic/Defs` 8 (B), `Entropy` 10/5.
- **Requests.** The head adds request rows only where new definitions enter a closure: `recordBits`,
  its matcher and the matcher of `zipWith_xor_cancel_right` in the five owners that import `BitLists`
  (`Adversary`, `EnsembleSecurity`, `Trapdoor`, `Strings`, PRF `Asymptotic/Defs`); no row is removed.
- **New declarations, canonical (coe A) and coe B: no failure.** In every owner, in both coe variants,
  no failure sits in a new declaration, and the two new modules have 0 failures in all four variants.
- **Strict A/B only: 16 errors in 6 new `FinDist` declarations, all `CoeFun` coercion mismatches**
  (`rule10/head/coe-attribution.txt`, each error read in the raw log): `Entropy`'s `FinDist.mixture`
  (its body, `prob a := w * p a + (1 - w) * q a`, as the brief writes it), `mixture_apply`,
  `mixture_isSource`, and `Samples`' `FinDist.map_apply_expect`, `map_map`, `map_prod_snd`. Under the
  strict seal the instance `FinDist.instCoeFunForallReal` is irreducible, so the brief's statements
  (written with the coercion, `(p.map f) b`, `mixture w … p q a`) elaborate to `CoeFun.coe …`, while every
  published `FinDist` reader (`map_apply`, `expect_eq`, `nonneg`, …) is stored in the unfolded `.prob`
  form; no reader-only proof can bridge the two without reading the instance. It is the projection
  coercion the brief lists as notation; at the base, five pre-existing `Entropy` declarations already fail
  in strict only, by the same mechanism (`shannonEntropy_nonneg`, `shannonEntropy_uniform`,
  `le_maxProb`, `maxProb_pos`, `flat_apply`: 10 strict errors against 5 coe), which is why the
  campaign's coe variant exists. Put to Seyoon as **CS1-W2** (§13).
- **Paired controls** (`rule10/head/controls-{strict,coe}/`, `ctlcheck-{strict,coe}.{json,log}`;
  generator `tools/mkctl_s1.py`, spec `tools/controls-spec.json`). DW-5's generator sealed controls
  with a downstream owner's record; the new modules have no downstream owner, so each control probe
  carries its own seal: the owner's whole closure **and its own definitions**. 19 owners, 20 pairs (two
  for `Tapes`: `tapeImpl`, `ovr`); a negative `theorem ctl… : type_of% @R := by intros; rfl` through the
  sealed definition and a positive `:= @R` through the published reader `R`: new definitions for
  `Tapes` (`tapeImpl_apply`, `ovr_cons`), `BitLists` (`recordBits_some`), `EncodingMachines`
  (`padTo_eq`), `Entropy` (`mixture_apply`), `Interaction` (`encodeMsgs_eq`, S1-18), `Trapdoor`
  (`pkPredictor_apply`, S1-17); an existing definition elsewhere (`copyTMView_eq`, `coinLen_eq`,
  `padFin_def`, `bitsToNat_def`, `atParam_eq`, `encodeList_cons`, `acceptGame_eq`, `fixLen_eq`,
  `MachineCodec.encodeLog_cons`, `toOracleAdversary_eq`, `probTrue_eq`, `expect_eq`; for
  `InteractionWords`, which defines nothing, `encodeMsgs` from its closure). 76 probes (38 strict, 38
  coe; unsealed pretests included): **each sealed negative fails exactly once (20 per variant), every
  positive passes, every unsealed probe rc 0, no stray error: strict `ALL_OK True`, coe `ALL_OK
  True`.**
- **Explicit-unfold scan** (`rule10/scan-compare.txt`; DW-5's `scan1_g40.py`, `scan2.py` and the
  archived lexer): head 1,504 items, 310 in the 69 new declarations, **0 foreign in new
  declarations**; the pre-existing foreign items are identical at base and head (multiset by file,
  declaration, tactic, item, resolution): 27 TCSlib-definition items in `IterateFindHost`'s untouched
  `copy_*` and `host_branch` proofs (DW-5's 27) and 2 core/Mathlib (`Real.logb` in
  `Entropy.shannonEntropy_uniform`). The base scan was run from a worktree at the check base; a first
  base run that had read the head sources is kept, marked invalid, under
  `rule10/base/scan-invalid-headsources/` (the seals read `git show <rev>` and were unaffected).
- **Notation, never sealed:** reducible abbreviations (`ModuleHost.hostTMView`, `ModuleHost.State`,
  `QueryImpl`, `ProbComp`, `NUPPT.Coins`, `Turing.Cfg.Halted`; the seal records list them as
  `term_excluded`), `PolyExpr.eval` (A variants), the `FinDist` coercion (coe variants).

## 9. Lint, sizes, docstrings (checks 8–10)

- **`style_lint.py`** on the 21 files at base and head (`lint/style_lint-{base,head}.txt`): no new
  finding (the one difference is the line number of a pre-existing `Strings.lean` finding,
  `canonFun_poly`, shifted by the insertion). `InteractionWords.lean` has a `## Main definitions`
  section ("None; this module proves one bridge lemma."), which the policy header asks for.
- **`campaign_style_lint.py <area> --check8b`** at the check base and head (`lint/campaign-*`):
  `TCSlib/Cryptography` **92 FAIL / 104 WARN over 518 files** at the base (the maintainer's baseline)
  → 92 / 103 over 520 at the head: the line sets differ only by one WARN removed (`Trapdoor.lean`
  "1 public def(s) without a lemma beside them (check 8): pkPredictor", now read by
  `pkPredictor_apply`); `TCSlib/InformationTheory` 5 / 2 over 7 → 5 / 2 over 7; `TCSlib/Complexity`
  25 / 390 over 500 → 25 / 390: **no new FAIL or WARN line**; check 8 lists none of the 7 new
  definitions.
- **Sizes and widths** (`lint/sizes.tsv`): every added line ≤ 100 characters (0 over; the files'
  pre-existing over-long lines are unchanged), no trailing whitespace added; every file ≤ 1000 lines:
  largest `Asymptotic/Sampling.lean` 965, `ZeroKnowledge/EncodingMachines.lean` 867,
  `Games/Tapes.lean` 346.
- **Docstrings and sketches** (`lint/docstrings-sketches.tsv`): all 69 open with the statement in
  words and state the formula; each carries the tag (`pkPredictor_apply`: `[PS10, Theorem 104.4,
  proof]`) or the glue note "Framework glue, no textbook counterpart."; every proof of 15 lines or
  more has a `**Proof sketch.**` (`expect_simulate_tapeImpl` 28 lines, `iterSnd_poly` 38,
  `polyTimeComputable_flatMap_range` 23, `StatClose.of_uprob_ne` 16, `ofFn_blocks_symm_eq_flatMap`
  15; shorter proofs with sketches too, from their copies). The changed files' module docstrings list
  the new declarations; the two new modules have the full policy header (copyright, imports, the
  three options, `# Title`, `## Main definitions`, `## Main results`, `## References` with the
  repository's [PS10] line verbatim and the location: `Games/Tapes` "Theorem 170.4 (book p. 170): the
  first consumer", `InteractionWords` "§4.4"). No citation was invented.

## 10. Name clash and shadow (check 11; `checks/clash/`)

(a) **0** exact full-name clashes with any declaration (public or private) in `TCSlib/` or `audits/` at
the check base (`clash.tsv`). (b) **54** targets have a short name that exists elsewhere; all 54 are
`protected`, equal to the brief's `P` marks (0 unprotected, 0 mismatches); `shortname.tsv` lists every
hit (the Stage 2 copies and homonyms). The 15 unmarked names have no declaration of that short name
anywhere. (c) Shadow scan over the 495 sweep modules: 361 unqualified occurrences, **0 needing
attention**: 53 are the new declarations' own lines; the rest are uses in modules inside or opening the
new name's namespace (chiefly the ETT files' `ovr`, `tapeImpl`, `freshImpl`, which open
`TCSlib.Cryptography.Games` and keep resolving to `ETTGame.*`, since every `Games` form is
`protected`); a fresh name had no declaration to resolve to. The sweep elaborates all these modules
unchanged.

## 11. Overlap and reuse (check 12; `reuse/reuse-table.md`)

Per target: short-name and shape greps over `TCSlib/` and `audits/`, Mathlib, Batteries and the core
sources, and `exact?` at the **check base** on the 23 statements that need no new definition
(`reuse/exact/`). **No E-DUP.** Every copy line of the brief is confirmed at the check tree.

- `exact?` closed 1 of 23 at the base: S1-16 with core `List.length_ofFn`, **by unfolding
  `NUPPT.coinLen`** (definitional, what Rule 10 forbids consumers): there is no equal reader form.
  It suggested the core relative `List.foldr_append` for the fold form of `ovr_append` (`Games.ovr`
  is a structural recursion, not a `foldr`).
- Disclosed overlaps (not in the brief): **`EncodingMachines.zeros_poly`** has two public,
  inter-derivable forms outside its home's closure (CS1-W1); `padTo` gives the same lists as
  Batteries' `List.takeD L w false` (a different, recursive definition; the target keeps the copies'
  body so Stage 2 can swap definitionally); `Complexity.FormulaKit.polyTimeComputable_flatMap_range`
  (`TCSlib/Complexity/FormulaKit/Emit.lean:127`) is S1-27's statement with the pair order swapped and
  is `sorry` at the base (an admission in another layout; noted for a future Complexity fill).
- S1-14: `TCSlib.Cryptography.encodeList_eq_flatMap` (`Asymptotic/BlockEncryptor.lean:60`) is public
  with the equal statement; the brief lists it as the Stage 2 copy (DL-46 puts the form beside the
  definition): as intended.

### The Stage 2 re-point table

`stage2/repoint.tsv` (98 rows: every copy as `path:line`, what it is, what it re-points to, and
whether the brief listed it). Copies the brief did not list (**FOUND**):

| Copy | Re-points to |
|---|---|
| `Authentication/Signatures/Lamport/MachineSpec.lean:259` (inline `hs`) | `Authentication.ofFn_splitBits_snd` (S1-11) |
| `Authentication/Signatures/HashAndSign/CollisionHandler.lean:464` (inline `hp`) | `Authentication.ofFn_splitBits_fst` (S1-11) |
| `SecureComputation/Yao/HybridProof/RowFromCoins.lean:416` (inline, in `assignmentBit_of_perm`, `:408`) | `getD_ofFn` (S1-15) |
| `Asymptotic/CollectionsHelpers.lean:112`; `Hashing/FromDiscreteLog.lean:97`, `:134` (inline `have`) | `NUPPT.length_ofFn_coins` (S1-16) |
| `Asymptotic/Collections.lean:796`, `:804` (inline, in rewrite arguments) | `NUPPT.length_ofFn_coins` (S1-16) |
| `Encoding/DyadicUniform.lean:83`, `:148`, `:216` (fibre counts by hand) | optionally `FinDist.map_uniform_equiv` at `Equiv.ofBijective` (S1-23; near-copies) |

Consumers that follow a re-pointed definition (also in the TSV): `EncryptThenTag/Games.lean:356`,
`EncryptThenTag/Lazy.lean:445` (`freshImpl`), `EncryptThenTag/Reduction.lean:93` (`extTape`), the
five users of the BlockEncryptor form, and the users of the Rejection forms in
`Randomness/Extraction.lean` and `Randomness/Learning/Law.lean`. Paths under `TCSlib/Cryptography/`
unless they start with `TCSlib/`; lines at the check tree (`IterateFind.lean` at the issue base).
The Stage 2 handover items of the brief (the seven DL-35 changes, DL-43, DL-42, DL-49) are carried in
the TSV unchanged.

## 12. Scope requests

**None.** No target needed a change outside the Scope table.

## 13. Questions for Seyoon (recommended option first)

- **CS1-W1 (`EncodingMachines.zeros_poly`, S1-27).** The reuse search found two public forms the brief
  does not list: `Games.EffFill.zeros_poly` (`Games/Efficiency/Strings.lean:152`, `z ↦ 0^{|f z|}` for a
  polynomial-time `f`) and `EnsembleLemmas.polyTimeComputable_zeros`
  (`Asymptotic/EnsemblesLemmas.lean:212`, `z ↦ 0^{p(|u z|)}`). Each is inter-derivable with the target by
  one length rewrite, but neither is in `EncodingMachines`' import closure, and neither has the
  unary-length hypothesis that `padTo_poly` uses.
  - (a) **Keep `zeros_poly` as the brief states it** (as delivered): the overlap is disclosed, and the
    two older forms are left for a later dedup.
  - (b) Drop it and inline the zero word in `padTo_poly`: 68 declarations, and the ThreeColoring copy
    (`ThreeColoring/Machines.lean:292`) would then have no Stage 2 target.
- **CS1-W2 (strict-variant seal failures in six new `FinDist` declarations, S1-24/S1-25).** In the
  canonical coe-A seal (and coe B) no new declaration fails. In strict A and B, `FinDist.mixture`,
  `mixture_apply`, `mixture_isSource`, `map_apply_expect`, `map_map` and `map_prod_snd` fail, only
  through the `CoeFun` instance: the brief's statements use the coercion (`(p.map f) b`), which the
  strict seal stops from unfolding, while the published readers are stored in the `.prob` form (§8).
  - (a) **Accept them as the projection-coercion notation the brief exempts** (the coe variant is
    canonical, as the brief says; at the base five `Entropy` declarations fail in strict only, the same way).
  - (b) Restate the six statements with `.prob` (a statement change, which needs your ruling; the
    `Rejection.lean` copies use the coercion, so Stage 2 would rewrite through it).

## 14. Evidence

`evidence/` with its manifest `evidence/SHA256SUMS` (every file listed is delivered; paths relative to
`evidence/`, no `./`); the top-level `SHA256SUMS` covers every delivered file except itself (this
report, `patches/`, `src/`, `evidence/`, `checkpoint-1/`). Layout:

- `logs/`: preflight, cache store, roots, cache fetch, package check, cache probe;
- `build/bootstrap/`, `build/sweep/`: per-module raw logs, `results.jsonl`, progress, notes, the sweep
  `summary.txt`; `build/base-snapshot-map.txt`;
- `admissions/`, `statements/` (decls2, header check, StmtDump, axioms, touched), `insertion/`;
- `rule10/base/`, `rule10/head/`: collectors, seal and control probe sources and records, raw logs
  and `results.jsonl`, `seals-*.tsv`, control plans and `ctlcheck-*`, the explicit-unfold scan;
  `rule10/compare.md`;
- `checks/` (clash and shadow, no-sorry, frozen), `lint/`, `reuse/`, `stage2/`;
- `lead/`: the lead's worktree checks; `subagents/A/`, `subagents/B/`: notes, patches, run logs,
  probes;
- `tools/`: every script run (this job's own, and the copies of DW-5's seal suite under `seal/`,
  unmodified except `seal/runner_full.py`, whose header records its two changes).
