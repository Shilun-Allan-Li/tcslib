# cleanup-stage1 · maintainer delivery review of the final (r1)

**Verdict (interim, phase 1 of 2): ACCEPT THE CODE AS DELIVERED. The report layer needs a maintainer Stage 2 addendum. Pending three rulings and the phase-2 Lean checks.**
- The code is exactly checkpoint 1's: the five patches and `COMMITS.tsv` are byte-identical, and the series reproduces to `c8021348f9bc2d16cfa52ca5e8ff489dc9543592`. **No code changed since the checkpoint**, so there is nothing to justify.
  - decls2 gives exactly the 69 targets ADDED, 0 CHANGED, 0 REMOVED. All 69 headers equal the brief.
  - The change is pure insertion: 43 hunks, all `-n,0`, +1,079 lines, 0 deletions, in the 21 Scope files only.
  - No `sorry` is in the new code, admissions are unchanged against `base-sorries.txt`, and the axioms are standard.
- The worker's Lean evidence recounts cleanly from the raw logs:
  - the bootstrap: 847/847;
  - the sweep: 495/495, bound to tree `985dd312`;
  - the merge-tree equality;
  - 144 seal records;
  - the controls: 20/20 per variant;
  - the unfold scan;
  - lint.
- **The report layer did not take the checkpoint-1 feedback.** The reuse table is byte-identical to checkpoint 1's.
  - CS1-C1-F01 (with ruling CS1-C1-Q1 / DL-53), F02, F04 and F06 are not closed, and CS1-W1 is posed again although it has been ruled (**CS1-F02**, major).
  - S1-26 `Strategy.msgAt_encodeMsgs` duplicates two public lemmas that nobody disclosed: the brief, the worker and the checkpoint review all missed them (**CS1-F01**, major).
  - The DL-35 alias removal that Stage 2 inherits needs seven more statement or body changes beyond the seven approved (three bodies, four statements), plus proof uses (**CS1-F04**, minor, from the brief).
- Phase 1 found 0 blockers, 2 majors, 3 minors and 5 infos. None needs a code change: this review's `stage2/stage2-addendum.tsv` closes the Stage 2 input.
- **Needed from Seyoon:**
  - Q1: accept with the maintainer addendum, or return the job for a report-only r2;
  - Q2: the DL-35 scope;
  - Q3: confirm that CS1-W1 and CS1-W2 are already answered;
  - Q4: the PR target.

## Delivery and landing
- **Delivery:** Claude, a lead with sub-agents A and B (the brief's split).
  - Final: exchange `5451d3cd6fa9b8c313c9f18f5a4da3542c85f02a` ("fill cleanup-stage1: final", 06:20).
  - Checkpoint 1: `bc2bf64a`. The final keeps `checkpoint-1/` unchanged (tree `c6a23dba…` at both commits).
  - Only these two commits touch `inbox/fills/cleanup-stage1/`, and the final touches no other path. I extracted it with `git archive` into a fresh empty directory.
  - The final commit is SSH-signed with the maintainer key (CS1-F06).
- **Issue base:** `daa6e173cdd94cad1475b9a96eca613bce53ba61` (#347).
  - Branch head `c8021348f9bc2d16cfa52ca5e8ff489dc9543592`, tree `508f9154…`. It equals checkpoint 1's.
  - Check base tree `01cc6259…`, check head tree `985dd312…`. Both are recomputed by `git merge-tree --write-tree` from `f99901fd`.
- **Files:** 21. 19 existing files grow by pure insertion (sizes below). There are two new modules: `Games/Tapes.lean` (346 lines) and `ZeroKnowledge/InteractionWords.lean` (44).
  - Frozen and other-campaign files are untouched: `Games/{Probability,Relational,Hopping}.lean`, `Pairing/Group.lean`, `Complexity/CircuitComplexity/**`, `Complexity/BranchingPrograms/**`, `ComputationalModels.lean`, `AdvancedEncryption/**`, `ModuleHost.lean`, `IterateFind.lean`, `TCSlib.lean`, `blueprint/` and every copy file.
- **Records tip:** `b8dfca4edeee569587f78f42256a3923cebb1159`, fetched by name. It includes #351 and #352, and it is **Lean-equal to `463f2244`** (snapshot #4's `T`): 0 Lean, toolchain, manifest or lakefile files differ.
  - The worker used `8b5435eb` (0 Lean files differ from `f99901fd`).
- **Merge checks** (`git merge-tree --write-tree`; all clean, 0 conflicts):
  - tip × #347 → `33fc852384aaae56c50423067b5f9bde3c11747a`;
  - **tip × #347 × Stage 1 (tip × `c8021348`) → `5a2e818df5a92fdf30b8dc276c4fdf32050133d6`**. It is Lean-equal to `463f2244` × `c8021348` (`05c1a0ec…`).
    - The 23 Stage 1 and #347 files are blob-equal to `c8021348`, except `Games.lean`. That file merges as a union: the `Relational` and `Tapes` imports and both `## Contents` entries, 70 lines (`landing/games-facade-union.diff`).
  - Stage 1 × #340 `916afc25` → `997a3626…`;
  - Stage 1 × #346 `98cb0e52` → `bcd0643a…`;
  - Stage 1 × GSW 6a (`land/gsw-6a-statements` `66036926`, O1 + statements + LE-ren; read only) → `931a3127…`;
  - tip × each of these → clean.

  No path is shared with #340 (1 file), #346 (8 files) or 6a (18 files). Rebuild sets do intersect (CS1-F10).
- **Evidence:** `cleanup-stage1-final-r1-phase1-evidence.zip`, SHA-256 `37bfa7506c63716b43e632c75c3af7490ffe3ffd1702f2725ec0c8b2fd0cdbd1`. It holds 66 entries under `cs1-final-r1/`: 56 files, with their own `SHA256SUMS`. `evidence-SHA256SUMS` sits beside it.

## Checks (phase 1)
- **Integrity.**
  - **Manifests,** with exact path sets and no `./`:
    - top level: 2342/2342;
    - `evidence/`: 2265/2265;
    - `checkpoint-1/`: 47/47.
  - **Issue package:** 8/8. `brief.md` is `56368c13…`, the dispatch pin.
- **Reproduction.** I ran `git -c commit.gpgsign=false am --committer-date-is-author-date` with committer `Claude <noreply@anthropic.com>`. It ran in a sparse, detached worktree at the issue base that holds only the 21 paths.
  - All 5 hashes equal `COMMITS.tsv`: `4881cf98`, `01f6b7e9`, `7b8a4d97`, `85797b50` and `c8021348`. The head tree is `508f9154…`.
  - The commits are unsigned (`%G?` = N), as the signing column `none` says.
  - `src/` equals the head byte for byte (21/21).
  - `git diff c8021348 HEAD` is empty, and `patches/` equals `checkpoint-1/patches/` file for file.
- **Statements.**
  - **decls2:** the records' tool (`fa81981a…`, unmodified) on the reproduced head against the issue base gives **69 ADDED, 0 CHANGED, 0 REMOVED**, with an empty `.err`. The output equals the delivered `decls2.tsv` and checkpoint 1's.
  - **Header check:** checkpoint 1's `stmtcmp.py` against the brief gives 67 OK. The 2 DIFF rows are unpinned bodies only:
    - the match arms of `zipWith_xor_cancel_right`;
    - the `where` fields of `FinDist.mixture`.

    The headers are token-equal, and the output is identical to checkpoint 1's.
  - **StmtDump:** `STMT-COUNT 69`, 0 errors.
  - **`protected`:** 54 names are `P` and 15 are fresh, equal to the brief.
- **Proofs and admissions.**
  - The added lines contain 0 `sorry`, `admit`, `@[simp]`, `attribute`, `unfold`, `delta` or `native_decide`.
  - The bootstrap has 26 `sorry` warnings in 12 modules, equal to `base-sorries.txt` module by module.
  - The sweep has 5 warnings in 4 modules: exactly the `base-sorries` modules that lie in the sweep.
- **Axioms** (`Axioms.log` recount): 69 prints, all within {`propext`, `Classical.choice`, `Quot.sound`}, split 34/12/6/4/13, with no `sorryAx`.
- **Scope and additivity.**
  - The 43 hunks are pure insertions.
  - The anchors and the restored-base hashes were checked at checkpoint 1 and are unchanged. The delivered insertion check is ALL_OK (19 × 4 controls).
  - No new import is added in a non-facade file.
- **Docstrings, tags, sketches, sizes, widths.** These are unchanged since checkpoint 1, and I re-ran the checks.
  - All 69 docstrings give the statement and the formula.
  - 68 glue notes; `padTo_of_length`'s wraps across a line break. `pkPredictor_apply` carries `[PS10, Theorem 104.4, proof]`, and the two new modules' References carry the verbatim [PS10] line with the brief's locators.
  - Every proof of 15 lines or more has a `**Proof sketch.**`: `iterSnd_poly` 38, `expect_simulate_tapeImpl` 28, `polyTimeComputable_flatMap_range` 23, `StatClose.of_uprob_ne` 16 and `ofFn_blocks_symm_eq_flatMap` 15. `FinDist.map_uniform_equiv` has 14 proof lines and needs no sketch.
  - Added lines are at most 100 characters wide, with no tab, trailing space or micro sign. Every file is at most 1,000 lines; the largest are `Sampling` 965 and `EncodingMachines` 867.
  - `style_lint` on the 21 head files finds 2 findings, both pre-existing at the base: `Strings` `canonFun_poly`, shifted by 11 lines, and the `BitLists` `## References` placeholder.
  - **Facades:** `Games.lean` has the import after line 11 and the brief's `## Contents` entry after line 47. `ZeroKnowledge.lean` has the import after line 7 and its entry after line 41, in the facade's backtick style, which was disclosed.
- **Clash and shadow.**
  - At the check base the 69 short names have 79 same-short-name declarations, and there are 0 unprotected names with an existing short name (checkpoint 1).
  - Recomputed at the tip, #340, #346 and 6a, the scan finds **0 new** same-short-name declarations.
  - Since the check base, only `Games.lean`, `Games/Probability.lean`, `Games/Relational.lean` and `Pairing/Group.lean` have changed in tip × #347. None of them uses a fresh Stage 1 name unqualified.
  - Resolution is unchanged.
- **Rule 10, delivered evidence recounted** (`recount/`, from the raw logs and probe sources):
  - **Seals:** 144 records (head 19 × 4, base 17 × 4). Each one checks out:
    - the probe hash is the recorded hash;
    - the probe minus the recorded harness insertions equals the owner source at tree `985dd312`/`01cc6259`;
    - the log hash matches;
    - the install and EOF masks have `requested = verified = N`;
    - the recounted errors equal the record.

    The failing declarations are attributed by the source line map:

    | Owner | Head requests sA/sB/cA/cB | Errors base → head | Notes |
    |---|---|---|---|
    | `IterateFindHost` | 251/251/251/251 | 16/16/16/16 → same | DW-5's 16 (`copy_*`, `host_dispatch/branch/halt`); S1-01–03 add none |
    | `PPT` | 543/544/543/544 | 0/1/0/1 → same | `runAtL_ofPolyTimeUniform` (B, `PolyExpr.eval`) |
    | `EnsembleSecurity` | 851/852/850/851 | 0/2/0/2 → same | `singleMessageSecure` (B) |
    | `Trapdoor` | 1636/1637/1635/1636 | 3/3/3/3 → same | pre-existing (`acceptProb_owpGen*_unit`, `predProb_pkPredictor_eq`) |
    | PRF `Asymptotic/Defs` | 667/668/666/667 | 0/8/0/8 → same | B only |
    | `Entropy` | 10/10/9/9 | 10/10/5/5 → 15/15/5/5 | strict +5 in `FinDist.mixture`, `mixture_apply`, `mixture_isSource`; coe unchanged |
    | `Samples` | 10/10/9/9 | 0/0/0/0 → 3/3/0/0 | strict only: `map_apply_expect`, `map_map`, `map_prod_snd` |
    | `Tapes` (new) | 59/59/58/58 | – → 0 | |
    | `InteractionWords` (new) | 748/749/748/749 | – → 0 | |
    | `Adversary`, `Sampling`, `Encoding`, `BitLists`, `Experiments`, `Strings`, `Machines`, `EncodingMachines`, `Interaction`, `FinDist` | as delivered | 0 → 0 | |

    - The rows added at the head are exactly `recordBits`, `recordBits.match_1` and `zipWith_xor_cancel_right.match_1_1`, in the five owners that import `BitLists`; none is removed.
    - In every owner, strict A minus coe A is exactly `FinDist.instCoeFunForallReal`, and strict B minus strict A is exactly `PolyExpr.eval`.
    - **In the canonical coe variants, no new declaration fails.** The 16 strict-only errors in new declarations are the `FinDist` coercion, which is notation by DW-10 Q3 (CS1-F07).
  - **Controls:** in each variant, every sealed negative fails exactly once (20/20). No positive fails, the unsealed pretests have 0 errors, there are 0 stray errors, and every source and log hash matches.
  - **Unfold scan:** 310 items in the 69 new declarations and **0 foreign**. The 2 owned-definition items are `Games.extTape` in its own readers. The 29 local items are hypotheses and `show … by omega` rewrites.
    - The pre-existing foreign multiset (29 items: 27 in `IterateFindHost`, 2 core/Mathlib in `Entropy`) is identical at base and head.
  - **The notations** are as ruled (DW-10 Q3; 2026-11-07): `FinDist`'s `CoeFun` and `PolyExpr.eval`, plus the reducible abbreviations, which the seal records list as `term_excluded`.
- **Builds, recounted** (`recount/buildrecount.out`):
  - **Bootstrap:** 847/847 rc 0, 0 errors in both forms, records equal to my recount.
    - The module list equals `order.txt` in order.
    - Every source hash equals the blob in tree `01cc6259` and the issued `SOURCE-SHA256SUMS`.
  - **Sweep:** 495/495 rc 0, 0/0 errors.
    - The set equals `DOWN` (493) plus the 2 new modules, a valid topological order in two parts (129 then 366).
    - Every source equals the blob in tree `985dd312` (= `git show HEAD`).
    - Module times are 0.92–1.32× the bootstrap's (median 1.00, over 65 modules longer than 5 s), so these were real compiles.
  - **The root and both `audits/*/Checks`** are downstream of the changed modules (497 with them), and the brief did not ask for them (CS1-F08). Phase 2 rebuilds them.
- **Lint, recounted.** `campaign_style_lint --check8b`, with line numbers ignored:
  - Cryptography 92/104 → 92/103 (only the `Trapdoor` `pkPredictor` WARN is gone);
  - InformationTheory 5/2 → 5/2;
  - Complexity 25/390 → 25/390.

  There is no new FAIL or WARN line.
- **Lean:** none run. The evidence settles elaboration (bootstrap, sweep and seals all at the head tree), and no probe was needed. The olean snapshot was not touched; only its map was read.

## CS1-C1 findings: closure in the final

| Checkpoint finding | Required in the final | Status |
|---|---|---|
| F01 `padL`/`padStr` overlap (ruling CS1-C1-Q1: disclose every padding/zero-word overlap, DL-53) | disclosure in *Overlap and reuse* and the Stage 2 table, citing DL-53 | **Not closed.** No `padL`, `padStr`, `padSq`, `padToLen` or `DL-53` anywhere in the delivery. The reuse table is byte-identical to checkpoint 1's (CS1-F02). Closed here by the addendum row (DL-53, deferred). |
| F02 `emitLoop_poly`, `Yao.lean:355 henc` | two rows in the Stage 2 table | **Not closed.** `repoint.tsv` has neither. Closed here by addendum rows. |
| F03 missing evidence | sub-agent notes and greps, raw `exact?` logs, sweep binding | **Closed.** `subagents/A/{NOTES.md,reuse-grep-1.txt,copylist-check.txt}` and `subagents/B/NOTES.md` are delivered. The `exact?` logs are in `reuse/exact/`, while the table still cites `exact-lead/` and `exact-ab/` (nit). The sweep's raw logs are in `build/sweep/summary.txt`, bound to `git show HEAD`. |
| F04 CS1-W1 (b) inaccuracy | correct (b): the ThreeColoring copy does have a target via `EnsembleLemmas.polyTimeComputable_zeros` | **Not closed.** REPORT §13 repeats the claim verbatim and poses CS1-W1 again, though CS1-C1-Q1 ruled it (keep S1-27, 69). |
| F05 binder order (optional) | a note | Not noted (optional). |
| F06 near relatives | name `expect_simulate_congr` and `flatMap_range_ite_eq` | **Not closed.** Addendum rows. |
| F07 `expect_simulate_rel` | optional citation | Not cited (optional); Gate 47 note stands. |
| F08 count | +1,079 | **Closed** (REPORT §3). |
| F09 tip | state the tip used; merge with the current tip | Tip stated (`8b5435eb`). The merge with the current tip is done here (`5a2e818d`). |
| F10 `Tapes` docstring (optional) | `freshImpl_apply`, `tapeImpl_apply` in `## Main results` | Not applied (no code change). Leave it for Stage 2's doc sweep. |
| F11 seal watch list | final check 6 | **Closed.** None of the listed steps fails in the coe seals. |

## The Stage 2 re-point table (`evidence/stage2/repoint.tsv`, 98 rows)
- **Locations.** I read every `path:line` of the table at the check base, and at the issue base for `IterateFind` (`stage2/rowlines-at-check-base.txt`, 158 locations).
  - Every row lands on the declaration or inline step it names.
  - None of these files changed between the check base and the tip, so the line numbers hold at the tip.
- **Targets and instances.** These were checked at checkpoint 1 (S1-04, S1-10, S1-12, S1-14, S1-22, S1-27). Here I also checked:
  - S1-08: all three copies are instances (`a=b=ℓ, a'=b'=ℓ'`; `a=b=n, a'=b'=m`; `a=b=n, a'=m₁, b'=m₂`);
  - S1-06: the five copies have the identical statement;
  - S1-07: `recBits n = recordBits (ettCt.eval n)` and `(ctP.eval n)`;
  - S1-11: the `FromDiscreteLog` copies have the identical statement over the same `Authentication.splitBits`, and `MachineSpec:259` and `CollisionHandler:464` are inline instances;
  - S1-15: the getD copies are instances (the `GI.getD_ofFn_lt'` statement is identical; the others are at `α = Bool` or `d = false`). `Garbling:202` and the theorem headers are proof re-points;
  - S1-16: the worker's added inline sites are instances. The look-alike `Strategy` coin lengths in `ComposeSecurity` are not, so they are correctly left out;
  - S1-20: `EfficiencyRep:101` has the same statement with the arguments reordered;
  - S1-21 and S1-23–25: same statements (binder order only, CS1-C1-F05).
- **Missing rows** (all in `stage2/stage2-addendum.tsv`; this is the maintainer addendum that Stage 2 takes together with `repoint.tsv`):
  - the undisclosed copies of S1-26 (CS1-F01);
  - CS1-C1-F02 and F06, and the DL-53 pointer (CS1-F02);
  - the brief's own `prfAdv_prfReduction` row;
  - the seven DL-35 changes, one per site (CS1-F05);
  - the further DL-35 sites: seven statement or body changes and the proof uses (CS1-F04);
  - DL-55 and DL-56 (ruled after dispatch);
  - further relatives (CS1-F09).
- **Is it complete and correct?** With the addendum, yes for every ledger row in Stage 1's scope.
  - The DL-38 "opportunistic folds" still have no `path:line`, because the brief gave none. The Stage 2 brief must list them.

## Findings

| # | Severity | Finding | Disposition |
|---|---|---|---|
| CS1-F01 | **major**, undisclosed duplicate | S1-26 `Strategy.msgAt_encodeMsgs` (`pairFstD (pairSndD^[i] (encodeMsgs hist)) = hist.getD i []`) duplicates two public lemmas:<br>• `ColZK.field_encodeMsgs` (`ZeroKnowledge/ThreeColoring/ColZKMachine.lean:142`), the statement verbatim;<br>• `ColMachines.getD_eq_pairFstD_iterate` (`ZeroKnowledge/ThreeColoring/Machines.lean:951`), the reversed equation.<br>Also affected is `ColZK.field_zero_encodeMsgs` (`:147`), the `i = 0` corollary.<br>Neither the brief, the reuse table, `repoint.tsv` nor the checkpoint review names them. The worker's short-name grep cannot find them; its shape grep should have. Both copies are downstream of `Interaction` and outside the Compose consumers' closure, so this is a Stage 2 copy, not an E-DUP: the same kind as the listed public `ComposeMachines.msgAt_encodeMsgs`. | No code change. Addendum rows (re-derive both from `Strategy.msgAt_encodeMsgs`). Extend DL-49 in the ledger. **Q1.** |
| CS1-F02 | **major**, feedback not acted on | The final changes nothing since checkpoint 1 in `reuse-table.md` (byte-identical), and `repoint.tsv` lacks every CS1-C1 item:<br>• F01: no `padL`/`padStr`/`padSq`/`padToLen` disclosure and no DL-53, although CS1-C1-Q1 (binding) requires "disclose every padding/zero-word overlap";<br>• F02: `emitLoop_poly` and `Yao.lean:355`;<br>• F04: CS1-W1 (b) repeats the inaccurate "no Stage 2 target", and CS1-W1 is posed again after it was ruled;<br>• F06: the two relatives.<br>The REPORT mentions only the parallelism ruling (05:11) as a relayed message. The head seals ran from 05:14 to 06:16, and the final came at 06:20. The CS1-C1 relay (review at 05:25, ruling at 05:26) may have arrived too late to act on; the delivery does not say. | Closed in this review by the addendum. **Q1:** accept the maintainer addendum (rec.), or return the job for a report-only r2. |
| CS1-F03 | info | Closed items: CS1-C1-F03 (nit: the table cites `exact-lead/`/`exact-ab/`, but they are delivered as `reuse/exact/Reuse{Lead,AB}.*`), F08, F09 (merge with the current tip here) and F11. The optional F05, F07 and F10 were not taken. | None. |
| CS1-F04 | minor, Stage 2 input (from the brief) | Removing the public alias `EnsembleLemmas.blocks` (CS1-Q2) needs more than the seven approved changes. At the check base (= tip) it also appears in:<br>• **bodies:** `bTapeOf` (`EncryptThenTag/CPAHandler.lean:180`), `bTapes` (`CPAReduction.lean:90`), `dTapes` (`Reduction.lean:89`);<br>• **statements:** `bTapeOf_eq` (`CPAHandler:185`), `bTapes_eq` (`CPAReduction:94`), `dTapes_eq` (`Reduction:93`) and `dTape_eq` (`Handler.lean:183`; the seventh change covers only `dTape`'s body);<br>• **proofs:** `CPAReduction:352`, `Reduction:327`, `ThreeColoring/ColRepSound.lean:184/187`.<br>The brief's handover missed them, and the worker carried it unchanged (its table lists `Reduction:93` only as an `extTape` consumer). All the changes are definitional (`blocks := FunFamily.blocks`). | **Q2**, before the Stage 2 brief is issued. Addendum rows; full list in `stage2/dl35-public-alias-uses-at-check-base.txt`. |
| CS1-F05 | minor, table gaps | `repoint.tsv` has these gaps:<br>• it omits the brief's own Stage 2 item `prfAdv_prfReduction` (`OracleFromPRF.lean:286` → `prfAdv_eq_expect`, `Pseudorandom/Functions/Defs.lean:118`);<br>• it carries the seven DL-35 changes as one pointer row, though "the gate checks each one";<br>• DL-55 and DL-56 (G44-01, ruled after dispatch) are records items, not the worker's. | Addendum rows. |
| CS1-F06 | minor, process | Exchange commit `5451d3cd` carries an SSH signature by `SHA256:32dP45eSMmVSt/G/CGvcxl/P+MO3Nwj9xeTh/GSA2wc`, the maintainer's records key (also on `4e749ec6`, `084bb8a1` and the exchange parent `2e015254`). Checkpoint 1 `bc2bf64a` is unsigned. This repeats BS-F08. The series commits are unsigned and reproduce, so the content is unaffected. | Fix the worker environment's signing configuration before the next dispatch (repeat of BS-F08). |
| CS1-F07 | info, CS1-W2 already ruled | The strict-only failures in six new `FinDist` declarations (16 errors) are the `CoeFun` instance by construction: strict minus coe requests is exactly `FinDist.instCoeFunForallReal`, and coe A/B have 0 failures in new declarations. DW-10 Q3 rules this notation: "strict-only failures are recorded, need no fix and no further ruling".<br>Separately, the **canonical** coe seals of `Entropy` already fail at the base in `IsFlatSource.isSource`, `isSource_uniform` and `le_minEntropy_iff` (5 errors), unchanged at the head. That is DW-10 / Stage 2 debt. | No ruling needed (**Q3** confirms). Record in the DW-10 inventory. |
| CS1-F08 | info, pack | The issued `closures.txt`/`order.txt` again omit `audits/pass-shelat/Checks` and `audits/garg-ch1-3/Checks`, which are downstream (BS-F04). `roots.txt` has two spurious lines, `Std.Sat.CNF` and `the`; the latter comes from the docstring line `import the counter loop.` in `Counter.lean:19`. The worker disclosed this and fetched 164 roots. | Phase 2 rebuilds both `Checks`. Fix the pack's closure and roots scripts. |
| CS1-F09 | info, relatives | Undisclosed near relatives with no target (CS1-Q10 notes):<br>• public `flatMap_range_ite_eq_flatten_ofFn` (`Asymptotic/OneWayLemmas.lean:245`) for S1-27 `flatMap_range_ite`;<br>• the Complexity-side private `QuasiPolyHierarchy.flatMap_range_ite` (`:190`).<br>Lamport's `MachineSpec.headD_drop_ofFn` (`:197`) is a disclosed `Bool` specialization of the existing `headD_drop_ofFn` (opportunistic Stage 2). | Addendum rows. |
| CS1-F10 | info, landing | No file overlaps with #340, #346 or 6a, but replays intersect:<br>• `Pairing/Assumptions` (#340);<br>• `IdentityBased/{BonehBoyen,BonehBoyenMachine,Defs}` (#346);<br>• root, `Complexity/CircuitComplexity` (facade) and `ComputationalModels` (6a).<br>All three are downstream of Stage 1/#347. | Whichever merges second re-replays (§6.1). Phase-2 P2-6. |

## Landing plan
- **Branch** `land/cleanup-stage1` from `daa6e173` (#347's head), with maintainer-signed cherry-picks of the five commits `4881cf98..c8021348`.
  - Authors are kept, the committer is the maintainer, and each commit is SSH-signed with the Co-Authored-By and Claude-Session trailers.
  - The picks go onto their own parents, so the head tree stays `508f9154…`. The expected range-diff is 5/5, with trailers only.
  - **No landing edit:** the code is accepted as delivered. CS1-C1-F10's docstring bullet goes to Stage 2's doc sweep, which keeps the series hash-traceable.
- **Stacked on #347,** because both touch the host files (`IterateFindHost.lean`), and Gate 47 audits #347 with Stage 1 together.
  - **Recommended (Q4 a):** open the Stage 1 PR as a draft with base **`cleanup/dw5-derand-readers`** (#347's branch). Its diff is then exactly the 21 files for Gate 47.
  - When #347 merges into `cryptography/pass-shelat-ch2-4`, retarget the Stage 1 PR to the records branch, then merge it there. GitHub retargets automatically if the branch is deleted on merge.
  - Never merge Stage 1 into #347's branch: the stage plan has #347 merge first, or the two merge together as separate merges.
  - Expected Lean after both merges: tree `5a2e818d` (tip × #347 × Stage 1).
- **Merge conditions:**
  - Gate 47 clears #347 and Stage 1;
  - phase 2 (below) passes on the merged tree;
  - Q1 and Q3 are ruled.

  Q2 gates the Stage 2 brief, not this merge.
- **Stage 2 input:** `repoint.tsv` plus this review's `stage2/stage2-addendum.tsv`, the Q2 ruling, and the DL-49/DL-53 ledger updates. Stage 2 starts after Stage 1 merges; the bb1-sim Games PR has already merged (`Relational` is at the tip).

## Phase-2 checklist (merged-tree replays on snapshot #4; `PHASE2-PLAN.txt` has the exact steps)
- **P2-0 Tip and snapshot.**
  - Re-fetch the tip and require 0 Lean, toolchain, manifest or lakefile files differing from `463f2244`.
  - Verify snapshot #4 (`$SP/olean-snapshot`, map `$SP/olean-snapshot.map-463f2244.tsv`, `6607620d…`) at 0/0/0 before and after.
  - The map's 1453 entries hold 1422 TCSlib/audits modules, equal to the closure of root + both `Checks` at `463f2244`.
- **P2-1 Landing branch** as above: range-diff 5/5, tree `508f9154`, and merge-tree with the tip giving `5a2e818d` or a Lean-equal tree. Check the export against `src/`.
- **P2-2 Replay R-S1 on tree `5a2e818d`** (`cp -al` of the snapshot, overlay, `stateplan`/`downorder`/`fullorder`, `runner.py`, with at most 3 Lean processes host-wide shared with GSW 6a).
  - Full order: **1424 modules** (1422 + `Games/Tapes` + `ZeroKnowledge/InteractionWords`).
  - Rebuild **551 modules**: 548 library modules (the 2 new ones included) + root + both `audits/*/Checks` (`landing/down-tip-x-347-x-stage1.txt`).
  - If #347 is replayed and adopted alone first (402 modules, snapshot #5), Stage 1 then needs **499** on #5.
  - Require rc 0 and 0 `error:`/`error(`, a state check that is OK over 1424, and link count 1.
  - Admissions +0 against `T`.
- **P2-3 Axioms:** the 69 use only the standard three (split 34/12/6/4/13), with no `sorryAx`.
- **P2-4 Rule 10 on R-S1:** the seals of the 19 owners in four variants.
  - Expect the delivered head counts and failing sets exactly. Since the check head, the only change in any owner's closure is `Games/Probability`, with +1 theorem and no definition.
  - coe: no failure in a new declaration. Strict-only failures are as recorded (DW-10 Q3).
  - Controls are ALL_OK in both variants (20 pairs), and the unfold scan finds 0 foreign in the 69.
- **P2-5 Lint:** `style_lint` 2 pre-existing findings. In `campaign_style_lint`, the only line-set change against the tip is the removed `Trapdoor` WARN.
- **P2-6 Cross-build (recommended):** tip × #347 × Stage 1 × #340 × #346 × 6a, with throwaway local merges. Expect rc 0 on the intersecting modules (CS1-F10).
- **P2-7 Order, adopt and record.**
  - #347 first, or together with Stage 1.
  - On the Stage 1 merge, adopt `$SP/olean-replay-cs1` (recipe step 6, new `snapshots.md` row) if the merge commit's Lean equals tree `5a2e818d`'s. Otherwise discard it and replay again.
  - Then zip the phase-2 evidence, finalize this review and add the decision-log row.

## Evidence (`cleanup-stage1-final-r1-phase1-evidence.zip`, under `cs1-final-r1/`)
- `PROVENANCE.txt`, `PHASE2-PLAN.txt`, `SHA256SUMS`.
- `integrity/`: manifests, path sets, the issued package, signing-key fingerprints.
- `reproduction/`: `am` hashes, equality with checkpoint 1 and `src/`, the `-U0` diff.
- `statements/`: `decls2.mine.tsv`, `stmtcmp.out` (with checkpoint 1's), `doccheck.out`, `prooflen.out`, `sizes.txt`, `style_lint-head.txt`, `added-scan.txt`.
- `clash/`: same-short-name hits at the check base, tip, #340, #346 and 6a.
- `recount/`: `buildrecount.out`, `sealrecount.out`, `seals.json`, `ctlrecount.out`, `scan-axioms-lint.txt`.
- `landing/`: `merge-trees.txt`, the facade union diff, the PR file lists, and the closure lists for P2-2.
- `stage2/`: `rowlines-at-check-base.txt`, `stage2-addendum.tsv`, `unlisted-copies-source.txt`, `dl35-public-alias-uses-at-check-base.txt`.
- `tools/`:
  - `buildrecount.py`, `sealrecount.py`, `ctlrecount.py`, `misc_recount.py`;
  - `imports.py`, `down.py`, `rowlines.py`, `prooflen.py`, `sizes.py`, `sigfp.py`;
  - checkpoint 1's `stmtcmp.py` and `doccheck.py`;
  - unmodified copies of `decls2.py` and `scripts/style_lint.py`.
- The scratch worktree and the extraction are deleted after the review. Nothing was added, committed or pushed, and no Lean process ran.

## Questions for Seyoon
- **Q1 (CS1-F01, CS1-F02): how to close the report layer.**
  - **(a) Recommended:** accept the delivery as is, since the code equals checkpoint 1 and is verified. This review's `stage2-addendum.tsv` joins the Stage 2 input. Extend DL-49 with `ColZK.field_encodeMsgs`, `ColMachines.getD_eq_pairFstD_iterate`, `emitLoop_poly` and `Yao.lean:355`. DL-53 stands as recorded. No round trip.
  - (b) Return the job for a report-only r2 (REPORT, reuse table, `repoint.tsv`), with the code unchanged. This delays Gate 47.
- **Q2 (CS1-F04): the DL-35 alias removal needs seven more statement or body changes, plus proof uses.**
  - **(a) Recommended:** approve them as the same kind as the seven (definitional), gate-checked one by one in Stage 2:
    - the bodies of `bTapeOf`, `bTapes` and `dTapes`;
    - the statements of `bTapeOf_eq`, `bTapes_eq`, `dTapes_eq` and `dTape_eq`;
    - and their proof uses.
  - (b) Keep the public alias `EnsembleLemmas.blocks`, deprecated by a docstring note. Stage 2 then removes only the private alias, which partly reverses CS1-Q2.
  - (c) Defer the public-alias removal to the post-merge consolidation.
- **Q3 (CS1-W1, CS1-W2): confirm both are already answered.**
  - **(a) Recommended:** W1 by CS1-C1-Q1 (keep `zeros_poly`; 69 declarations), and W2 by DW-10 Q3 (`FinDist` coercion is notation; strict-only failures recorded, no fix).
  - (b) Rule W2 again, restating the six `FinDist` statements in `.prob` form. That would be a statement change in Stage 2; not recommended.
- **Q4: the Stage 1 PR target.**
  - **(a) Recommended:** a draft stacked on `cleanup/dw5-derand-readers`, retargeted to `cryptography/pass-shelat-ch2-4` after #347 merges.
  - (b) Target the records branch now and merge after #347. Its diff shows #347's two commits until then.

**Not yet clear to merge — rulings Q1–Q4 (and Gate 47) are needed, and phase 2 (the merged-tree replay on snapshot #4) has not run yet; no PR is opened**
