# Cleanup Stage 2, S2-A batch D1 (steps A01–A18): report

**Status:** D1 is done in-house. It is on the branch `cleanup/stage2-s2a`, as 18 signed commits, one per plan step, and
the branch is pushed to origin. No PR is open and nothing is merged. All 174 TSV rows of A01–A18 are done or retired as
planned (`items-d1.tsv`). The D1 replay, the seals, the admissions, the lints and decls2 are all clean against the base.
D2 (A19–A38) is not started.

Evidence is in the session scratchpad, `$SP/s2a-d1/`, where `$SP` is
`/tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad`. Its `SHA256SUMS` file has SHA-256
`dfab3215438b2976922e2dc250a20bec0ed8c204f8bc78d209b9c3bec1a02096`.

| Pin | Value |
|---|---|
| Base (records tip) | `61a5f0fb640622c15fdd33df56efa470b2bf26c8`. It is Lean-equal to snapshot #10's T `cf6a2266e9556ca8ad61e56f7232266ccc6d4e62`: the `*.lean`, toolchain and manifest diff is empty |
| Branch head | **`c119a3c4f1d8642b1328740f1d1d1165a92f5567`** (`origin/cleanup/stage2-s2a`) |
| Worktree | `$SP/wt-s2a`: sparse, cone mode, with `TCSlib`, `scripts`, `audits`, `PFR`, `blueprint` and the root files. `.lake/packages` is a symlink to the repo's |
| Inputs | `s2a-workplan-r1.md`, `s2a-items.tsv`, and `cleanup-stages.md` "S2-A rulings Q-A1 to Q-A11" at the records tip |

## 1. Commits (one per step, all `git commit -S`, staged by explicit path)

| Step | Commit | Files (+/−) |
|---|---|---|
| A01 Q11 provider readers | `70503f3cf0a7bb88a376a88020a70a4edc01828a` | `Complexity/TuringMachine/Encoding` +47 −1 |
| A02 iterateFind elim reader + majority B-fix | `e548dcaf1d17b070cd7b257f95071cf709f42b43` | `Complexity/Randomized/Repetition` +24 −1 |
| A03 DL-59 `Games.extTape` at `Type*` + Tapes nit | `da4c401cacac882bf4377aa7d13505ad97de0f0b` | `Games/Tapes` +5 −4 |
| A04 DL-43 `ProbComp.mul_prob_le_expect` | `80990814b8c81fa08109dceeb05d235437c3982c` | `Games/Probability` +20 −0 |
| A05 DL-55 move + Pairing and DL-47 re-points | `2950d13c86612bb12356c064462cdb30a91a03b2` | `TrapdoorPredictor` +0 −4, `Foundations/BitLists` +8 −2, `Pairing/Assumptions` +1 −2 |
| A06 DL-57 promotion (Q-A6 b) | `da5d4ed6bf1c55ffb2fcb36d991ade515e87b549` | `IdentityBased/Defs` +34 −0, `Games/BitCodec` +9 −0 |
| A07 Asymptotic cross-job readers | `bbd628bc60acca40f7d6b41055679eecb36e8aba` | `Ensembles` +29, `EnsemblesLemmas` +7, `Permutations` +21 |
| A08 GeneratorFromPermutation readers | `0f21dcd3bd86dc79c39f4aeea95cb189a064283a` | `Pseudorandom/GeneratorFromPermutation` +18 |
| A09 DL-56 `InteractiveHandler` readers (Q-A5 a) | `62cb7753be3950b01993aa244e0bdd7fe24ba488` | `Games/Efficiency` +14 |
| A10 ModuleHost seal fixes (DW-9) | `5f628db877a2e9da2e03bad2382def7af65be96a` | `Build/ModuleHost` +60 −18 |
| A11 delete `host_*` + copy_clean/copy_finish | `6cdf8bab5df879b310bd2aea0b02c212337332e8` | `Build/IterateFindHost` +30 −68 |
| A12 IterateFindHost remaining seal fixes | `24c6d1491cd86a4fe7bdecad8aaf53421560ec58` | `Build/IterateFindHost` +34 −33 |
| A13 PairSplit part 1 (pairDecode readers) | `3d2334937f750df026bdfb259c3ce9722b0953f8` | `Build/PairSplit` +42 −41 |
| A14 PairSplit part 2 | `ca9219439581e8b7cf660a811981bddffecdbcbb` | `Build/PairSplit` +62 −43 |
| A15 UnaryMul (incl. needs-check SL-089) | `c739a6061a727999da927b133a1c15beb7bf9fc6` | `Build/UnaryMul` +20 −15 |
| A16 Primitives + PPT | `1c9723c1f69cdce3e8b988f50063bfea2183068e` | `Randomized/PPT` +2 −1, `Randomized/Primitives` +9 −5 |
| A17 IterateFind re-points + PS10 A1 | `a3c7c6e2ff10ac9389c2d57135b71ac037ccefd0` | `Build/IterateFind` +7 −21 |
| A18 PS10 Tier A, Theorem 180.1 | `c119a3c4f1d8642b1328740f1d1d1165a92f5567` | `SeedMajority` +16 −15, `SeedMajority/Enumeration` +1 −1, `/State` +6 −6, `/Words` +5 −5, `Derandomization/RootSchedule` +4 −3 |

- **Changes:** 26 modules (the plan had 25; Q-A6 b adds `Games/BitCodec`), +535 / −289 lines
  (`git diff --shortstat` base..head).
- **Commit messages:** each is `S2-A <step>: <summary>` and ends with the two required trailer lines.
- **Rewrite after the lints:** A09 and A10 were amended once, before the replay and the push. The two fixup commits were
  autosquashed and every commit was re-signed. The reason is in §3, item 8.

## 2. Checks

**Per-step file checks** (`scripts/lean_check_tree.sh`, one Lean process at a time):
- **Where:** a `cp -al` working copy of snapshot #10 with the Mathlib overlay. The copy has since been deleted.
- **What was checked:**
  - every changed file of every step;
  - for A03, the facade importer;
  - for A05, the move, all **30 direct importers**;
  - for A06, the five BB1 consumers of the promoted names, to rule out name clashes;
  - for A11, the deletion, its direct importer `IterateFind`.
- **Result:** all rc 0, 0 errors, and no new `sorry`. The one `sorry` warning in `Encoding` is the pre-existing
  `pairDiagTM_computes`. Logs: `checks/<step>/`.

**Development seals** (probes before committing): the J1 owners' coe-A seals at the base, then after each fix.
- **Base failures:** ModuleHost 10, IterateFindHost 16, PairSplit 18, UnaryMul 3, Primitives 2 (B 5), PPT B 1.
- **Needs-check items:** S2-SL-089 and S2-SL-108 were probed first, in their steps (§3).

**D1 replay** (`replay/`):
- **Setup:** the recipe of `snapshots.md`, run on `$SP/olean-replay-s2a-d1`, a `cp -al` copy of snapshot #10.
  - **Plan:** `stateplan` init at `cf6a2266`, then `downorder`, then `fullorder`.
  - **Queue:** 26 changed modules, **778 to build** (the plan's 776 plus `BitCodec`'s own downstream) and 669 reused.
  - **Runner:** the recipe's runner (unmodified), one module per call, slot-gated.
- **Results:**

  | Check | Result |
  |---|---|
  | `permod` | 778 modules; rc≠0 0; `error:` 0; `error(` 0 |
  | `sorry` warnings | 74, in 16 modules, equal module by module to the syntactic admissions at the base |
  | `stateplan update`, then `check` over the 1,447-module full order | **RESULT OK** |
  | Link counts | 778 rebuilt `.olean` at link count 1; 669 reused, all hard links |
  | Snapshot #10 rehash (map `84d88738…2771`) | 0/0/0 before the work, after the replay and at the end |
  | Output map (`mapnoml.py`, no Mathlib) | 1,478 entries, SHA-256 `216f81311de013d93dc6625fd73f66b1173e88695db34a616fada9d5f62730bf` |

- **Kept for D2:** the output tree. Delete it if D2 replays elsewhere.

**Admissions** (`admissions/`, `sorryscan.py` over the full order): base and head both give
`TOTAL 192 in 44 modules; native_decide 0; axiom 0`. The two files are byte-identical.

**Seals at the head** (`seal/d1/`):
- **Setup:**
  - **Collector and instrumenter:** a collector over the 26 touched owners, then canonical **coe-A** and **coe-B** with
    the archived Gate 06/10 instrumenter, unmodified.
  - **Tree and runner:** the replay output, through the gated runner (`lean -DmaxErrors=0`, no `-o`).
  - **Deduplication:** 12 B probes are byte-identical to their A probe (normalized label). They were run once and are
    recorded in `order/ab-dedup.tsv`.
- **Base comparison** (`seal/base/`): the same owners at the base, on a temporary `cp -al` copy of snapshot #10 with the
  overlay, since deleted.

| Owner | coe-A base → head | coe-B base → head |
|---|---|---|
| ModuleHost, IterateFindHost, PairSplit, UnaryMul | 10, 16, 18, 3 → **0** | (= A) → **0** |
| Primitives, PPT, Repetition | 2, 0, 0 → **0** | 5, 1, 1 → **0** |
| IterateFind, SeedMajority ×4, RootSchedule, Tapes, Probability, BitLists, BitCodec, Efficiency, IBE `Defs`, Permutations, GeneratorFromPermutation, Pairing/Assumptions | 0 → 0 | 0 → 0 |
| `Asymptotic/Ensembles` | 12 → 12 | 16 → 16 |
| `Asymptotic/EnsemblesLemmas` | 11 → 11 | 11 → 11 |
| `Encryption/PublicKey/TrapdoorPredictor` | 2 → 2 | 2 → 2 |
| `TuringMachine/Encoding` | 4 → 4 | (= A) |

The remaining failures are in the same declarations at the base and at the head (`tools/errdecl.py`, by enclosing
declaration). None of them belongs to D1:
- **`Ensembles`:** `Indist.copies/symm/trans`, `IndistLit.toIndist`, `indist_iff_exists_negligible`, `hybrid_lemma`,
  `predict_eq`, `prediction_lemma`; with B, also `copies` and `copies_X`. These are A25/A26.
- **`EnsemblesLemmas`:** the S2-SL-151..161 declarations, which are A21.
- **`TrapdoorPredictor`:** `tdpPredictor_runAtL` and `uprob_tdpPredictor`, which are S2-B's S2-SL-270..273.
- **`Encoding`:** `CodeTM.one_le_spaceUsed`, `computesFunInTime_pairEncode_diag` and `pairDiag_step`. The file is handed
  off (DW-10 Q1), and S2-A only inserts the two readers there.

`IterateFind` passes A and B: it is re-sealed clean (F-01).

**Lints** (`lint/`):
- **`style_lint`:** on the 26 files, head = base, byte-identical. The 2 findings are pre-existing: `Enumeration` has no
  `## Main definitions`, and `BitLists`' `## References` has no citation.
- **`campaign_style_lint --check8b`:** over `TCSlib/Complexity` and `TCSlib/Cryptography`. FAIL is 25/92, unchanged.
  WARN goes 390→389 and 103→103, with no new line; the WARN lines that changed only shrink:
  - check 8b `toFinTM` is gone;
  - check 8 loses `Samplable`, `swapAux`, `owpGen`, `owpPair` and `owpGenNot`.
- **Line width:** every line added is at most 100 characters.

**decls2** (`decls2/base-vs-head.tsv`, `maintainer/tools/decls2.py` over the 26 files):

| Kind | Declarations | Ruled item |
|---|---|---|
| ADDED (30) | the 30 readers and promotions of §1.1 | as planned (§4 interface) |
| REMOVED (3) | `Complexity.IterateFind.host_dispatch`, `host_branch`, `host_halt` | S2-RP-004, approved |
| REMOVED/ADDED pair | `TCSlib.Cryptography.decide_singleton_eq_true`, identical statement, `TrapdoorPredictor` → `BitLists` | DL-55, S2-DL-01 |
| CHANGED (4) | `Games.extTape`, `extTape_of_lt`, `extTape_of_not_lt`, `extTape_update` | `{C : Type}` → `{C : Type*}`, DL-59 / Q8 (S2-DL-10) |

There is no other CHANGED or REMOVED.

## 3. Deviations from the plan text (none changes a statement or adds an unplanned declaration)

1. **Q-A6 (b).** `zeroBits_eq_cast` is `Games.zeroBits_eq_cast` in `Games/BitCodec.lean`, so there are 26 changed modules
   and 778 rebuilt (the plan had 25 and 776). The checks above cover it.
2. **A05.** The Pairing re-point appends `decide_singleton_eq_true` to the existing `rw` chain, instead of a separate
   `rw` after it. Same effect.
3. **Row placement inside one declaration.**
   - S2-SL-012/013 (A12 in the TSV) are the last two lines of `copy_finish` and were done in A11 with the rest of the
     declaration.
   - S2-SL-061 (A14) is in `split_sep` and was done in A13.
   - S2-SL-029..032 (A12) were in `host_branch` and are retired by its deletion in A11.
4. **S2-SL-089** (needs-check, A15).
   - **Diagnosis:** the coe-A failure is not the `k`/`State` field. `mul_back` passes the machine's own `mul_tr_back` to
     `PairParse.rewind_run`, whose hypothesis is stated with a `match w 0`. Unifying the two statement matchers needs to
     unfold PairSplit's matcher, which is sealed.
   - **Fix:** discharge the hypothesis in place: `fun inp w => by rw [mul_tr_back]; cases w 0 <;> rfl`. No field
     equations of the private machine are added.
5. **S2-SL-108** (needs-check, A16): fixed as the TSV describes, through `FinTM.computesFunInTime_iff` and a case split on
   `pairDecode z`.
6. **S2-BO-031** (A16). Adding `PolyExpr.eval_const` to the simp set left the goal open under seal B: the instance proof
   inside `ofPolyTimeUniform` blocks `output_ofPolyTime`. The proof is now
   `simp only [runAtL, output_ofPolyTimeUniform]; rfl`. It is proof-only, and seal B gives 0.
7. **A13/A14.**
   - **Shared lemmas:** the non-writing steps go through the published `PairParse.apply_cfg_stay` and
     `apply_cfg_advance`, applied by `.trans` because the cfg type is `pairSplitTM.k`-indexed. Those two lemmas are
     themselves fixed with the `Action.apply` field equations.
   - **Writing steps:** the field equations are used directly.
8. **Post-lint amendments** (fixups squashed into A09 and A10, then re-signed).
   - **A09:** the reader docstrings are now one line each. The four readers had taken `Games/Efficiency.lean` to 1,001
     lines, a `style_lint` FAIL; it now has 996.
   - **A10:** proof sketches are added to `stop_step` (25 lines) and `pad_run` (21 lines), which had grown past the
     ~20-line sketch threshold.
9. **Docstring tags.**
   - **A02:** `polyTimeComputable_iterateFind_elim` carries a "Glue" note and no PS10 tag, because it restates an
     existing lemma.
   - **A04:** `mul_prob_le_expect` takes its `α` from the section variable `{α β : Type}`. The elaborated statement is the
     pinned header's.
10. **A18.** The rewording of `SeedMajority.lean`'s module paragraph re-wraps the four lines after it (whitespace only).
11. **Recipe step 2.** `Mathlib/.../NthRootLemmas.olean` was copied byte-identical (SHA-256 `c0a9cff0…`) from an existing
    overlay instead of being recompiled with `mathlibextra.sh`.

## 4. Helpers and duplication

- **New public declarations:** only the planned ones (decls2 ADDED). There are no new helper lemmas.
- **Local `have`s in ModuleHost** (`stop_step`, `pad_run`):
  - **What they prove:** the flagged or padded configuration reads the module's input symbol (through
    `FinTM.bufferTape_inputSymbol`) and work symbols (through `Cfg.workTapeSymbols_eq`).
  - **Search:** the TuringMachine and SpaceComplexity layers have no published lemma that `Cfg.inputSymbol` depends only
    on `inputPos`. `rg "^(theorem|lemma).*inputSymbol"` finds only per-position readers.
- **`split_dbl_append`:**
  - **Change:** this pre-existing private lemma is re-proved through `dbl_nil`/`dbl_cons`, as the TSV says.
  - **Search:** `rg "dbl_append"` finds a public `dbl_append` only in
    `Cryptography/Encryption/PrivateKey/FromPRF/ReductionMachine.lean`, which is downstream of PairSplit and cannot be
    imported.
  - **Status:** the duplicate is old, not new. It is noted for the ledger: `dbl_append` belongs beside `dbl` in
    `Encoding.lean`.
- **Re-proofs:** no inline derivation re-proves a public TCSlib or Mathlib fact.

## 5. Items left undone

None in D1. Out of D1's scope, and as planned, these stay open:
- the `Ensembles`/`EnsemblesLemmas` seal items (A21, A25, A26);
- `TrapdoorPredictor`'s S2-SL-270..273 (S2-B);
- `Encoding`'s three handed-off failures.

## 6. Questions for Seyoon (recommended option first)

- **Q-D1-1. Two "step 4" labels outside PS10 A1's site list.** The `## References` lines of
  `SeedMajority/Enumeration.lean:31` and `SeedMajority/State.lean:41` still say "§8.2, Theorem 180.1, step 4". The
  cite-check scanned bracket tags only.
  - **(a) Recommended:** fix both in D2, with the same text "final paragraph of the proof", as a docstring-only addition
    to A31's or A38's commit.
  - (b) Leave them; Tier A counts only the 17 tagged sites.
- **Q-D1-2. The D1 replay output `$SP/olean-replay-s2a-d1`** (~0.8 GB of new oleans).
  - **(a) Recommended:** keep it as D2's starting tree, a `cp -al` of it, so D2 rebuilds only its 339 modules. Adopt or
    discard it with D2.
  - (b) Discard it now, and replay D2 from snapshot #10 over the union closure.
- **Q-D1-3. Old duplicate `dbl_append`** (§4).
  - **(a) Recommended:** record it in the duplication ledger, with the move to `Encoding.lean` queued for Stage 3.
  - (b) Move it now, in D2 (this adds a declaration to a handed-off file).

**Ready to run** — D2 (A19–A38) can start on `c119a3c4`.
