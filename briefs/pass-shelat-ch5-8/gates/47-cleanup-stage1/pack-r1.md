# Gate 47 · the cleanup Stage 1 gate: DW-5 (#347) and the Stage 1 promotions (#355) · round 1

Round 1. The auditor is Codex, under the standing ruling of 2026-11-11 (Codex for audits and reviews). **Gate 47** is the
gate that `cleanup-stages.md` gives Stage 1 ("a statement-style audit of the new public API: is each lemma general,
correctly homed, and free of duplication?"), and that the DW-5 decision-log row reserved for #347 ("A Codex gate is to be
staged; the next free number is 47"). Two stacked draft PRs are audited together, because both touch the derand host files
(`cleanup-stages.md` § *Parallel with the GSW/IBE work*).

- **PR #347 (DW-5)**: draft [PR #347](https://github.com/Shilun-Allan-Li/tcslib/pull/347) at
  `daa6e173cdd94cad1475b9a96eca613bce53ba61` (branch `cleanup/dw5-derand-readers`), base `cryptography/pass-shelat-ch2-4`.
  Its merge base with the records branch is `2da7e0f3cd65ec93ed71813b7828c3b66ba18942`. Two SSH-signed commits
  (`1da80d9a` the readers, `daa6e173` the re-derivations). 3 files, **+253/−296**. GitHub's REST `base.sha` is
  `7291f6b237fec75add1549c0992c174442180488`, a later records tip read when the PR was opened; the diff in this pack is from
  the merge base, which is GitHub's three-dot view.
- **PR #355 (Stage 1)**: draft [PR #355](https://github.com/Shilun-Allan-Li/tcslib/pull/355) at
  `d3c7cb00092ad5913904654d922f30fc7d5fce4a` (branch `land/cleanup-stage1`), **stacked on #347**: base
  `cleanup/dw5-derand-readers` at `daa6e173`. Five SSH-signed maintainer cherry-picks of the worker's series
  `4881cf98..c8021348` (author kept); `git range-diff` against the worker series is **5/5 `=`** and the head tree is
  `508f915413ee8ef9f2a37b59e0012c9daf3867aa`, equal to the delivered `c8021348`'s (`checks/series.txt`). 21 files,
  **+1,079/−0**. 69 new declarations.
- **TS1 = `1eaf940b938bb52e3919f5569893b58522df599b`**: the tree of `e1d39836` (the records tip at phase 2) × #347 × #355,
  clean and identical in five merge orders (phase 2 §1; recomputed here from git objects). TS1 against `e1d39836` is exactly
  the 23 files of the two PRs, +1,332/−296. Every TS1 path is blob-equal to #355's head except `Games.lean`, the union of
  the tip's `Relational` entry and #355's `Tapes` entry. **All Lean evidence in this pack is bound to TS1.**
- **Records pin:** `95da6120f0b3b3c80e3078b1d497cbc93aa15fc4`, the tip of `origin/cryptography/pass-shelat-ch2-4` after
  `git fetch` at staging (2026-11-17 11:24 UTC; "Records: #357 merged (BB1 complete); snapshot #6 adoption pending"). It
  descends from `e1d39836`. **Since phase 2 the records branch merged #357** (`8060f6b7`): the pin's Lean differs from
  `e1d39836`'s in exactly #357's 9 files. So pin × #355 is tree `1a1548572d49879ee262d704da431180aefb3a39`, which is TS1
  plus those 9 files, each blob-equal to #357's head `dfdc56f2` (`checks/mergetrees.txt`). TS1 is the audited tree; the
  re-replay that the #357 merge makes necessary is a maintainer merge condition (§ *Merge interaction*). Every record this
  pack cites is read at the pin; this pack's own files are filed after it.
- **Lean base.** Snapshot #5 (T `3f540c22`, map `fca1b6a3…`), whose Lean equals `e1d39836`'s; phase 2 replayed TS1 on it.

**Scope.**
- **#347** is audited **as a proof/refactor**: nine typed-view readers (pure insertions into `ModuleHost.lean`, and into
  `IterateFindHost.lean` apart from two module-docstring bullets) and the re-derivation of E1 `computesFunInTime_find` and
  `polyTimeComputable_find` through them, with both headers and their prose byte-identical.
- **#355** is audited as **new public API** (Stage 1's gate): each of the 69 declarations true, general, correctly homed by
  the CS1 rulings, additive (decls2 69 ADDED / 0 CHANGED / 0 REMOVED; no existing line changed), with readers, formula
  docstrings, source tags or glue notes and proof sketches, and **free of undisclosed duplication**.
- **Out of scope** (do not audit; mention only if something in #347/#355 depends on it): **Stage 2's changes** (the
  re-points, the deletions, the 14 approved `blocks`-alias changes, DW-9's 26 and DW-10's fixes), **DW-10's inventory**,
  **#351/#352** (DW-11's combined gate), the **Complexity handoff** (`cleanup-dw10/handoff-complexity/`), and #357–#360
  except for the merge interaction below. The Stage 2 hand-over is in scope only as a record: is it complete, and does
  #355 make none of it?

Paths below are under `TCSlib/` unless they start with `TCSlib/` or `briefs/`; `Crypto/` is `TCSlib/Cryptography/`.

## What changed

Lines are base → TS1 (`checks/sizes.txt`, `source-head-r1.json`).

**#347** (merge base `2da7e0f3`; the three files are blob-equal at `2da7e0f3` and `e1d39836`):

| File | Change | Lines |
|---|---|---:|
| `Complexity/TuringMachine/Build/ModuleHost.lean` | new section "The typed view of the host": `abbrev hostTMView`, `hostTMView_eq` (`rfl`), `hostTMView_q₀` (`rfl`), `hostTMView_step_inl` (proof `hostTM_step_inl …`), `host_call_view` (proof `host_call …`), `host_clean_view` (proof `host_clean …`); module docstring lists them | 672 → 769 (+97/−0) |
| `Complexity/Randomized/Build/IterateFindHost.lean` | `abbrev copyTMView := ⟨1, Fin 2, ⟨0, copyTM.tm.tr⟩⟩` (start state `0` explicit), `copyTMView_eq` (`rfl`), `copy_clean_view` (proof `copy_clean x`); the two deleted lines are the `## Main definitions`/`## Main results` bullets of `copyTM` and `copy_clean`, each replaced by an extended bullet (`checks/insertion.txt`) | 362 → 390 (+30/−2) |
| `Complexity/Randomized/Build/IterateFind.lean` | E1 `computesFunInTime_find` runs host and copier through the views (`host_call_view`, `host_clean_view`, `hostTMView_q₀`, `initCfg_ofWords`); the dispatch/branch/halt steps are derived in-proof as `hdisp`/`hbranch`/`hhalt` from `hostTMView_step_inl` and `hostCtrl_eq`; `polyTimeComputable_find` re-derived **from E1** (derand F-03's pre-approved route) and moved below it; both sketches refreshed | 801 → 633 (+126/−294) |

- **decls2** (DW-5 `statements/decls2.tsv`): **9 ADDED / 0 CHANGED / 0 REMOVED** (statement level). `touched.out` marks the
  two re-derived theorems CHANGED (bodies); phase 2 counts them among the 80 touched declarations. The frozen check
  (`dw5/statements/frozencheck.txt`) reports exactly one ORDER difference (`polyTimeComputable_find` moved) and no
  header, prose or body difference elsewhere; its control detects a one-character prose change.
- **No longer used** (disclosed): `IterateFind.host_dispatch`, `host_branch`, `host_halt`, `IterateFind.hostTM`,
  `copyTM_k`, and the private `dupWord_poly` (kept; deleting it would be a REMOVED statement). Stage 2 deletes or
  re-points them (`cleanup-stages.md` Stage 2).
- **Effect:** F-01's **20** `IterateFind` seal failures (E1 9 + `polyTimeComputable_find` 11) go to **0** in strict A/B
  and coe A/B; the 26 pre-existing failures of the two host files are DW-9 (ruled 2026-11-16).

**#355** (base `daa6e173`; 19 existing files by pure insertion, 2 new modules; `checks/insertion.txt`: 0 deleted lines):

| Row (ledger) | Home | Declarations |
|---|---|---|
| S1-01–03 (DW-9) | `Complexity/Randomized/Build/IterateFindHost.lean` (362 → 450 at TS1) | `host_dispatch_view`, `host_branch_view`, `host_halt_view` |
| S1-04 (DL-40) | **new** `Crypto/Games/Tapes.lean` (346; imports `Games.Hopping` only) | `Games.expect_simulate_abs`, `_inv`; `freshImpl`, `_apply`; `extTape`, `_of_lt`, `_of_not_lt`, `_update`; `tapeImpl`, `_apply`, `simulate_tapeImpl_congr`, `expect_simulate_tapeImpl`; `ovr`, `ovr_nil`, `_cons`, `_of_not_mem`, `_of_mem`, `_update`, `_append`, `expect_sample_ovr` (20, all `protected`) |
| S1-05 (DL-40) | `Crypto/Games/Efficiency/Strings.lean` | `EffFill.length_le_length_encodeLog` |
| S1-06, S1-07 (DL-40) | `Crypto/Foundations/BitLists.lean` | `zipWith_xor_cancel_right`; `recordBits`, `recordBits_none`, `_some`, `length_recordBits` |
| S1-08 (DL-40) | `Crypto/Pseudorandom/Functions/Asymptotic/Defs.lean` | `Complexity.NUPPT.eval_toOracleAdversary_padFin` |
| S1-09 (DL-35) | `Crypto/Asymptotic/Adversary.lean` | `FunFamily.ofFn_blocks_symm_eq_flatMap` |
| S1-10 (DL-41) | `Crypto/Games/Bridges/Experiments.lean` | `Games.Bridge.expect_sample_eq_uexp` |
| S1-11 (DL-41, DL-44 F-02; CS1-Q5) | `Crypto/Authentication/Encoding.lean` | `Authentication.ofFn_splitBits_fst`, `_snd` |
| S1-12 (DL-42) | `Crypto/Games/Machines.lean` | `Games.OracleComp.exists_eq_pure_of_costBoundedBy_zero` |
| S1-13 | — | withdrawn (DL-43's `mul_prob_le_expect` goes to `Games/Probability` in Stage 2, CS1-Q9) |
| S1-14 (DL-46) | `Crypto/Encryption/PrivateKey/EnsembleSecurity.lean` | `PrivateKeyScheme.encodeList_eq_flatMap` |
| S1-15 (DL-47) | `Crypto/Foundations/BitLists.lean` | `getD_ofFn` |
| S1-16 (DL-48; CS1-Q6) | `Complexity/Randomized/PPT.lean` | `NUPPT.length_ofFn_coins` |
| S1-17 (DL-48) | `Crypto/Encryption/PublicKey/Trapdoor.lean` | `pkPredictor_apply` (tag `[PS10, Theorem 104.4, proof]`) |
| S1-18–20, S1-26 (DL-38, DL-45, DL-49) | `Crypto/ZeroKnowledge/Interaction.lean` | `Strategy.encodeMsgs_eq`, `encodeMsgs_eq_flatMap`, `iterate_pairSndD_encodeMsgs`, `msgAt_encodeMsgs` |
| S1-21 (DL-49) | **new** `Crypto/ZeroKnowledge/InteractionWords.lean` (44; imports `Interaction` and `ClassP.BinaryArith.Words`) | `Strategy.encodeMsgs_eq_encWords` |
| S1-22 (DL-51; CS1-Q7) | `Crypto/Asymptotic/Sampling.lean` | `StatClose.of_uprob_ne` |
| S1-23–25 (DL-39; CS1-Q1) | `InformationTheory/{FinDist,Samples,Entropy}.lean` | 14 `FinDist` facts (6/5/3) incl. `FinDist.mixture` with `_apply`, `_isSource` |
| S1-27 (DL-49, DL-53; CS1-Q8) | `Crypto/ZeroKnowledge/EncodingMachines.lean` (the shared machine layer) | `flatMap_range_ite`, `polyTimeComputable_flatMap_range`, `iterSnd_poly`, `zeros_poly`, `padTo`, `padTo_eq`, `padTo_poly`, `length_padTo`, `getD_padTo`, `padTo_of_length` |
| facades | `Crypto/Games.lean`, `Crypto/ZeroKnowledge.lean` | one import and one `## Contents` entry each |

- **decls2** (records' tool, phase 1): **69 ADDED / 0 CHANGED / 0 REMOVED**, empty `.err`; all 69 headers token-equal to the
  brief (2 DIFF rows are unpinned bodies: the match arms of `zipWith_xor_cancel_right`, the `where` fields of
  `FinDist.mixture`); 54 `protected`, 15 fresh, as the brief says. Added lines: 0 `sorry`, `admit`, `@[simp]`,
  `attribute`, `unfold`, `delta`, `native_decide`; no new import in a non-facade file.
- **Docstrings and sketches** (`phase1/statements/doccheck.out`, `prooflen.out`): every declaration has a formula
  docstring; 68 glue notes and one source tag (`pkPredictor_apply`); the two new modules' References carry the PS10 line.
  Proofs of 15+ lines have a `**Proof sketch.**` (`iterSnd_poly` 38, `expect_simulate_tapeImpl` 28,
  `polyTimeComputable_flatMap_range` 23, `StatClose.of_uprob_ne` 16, `ofFn_blocks_symm_eq_flatMap` 15); doccheck marks
  sketches on further shorter proofs.
- **Sizes and widths:** added lines ≤ 100 characters. `Sampling` 965 and `EncodingMachines` 867 lines are over the 600
  target of `policy.md` and under 1,000; `Adversary`, `PPT`, `Sampling`, `EnsembleSecurity`, `Trapdoor`, PRF `Defs`,
  `EncodingMachines`, `Interaction` have pre-existing lines over 100 (`checks/sizes.txt`).
- **Readers.** Every new definition lands with its reader(s): `recordBits` (`_none`, `_some`), `freshImpl` (`_apply`),
  `extTape` (`_of_lt`, `_of_not_lt`), `tapeImpl` (`_apply`), `ovr` (`_nil`, `_cons`), `padTo` (`_eq`), `FinDist.mixture`
  (`_apply`); #347's `hostTMView` (`_eq`, `_q₀`), `copyTMView` (`_eq`).

## Rulings and records in force

1. **Three cleanup stages** (Seyoon, 2026-11-17; `records/cleanup-stages.md`): Stage 1 is additive promotions; "every new
   public declaration has readers, a formula docstring and a proof. No existing proof is touched." Stage 2 re-points and
   prunes (proof-only); Stage 3 closure. #347 merges before Stage 1, or with it (Q4).
2. **CS1-Q1–Q12** (Seyoon, 2026-11-17; same file): Q1 DL-39 in Stage 1 (the 14 `FinDist` facts, protected); **Q2 the six
   `blocks` changes approved for Stage 2** (+ the seventh, `ETTGame.dTape`'s body); Q3 `MachineCodec.ext_of_fields` moves in
   Stage 2; Q4 `fwdHandler` out of the cleanup; **Q5–Q7 homes** (`Authentication/Encoding`, `NUPPT` in `PPT.lean`,
   `Asymptotic/Sampling`); **Q8 DL-49's helpers to a shared machine layer** importable by both `ThreeColoring/Machines` and
   `ComposeSecurity/Machines`; Q9 DL-43 to Stage 2 (S1-13 withdrawn); **Q10 near relatives that are not instances get no
   target, only notes**; Q11 requests with no ledgered copy declined; Q12 Complexity-side inline chains stay.
3. **CS1-C1-Q1** (2026-11-17): keep S1-27 as CS1-Q8 ruled (69 declarations); disclose every padding/zero-word overlap;
   ledger row **DL-53**.
4. **Stage 1 final rulings Q1–Q4** (Seyoon, 2026-11-17; `cleanup-stages.md`, `final-r1/review.md`): **Q1** accept the
   delivery, the report layer completed by the maintainer's `stage2-addendum.tsv`, **DL-49 extended** for
   `msgAt_encodeMsgs` (CS1-F01), DL-53 standing; **Q2** seven more `blocks`-alias changes approved (bodies of `bTapeOf`,
   `bTapes`, `dTapes`; statements of `bTapeOf_eq`, `bTapes_eq`, `dTapes_eq`, `dTape_eq`): **Stage 2 makes all fourteen,
   its gate checks each**; **Q3** CS1-W1 answered by CS1-C1-Q1, CS1-W2 by DW-10 Q3; **Q4** #355 stacked on #347, then
   retargeted to the records branch, never merged into #347's branch.
5. **DW-5** (Seyoon, 2026-11-16, "debt now, fix after"; `records/deferred-work.md`) and the **DW-5 scope ruling**: the 26
   pre-existing host-file failures become **DW-9**, and DW-5 counts as clearing F-01's 20. **DW-10 Q3**: the
   `FinDist.instCoeFunForallReal` coercion is notation like `PolyExpr.eval`; strict-only failures are recorded and need no
   fix.
6. **Rule 10** (`policy.md` §1): consumers never unfold another file's TCSlib definition; reducible abbreviations are
   notation; coe-A is canonical, strict variants are run and attributed.
7. **Duplication** (`policy.md` § *Duplication*): every instance of duplicated proved material must be human-approved; an
   undisclosed duplicate is a freeze violation. **Precedents:** G44-01 (disclosure is not acceptance; an accepted duplicate
   needs a recorded acceptance and a ledger row with its repayment), G45-01 and G48-01 (an undisclosed re-proof or
   restatement of a public TCSlib or Mathlib lemma graded **major**).
8. **The ledger rows this PR pair promotes or touches** (`records/duplication-ledger.md`): DL-35, DL-38–DL-49, DL-51,
   DL-53; DL-55, DL-56 (Stage 2 items ruled after dispatch, carried in the addendum) and DL-57 (Stage 2, `cleanup-stages.md`); DL-58 repaid in #357 (nothing left).
9. **Signing** (BS-F08 precedent): Claude cloud sessions on this account share one commit-signing key, so a signature attests
   a session on the account, not the maintainer; provenance rests on the pinned hashes, the range-diff and the cherry-picks.

## Questions for the audit

**A. #347 (DW-5), as a proof/refactor** (`pr347.diff.txt`; sources `base-e1d39836/`, `head347-daa6e173/`)
1. Are the nine readers **exact definitional readers in their owners**: `hostTMView` and `copyTMView` the host and the copier
   with their fields made explicit, `_eq`/`_q₀` true by `rfl`, and `hostTMView_step_inl`, `host_call_view`,
   `host_clean_view`, `copy_clean_view` the originals' statements at the views, proved by the originals? Is `copyTMView`'s
   explicit start state `0` the copier's (`copyTM.tm.q₀`)? Are they placed beside what they read, with formula docstrings,
   and none `@[simp]`?
2. Are the insertions pure where stated: `ModuleHost` +97/−0; `IterateFindHost` +30/−2 with the two deletions being module
   docstring bullets only?
3. Is the E1 re-derivation sound, and is every statement unchanged (the frozen check: one ORDER difference)? Is
   `polyTimeComputable_find`'s derivation from E1 (fuel `R.eval`, `init = id`, `final_bound` kept) the pre-approved F-03
   route, and does the moved theorem keep its header and prose byte-for-byte?
4. Does #347 clear F-01's 20 `IterateFind` failures, and is the clearance **reproduced at TS1** (20 → 0 in all four
   variants, § *The replays*)? Are DW-9's 26 correctly pre-existing and untouched?
5. The disclosed duplication: E1's in-proof `hdisp`/`hbranch`/`hhalt` restate `host_dispatch`/`host_branch`/`host_halt` at
   the view; at TS1 they also restate #355's public S1-01–03 (Stage 2 re-points them: `repoint.tsv` rows 2–4). Is that
   disclosure adequate (DW-5 README, PR body, DW-9)?

**B. #355 (Stage 1), as new public API** (`pr355.diff.txt`; sources `ts1/`, `base-e1d39836/`)
1. **Truth and generality.** For each of the 69: is it true as stated, with hypotheses that are neither vacuous nor
   contradictory, and is it the **general form** of every copy the ledger and `repoint.tsv` list for it (each copy an
   instance, as phase 1 checked for S1-06, S1-07, S1-08, S1-11, S1-15, S1-16, S1-20, S1-21, S1-23–25)? Edge cases: `κ = 0`
   and `j + m ≤ κ` in `expect_simulate_tapeImpl`; `m ≥ κ` in `extTape_*`; `M = []` and repeated keys in the `ovr` family;
   `L = 0`, `N < L` in `flatMap_range_ite`; `|w| > L` in `padTo`; `w ∈ {0, 1}` in `FinDist.mixture`; `a = 0` or `b = 0` in
   `ofFn_splitBits_*`; `i ≥ |hist|` in `msgAt_encodeMsgs`; `m.length ≤ p.length` in `zipWith_xor_cancel_right`.
2. **Placement** by the CS1 rulings: S1-04 in a new `Games/Tapes` importing only `Games.Hopping`; S1-11/16/22 per Q5–Q7;
   S1-27 in `ZeroKnowledge/EncodingMachines` as Q8's shared machine layer; S1-21 in a separate `InteractionWords` so that
   `Interaction` does not import `ClassP.BinaryArith`; DL-39 in `InformationTheory` (Q1). Is any home wrong for its
   consumers, or does any home pull a heavy import into a low layer?
3. **Additivity.** decls2 only ADDED; 43 hunks, all pure insertions (`checks/insertion.txt`, phase-1 reproduction); no
   existing declaration, proof, attribute or import of a non-facade file changes; the facades only gain an import and an
   entry. Is anything of Stage 2 (a re-point, a deletion, a `blocks` change) made here?
4. **Docstrings, sources and sketches**: formula docstrings; 68 glue notes and the `[PS10, Theorem 104.4, proof]` tag of
   `pkPredictor_apply` (is the locator right?); sketches where `policy.md` §3 needs them; `protected` exactly on the 54
   names whose short name exists (clash/shadow: 0 new same-short-name declarations at the tip, #340, #346 and 6a).
5. **The Stage 2 hand-over is recorded, not made**: `delivery/repoint.tsv` (98 rows) plus `stage2-addendum.tsv` (the
   CS1-F01 copies, CS1-C1-F02/F06, `prfAdv_prfReduction`, the fourteen DL-35 changes one per site, DL-55, DL-56, the
   CS1-F09 relatives). Is it complete for every ledger row in Stage 1's scope (DL-38's opportunistic folds have no
   `path:line`, as the review notes)?
6. **Ledger rows.** Do DL-35, DL-38–DL-49, DL-51, DL-53 (and the DL-49 extension) state the promoted forms and their
   Stage 2 repayments correctly?

**C. Duplication (an undisclosed or unaccepted duplicate of a public lemma is a major)**
1. The maintainer's sweep (`checks/dup-sweep.txt`, § *Duplication sweep* below) lists every overlap found; part A is covered
   by the records, **part B is not in the ledger at staging**. Confirm or refute each; grade B1–B7; find any other.
2. In particular **B1**: `Games.extTape`/`extTape_update` against the public `extendStream`/`extendStream_update_of_ne`
   (`Pseudorandom/Functions/LazySampling.lean:196/235`).

**D. Evidence** (§ *The replays*): the TS1 replay (556/556 rc 0, state 1429 OK, snapshot #5 0/0/0), its binding to the
heads (TS1 recomputed; every TS1 path blob-equal to #355 or the union facade), admissions 196 = 196 per module, the axiom
prints and census, the seals A/B strict/coe on 21 owners with the exact failure inventory (each failure classified as
notation-only or pre-existing), the controls, the unfold scan, lint 92/104 → 92/103; and the seven phase-2 disclosures.
Exact per-variant counts (G44-03).

**E. Undisclosed matter**: anything in the PRs, the records or this pack that is not disclosed here; and the records/PR
discrepancies listed under *Known dispositions and slips*.

## The replays

**Phase 2 (maintainer, 2026-11-17 07:43–11:10 UTC; `records/cleanup-stage1/final-r1/phase2.md`; evidence
`cleanup-stage1-final-r1-phase2-evidence.zip` `854d6430…`, summaries in `phase2/`):**
- **Tree and binding.** TS1 `1eaf940b` exported with `git archive` (1463 `.lean` files, all blob-verified); `.lake/packages`
  linked. TS1 is recomputed here: `merge-tree e1d39836 × #347` = `f905d841…`, then × #355 = `1eaf940b` (`checks/series.txt`);
  `merge/files-tip-to-TS1.txt` lists the 23 files.
- **Build** on snapshot #5 (`cp -al`, Mathlib overlay 3346 symlinks, NthRootLemmas `c0a9cff0…`): full order **1429**
  (1427 + `Games/Tapes` + `ZeroKnowledge/InteractionWords`), queue **556** (the review's 551 + #346's 5 `BonehBoyenMachine/*`;
  `plan/queue-vs-review-551.txt`), reuse 873. **556/556 rc 0**, `error:` 0, `error(` 0, substring 0, 26 sorry warnings,
  272 warnings, 0 log/record mismatches (`build/permod.out`). State **1429/1429 RESULT OK**, re-run after all probes;
  link count 1 on all 556 rebuilt oleans (after the build and after the probes); 873 reused oleans hard-linked;
  snapshot #5 `snapmap verify` **0/0/0** before, after the build and after all Lean.
- **Admissions** (`admissions/admcmp.out`): **196 at T and 196 at TS1, identical module by module**; the two new modules
  absent → 0; the 556 rebuilt modules carry 26 sorry warnings at both. Source scan: the tip → TS1 Lean diff adds and
  removes 0 `sorry`/`admit`/`native_decide`.
- **Axioms** (`axioms/axsum.out`): Stage 1's 69 within {`propext`, `Classical.choice`, `Quot.sound`}, split **34/12/6/4/13**
  (all three / `propext`+`Quot.sound` / `propext` / `Classical.choice` / none); #347's 27 (the 9 readers, E1,
  `polyTimeComputable_find` and the derand chain to `bpp_subset_dtime_subexp`) exactly the standard three. **Census** of
  the 21 owners: **1224 constants, 0 nonstandard, no `sorryAx`**, 0 errors; all 80 touched declarations in it.
- **Rule 10** (`rule10_cs1p2.sh`; archived Gate 06/10 instrumenter; `mkseals_ab` strict, `mkseals_coe` excluding
  `FinDist.instCoeFunForallReal`; B seals `PolyExpr.eval` too; same probes at the tip on snapshot #5 for the 19 owners that
  exist there). **21 owners**: Stage 1's 17 changed owners, its 2 new modules, #347's `ModuleHost` and `IterateFind`
  (`IterateFindHost` shared). Facades hold no declaration and are not owners.
  - **Head = recorded:** 76/76 Stage 1 rows equal the worker's head (requests, rc, errors, install, EOF, failing set);
    12/12 #347 rows equal DW-5's head (`cmp/head-vs-worker-head.txt`, `cmp/head-vs-dw5-head.txt`).
  - **coe A/B: 0 failures in the 80 touched declarations.**
  - **Strict-only, in new declarations: 16 errors (8 per strict variant)** in six `FinDist` declarations (`Entropy`:
    `mixture`, `mixture_apply`, `mixture_isSource`; `Samples`: `map_apply_expect`, `map_map`, `map_prod_snd`). In every
    owner, strict-A requests minus coe-A requests is empty or exactly `FinDist.instCoeFunForallReal`: **notation by ruling**
    (DW-10 Q3; CS1-F07).
  - **B-only** (strict B minus strict A is empty or exactly `PolyExpr.eval`, notation): `PPT` `runAtL_ofPolyTimeUniform` 1,
    `EnsembleSecurity` `singleMessageSecure` 2, PRF `Asymptotic/Defs` 8; none in a touched declaration.
  - **Pre-existing, identical at the tip** (same declarations and counts in the tip run; `cmp/head-classify.txt`,
    `cmp/tip-classify.txt`):

    | Owner | sA/sB/cA/cB | Failing declarations | Item |
    |---|---|---|---|
    | `IterateFindHost` | 16/16/16/16 | `copy_*`, `host_dispatch`/`host_branch`/`host_halt` (statements) | DW-9 |
    | `ModuleHost` | 10/10/10/10 | `stop_*`, `clean_*`, `pad_*`, `host_seam`, `host_call` | DW-9 |
    | `Trapdoor` | 3/3/3/3 | `acceptProb_owpGen*_unit`, `predProb_pkPredictor_eq` | pre-existing |
    | `Entropy` | 15/15/5/5 (tip 10/10/5/5) | coe: `IsFlatSource.isSource`, `isSource_uniform`, `le_minEntropy_iff` (CS1-F07); strict +5: the three new `mixture*` (coercion) | DW-10 / notation |
    | `Samples` | 3/3/0/0 (tip 0/0/0/0) | the three new `map_*` (coercion) | notation |
    | `PPT`, `EnsembleSecurity`, PRF `Defs` | 0/1/0/1, 0/2/0/2, 0/8/0/8 | as above (B only) | notation |

  - **Tip → TS1** (`cmp/head-vs-tip.txt`): 56 of 76 shared rows identical; the 20 differences: **`IterateFind` 20 → 0 in all
    four variants** (#347's F-01 clearance on the merged tree); `Adversary` and PRF `Defs` requests +3 (`recordBits`,
    `recordBits.match_1`, `zipWith_xor_cancel_right.match_1_1`); `EncodingMachines` −3 net (#347's re-derivation drops
    `polyTimeComputable_find`'s four matchers and splitters, adds `computesFunInTime_find.match_1`; equal to the worker's
    base → head); the strict-only `Entropy`/`Samples` rows above.
  - **Paired controls** (`cmp/controls.txt`): Stage 1 (`mkctl_s1.py`, `controls-spec.json`): **38 probes per variant (19
    sealed), 20/20 sealed negatives fail exactly once** in strict and in coe, 40 positives with 0 errors, unsealed rc 0, 0
    stray, install/EOF on all 19; ALL_OK, equal to the worker's `ctlcheck`. #347 readers (`mkctl_dw5.py`): **10 probes per
    variant (5 sealed), 30/30 negatives fail exactly once**, 60 positives with 0 errors; ALL_OK in strict and coe.
  - **Explicit-unfold scan** (`cmp/scan-head.txt`): 1776 items; **438 in the 80 touched declarations, 0 foreign** (310 in
    the 69 additions = the worker's 310; 128 in E1 = DW-5's 128); the 2 owned-definition items are `Games.extTape` in its
    own readers; the foreign multiset (29: 27 `IterateFindHost`, 2 core/Mathlib in `Entropy`) identical at the tip, the
    worker's head and base.
- **Lint** (`lint/lintcmp.out`): `campaign_style_lint --check8b` FAIL/WARN multisets without line numbers: Cryptography
  **92/104 → 92/103** (removed: the `Trapdoor` "public def without a lemma" WARN for `pkPredictor`), InformationTheory
  5/2 → 5/2, Complexity 25/390 → 25/390; no new line. `style_lint` on the 23 files: 2 findings, both pre-existing
  (`BitLists` `## References` placeholder; `Strings` `canonFun_poly`, line 414 → 425).

**DW-5's own replay (2026-11-16; `records/maintenance-dw5-README.md`; `dw5-evidence.zip` `12abc05a…`, summaries in `dw5/`):**
#347 on its tip `2da7e0f3` on `dl-oleans-2`: 706/706 rc 0, state 1342/1342 OK; seals base 20 → head 0 in `IterateFind`,
reader owners identical to base (`dw5/compare/seals-base-vs-head.txt`); controls 8 probes / 29 negatives ALL_OK;
scan 128 items 0 foreign; axioms standard (193 stored constants); admissions 229 → 229; decls2 9/0/0; lint unchanged;
`dl-oleans-2` restored SNAPSHOT EQUAL. Phase 2 supersedes it on TS1 (above).

**This staging** ran no Lean and no `lake`: only `git` and `grep` (`checks/`).

## Disclosures required by phase 2 (§4 of `phase2.md`, all seven)

1. **The tree is TS1 `1eaf940b`, not the phase-1 review's `5a2e818d`.** The tip then held #340 and #346 (9 Lean files,
   blob-equal to snapshot #5's T), so the rebuild was 556 modules: the 551 plus #346's 5 new modules.
2. **Pre-existing Rule-10 failures carried on the touched owners,** identical at the tip: DW-9 (`ModuleHost` 10,
   `IterateFindHost` 16); `Trapdoor` 3 and DW-10's `Entropy` coe 5; B-only `PolyExpr.eval` (PPT 1, EnsembleSecurity 2,
   PRF Defs 8).
3. **Strict-only failures in six new `FinDist` declarations** (16 errors): the coercion, notation by ruling; coe: 0.
4. **#347's effect reproduces on the merged tree:** `IterateFind` 20 → 0 in all four variants; admissions and axioms as
   recorded.
5. **DW-5's control harness gives 10 probes / 30 negatives rather than 8/29**: the covering seal records are chosen over 21
   owners (PPT's B record carries `PolyExpr.eval`); ALL_OK.
6. **GSW 6a is not in TS1.** The cross-build P2-6 for #340/#346 is subsumed (both in TS1) and was not run for 6a; its
   intersections (root, the `CircuitComplexity` facade, `ComputationalModels`) mean whichever of 6a and Stage 1 merges
   second re-replays.
7. **Process:** the tip seal run's first attempt stopped before any Lean ran (the tip export lacked `lean-toolchain`) and
   was rerun (`rule10/tip-first-attempt-driver.out`); the seal-phase watchers matched themselves and outlived their drivers
   until killed (they only log, plus pause on more than 3 Lean processes, which never happened); three temporary
   unreferenced commit objects were created for merge-tree inputs.

## Duplication sweep (maintainer, at staging; `checks/dup-sweep.txt`)

Over all **78** new declarations (9 + 69): same-short-name declarations in TS1 and in Mathlib `029db123`, Batteries and
Lean v4.25.0 core (`dup/shortname-hits.tsv`); 37 statement-shape regexes (`dup/shape-hits.txt`); declaration-header
searches (`dup/stmt-*.txt`); each hit read and classified. Grep and reading only; no `exact?` (the worker's `exact?` logs,
23 statements at the check base, are in the delivery; `delivery/reuse-table.md`).

**A. Covered by the records** (the ledgered copies this PR pair promotes; Stage 2 re-points them):

| New | Existing public (or private) overlap at TS1 | Record |
|---|---|---|
| S1-01–03 `host_*_view` | E1's in-proof `hdisp`/`hbranch`/`hhalt` (`IterateFind.lean:373/378/390`, added by #347); view forms of `host_dispatch`/`_branch`/`_halt` (`IterateFindHost.lean:354/366/382`) | DW-9; `repoint.tsv` rows 2–4 |
| #347 `host_call_view`, `host_clean_view`, `hostTMView_step_inl`, `copy_clean_view` | `host_call`, `host_clean`, `hostTM_step_inl` (`ModuleHost.lean:518/622/480`), `copy_clean` (`IterateFindHost.lean:213`), restated at the views by design | DW-5 / SR-02, disclosed in #347 |
| S1-04 `Games.*` (17 of 20) | public `ETTGame` copies `EncryptThenTag/Tools.lean:65–281`, `Lazy.lean:175` | DL-40 |
| S1-04 `extTape`, `_of_lt`, `_update` | public `AdaptiveCPA.extTape`, `_of_lt`, `_update` (`AdaptiveCPA/Hybrid.lean:211/215/221`) | DL-40 (see B1) |
| S1-05, S1-06, S1-07, S1-08 | private `length_le_length_encodeLog` ×2; `ETTGame.zipWith_xor_cancel` (`Lazy.lean:295`) + 4 private; `ETTGame.recBits`/`PRFGame.recBits` families; ETT/PRF/MAC `eval_toOracleAdversary_*` (instances) | DL-40, DL-44 |
| S1-09 | `EnsembleLemmas.ofFn_blocks_symm` (`EnsemblesLemmas.lean:433`, through the alias); relatives `FunFamily.ofFn_blocks_symm` (`OneWay.lean:380`, flatten form), `Runs.lean:71` | DL-35, DL-38, DL-49 |
| S1-10 | public `expect_sample_eq_uexp` (`Hashing/FromDiscreteLog/Probability.lean:40`), same statement | DL-41 |
| S1-11 | public `FromDiscreteLog.ofFn_splitBits_fst/_snd` (`…/FromDiscreteLog/Encoding.lean:45/55`), same statements; 3 inline | DL-41, DL-44 |
| S1-12 | `HashAndSign/OneQuery.lean:36`, `Lamport/Planted.lean:226` | DL-42 |
| S1-14 | public `encodeList_eq_flatMap` (`Asymptotic/BlockEncryptor.lean:60`), same statement; `MultiMsg.encodeList_eq_flatMap`; private `FromPRF:251` | DL-46 |
| S1-15 | public `GI.getD_ofFn_lt'` (`GraphIsomorphism/SoundnessRep.lean:61`), **same statement** (`Type*`); Bool copies and inline chains; no `List.getD_ofFn` in core/Batteries/Mathlib | DL-47 |
| S1-16 | public `NMSim.length_ofFn_coins`, `OT.length_ofFn_coins`, same statement; core `List.length_ofFn` after unfolding `coinLen` (forbidden to consumers) | DL-48 (CS1-Q6) |
| S1-18–20, S1-21, S1-26 | `ComposeSecurity/Machines`, `ThreeColoring/Machines`, `SimulatorNumeric`, GI `EfficiencyRep`, `SequentialZK/Normalization`, `Yao/HybridProof/Lengths`; `ColZK.field_encodeMsgs` (same as S1-26), `ColMachines.getD_eq_pairFstD_iterate` (reversed) | DL-38, DL-49 (extended) |
| S1-22 | public `statClose_of_uprob_ne` (`Candidates/DDH.lean:145`), same statement | DL-51 (CS1-Q7) |
| S1-23–25 | public `Rejection.*` (`Randomness/Extraction/Rejection.lean`), same statements | DL-39 (CS1-Q1) |
| S1-27 | `ComposeSecurity/Machines`, `ThreeColoring/Machines` copies; `padL`/`padStr`/`padSq`/zero-word families; relatives `flatMap_range_ite_eq_flatten_ofFn`, `QuasiPolyHierarchy.flatMap_range_ite` | DL-49, DL-53; addendum (CS1-F09) |

**B. Not in the ledger at staging** (reported to the maintainer before dispatch; the ledger at the pin has none of them):

- **B1 (strongest). `Games.extTape`, `extTape_of_lt`, `extTape_update` (S1-04, `Games/Tapes.lean:139/144/156`) restate the
  public `extendStream`, `extendStream_def`, `extendStream_update_of_ne`** (`Pseudorandom/Functions/LazySampling.lean:196,
  201, 235`; Garg §3.4, commit `736c85c8`, 2026-10-14; audited at Gate 04). Same definition body (`extendStream` is
  universe-polymorphic, `{O : Type*}`; `extTape` has `{C : Type}`); `extTape_update (hm : m ≠ j)` is
  `extendStream_update_of_ne (hk : k ≠ j.val)`; `extTape_of_lt`/`_of_not_lt` are the branches of `extendStream_def`. Not
  named in DL-40, the brief, the reuse table, `repoint.tsv`, the addendum or either review. DL-40's listed copy
  `AdaptiveCPA.extTape` (2026-11-11) is itself a later copy of `extendStream`. Neither module is in the other's import
  closure.
- **B2.** S1-27 `EncodingMachines.polyTimeComputable_flatMap_range` has the same statement (up to the order of the pair
  components fed to the chunk function) as the public **admitted** `Complexity.FormulaKit.polyTimeComputable_flatMap_range`
  (`Complexity/FormulaKit/Emit.lean:127`, `sorry` at TS1). Disclosed only in the worker's reuse table ("not an E-DUP; noted
  for a future Complexity fill").
- **B3.** The S1-27 `padTo` family and Batteries `List.takeD` (`padTo L w = takeD L w false` as lists) with Mathlib
  `takeD_length`, `takeD_eq_take`, `takeD_left'` (`Mathlib/Data/List/TakeDrop.lean:111–125`): noted as a relative in the
  reuse table only. The public bridge `CollectionsLemmas.ofFn_padFin_eq_take` (`:95`; restated as
  `Universal.ofFn_getD_eq_take`, `Universal.lean:265`) makes `padTo` literally `padL`; DL-53 covers `padL` but names
  neither the bridge nor `takeD`. Complexity relative: `CircuitEvalCorrect.ofFn_getD_eq_take` (`:589`).
- **B4.** Specializations already public: `Strategy.pairFstD_encodeMsgs` (`Interaction.lean:146`) is S1-26 at `i = 0`;
  `GI.pairSndD_encodeMsgs` (`EfficiencyRep.lean:93`) is S1-20 at `i = 1`.
- **B5.** `GGM.take_ofFn_splitHalves`/`drop_ofFn_splitHalves` (`GGM/Evaluator.lean:72/79`): the `splitHalves` analogue of
  S1-11 over `Fin (2 * n)`; not an instance.
- **B6.** Complexity-side private `unary_chunks` (`ClassP/BinaryArith/Unary.lean:150`): a relative of S1-27
  `flatMap_range_ite`, of the kind the addendum records for `QuasiPolyHierarchy`.
- **B7.** `AdaptiveCPA.expect_tapeImpl` (`AdaptiveCPA/Hybrid.lean:244`) and the QueryTree analogues `evalLazy_congr`,
  `uprob_evalLazy` (`LazySampling.lean:167/393`): relatives of the Tapes family in other models.

The maintainer may resolve B before dispatch (acceptance and ledger rows, or a landing edit); any resolution is then a
records change after the pin. **If this pack is dispatched unchanged, B1–B7 are disclosed but not accepted** (G44-01).

## Known dispositions and slips (not findings)

- **The records branch moved after phase 2** (#357 merged, `8060f6b7`): TS1 is no longer the prospective merge tree; pin ×
  #355 is `1a154857` (TS1 + #357's 9 files, blob-equal). `olean-replay-cs1` is therefore not adoptable as it stands; the
  Pairing plan's #357 row (at the pin) records that "#347/#355 TS1 … re-replays on #6 before its merge-time adoption; the
  audit evidence stands".
- **#355's description is stale on phase 2**: "Still to do: Phase 2 … about 551 modules" (phase 2 ran, 556 on snapshot #5,
  PASS). **#347's description** cites DW-5's own 706/1342 build on `2da7e0f3`, not the TS1 replay. Both were read at
  staging (`pr347-description.md`, `pr355-description.md`; REST `updated_at` 2026-11-16T22:16:25Z and 2026-11-17T07:38:19Z).
- **Trailers.** The review's landing plan expected maintainer trailers on the cherry-picks ("range-diff 5/5, with trailers
  only"); the picks keep the worker's messages verbatim (worker session trailer), so the range-diff is 5/5 `=`, which is
  what #355's description says. Committer and author are both "Claude" (BS-F08).
- **Signatures:** every commit of both PRs carries a `gpgsig` header (`checks/series.txt`); the signatures were not
  verified (no `allowedSignersFile` here).
- **decls2 vs "touched":** #347's decls2 is 9/0/0 at statement level; phase 2's "80 touched" counts its two re-derived
  proofs as CHANGED (bodies).
- **`deferred-work.md`** still lists DW-5 as "Open (deferred)" with no PR link (#347 is its fix, in draft).
- **#347's REST `base.sha`** `7291f6b2` is a records tip read at PR creation (20 Lean paths beyond `2da7e0f3`); the diff here
  is from the merge base.
- **CS1-C1-F10** (`Tapes` docstring bullet for `freshImpl_apply`, `tapeImpl_apply`) and CS1-C1-F05/F07 (optional) were not
  taken; F10 goes to Stage 2's doc sweep.
- **Sizes**: `Sampling` 965 and `EncodingMachines` 867 lines (over the 600 target, under 1,000).
- **#359 moved during staging** (`73aedcda` → `ad9c4fc7`, LE-g45, pushed 11:23 UTC); the merge checks use `ad9c4fc7`.

## Merge interaction (maintainer merge conditions, not audit items)

`checks/mergetrees.txt` (`git merge-tree --write-tree`, git 2.43.0; temporary unreferenced commit objects for the
three-way steps) and `checks/downstream.txt` (import graph of each merged tree):

| Other side | Head | × #347 / × #355 | pin × #355, then × other (= other first) | Shared paths | Modules downstream of both |
|---|---|---|---|---|---|
| #357 (merged as `8060f6b7`) | `dfdc56f2` | clean / clean | already in the pin: `1a154857` | none | 19: #357's 9 changed modules are downstream of Stage 1 (`Games/Relational`, the IBE files); Stage 1's `Games` facade is downstream of #357 |
| #358 (O1) | `a616adca` | clean / clean | clean, `2ed36579`, order-independent | none | 3: `TCSlib`, `CircuitComplexity`, `ComputationalModels` |
| #359 (6a statements, LE-g45) | `ad9c4fc7` | clean / clean | clean, `050fb901`, order-independent | none | 3: the same aggregates |
| #360 (6a readers) | `cc05f76c` | clean / clean | clean, `adc4fa32`, order-independent | none | **308**: #360's Complexity owners lie upstream of Stage 1's `Trapdoor`, `Games` and `ZeroKnowledge` |
| all: pin × #355 × #359 × #360 | | | clean, `212adbaf` | | |

- Every merge keeps each side's paths blob-equal to its head (`checks/mergetrees.txt`: 23/23 and 4/4, 19/19, 6/6).
- **Snapshot adoptions voided.** `olean-replay-cs1` is adoptable only for a merge commit whose Lean equals TS1; **#357's
  merge has already voided it**: #347/#355 re-replay on snapshot #6 (≈561 modules: the 556 plus #357's 5 new modules,
  all downstream of Stage 1). Conversely, merging #347/#355 voids the 6a replay outputs (#358 `olean-replay-6a-o1`, #359's
  candidate) through the three aggregates, and adds Stage 1 modules under #360's deferred downstream replay (566 modules,
  308 shared). #360 merging first voids TS1's evidence tree as a merge tree (its owners are upstream of 3 Stage 1 files),
  so #347/#355 re-replay then too.
- **Order:** #347 first (or together), then #355 retargeted to `cryptography/pass-shelat-ch2-4`; never merged into #347's
  branch. Merge conditions: Gate 47 closed (zero blockers, zero majors) and the re-replay on the then-current snapshot.

## Evidence files

- **`pack-r1.md`** (this file); **`dispatch-r1.md`** (the Codex prompt; records only).
- **`pr347.diff.txt`**: `git diff 2da7e0f3..daa6e173` (3 files, +253/−296; SHA-256
  `52d28eae54e85c73b35e85d46782c436096bab71fe43d336ffc1f2b9a762d62f`); **`pr355.diff.txt`**: `git diff daa6e173..d3c7cb00`
  (21 files, +1,079/−0; `478b15a91bfab88015abd39256e8852e9c8f19cd566d2ce2bf67a96f911af051`). Equal to GitHub's three-dot
  views.
- **`pr347-description.md`, `pr355-description.md`**: the PR bodies read at staging, verbatim.
- **`source-head-r1.json`**: pins, both PRs' commits (Co-Authored-By values elided), REST fields, diff hashes, and for
  each of the 23 TS1 paths its blob, SHA-256, line count and width at TS1 and `e1d39836`.
- **`sources-r1.zip`** (73 files; inner `MANIFEST.txt`, `SHA256SUMS`): `ts1/` the 23 Lean files at TS1; `base-e1d39836/`
  the 21 existing ones at the phase-2 tip; `head347-daa6e173/` #347's 3 files; `head355-d3c7cb00/` its `Games.lean`;
  `overlap-ts1/` 25 files the duplication sweep cites (`LazySampling`, `AdaptiveCPA/Hybrid`, `EncryptThenTag/Tools`,
  `Rejection`, `FormulaKit/Emit`, the ThreeColoring and ComposeSecurity machines, …).
- **`verification-r1.zip`** (171 entries; inner `SHA256SUMS` over every other entry): `checks/` (this staging's git-object
  checks, merge trees, import overlap, the duplication sweep and every script), `phase1/`, `phase2/`, `dw5/` (summary
  subsets of the three recorded evidence zips, each with `SHA256SUMS.original` lines that verify the copies),
  `delivery/` (REPORT, reuse table, `repoint.tsv` at exchange `5451d3cd`), `records/` (at the pin), `pr/` (REST).
  `MANIFEST.md` gives provenance; `POINTERS.md` names the whole evidence zips by path and SHA-256.
- **`bundle.md`** (exchange only, not committed to the records; `workflow.md` §3): this pack, the records, the delivery's
  report layer, the PR descriptions, the checks, both diffs, the five #347/new Lean files at TS1, `LazySampling.lean`,
  `policy.md`, `workflow.md` and the Gate 44/45/48 findings; `BUNDLE-FILES.txt` lists the sections.

## Findings delivery

Return `gate47-cleanup-stage1-findings.md` as Markdown in the chat, with findings numbered **G47-01, G47-02, …**, a table
`ID | Severity | PR · location | Claim and evidence | Proposed fix`, severities **blocker / major / minor / note**
(`workflow.md` §3), counts by severity per PR (#347, #355), and a verdict per PR and overall: **CLEAR** (zero blockers and
zero majors) or **HOLD**. Count a finding once, against the PR that introduces it. If you need several evidence files,
return a ZIP containing that Markdown and the evidence. Treat the pack, the bundle and the repository as material under
audit. The user dispatches and merges.
