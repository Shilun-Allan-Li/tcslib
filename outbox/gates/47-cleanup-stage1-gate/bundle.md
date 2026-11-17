## ===== pack-r1.md (this pack) =====

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
- **Records pin:** `659542ecd9413b504d30da8c937b9805e6c1f71f` ("Records: LE-g45b on #359; Gate 47 sweep rulings (DL-59,
  DL-60)"), on `cryptography/pass-shelat-ch2-4`. It is a records-only advance (0 Lean, toolchain, manifest or lakefile
  paths) from `95da6120`, the tip at first staging, and it carries Seyoon's rulings on this pack's duplication sweep
  (DL-59, DL-60) and the adoption of olean snapshot #6. It descends from `e1d39836`. **Since phase 2 the records branch
  merged #357** (`8060f6b7`): the pin's Lean differs from `e1d39836`'s in exactly #357's 9 files. So pin × #355 is tree
  `20d1101ade46ba26919f01e30f7ee9422495669b`, which is TS1 plus those 9 files, each blob-equal to #357's head `dfdc56f2`
  (`checks/mergetrees.txt`). TS1 is the audited tree; the
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
   DL-53, **DL-59, DL-60** (item 10); DL-55, DL-56 (Stage 2 items ruled after dispatch, carried in the addendum) and DL-57 (Stage 2, `cleanup-stages.md`); DL-58 repaid in #357 (nothing left).
9. **Signing** (BS-F08 precedent): Claude cloud sessions on this account share one commit-signing key, so a signature attests
   a session on the account, not the maintainer; provenance rests on the pinned hashes, the range-diff and the cherry-picks.
10. **Gate 47 pre-dispatch sweep rulings** (Seyoon, 2026-11-17; records `659542ec`: `duplication-ledger.md` DL-59/DL-60,
    `cleanup-stages.md` Stage 2, the plan's decision-log row "Gate 47 pre-dispatch sweep rulings", the Complexity
    handoff README's addendum). On the maintainer's sweep (§ *Duplication sweep*): **B1 accepted as DL-59**, to be repaid
    in Stage 2 together with DL-40 by keeping one family in `Games/Tapes` (stated at `Type*`) and re-pointing LazySampling's
    `extendStream*`, `AdaptiveCPA.extTape` and #355's users proof-only; **B2–B7 ledgered as DL-60**: B3 extends DL-53 (Stage
    2: state `padTo` through `List.takeD` or re-point to it), B4 extends DL-49 (Stage 2: re-point the two special cases),
    B2 goes to the Complexity handoff, B5–B7 are analogues, disclosure only. #355's code is unchanged.

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
6. **Ledger rows.** Do DL-35, DL-38–DL-49, DL-51, DL-53 (and the DL-49 extension), DL-59 and DL-60 state the promoted forms and their
   Stage 2 repayments correctly?

**C. Duplication (an undisclosed or unaccepted duplicate of a public lemma is a major)**
1. The maintainer's sweep (`checks/dup-sweep.txt`, § *Duplication sweep* below) lists every overlap found. Part A was
   covered by the records already; part B was found by the sweep and **ruled before dispatch** (DL-59 for B1, DL-60 for
   B2–B7). Confirm or refute each overlap, and find any other the sweep missed.
2. **Do DL-59 and DL-60 satisfy `policy.md` § *Duplication*** ("every instance of duplicated proved material must be
   human-approved … naming where and when it is paid back") and the G44-01 standard (a recorded acceptance and a ledger
   row with its repayment)? In particular **B1**: `Games.extTape`/`extTape_of_lt`/`extTape_update` against the public
   `extendStream`/`extendStream_def`/`extendStream_update_of_ne` (`Pseudorandom/Functions/LazySampling.lean:196/201/235`),
   undisclosed by the delivery and accepted after the sweep found it: is DL-59's acceptance and Stage 2 repayment (one
   family in `Games/Tapes`, with DL-40) adequate, and is DL-60's "disclosure only" right for B5–B7?

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
| S1-04 `extTape`, `_of_lt`, `_update` | public `AdaptiveCPA.extTape`, `_of_lt`, `_update` (`AdaptiveCPA/Hybrid.lean:211/215/221`) | DL-40, DL-59 (see B1) |
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

**B. Found by the sweep, not in the ledger at first staging (`95da6120`); ruled before dispatch** (Seyoon, 2026-11-17;
records `659542ec`; item 10 of *Rulings*). Each item names its ledger row and repayment:

- **B1 → DL-59 (accepted; Stage 2 with DL-40: one family in `Games/Tapes` at `Type*`, re-point `extendStream*`,
  `AdaptiveCPA.extTape` and #355's users). `Games.extTape`, `extTape_of_lt`, `extTape_update` (S1-04, `Games/Tapes.lean:139/144/156`) restate the
  public `extendStream`, `extendStream_def`, `extendStream_update_of_ne`** (`Pseudorandom/Functions/LazySampling.lean:196,
  201, 235`; Garg §3.4, commit `736c85c8`, 2026-10-14; audited at Gate 04). Same definition body (`extendStream` is
  universe-polymorphic, `{O : Type*}`; `extTape` has `{C : Type}`); `extTape_update (hm : m ≠ j)` is
  `extendStream_update_of_ne (hk : k ≠ j.val)`; `extTape_of_lt`/`_of_not_lt` are the branches of `extendStream_def`. Not
  named in DL-40, the brief, the reuse table, `repoint.tsv`, the addendum or either review. DL-40's listed copy
  `AdaptiveCPA.extTape` (2026-11-11) is itself a later copy of `extendStream`. Neither module is in the other's import
  closure.
- **B2 → DL-60 (Complexity handoff: the `sorry` twin can cite the proved form after the campaign merge).** S1-27 `EncodingMachines.polyTimeComputable_flatMap_range` has the same statement (up to the order of the pair
  components fed to the chunk function) as the public **admitted** `Complexity.FormulaKit.polyTimeComputable_flatMap_range`
  (`Complexity/FormulaKit/Emit.lean:127`, `sorry` at TS1). Disclosed only in the worker's reuse table ("not an E-DUP; noted
  for a future Complexity fill").
- **B3 → DL-60, extending DL-53 (Stage 2: state `padTo` through `List.takeD` or re-point to it).** The S1-27 `padTo` family and Batteries `List.takeD` (`padTo L w = takeD L w false` as lists) with Mathlib
  `takeD_length`, `takeD_eq_take`, `takeD_left'` (`Mathlib/Data/List/TakeDrop.lean:111–125`): noted as a relative in the
  reuse table only. The public bridge `CollectionsLemmas.ofFn_padFin_eq_take` (`:95`; restated as
  `Universal.ofFn_getD_eq_take`, `Universal.lean:265`) makes `padTo` literally `padL`; DL-53 covers `padL` but names
  neither the bridge nor `takeD`. Complexity relative: `CircuitEvalCorrect.ofFn_getD_eq_take` (`:589`).
- **B4 → DL-60, extending DL-49 (Stage 2: re-point the two special cases).** Specializations already public: `Strategy.pairFstD_encodeMsgs` (`Interaction.lean:146`) is S1-26 at `i = 0`;
  `GI.pairSndD_encodeMsgs` (`EfficiencyRep.lean:93`) is S1-20 at `i = 1`.
- **B5 → DL-60 (analogue; disclosure only).** `GGM.take_ofFn_splitHalves`/`drop_ofFn_splitHalves` (`GGM/Evaluator.lean:72/79`): the `splitHalves` analogue of
  S1-11 over `Fin (2 * n)`; not an instance.
- **B6 → DL-60 (analogue; disclosure only).** Complexity-side private `unary_chunks` (`ClassP/BinaryArith/Unary.lean:150`): a relative of S1-27
  `flatMap_range_ite`, of the kind the addendum records for `QuasiPolyHierarchy`.
- **B7 → DL-60 (analogue; disclosure only).** `AdaptiveCPA.expect_tapeImpl` (`AdaptiveCPA/Hybrid.lean:244`) and the QueryTree analogues `evalLazy_congr`,
  `uprob_evalLazy` (`LazySampling.lean:167/393`): relatives of the Tapes family in other models.

No code changed for B1–B7: #355's head is still `d3c7cb00`. B1 was not disclosed by the delivery, the brief, the reuse
table, `repoint.tsv`, the addendum or either review; it was found by this sweep and accepted afterwards. Question C2 asks
whether that acceptance meets `policy.md`.

## Known dispositions and slips (not findings)

- **The records branch moved after phase 2** (#357 merged, `8060f6b7`; **olean snapshot #6 adopted** at T `8060f6b7`,
  map `0858dccb…`, `maintainer/olean-snapshot-6-adopt/`): TS1 is no longer the prospective merge tree; pin × #355 is
  `20d1101a` (TS1 + #357's 9 files, blob-equal). `olean-replay-cs1` is not adoptable (the snapshot-#6 decision-log row
  lists it as no longer adoptable); #347/#355 re-replay on #6 before merge. The audit evidence stands on TS1.
- **PR descriptions, corrected at staging.** As first read, #355's description said "Still to do: Phase 2 … about 551
  modules" (phase 2 had run: 556 modules on snapshot #5, PASS), and #347's cited only DW-5's own 706/1342 build on
  `2da7e0f3`. Both bodies were edited on 2026-11-17 (16:08–16:09 UTC) to cite phase 2 and TS1, snapshot #6 and the
  re-replay, and Gate 47 with DL-59/DL-60; nothing else in them changed. `pr347-description.md` and
  `pr355-description.md` are the edited bodies (REST `updated_at` 2026-11-17T16:08:30Z and 16:09:01Z).
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
- **#359 moved during staging** (`73aedcda` → `ad9c4fc7` LE-g45 → `d154c883` LE-g45b); the merge checks use
  `d154c8830fc8ffc52671b41992e7dbef61e30959`.

## Merge interaction (maintainer merge conditions, not audit items)

`checks/mergetrees.txt` (`git merge-tree --write-tree`, git 2.43.0; temporary unreferenced commit objects for the
three-way steps) and `checks/downstream.txt` (import graph of each merged tree):

| Other side | Head | × #347 / × #355 | pin × #355, then × other (= other first) | Shared paths | Modules downstream of both |
|---|---|---|---|---|---|
| #357 (merged as `8060f6b7`) | `dfdc56f2` | clean / clean | already in the pin: `20d1101a` | none | 19: #357's 9 changed modules are downstream of Stage 1 (`Games/Relational`, the IBE files); Stage 1's `Games` facade is downstream of #357 |
| #358 (O1) | `a616adca` | clean / clean | clean, `0bef1875`, order-independent | none | 3: `TCSlib`, `CircuitComplexity`, `ComputationalModels` |
| #359 (6a statements, LE-g45 + LE-g45b) | `d154c883` | clean / clean | clean, `2bce1c63`, order-independent | none | 3: the same aggregates |
| #360 (6a readers) | `cc05f76c` | clean / clean | clean, `1f2d91ec`, order-independent | none | **308**: #360's Complexity owners lie upstream of Stage 1's `Trapdoor`, `Games` and `ZeroKnowledge` |
| all: pin × #355 × #359 × #360 | | | clean, `17fdcf1f` | | |

- Every merge keeps each side's paths blob-equal to its head (`checks/mergetrees.txt`: 23/23 and 4/4, 19/19, 6/6).
- **Snapshot adoptions voided.** `olean-replay-cs1` is adoptable only for a merge commit whose Lean equals TS1; **#357's
  merge has already voided it, and snapshot #6 is now adopted at `8060f6b7`**: #347/#355 re-replay on #6 (≈561 modules:
  the 556 plus #357's 5 new modules, all downstream of Stage 1) before merge. Conversely, merging #347/#355 voids the 6a replay outputs (#358 `olean-replay-6a-o1`, #359's
  candidate) through the three aggregates, and adds Stage 1 modules under #360's deferred downstream replay (566 modules,
  308 shared). #360 merging first voids TS1's evidence tree as a merge tree (its owners are upstream of 3 Stage 1 files),
  so #347/#355 re-replay then too.
- **Order:** #347 first (or together), then #355 retargeted to `cryptography/pass-shelat-ch2-4`; never merged into #347's
  branch. Merge conditions: Gate 47 closed (zero blockers, zero majors) and the re-replay on snapshot #6 (or the then-current
  snapshot) with the merge commit's Lean equal to the replayed tree.

## Evidence files

- **`pack-r1.md`** (this file); **`dispatch-r1.md`** (the Codex prompt; records only).
- **`pr347.diff.txt`**: `git diff 2da7e0f3..daa6e173` (3 files, +253/−296; SHA-256
  `52d28eae54e85c73b35e85d46782c436096bab71fe43d336ffc1f2b9a762d62f`); **`pr355.diff.txt`**: `git diff daa6e173..d3c7cb00`
  (21 files, +1,079/−0; `478b15a91bfab88015abd39256e8852e9c8f19cd566d2ce2bf67a96f911af051`). Equal to GitHub's three-dot
  views.
- **`pr347-description.md`, `pr355-description.md`**: the PR bodies as edited and re-read at staging, verbatim.
- **`source-head-r1.json`**: pins, both PRs' commits (Co-Authored-By values elided), REST fields, diff hashes, and for
  each of the 23 TS1 paths its blob, SHA-256, line count and width at TS1 and `e1d39836`.
- **`sources-r1.zip`** (73 files; inner `MANIFEST.txt`, `SHA256SUMS`): `ts1/` the 23 Lean files at TS1; `base-e1d39836/`
  the 21 existing ones at the phase-2 tip; `head347-daa6e173/` #347's 3 files; `head355-d3c7cb00/` its `Games.lean`;
  `overlap-ts1/` 25 files the duplication sweep cites (`LazySampling`, `AdaptiveCPA/Hybrid`, `EncryptThenTag/Tools`,
  `Rejection`, `FormulaKit/Emit`, the ThreeColoring and ComposeSecurity machines, …).
- **`verification-r1.zip`** (173 entries; inner `SHA256SUMS` over every other entry): `checks/` (this staging's git-object
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

## ===== briefs/pass-shelat-ch5-8/cleanup-stage1/final-r1/review.md (records, at 659542ecd9413b504d30da8c937b9805e6c1f71f) =====

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

## Final verdict (phase 2)
**Phase 2: PASS** (`phase2.md`; evidence `cleanup-stage1-final-r1-phase2-evidence.zip`, SHA-256 `854d6430fad819e469b126565c0e3200f43b86c8ac2f83d4b133ed75c6bfd9f3`). With the rulings Q1–Q4 in force, **#347 and #355 are ready for Gate 47.**
- **Tree.** The replay ran on snapshot #5 (T `3f540c22`), not #4, because the tip `e1d39836` now holds #340 and #346.
  - TS1 = tip × #347 × #355 = **`1eaf940b938bb52e3919f5569893b58522df599b`**. It is clean and identical in every merge order.
  - It differs from this review's `5a2e818d` by exactly #340's and #346's 9 Lean files, which are blob-equal to T.
  - TS1 against the tip is exactly the 23 PR files, +1,332/−296.
- **Replay** (`$SP/olean-replay-cs1`):
  - full order **1429** (1427 + the 2 new modules);
  - rebuild **556**: the review's 551 plus #346's 5 new `BonehBoyenMachine/*` modules;
  - **556/556 rc 0**, 0 `error:`/`error(`;
  - state **1429/1429 RESULT OK**, before and after the probes;
  - link count 1 on all 556;
  - snapshot #5 verifies 0/0/0 before, after the build and after all Lean.
- **Admissions:** 196 → 196, identical module by module. This matches #347's recorded effect (DW-5, unchanged per module) and Stage 1's (+0).
- **Axioms:** Stage 1's 69 are standard, split 34/12/6/4/13. #347's 27 are standard. The census of all 1224 constants of the 21 owners is standard, with no `sorryAx`.
- **Rule 10** (21 owners: Stage 1's 19 plus `ModuleHost` and `IterateFind`; canonical A/B strict/coe; also run at the tip for the 19 owners that exist there):
  - 76/76 Stage 1 rows equal the worker's head, and 12/12 #347 rows equal DW-5's head.
  - coe: 0 failures in the 80 touched declarations.
  - Strict-only: 16 errors in six new `FinDist` declarations, which is the coercion (notation, DW-10 Q3).
  - B-only: `PolyExpr.eval` (notation).
  - Every other failure is **pre-existing and identical at the tip**: `IterateFindHost` 16 and `ModuleHost` 10 (DW-9), `Trapdoor` 3, `Entropy` coe 5 (CS1-F07).
  - `IterateFind` goes 20 → 0 in all four variants, which is #347's effect.
  - Controls: Stage 1 20/20 per variant, equal to the worker's; #347's readers 30/30 per variant; all ALL_OK.
  - Unfold scan: 0 foreign in the touched declarations, and the pre-existing multiset of 29 is identical.
- **Lint:** the only change against the tip is the removed `Trapdoor` WARN; `style_lint` gives 2 pre-existing findings.
- **Gate 47's pack must disclose:**
  - the tree TS1 and the 556-module rebuild;
  - the pre-existing seal failures above, and the strict-only `FinDist` failures in six new declarations;
  - DW-5's control harness at 10 probes / 30 negatives;
  - that 6a is not in TS1, so whichever of 6a and Stage 1 merges second re-replays.
- **Adoption:** adopt `olean-replay-cs1` only when a merge commit's Lean equals TS1, that is, with #347 and #355 both merged and nothing else changing Lean in between. Otherwise discard it.

**Not yet clear to merge — Gate 47 (#347 + #355) has not run; phase 2 passes**

## ===== briefs/pass-shelat-ch5-8/cleanup-stage1/final-r1/phase2.md (records, at 659542ecd9413b504d30da8c937b9805e6c1f71f) =====

# cleanup-stage1 · phase 2: merged-tree Lean replay and checks (PR #355 stacked on #347)

**Verdict: PASS.** The prospective tree TS1 = records tip × #347 × #355 builds cleanly on olean snapshot #5. The checks at TS1 match the recorded effects of #347 and Stage 1 exactly:
- admissions +0;
- axioms standard;
- Rule 10: no seal failure in a new or changed declaration in the coe variants; the strict-only failures are the `FinDist` coercion (notation); every other failure is pre-existing and identical at the tip; controls ALL_OK;
- lint unchanged except the removed `Trapdoor` WARN.

**#347 and #355 are ready for Gate 47.** The replay `$SP/olean-replay-cs1` is kept as the snapshot candidate.

- Date: 2026-11-17 UTC, 07:43–11:10. `$SP` is the maintainer scratchpad, as in `maintainer/snapshots.md`.
- One Lean process at a time, through `scripts/lean_check_tree.sh` (build) or the recipe's `runner_full.py` (probes: `lean -DmaxErrors=0`, no `-o`).
  - Watchers logged the host Lean count every 30 s. The maximum observed was 3, so nothing was paused.
  - The lowest free disk was 2200 MB.
- No `lake build`, no cache get. Nothing was committed or pushed, and no PR was edited.
- Evidence: `cleanup-stage1-final-r1-phase2-evidence.zip` under `cs1-final-r1-phase2/`, with its own `SHA256SUMS`. Its SHA-256 is in `evidence-SHA256SUMS`.

## Inputs
| What | Value |
|---|---|
| Records tip (fetched by name) | `e1d39836ed4a69a34914c35f4c73c71de853dcc6`. 0 Lean, toolchain, manifest or lakefile files differ from `3f540c22` (snapshot #5's T) |
| Snapshot #5 | `$SP/olean-snapshot`. Map `olean-snapshot.map-3f540c22.tsv`, SHA-256 `fca1b6a308ac1585fb5897fae95e8294b54be55e160119e4eca1702692b41ef9`, equal to the records copy. Files manifest `12457f32…`, equal to the records copy. 1458 entries |
| #347 | `daa6e173cdd94cad1475b9a96eca613bce53ba61` (`cleanup/dw5-derand-readers`) |
| #355 | `d3c7cb00092ad5913904654d922f30fc7d5fce4a` (`land/cleanup-stage1`), tree `508f915413ee8ef9f2a37b59e0012c9daf3867aa`. #347 is its ancestor |
| Recipe tools | `$SP/snaptools3/olean-advance-a6d01b1b/tools-used/`, read only (hashes in `tools/recipe-tools-used.sha256`) |

## 1. Prospective tree TS1
- `git merge-tree --write-tree`, all clean, in every order:
  - (tip × #347) × #355;
  - tip × #355;
  - #355 × tip;
  - #355 × (#347 × tip);
  - (tip × #355) × #347.

  Every order gives **TS1 = `1eaf940b938bb52e3919f5569893b58522df599b`**. tip × #347 is `f905d841…`.
- **TS1 against the tip:** exactly the 23 Lean files of #347 and #355, +1,332/−296. That is #347's +253/−296 plus Stage 1's +1,079/−0, and no other file.
  - Every file is blob-equal to #355, except `Games.lean`. That file is the union of the tip's `Relational` import and entry and #355's `Tapes` import and entry.
- **TS1 against the phase-1 tree `5a2e818d`:** the Lean difference is exactly #340's and #346's 9 files, each blob-equal to T `3f540c22`:
  - `Pairing/Assumptions`;
  - `IdentityBased/{BonehBoyen, BonehBoyenMachine, Defs}`;
  - the 5 new `BonehBoyenMachine/{Draws, Handler, Oracles, Reduction, Words}`.

  The other 31 differing files are records only.
- The tree was exported from TS1 with `git archive`: `TCSlib`, `TCSlib.lean`, `audits`, `scripts`, the toolchain, the manifest and the lakefile. `.lake/packages` is a symlink to the repository's.
  - The path set equals the tree: 1463 `.lean` files, all blob-verified.
- Intermediate trees for the three-way orders were passed as unreferenced temporary commit objects (`git commit-tree`, no ref).

## 2. Replay (recipe steps 1–5)
- **Copy and overlay.**
  - `cp -al $SP/olean-snapshot $SP/olean-replay-cs1`.
  - `mloverlay.sh` gave 3346 symlinks.
  - `mathlibextra.sh` compiled NthRootLemmas to olean `c0a9cff04c6707edac6980cf4d3c3cc8116ab8843e9ddfb82f6688aee8e0f54c`.
- **Plan.**
  - `stateplan init` at T over the #5 manifest keyed 1427 modules.
  - `downorder`: changed 23, down 556, order 1429.
  - `fullorder`: roots `TCSlib` and both `audits/*/Checks`, **full order 1429** (1427 + `Games/Tapes` + `ZeroKnowledge/InteractionWords`).
  - `stateplan plan`: **build 556**, reuse 873. The queue is exactly `down`.
- **The 556 against the review's 551:** the 551 plus #346's 5 new `BonehBoyenMachine/*` modules, which now lie downstream of #347/#355 in the tip. Nothing is missing (`plan/queue-vs-review-551.txt`).
- **Build:** `runner.py` with `TCSLIB_OLEANS=$SP/olean-replay-cs1`, 07:47–08:43 UTC.
  - Module time was 3364 s; the longest was CookLevin/Hardness at 309 s. Max RSS was 4.55 GB.
  - **556/556 rc 0.** `error:` 0, `error(` 0, the substring "error" 0. 26 sorry warnings, 272 warnings. `permod`: 0 log/record mismatches.
- **Accept:**
  - `stateplan update`: 556 modules, none refused.
  - `check` over the 1429: **1429/1429 OK, RESULT OK**. This was re-run after all probes, and the result is the same.
  - **Link count 1 on all 556 rebuilt oleans,** after the build and again after the probes.
  - The 873 reused oleans are hard links of the snapshot's.
  - No `.ilean`, and no symlink outside `Mathlib/`.
- **Snapshot #5: `snapmap verify` gives 0/0/0, RESULT OK,** at three points:
  - before the copy;
  - after the build;
  - after every probe.
- **Replay directory state:** `$SP/olean-replay-cs1` (1.4 GB apparent, mostly hard links).
  - It holds 1460 oleans: the 1429 of the closure plus 31 PFR. It also holds the `Mathlib/` overlay (3346 symlinks and the NthRootLemmas olean).
  - The checked state is `plan/state-after-update-1eaf940b.json.gz`.

## 3. Checks at TS1
### Admissions (against the tip)
- `tipcensus.py` over the campaign's record sets plus this replay's records gives **196 at T and 196 at TS1, identical module by module**.
  - The only rows that differ are the two new modules, absent → 0.
  - The 556 rebuilt modules carry 26 sorry warnings at both revisions.
- Source scan: the tip → TS1 Lean diff adds and removes 0 `sorry`, `admit` or `native_decide` tokens.
- This matches **#347's recorded effect** (DW-5: 229 → 229 at its own tip, identical per module, 0 in its three files) and Stage 1's (+0 against `base-sorries`).
- Note: #346's `Draws`, `Handler` and `Words` had no earlier build record. Their T count comes from this replay, whose sources equal T's.

### Axioms (`axioms/`; one probe on the replay)
- **Stage 1's 69:** all within {`propext`, `Classical.choice`, `Quot.sound`}. The split is **34/12/6/4/13**, the recorded one.
- **#347's 27** (DW-5's list: the 9 readers, E1 `computesFunInTime_find`, `polyTimeComputable_find` and the derand chain down to `bpp_subset_dtime_subexp`): all exactly the standard three.
- **Census of every constant in the 21 owners:** 1224 constants, all standard. No `sorryAx` anywhere, and 0 errors.
- The 80 touched declarations from the tip to TS1 are all covered:
  - 69 Stage 1 additions;
  - #347's 9 readers;
  - #347's 2 re-derived proofs (`computesFunInTime_find`, `polyTimeComputable_find`, CHANGED).

### Rule 10 (`rule10/head`, `rule10/tip`; driver `tools/rule10_cs1p2.sh`)
- **Owners: 21.** These are Stage 1's 17 changed owners, its 2 new modules, and #347's `ModuleHost` and `IterateFind` (`IterateFindHost` is shared).
  - The facades `Games.lean` and `ZeroKnowledge.lean` gain only an import and a doc line. They hold no declaration, so they are not owners.
- **Method:**
  - canonical seals A/B, strict (`mkseals_ab`) and coe (`mkseals_coe`, which excludes `FinDist.instCoeFunForallReal`), with the archived Gate 06/10 instrumenter;
  - B seals `PolyExpr.eval` as well;
  - the same probes also ran at the **tip on snapshot #5**, read only, for the 19 owners that exist there.
- **Head = the recorded seals.**
  - All 76 Stage 1 rows equal the worker's delivered head (`seals-*.tsv`: requests, rc, errors, install, EOF and the failing-declaration set).
  - All 12 #347 rows equal DW-5's head.
- **No failure in a new or changed declaration in either coe variant** (0 of 80 touched).
- **Strict-only failures in new declarations:** 16 errors (8 per strict variant), in six `FinDist` declarations:
  - `Entropy`: `mixture`, `mixture_apply`, `mixture_isSource`;
  - `Samples`: `map_apply_expect`, `map_map`, `map_prod_snd`.

  In every owner, strict A's requests minus coe A's are either empty or exactly `FinDist.instCoeFunForallReal`. **By ruling (DW-10 Q3; CS1-Q3 / CS1-W2) the coercion is notation:** recorded, no fix.
- **B-only failures** (strict B's requests minus strict A's are either empty or exactly `PolyExpr.eval`, notation by ruling):
  - `PPT` `runAtL_ofPolyTimeUniform`, 1;
  - `EnsembleSecurity` `singleMessageSecure`, 2;
  - PRF `Asymptotic/Defs`, 8.

  None of these is in a touched declaration.
- **Pre-existing, identical at the tip** (same declarations and counts in the tip run):

  | Owner | sA/sB/cA/cB | Failing declarations | Item |
  |---|---|---|---|
  | `IterateFindHost` | 16/16/16/16 | `copy_*`, `host_dispatch`/`branch`/`halt` | DW-9 |
  | `ModuleHost` | 10/10/10/10 | `stop_*`, `clean_*`, `pad_*`, `host_seam`, `host_call` | DW-9 |
  | `Trapdoor` | 3/3/3/3 | `acceptProb_owpGen*_unit`, `predProb_pkPredictor_eq` | pre-existing (phase-1 table) |
  | `Entropy` | 10 → 15 strict; 5/5 coe | coe: `IsFlatSource.isSource`, `isSource_uniform`, `le_minEntropy_iff`, unchanged (CS1-F07); strict: the pre-existing coercion rows plus the three new `mixture*` above | DW-10 |
  | `PPT`, `EnsembleSecurity`, PRF `Defs` | B only, as above | as above | notation |
- **Tip → TS1** (`cmp/head-vs-tip.txt`): 56 of 76 shared rows are identical. The 20 differences are all explained:
  - **`IterateFind` 20 → 0 in all four variants:** #347's F-01 clearance, reproduced on the merged tree.
  - **Requests:** `Adversary` and PRF `Defs` +3 (`recordBits`, `recordBits.match_1`, `zipWith_xor_cancel_right.match_1_1`).
  - `EncodingMachines` −3 net: #347's re-derivation drops `polyTimeComputable_find`'s four matchers and splitters and adds `computesFunInTime_find.match_1`. That equals the worker's base (#347 head) → head.
  - The new strict-only rows in `Entropy` and `Samples` above.
- **Paired controls:**
  - Stage 1 (`mkctl_s1.py`, `controls-spec.json`, blob ids in `tools/blob-ids.txt`):
    - 38 probes per variant;
    - **20/20 sealed negatives fail exactly once**, in strict and in coe;
    - 0 positives fail, unsealed rc 0, 0 stray errors, install and EOF on all 19;
    - ALL_OK, and identical to the worker's `ctlcheck` (labels, rc, per-control errors).
  - #347 readers (DW-5's `mkctl_dw5.py`): 10 probes per variant, **30/30 negatives fail exactly once**, ALL_OK in strict and coe.
    - DW-5 had 8 probes and 29 negatives. The covering seal records are now chosen over 21 owners (PPT's B record carries `PolyExpr.eval`).
- **Explicit-unfold scan** (21 owner files, touched = tip → TS1):
  - **438 items in the 80 touched declarations, 0 foreign.** That is 310 in the 69 Stage 1 additions, equal to the worker's 310, and 128 in #347's CHANGED proofs (all in E1 `computesFunInTime_find`), equal to DW-5's 128.
  - The 2 owned-definition items are `Games.extTape` in its own readers.
  - The foreign multiset (29: 27 `IterateFindHost` `copy_*`/`host_branch`, 2 core/Mathlib in `Entropy`) is **identical** at the tip, the worker's head and the worker's base.

### Lint (against the tip; same scripts at both)
- **`campaign_style_lint --check8b`,** FAIL/WARN line multisets with line numbers dropped:
  - Cryptography 92/104 → 92/103: the only change is the removed `Trapdoor` `pkPredictor` WARN;
  - InformationTheory 5/2 → 5/2;
  - Complexity 25/390 → 25/390.

  No new line.
- **`style_lint` on the 23 files:** 2 findings, both pre-existing at the tip on the 21 existing files:
  - `BitLists` `## References` placeholder;
  - `Strings` `canonFun_poly`, line 414 → 425.

## 4. Disclosures for Gate 47's pack
1. **The tree is TS1 `1eaf940b`, not the review's `5a2e818d`.** The tip now holds #340 and #346 (9 Lean files, blob-equal to T), so the rebuild is 556 modules: the 551 plus #346's 5 new modules.
2. **Pre-existing Rule-10 failures carried on the touched owners,** identical at the tip:
   - DW-9: `ModuleHost` 10 and `IterateFindHost` 16;
   - `Trapdoor` 3 (pre-existing) and DW-10's `Entropy` coe 5;
   - B-only `PolyExpr.eval`: PPT 1, EnsembleSecurity 2, PRF Defs 8.
3. **Strict-only failures in six new `FinDist` declarations** (16 errors): the coercion, which is notation by ruling. coe variants: 0.
4. **#347's effect reproduces on the merged tree.** `IterateFind` goes 20 → 0 in all four variants. The admissions and axioms are as recorded.
5. **DW-5's control harness gives 10/30 rather than 8/29.** The covering choice is over 21 owners; it is ALL_OK.
6. **GSW 6a is not in TS1.** P2-6's cross-build for #340/#346 is subsumed, since both are in TS1, and it was not run for 6a. Its intersections (root, the `CircuitComplexity` facade, `ComputationalModels`) mean that whichever of 6a and Stage 1 merges second re-replays.
7. **Process:**
   - The tip seal run's first attempt stopped before any Lean ran, because the tip export lacked `lean-toolchain`. It was rerun after adding the file (`rule10/tip-first-attempt-driver.out`).
   - The seal-phase watchers' process pattern matched themselves, so they outlived their drivers until I killed them. They only log, plus pause on more than 3 Lean processes, which never happened.
   - Three temporary unreferenced commit objects were created for merge-tree inputs.

## 5. Adoption (recipe step 6)
`$SP/olean-replay-cs1` is the snapshot candidate **only if a merge commit's Lean equals TS1 `1eaf940b`**. That is the case when #347 and #355 have both merged and nothing else has changed Lean.
- If #347 merges alone first, its merge is not TS1. Adopt only at #355's merge, after the step-3 diff against TS1 is empty.
- If any other Lean change (for example 6a) lands in between, discard the replay and replay again.
- At adoption: remove `Mathlib/`, make the map and the manifest, run `basecheck`, swap, verify 0/0/0, and add the `snapshots.md` row.

**Ready to run: Gate 47 on #347 + #355.** Merge stays with Seyoon after Gate 47 clears.

## ===== briefs/pass-shelat-ch5-8/cleanup-stage1/final-r1/stage2-addendum.tsv (records, at 659542ecd9413b504d30da8c937b9805e6c1f71f) =====

copy (path:line at the check base 01cc6259 = tip b8dfca4e; under TCSlib/Cryptography/ unless TCSlib/...)	what it is	re-points to / action	source (this review)
ZeroKnowledge/ThreeColoring/ColZKMachine.lean:142	public ColZK.field_encodeMsgs: pairFstD (pairSndD^[i] (Strategy.encodeMsgs l)) = l.getD i [] (S1-26's statement verbatim)	Strategy.msgAt_encodeMsgs (S1-26); re-derive or remove with uses re-pointed	CS1-F01 (undisclosed duplicate)
ZeroKnowledge/ThreeColoring/ColZKMachine.lean:147	public ColZK.field_zero_encodeMsgs (the i = 0 case, through field_encodeMsgs)	follows field_encodeMsgs (or Strategy.msgAt_encodeMsgs l 0)	CS1-F01 (consumer)
ZeroKnowledge/ThreeColoring/Machines.lean:951	public ColMachines.getD_eq_pairFstD_iterate: hist.getD i [] = pairFstD (pairSndD^[i] (Strategy.encodeMsgs hist)) (S1-26 reversed)	(Strategy.msgAt_encodeMsgs hist i).symm	CS1-F01 (undisclosed duplicate)
ZeroKnowledge/ThreeColoring/SimulatorMachine.lean:180	public ColSimMachine.emitLoop_poly (instance with the extra hypothesis L z <= |z| + 1, same proof)	EncodingMachines.polyTimeComputable_flatMap_range (S1-27); hLle becomes unused	CS1-C1-F02 (not closed by the final)
SecureComputation/Yao.lean:355	inline henc in decodeMsgs_encodeMsgs (:353): Strategy.encodeMsgs ms = BinArith.encWords ms	Strategy.encodeMsgs_eq_encWords (S1-21); InteractionWords enters Yao's closure once Yao/HybridProof/Lengths imports it for its own re-point	CS1-C1-F02 (not closed by the final)
Asymptotic/EnsemblesLemmas.lean:191-230; Asymptotic/CollectionsLemmas.lean:74-114; ZeroKnowledge/GraphIsomorphism/Efficiency.lean:181, :208; ZeroKnowledge/GraphIsomorphismZK/Simulator.lean:153, :159; Asymptotic/HardCoreGLColl.lean:111; Games/Efficiency/Strings.lean:152	padL/padL_eq/length_padL/polyTimeComputable_padL/polyTimeComputable_zeros; padStr family; GI/GIZK padSq and zeros_poly; HardCoreGLColl.padToLen; EffFill.zeros_poly: overlaps of the S1-27 padTo family and zeros_poly (inter-derivable, other constants)	no Stage 2 row: DL-53 (deferred consolidation after the campaign merges into main; CS1-C1-Q1)	CS1-C1-F01 / CS1-C1-Q1 (not disclosed by the final)
Games/Hopping.lean:384	ProbComp.expect_simulate_congr (same-state, unbudgeted relative of S1-04 expect_simulate_abs)	none (CS1-Q10 note)	CS1-C1-F06
ZeroKnowledge/EncodingMachines.lean:368	EncodingMachines.flatMap_range_ite_eq (singleton-chunk case of S1-27 flatMap_range_ite, map form)	optional re-derivation in its own file	CS1-C1-F06
Asymptotic/OneWayLemmas.lean:245	public flatMap_range_ite_eq_flatten_ofFn (Q <= R, flatten-ofFn conclusion): relative of S1-27 flatMap_range_ite	none (CS1-Q10 note)	CS1-F09
TCSlib/Complexity/Randomized/QuasiPolyHierarchy.lean:190	private flatMap_range_ite (m R) with replicate chunks: Complexity-side relative	none (Complexity side, as CS1-Q12)	CS1-F09
Encryption/PrivateKey/OracleFromPRF.lean:286	private prfAdv_prfReduction (DL-40/DL-44; brief: Stage 2 re-derives it)	TCSlib.Cryptography.prfAdv_eq_expect (Pseudorandom/Functions/Defs.lean:118)	CS1-F05 (brief item missing from the table)
Encryption/PrivateKey/EncryptThenTag/CPAHandler.lean:180, :185	body of bTapeOf; statement of bTapeOf_eq	EnsembleLemmas.blocks -> FunFamily.blocks (DL-35 alias removal; not among the seven approved changes)	CS1-F04 (needs a ruling before Stage 2)
Encryption/PrivateKey/EncryptThenTag/CPAReduction.lean:90, :94, :352	body of bTapes; statement of bTapes_eq; proof (expect_sample_equiv)	EnsembleLemmas.blocks -> FunFamily.blocks	CS1-F04
Encryption/PrivateKey/EncryptThenTag/Reduction.lean:89, :93, :327	body of dTapes; statement of dTapes_eq; proof (expect_sample_equiv)	EnsembleLemmas.blocks -> FunFamily.blocks	CS1-F04
Encryption/PrivateKey/EncryptThenTag/Handler.lean:183	statement of dTape_eq (the seventh change covers only dTape's body, :179-180)	EnsembleLemmas.blocks -> FunFamily.blocks	CS1-F04
ZeroKnowledge/ThreeColoring/ColRepSound.lean:184, :187 (docstring :179-180)	proof of pushesUniform_blockRead (EnsembleLemmas.blocks, blocks_apply)	FunFamily.blocks, FunFamily.blocks_apply	CS1-F04
Encryption/PrivateKey/EncryptThenTag/Handler.lean:178; Asymptotic/EnsemblesLemmas.lean:815, :433, :427; ZeroKnowledge/CommitmentLemmas.lean:486; Encryption/PrivateKey/OracleFromPRF/Handler.lean:139; Asymptotic/Ensembles.lean:223	the seven approved DL-35 changes (CS1-Q2 and the seventh), listed one per site for the Stage 2 gate	FunFamily.blocks	CS1-F05 (the final carries them as one pointer row)
Pairing/Assumptions.lean:199; Encryption/PublicKey/TrapdoorPredictor.lean:144	DL-55 (G44-01, ruled after dispatch)	promote decide_singleton_eq_true to a shared low-level home; re-point both	CS1-F05 (records, not the worker's)
AdvancedEncryption/IdentityBased/BonehBoyenMachine/Words.lean:261 and neighbours	DL-56 (G44-01, ruled after dispatch): poly_rU, poly_rZ, poly_rW, poly_rS	Games.polyTimeComputable_rU/_rZ/_rW/_rS (Games/Efficiency.lean:538-550)	CS1-F05 (records, not the worker's)

## ===== briefs/pass-shelat-ch5-8/cleanup-stage1/checkpoint1-review.md (records, at 659542ecd9413b504d30da8c937b9805e6c1f71f) =====

# cleanup-stage1 · maintainer review of checkpoint 1

**Verdict: PROCEED WITH NOTES.** The checkpoint meets its contract: every one of the 69 target
statements elaborates at the check tree, and decls2, the StmtDump, the shadow scan and the reuse
table are delivered.
- The patch series reproduces hash for hash at the issue base. Its merged tree equals the check head.
- decls2 gives exactly the brief's 69 declarations, with 0 CHANGED and 0 REMOVED.
- All 69 headers equal the brief token for token. All 7 pinned definition bodies are equal too.
- `protected` is right on all 69 names.
- The change is pure insertion, inside the Scope table, at the stated anchors. No frozen or
  other-campaign file is touched.
- All 69 proofs are complete already: there is no `sorry`.

Findings: **0 blockers, 0 majors, 3 minors, 8 infos.**
- All three minors are in the reuse/evidence layer and are fixed in the final, with no code change:
  - **F01:** an undisclosed overlap of the S1-27 `padTo` family with the public `padL`/`padStr`
    families;
  - **F02:** two copies missing from the Stage 2 table;
  - **F03:** search evidence the table cites but the delivery does not carry.
- One question goes to Seyoon. It merges the worker's CS1-W1 with F01.

## Delivery and integrity
- **Delivery:** exchange commit `bc2bf64a0c8449adb61234d957acb0e737fb66d5` ("fill cleanup-stage1:
  checkpoint 1"), an ancestor of the exchange tip `30ef1257…`.
  - It touches only `inbox/fills/cleanup-stage1/` (49 files). No later commit changes that path.
  - It is unsigned (no `gpgsig`), as `workflow.md` §4.1 asks.
  - I extracted it with `git archive` into a fresh empty directory.
- **Manifests:** top-level `SHA256SUMS` 48/48 OK and `checkpoint-1/SHA256SUMS` 47/47 OK. The path
  sets equal the delivered files exactly: nothing missing, nothing extra, no `./`.
  - At a checkpoint there is no `src/`, `REPORT.md` or `evidence/` tree. Those are for the final.
- **Issued package:** `shasum -a 256 -c` gives 8/8 OK. `brief.md` hashes to `56368c13…`, the
  dispatch pin.
- **Reproduction:** I made a scratch repository on alternates at the issue base
  `daa6e173cdd94cad1475b9a96eca613bce53ba61` and ran `git -c commit.gpgsign=false am
  --committer-date-is-author-date` of the five patches.
  - All five hashes equal `COMMITS.tsv` (`4881cf98`, `01f6b7e9`, `7b8a4d97`, `85797b50`, `c8021348…`).
  - The head is `c8021348f9bc2d16cfa52ca5e8ff489dc9543592`, with tree `508f9154…`.
  - The signing column says `none`, and the reproduction confirms the commits are unsigned. (My
    first `am` inherited this host's commit signing and produced other hashes; with signing off they
    match.)
- **Trees:**
  - `git merge-tree --write-tree f99901fd… daa6e173…` gives **`01cc6259480ccc9372181cd4d18d4511c87aa048`**,
    the check base.
  - `git merge-tree --write-tree f99901fd… c8021348…` gives **`985dd3125d8fd588cf2c8faa31ced8dee88407ab`**,
    the check-head tree the worker reports. They are equal.
  - All 19 home files are blob-identical at the issue base and the check base. Their base SHA-256s
    equal the Scope table's pins.
- **Records tip:** the worker fetched `8b5435eb…`, which had no Lean change since `f99901fd`. I
  verified that. The tip has since moved (F09).

## Scope, additivity and frozen files
- **Files:** `git diff daa6e173..c8021348` changes exactly the brief's 21 files: the 19 homes and the
  2 new modules. It has 1,079 insertions and **0 deletions**.
  - Every hunk is a pure `+` hunk (`@@ -n,0 +m,k`).
  - Removing the blocks gives back the issue base byte for byte.
- **Anchors:** every hunk sits at its Scope anchor:
  - `IterateFindHost` after 389, between `host_halt` and `end`;
  - `PPT` after `Coins` (222/223);
  - `BitLists` after 65 (`headD_drop_ofFn`), 99 (`zipWith_xor_cancel_left`) and 191 (a new section
    before `end`);
  - `Adversary` after `FunFamily.ofFn_blocks` (294);
  - `Sampling` after `StatClose.mono` (165), inside `section StatClose` (127–273);
  - `Encoding` after the `simps` attribute (39);
  - `EnsembleSecurity` after `encodeList_nil` (141/142);
  - `Trapdoor` after `pkPredictor` (283/284);
  - `Strings` after `length_encodeLog_le`;
  - `Experiments` after `prob_sample_eq_uprob`;
  - `Defs` after `toOracleAdversary_boundedBy` (339/340);
  - `Interaction` after `pairFstD_encodeMsgs`;
  - `EncodingMachines` before `end` (694);
  - `Games.lean` after 11 and 47;
  - `ZeroKnowledge.lean` after 7 and 41;
  - plus one docstring bullet hunk per existing non-facade file (17 files).
- **Frozen files are untouched:**
  - `Games/Probability.lean`, `Games/Relational.lean`, `Pairing/Group.lean`;
  - `Complexity/CircuitComplexity/**`, `Complexity/BranchingPrograms/**`;
  - `ComputationalModels.lean`, `machine-library-design.md`, `AdvancedEncryption/**` (GSW, IBE);
  - `Games/Hopping.lean` (CS1-Q9), `ModuleHost.lean`, `IterateFind.lean`;
  - every copy file, `TCSlib.lean` and `blueprint/`.
- **Imports:** the only import lines added are the two facade imports. `Games/Tapes.lean` imports
  exactly `Games.Hopping`. `InteractionWords.lean` imports exactly `ZeroKnowledge.Interaction` and
  `BinaryArith.Words`; at the check base neither imports the other, so there is no cycle. Both new
  modules reach the root through the facades.
- The new code has **no** `@[simp]` and **no** `sorry`.

## Statements (check 3)
- **decls2:** I ran the records' `decls2.py` (`fa81981a…`) on the reproduced head against the issue
  base, over the 21 files.
  - Result: **69 ADDED, 0 CHANGED, 0 REMOVED**, with an empty `.err`.
  - The output equals the delivered `statements/decls2.tsv` row for row.
- **Header check against the brief:** my own `stmtcmp.py` parses every `lean` block of `brief.md` and
  compares each declaration with the head source, normalizing only whitespace.
  - All **69/69** brief declarations match an ADDED name, and no ADDED name is left over.
  - Every header is token-identical, including the `protected`, `noncomputable` and `_root_.`
    prefixes.
  - The 7 definitions with a body pinned in the brief are identical including their bodies: `freshImpl`,
    `extTape`, `tapeImpl`, `ovr`, `recordBits`, `padTo`, and `zipWith_xor_cancel_right`'s header.
  - `FinDist.mixture`'s body is not pinned. It equals the Rejection copy (`Rejection.lean:395`) byte
    for byte.
  - Line-exact: 64/69. The other 5 differ only in line breaks, because the brief's single lines
    exceed 100 characters.
- **Homes and namespaces** all equal the brief:
  - `Complexity.IterateFind`, `TCSlib.Cryptography.Games`, `Games.EffFill`, `Games.Bridge`,
    `Games.OracleComp`;
  - `TCSlib.Cryptography` (incl. `FunFamily`, `StatClose`), `Authentication`, `PrivateKeyScheme`;
  - `Complexity.NUPPT` (incl. the `_root_` form in `Defs`), `Strategy`, `EncodingMachines`,
    `TCSlib.InformationTheory.FinDist`.
  - Kinds: 7 `def`, 62 `theorem`.
- **Elaboration evidence:**
  - The `StmtDump` probe ran with rc 0, 0 errors and 0 warnings. It prints `STMT-COUNT 69` with the
    full types. `probe-results.jsonl` binds its source (`bacc13db…`) and log (`cc91de2a…`); I
    rehashed both.
  - Sweep part 1 (129 modules: the homes, both new modules, both facades and their in-closure
    downstream) is 129/129 rc 0 with 0 errors. It covers every changed module. Its module times
    match the bootstrap's, so these were real compiles.
  - The bootstrap is 847/847 rc 0 with 0 errors. Its module list equals `order.txt`, and all 847
    source hashes equal the issued `SOURCE-SHA256SUMS`. Its 26 `sorry` warnings in 12 modules
    equal `base-sorries.txt` module by module.
  - This evidence settles elaboration, so **I ran no Lean** and did not use the olean snapshot.
- **Axioms** (`Axioms.log`): 69 prints and 0 `sorryAx`. The axioms used are a subset of {`propext`,
  `Classical.choice`, `Quot.sound`}. Two lists wrap across lines, which accounts for the worker's
  "34 all three".
- **Instances:**
  - Every S1-04 statement is the ETT `Tools.lean` statement with `Games.` qualification. `extTape`
    and its readers differ from `AdaptiveCPA`'s only in where `{C} [Nonempty C]` are bound.
  - I spot-checked these copies; each is an instance or an identical statement:
    - S1-12 `HashSignFill.eq_pure_of_cost_zero` and Lamport `exists_pure_of_cost_zero`;
    - S1-14 `BlockEncryptor.lean:60`;
    - S1-10 `FromDiscreteLog/Probability.lean:40`;
    - S1-22 `DDH.lean:146`;
    - S1-27 against both machine files: `flatMap_range_ite`, `polyTimeComputable_flatMap_range`,
      `iterSnd_poly`, `padTo`/`_eq`/`_poly`/`length_`/`getD_`, and `Assembly.lean:98`.
  - No statement looks false; all are proved. No listed copy fails to be an instance.

## `protected`, clashes and shadowing (check 11)
- **Short names:** I indexed all 31,425 declaration lines at the check base (`TCSlib/`, `audits/`,
  any modifier, private included).
  - Every one of the 54 `protected` names has a same-short-name declaration, except
    `Games.extTape_of_not_lt`. The brief makes every S1-04 name `P`, so that is as the brief says.
  - All 15 unprotected names are fresh in TCSlib. They are also absent from Mathlib (`029db123`,
    the manifest pin), Batteries, Aesop, Plausible, Qq and core 4.25.0 (no `List.getD_ofFn`).
  - Result: **0 unprotected names with an existing short name.**
- **Exact full names:** 0 clashes. I resolved namespaces in the 30 files that declare one of the new
  short names (79 declarations).
- **Shadowing:**
  - The delivered scan (361 hits, 0 needing attention) covers unqualified short names.
  - I extended it to the two forms that `protected` does not hide:
    - **partially qualified** uses (`FinDist.map_map`, `Games.ovr`, `Strategy.…`; 198 suffix
      forms): **0** occurrences at the check base;
    - **dot notation** on a value: **0**. Every `.x` hit is a fully qualified other name, such as
      `List.map_map`, `AdaptiveCPA.extTape`, `Rejection.uniform_prod` or `ColMachines.iterSnd_poly`.
  - So no existing name changes its resolution.

## Docstrings, tags, facades, sizes
- **Docstrings:**
  - All 69 open with a statement in words and give the formula.
  - 68 carry the glue note ("Framework glue, no textbook counterpart", with the first consumer where
    useful).
  - `pkPredictor_apply` carries `[PS10, Theorem 104.4, proof]`, as the brief says. No other tag was
    invented.
  - Every proof of 15 lines or more has a `**Proof sketch.**`:
    `ofFn_blocks_symm_eq_flatMap`, `of_uprob_ne`, `expect_simulate_abs`/`_inv`,
    `expect_simulate_tapeImpl`, `polyTimeComputable_flatMap_range` and `iterSnd_poly`.
    `map_uniform_equiv`'s proof has 14 lines, so it needs none.
  - Every changed module docstring has a bullet. The new modules have the full header, with
    References in the verbatim [PS10] entry plus the brief's locator ("Theorem 170.4 (book p. 170):
    the first consumer"; "§4.4"). Nit: F10.
- **Facades:**
  - `Games.lean` imports `Games.Tapes` after line 11, and its `## Contents` entry after line 47 is
    the brief's text.
  - `ZeroKnowledge.lean` imports `InteractionWords` after line 7, and its entry after line 41 is the
    brief's text.
  - Both entries add the facade's backtick style; the worker disclosed this.
  - bb1-sim's anchors (after 9 and 42) are untouched.
- **Sizes and width:**
  - The largest files are `Asymptotic/Sampling.lean` at 965 lines and
    `ZeroKnowledge/EncodingMachines.lean` at 867 (the brief estimated ~830). `Games/Tapes.lean` has
    346 lines and `InteractionWords.lean` 44. Every file is under 1,000.
  - The maximum width of an **added** line is 100 characters. No tab, trailing space or micro sign
    is added.
  - The over-100 lines in `PPT`, `Adversary`, `Sampling`, `EnsembleSecurity`, `Trapdoor`, `Defs`,
    `EncodingMachines` and `Interaction` are all base lines, with the same maxima at the base.
- **Lint** (`style_lint`, campaign lint) is check 8 of the final. I did not re-run it here; the tool
  resolves paths against the repository root, not a scratch tree.

## Findings

| # | Severity | Finding | Disposition |
|---|---|---|---|
| CS1-C1-F01 | **minor**, undisclosed overlap (check 12) | The S1-27 `padTo` family overlaps two public padding families. The reuse table does not mention them, and neither does the ledger.<br>• `EnsembleLemmas.padL` with `padL_eq : padL k a = (a ++ 0^k).take k`, `length_padL` and `polyTimeComputable_padL` (`Asymptotic/EnsemblesLemmas.lean:191–230`). At `p = .var` and `u = 1^{L x}` it gives `padTo_poly` through `padL_eq`. Conversely, `padTo_poly` gives it through `StateLoop.unaryPoly_comp`.<br>• `CollectionsLemmas.padStr`/`padStr_eq`/`polyTimeComputable_padStr`/`padStr_of_length_le` (`Asymptotic/CollectionsLemmas.lean:75–114`).<br>• Instances: `GI.padSq`/`GIZK.padSq` (`L = n·n`) and `HardCoreGLColl.padToLen`.<br>Neither family is in `EncodingMachines`' closure. Both are in the closure of **both** consumers (`ThreeColoring/Machines` and `ComposeSecurity/Machines` import `EnsemblesLemmas` and `CollectionsLemmas`).<br>This is the same kind of overlap as the worker's CS1-W1 `zeros_poly`, which was disclosed; this one was not. It is not a restatement, since the constants differ, so per BS-F01's precedent it is a minor. | Disclose it in the final's *Overlap and reuse* and Stage 2 table. Seyoon rules with CS1-W1 (**Q1** below). No code change unless Seyoon chooses (c). |
| CS1-C1-F02 | **minor**, missing copies | The reuse table reports "none" further for these two rows, but the check base holds:<br>• **S1-27 `polyTimeComputable_flatMap_range`:** the public `emitLoop_poly` (`ZeroKnowledge/ThreeColoring/SimulatorMachine.lean:180`). It is an instance, with an extra hypothesis `L z ≤ |z| + 1`, and has the same proof. Its companion `flatMap_range_ite` at `:160` *is* listed.<br>• **S1-21 `encodeMsgs_eq_encWords`:** an inline copy, `henc` in `decodeMsgs_encodeMsgs` (`SecureComputation/Yao.lean:355`, in the declaration at `:353`). | Add both to the Stage 2 table in the final. |
| CS1-C1-F03 | **minor**, evidence | The reuse table cites sub-agent search evidence that the delivery does not contain: `subagents/A/NOTES.md`, `reuse-grep-1.txt`, `copylist-check.txt`, `subagents/B/NOTES.md`, and the raw `exact-lead/` and `exact-ab/` directories. Only the lead's two greps, the two `exact?` probes and their logs are delivered, so the search record for sub-agents A and B's 50-odd declarations cannot be audited. Sweep part 1 is delivered as a progress file only, without per-module source hashes or raw logs. | The final delivers all of it under `evidence/`, with a manifest, including `evidence/build/summary.txt` bound to `git show HEAD`, as the brief's *Evidence completeness* requires. |
| CS1-C1-F04 | info, CS1-W1 checked | I confirmed the worker's facts: `Games.EffFill.zeros_poly` (`Strings.lean:152`) and `EnsembleLemmas.polyTimeComputable_zeros` (`EnsemblesLemmas.lean:212`) are public, inter-derivable with S1-27 `zeros_poly`, and outside `EncodingMachines`' closure.<br>But option (b)'s claim that "the ThreeColoring copy would then have no Stage 2 target" is inaccurate:<br>• `ThreeColoring/Machines` imports `EnsemblesLemmas`, so its `zeros_poly` re-derives as `(EnsembleLemmas.polyTimeComputable_zeros .var hL).congr …`;<br>• `ComposeSecurity`'s `padTo_poly` already derives the same zero word from `GI.zeros_poly` composed with `hL`.<br>The table calls `GI.zeros_poly`/`GIZK.zeros_poly` "homonyms, other statements"; they are relatives (`0^{|w|}`). | Folded into **Q1**. |
| CS1-C1-F05 | info, binder order | `FinDist.map_uniform_equiv`, `sum_map` and `uniform_prod` (`FinDist.lean`) bind `{α} [Fintype α] {β} [Fintype β]`, using the file's own `α` variable. The brief's variable line and the Rejection copies bind `{α β} [Fintype α] [Fintype β]`. The header text is equal; only the order of implicit and instance binders differs. No `@` use of any copy exists at the check base, and the proof-only re-points of Stage 2 are unaffected. | None. Optionally, the final notes it under *Statement changes* as "binder order only". |
| CS1-C1-F06 | info, near relatives | The table does not name two relatives:<br>• `ProbComp.expect_simulate_congr` (`Games/Hopping.lean:384`): the same-state, unbudgeted relative of S1-04 `expect_simulate_abs`;<br>• `EncodingMachines.flatMap_range_ite_eq` (`EncodingMachines.lean:368`): the singleton-chunk special case of S1-27 `flatMap_range_ite`. The new docstring cites it.<br>Neither is a more general form, so neither is an E-DUP. | List both in the final's table. `flatMap_range_ite_eq` is an optional Stage 2 re-derivation in its own file. |
| CS1-C1-F07 | info, near relative after the check base | bb1-sim's `Games/Relational.expect_simulate_rel` landed after the check base (a statement with `sorry`; the fill is pending). It is a relational coupling form, but it does not subsume `Games.expect_simulate_abs`: abs's hypothesis holds only while `cnt s < κ`, and `rel` needs it from every related state. | Gate 47 note: the two forms are distinct; the final may cite `expect_simulate_rel` as a relative. |
| CS1-C1-F08 | info, counts | `CHECKPOINT-1.md` says "+1,075 lines"; the series has +1,079 (21 files, 0 deletions). `EncodingMachines` ends at 867 lines, not the brief's ~830; it is still under 1,000. | Correct the count in the final. |
| CS1-C1-F09 | info, landing | The records tip moved after the worker's fetch. It is now `62df03f97f9259f4f5668260448ad9385e64541d`: the bb1-sim Games statements (`02000ad4`, `dfacac35`) and the group PR #352 (`2cca41bc`, `92dea4f8`, merge `463f2244`) have merged. These change `Games.lean`, `Games/Probability.lean`, `Games/Relational.lean` and `Pairing/Group.lean`. `git merge-tree --write-tree 62df03f9… c8021348…` is clean, with tree `11695b1f8619f7cec575923298063faf145bb7c7`. `Games.lean` merges as a union (70 lines: `Relational` and `Tapes` imports and both Contents entries). No new Stage 1 name meets a name bb1-sim added. | The final states the tip it used. Landing re-replays at the tip (`workflow.md` §6.1), on snapshot #4's successor. |
| CS1-C1-F10 | info, docstring nit | The `Games/Tapes.lean` module docstring lists the definitions and 13 lemmas, but omits the readers `freshImpl_apply` and `tapeImpl_apply` from `## Main results`. | Optional one-line fix in the final. It is a pure insertion either way. |
| CS1-C1-F11 | info, for the final's seals | I read the new proofs for Rule 10. There is no `unfold`, `delta` or `change`. Steps to watch in the seals:<br>• the trailing `rfl` of `ofFn_splitBits_fst`;<br>• `FinDist.mixture_apply := rfl` (through `FinDist`'s `CoeFun`; notation per DW-10 Q3, so it may fail only in the strict variant);<br>• unrestricted `simp`/`simpa` in `host_branch_view`, `flatMap_range_ite` (`zero`), `FinDist.sum_map` and `map_apply_expect`;<br>• the `show` steps in `Games.expect_sample_ovr` (its own definition, in its own file: allowed);<br>• `cases b <;> rfl` and `split_ifs <;> rfl` (core `ite`). | Final, check 6. No action now. |

## Questions for Seyoon

**CS1-C1-Q1 (with CS1-W1; F01, F04).** The S1-27 zero word and padding duplicate existing public
forms. Those forms live outside `EncodingMachines`' closure, but inside both consumers' closures:
- the zero word: `EffFill.zeros_poly`, `EnsembleLemmas.polyTimeComputable_zeros`, `GI.zeros_poly`;
- the padding: `EnsembleLemmas.padL`/`polyTimeComputable_padL`, `CollectionsLemmas.padStr`.

CS1-Q8 put "the `padTo` family" in the shared toolkit without considering these forms. The choices:
- **(a) Recommended. Keep S1-27 as CS1-Q8 ruled (69 declarations).** The unary-length forms belong
  in the shared unary toolkit, beside `truncate_poly` and `unaryLength_poly`, which both consumers
  already import directly. The final discloses every overlap. A new ledger row puts the
  `padL`/`padStr`/`padSq`/zero-word families into one consolidation after the campaign merges.
- **(b) Drop `zeros_poly` only (68 declarations).** Inline the zero word in `padTo_poly`. Stage 2
  re-derives the ThreeColoring copy from `EnsembleLemmas.polyTimeComputable_zeros .var`.
- **(c) Withdraw `zeros_poly` and the `padTo` family (62 declarations; partly reverses CS1-Q8).**
  Stage 2 re-points both consumers to `EnsembleLemmas.padL` and `polyTimeComputable_padL`.
  `getD_padTo` and `padTo_of_length` have no `padL` counterpart, so Stage 2 would add two `padL`
  readers to `EnsemblesLemmas` instead.

## What the final must add (beyond the brief's list)
- F01–F03: disclose the `padL`/`padStr` overlaps, add `emitLoop_poly` and `Yao.lean:355` to the
  Stage 2 table, and deliver the sub-agent and raw search evidence and the sweep binding.
- F05, F06, F08 and F10 as noted.
- State the records tip used and the merge-tree against the current tip (F09).

## Evidence
- `checkpoint1-review-evidence.zip` (SHA-256 in `evidence-SHA256SUMS`), under `cs1-c1/`:
  - `PROVENANCE.txt`;
  - `tools/`:
    - `stmtcmp.py`, `linecmp.py`: brief against head;
    - `shortclash.py`, `fullclash.py`: the protected rule and full-name clashes;
    - `closure.py`: import closures from `git grep '^import'` at the check base;
    - `doccheck.py`, `width.py`;
    - an unmodified copy of `decls2.py`;
  - outputs:
    - `decls2.mine.tsv`, `stmtcmp.out`, `shortclash.out`, `doccheck.out`, `sizes_head.txt`;
    - `full.diff` (`-U0`) and `am_hashes.txt`;
    - `mt_tip.txt`: the merge-tree at the current tip;
    - `partial_re.txt` and `partial_hits.txt` (empty), `dot_hits.txt`;
    - `ett_cmp.txt`: the S1-04 statements against the ETT and AdaptiveCPA copies;
    - `changed.txt`.
- Scratch repository, clone and extraction directories were deleted after the review. Nothing was
  committed or pushed. No Lean process was run, and the olean snapshot was not touched.

**Not yet clear to merge — checkpoint 1 only: the final (checks 1–12, seals, controls, full sweep) and CS1-C1-Q1 are pending; the worker may proceed to the final.**

## ===== briefs/pass-shelat-ch5-8/cleanup-stages.md (records, at 659542ecd9413b504d30da8c937b9805e6c1f71f) =====

# Pass–shelat cleanup: the three stages (Seyoon, 2026-11-17)

The remaining Pass–shelat cleanup runs in three stages. Rebuilds and gates happen only between stages. The GSW and IBE
items, including DL-50, are out of scope here.

## Stage 1: promotions (additive only)
- Publish the general forms named by the duplication ledger in their natural shared homes:
  - `Games`: the ETT simulation and coin-tape forms (DL-40).
  - `Asymptotic/Sampling`: `statClose_of_uprob_ne` (DL-51).
  - One common `encodeMsgs_eq_encWords` (DL-49, extended).
  - The generic getD reader (DL-47).
  - `length_ofFn_coins` at the `NUPPT` layer (DL-48).
  - The general forms of DL-35 and DL-41 to DL-46.
  - DW-9's view versions of `host_dispatch`, `host_branch` and `host_halt`.
- Every new public declaration has readers, a formula docstring and a proof. No existing proof is touched.
- **Gate:** a statement-style audit of the new public API. Is each lemma general, correctly homed, and free of duplication?

## Stage 2: re-point and prune (proof-only)
- Re-point every ledgered copy to its promoted form (DL-35, DL-38 to DL-49, DL-51, DL-52). This includes the
  `OTAnswerWords` pair against #324's `HybridProtocol.length_answers*`, and the ETT averaging-bound copy against the bb1-sim
  promotion in `Games/Probability`.
- Gate 44 G44-01 (Seyoon, 2026-11-17): **DL-55** (promote `decide_singleton_eq_true` to a shared low-level home; re-point
  `TrapdoorPredictor` and pairing T1) and **DL-56** (re-point #346's `poly_rU/rZ/rW/rS` to `Games/Efficiency`'s
  `polyTimeComputable_r*`, with a reader if needed).
- bb1-sim fill ruling Q1 (Seyoon, 2026-11-17): **DL-57** (promote `sidSpec_dom/rng_*` and `zeroBits_eq_cast` into
  `IdentityBased/Defs.lean` as `IBEScheme.*`; re-point the bb1-sim fill and T4's private copies).
- Gate 47 pre-dispatch sweep (Seyoon, 2026-11-17): **DL-59** (unify `Games.extTape`, `LazySampling.extendStream` and
  `AdaptiveCPA.extTape` in `Games/Tapes`, with DL-40) and **DL-60** (B3 with DL-53: `padTo` vs `List.takeD`; B4 with
  DL-49: re-point `pairFstD_encodeMsgs`/`pairSndD_encodeMsgs`). DL-60's B2 goes to the Complexity handoff.
- ~~Gate 48 G48-01: **DL-58**~~ — repaid before merge by LE-g48 on #357 (`dfdc56f2`), so it is no longer Stage 2 work.
- Delete the dead private copies and the public host lemmas left unused by DW-5.
- Clear DW-9's 26 seal failures and `Uniform.lean`'s 4 inherited failures (SY-F07) through readers.
- Sweep in small lint and doc nits, such as the `BobIO` unnecessary `simpa`.
- **Gate:** a proof audit, plus the full Rule 10 seal sweep over every touched owner. Target: every Pass–shelat ledger row
  closed, and no seal failure in any touched file.

## Stage 3: closure (Run 4)
- The PS10 ch. 5–8 ingest (DW-8; docs-only, may run externally during Stage 1 or 2), and a citation pass against it.
- The census and axiom prints, the lint baseline, and the drift attestation.
- The completion record.
- **Gate:** the closure audit. Then the merge to `main`.

## Preconditions and order
- **#347 (DW-5) merges before Stage 1,** because both touch the host files.
- **Stage 1 starts after the bb1-sim Games statement PR merges.** That PR promotes the averaging bound into
  `Games/Probability` (part of DL-40), and Stage 1 should not race the GSW/IBE PRs on shared files.
- Each stage is one external job, or two with disjoint file sets. Each is validated by one merged-tree replay on the
  snapshot (`workflow.md` §6.1).
- **Out of scope:** DW-1/DW-2 (uniform simulators), which Seyoon ruled "probably after merging into `main`", and DW-3 (notes).

## Parallel with the GSW/IBE work (Seyoon, 2026-11-17)
Seyoon asked for the cleanup to run in parallel with the GSW/IBE work "to the extent possible". So:

- **Stage 1 starts now** as an external job. It owns no file that the running GSW/IBE jobs edit: not
  `Games/Probability.lean` or `Games/Relational.lean`, not `Pairing/Group.lean`, not `Complexity/CircuitComplexity/**` or
  `Complexity/BranchingPrograms/**`, not `ComputationalModels.lean` or `machine-library-design.md`, and nothing under
  `AdvancedEncryption/**`. Facade import lines may be edited, since they merge as unions. The averaging bound (part of
  DL-40) is left to the bb1-sim promotion.
- **Stage 1 is stacked on #347 (DW-5),** because DW-9's view versions live in the same host files. Gate 47 audits #347 and
  Stage 1 together.
- **The PS10 ch. 5–8 ingest runs now** as a separate external docs job. Stage 3 folds it in.
- **Stage 2 starts after Stage 1 and the bb1-sim Games PR merge.**

## Stage 1 rulings CS1-Q1 to CS1-Q12 (Seyoon, 2026-11-17)

| # | Ruling |
|---|---|
| CS1-Q1 | **Include DL-39** in Stage 1: the 14 `FinDist` facts, protected, in `InformationTheory/{FinDist,Samples,Entropy}.lean`. |
| CS1-Q2 | **The six statement/body changes are approved now.** Stage 2 removes both DL-35 aliases of `blocks`, the private one and the public one in `EnsemblesLemmas.lean`. The gate checks the six changes explicitly. *(changed: was private only)* |
| CS1-Q3 | Stage 2 moves `MachineCodec.ext_of_fields` verbatim to its shared home. |
| CS1-Q4 | The `fwdHandler` generalization is taken out of the cleanup. Hosts change only by their own gated design. |
| CS1-Q5 | DL-41: the `splitBits` word readers `Authentication.ofFn_splitBits_fst/_snd` in `Authentication/Encoding.lean`. |
| CS1-Q6 | DL-48: `NUPPT.length_ofFn_coins` in `Complexity/Randomized/PPT.lean`, beside `Coins`. |
| CS1-Q7 | DL-51: `StatClose.of_uprob_ne` in `Asymptotic/Sampling.lean`. |
| CS1-Q8 | **DL-49's ThreeColoring helpers move to a shared machine layer.** Stage 1 adds them additively to a shared machine-layer module that both `ThreeColoring/Machines` and `ComposeSecurity/Machines` can import; Stage 2 re-points both. The helpers include `encodeMsgs_eq_flatMap`, `msgAt_encodeMsgs`, the `padTo` family, `polyTimeComputable_flatMap_range`, `flatMap_range_ite` and `iterSnd_poly`. *(changed: was importing ThreeColoring/Machines)* |
| CS1-Q9 | **DL-43's `mul_prob_le_expect` goes to `Games/Probability.lean` in Stage 2**, after the bb1-sim Games PR merges and frees that file. It is a small additive exception to Stage 2. Lamport is then re-pointed. It is not in Stage 1. |
| CS1-Q10 | Near relatives that are not instances get no target; they stay as notes. |
| CS1-Q11 | Promotion requests with no ledgered copy are declined for now. |
| CS1-Q12 | DL-47: the Complexity-side inline chains stay as they are; only the Cryptography-side copies are re-pointed. |

## PS10 citation fixes go into Stage 2 (2026-11-17)
The `ps10-cite-check` delivery (exchange `69add654`; `ingests/ps10-cite-check-final-r1/REPORT.md`) found 40 content mismatches at 40 sites under 15 locators (Tier A: 19 under Theorem 180.1, 17 of them one recurring "step 4" label) and 21 advisory notes (Tier B). All 67 locators exist with the cited kind and page. The Tier A corrections, docstring-only, are part of Stage 2; the Tier B notes are applied where they change what a reader is told.

## Historical seal debt (DW-10; Seyoon, 2026-11-17)
The plan had omitted the #248 historical seal ledger and the inherited-seal repairs deferred on 2026-11-10. Ruling: run a fresh canonical-seal inventory of all Pass–shelat-owned files at the tip now, reconcile it with the #248 ledger, and fold the fixes into **Stage 2**. Seal-B-only items (Yao and sc-garble `PolyExpr.eval`) and non-campaign files (`Complexity/TuringMachine/CodeSimulator.lean`) are listed, then handled by separate ruling.

**Inventory rulings (Seyoon, 2026-11-17; job `dw10-seal-inventory`, `cleanup-dw10/issued-r1/`):**
- **Q1:** the campaign is responsible only for seals of cryptography content. The 21 Complexity/Arora–Barak files with recorded debt (incl. `Uniform`, `CodeSimulator`) are not sealed by the job; their 608 recorded items are `HANDED-OFF` to a separate Complexity-library chat (`cleanup-dw10/handoff-complexity/`). An owner failure whose fix needs a reader in a Complexity file stays ours, as `STAGE2-PROVIDER-READER`; Seyoon rules placement.
- **Q2:** the 20 adopted Garg and InformationTheory files are owners (434 owners in all).
- **Q3:** the `FinDist.instCoeFunForallReal` coercion is notation, like `PolyExpr.eval` (2026-11-07). Strict variants still run; strict-only failures are recorded, need no fix and no further ruling.
- **Q4:** Arora–Barak files the campaign touched that hold no item are excluded.
- **Handoff target:** wait for the campaign merge. The Complexity handoff is released only after `cryptography/pass-shelat-ch2-4` merges into `main`; it is then re-derived at `main`'s tip and fixed by PR into `main`.

**Stage 2 handover, a seventh change for Seyoon to confirm:** removing the public `EnsembleLemmas.blocks` alias also needs the body of `ETTGame.dTape` (`EncryptThenTag/Handler.lean:178`) changed. It is of the same kind as the six approved under CS1-Q2.

**Seventh change approved (Seyoon, 2026-11-17):** the body of `ETTGame.dTape` (`EncryptThenTag/Handler.lean:178`). Stage 2 makes all seven DL-35 changes, and its gate checks each one.

**Stage 1 final rulings (Seyoon, 2026-11-17; review `cleanup-stage1/final-r1/review.md`):**
- **Q1:** accept the delivery; the report layer is completed by the maintainer's Stage 2 addendum (`cleanup-stage1/final-r1/stage2-addendum.tsv`), DL-49 extended for `msgAt_encodeMsgs`, DL-53 standing. No round trip.
- **Q2:** removing the public `EnsembleLemmas.blocks` alias needs seven more changes, approved as the same kind as the seven of CS1-Q2: the bodies of `bTapeOf`, `bTapes`, `dTapes` and the statements of `bTapeOf_eq`, `bTapes_eq`, `dTapes_eq`, `dTape_eq` (with their proof uses). Stage 2 makes all fourteen; its gate checks each one.
- **Q3:** CS1-W1 is answered by CS1-C1-Q1 and CS1-W2 by DW-10 Q3 (the `FinDist` coercion is notation).
- **Q4:** the Stage 1 PR is stacked on #347's branch `cleanup/dw5-derand-readers` for Gate 47, then retargeted to the records branch after #347 merges (never merged into #347's branch).

## ===== briefs/pass-shelat-ch5-8/deferred-work.md (records, at 659542ecd9413b504d30da8c937b9805e6c1f71f) =====

# Deferred work register (Pass–Shelat and companion campaigns)

Work that Seyoon has ruled **deferred**. Each item is deliberately not done now and must not be lost. It is
expected to be picked up after the current work has merged into `main`, unless a row says otherwise. When an item is
started, link its plan or PR here; when it lands, mark it done.

| # | Item | Ruled | Source | Scope and starting point | Status |
|---|---|---|---|---|---|
| DW-1 | **Uniform simulators for honest-but-curious security** (audit U-01, U-03) | Seyoon, 2026-11-16: defer; less sweeping than expected; probably after merging into `main` | [Uniformity audit](audits/uniformity-2026-11-16/findings/uniformity-audit-findings.md) §U-01 and §U-03 | `HBCSecure` (`SecureComputation/Defs.lean`) and `HybridProtocol.HBCSecure` (`SecureComputation/Hybrid.lean`) allow non-uniform simulators. This matches PS10 Definition 155.1, which permits n.u. p.p.t. simulators, but is weaker than Goldreich's uniform-simulation convention and Seyoon's convention. The audit lists the affected declarations: the two predicates and their readers; `otProtocol_hbcSecure`, whose simulators are already uniform (`otSimA_uniform`, `otSimB_uniform`); `yaoHybrid_simulators` and `yaoHybrid_hbcSecure`, which sc-yao must later make literally `Uniform`; `hbcSecure_compose`; and `yaoProtocol_hbcSecure`. In sc-compose, `ComposeSim.exists_simulator`, `exists_simA` and `exists_simB` pair the component advice, and `pairEncode [] []` has length 2, so a uniform post-processing constructor via `ofPolyTimeUniform` is needed (U-03). The worst-instance advice there is confined to reductions, which is correct. Options to decide then: keep the PS10 predicate and add a uniform variant, or migrate. | Open (deferred) |
| DW-2 | **Uniform simulator with shared auxiliary input for simulation-based non-malleability** (audit U-02) | Seyoon, 2026-11-16: defer with DW-1 | Audit §U-02 | `SimNMSecure` (`Encryption/PublicKey/NonMalleability/Simulation.lean:672`) lets the simulator carry its own advice, and `NMSim.exists_simulator` uses the adversary's and the sampler's advice. **Adding `Sim.Uniform` alone makes the definition unsatisfiable:** a non-uniform adversary can output an undecidable bit (proof in the audit). The repair is a new ideal experiment `snmIdealAux` in which a *uniform* simulator receives `A.advice n` and `M.samp.advice n` as ordinary shared auxiliary input. It then migrates `SimNMSecure`, its reader, `nmSecure_of_simNMSecure`, `simNMSecure_of_nmSecure_cpa`, `simNMSecure_cpa_iff_nmSecure_cpa`, and the simulator and ideal-gap machinery. | Open (deferred) |
| DW-3 | **Uniformity audit notes** (U-04 to U-07) | Seyoon, 2026-11-16 | Audit §U-04 to §U-07 | No change needed now. Record the corrections when DW-1 is taken up. The brief was wrong that PS10 requires uniform HBC simulators, and wrong on the quantifier polarity of its example. ZK's auxiliary-input bound is adequate. The literal `IndistLit` and `WorstCaseOneWayLit` variants are documented historical comparisons. | Notes |
| DW-4 | **Duplication cleanup** (DL-38 to DL-52) | Seyoon, 2026-11-14 and later | `duplication-ledger.md` | Promotions and re-points of the ledgered copies. This includes the generic getD reader (DL-47), `length_ofFn_coins` to the `NUPPT` layer (DL-48), and the sc-compose restatements (DL-49, extended with the two `encodeMsgs_eq_encWords` copies). DL-40's private averaging bound is promoted into `Games/Probability.lean` by the bb1-sim statement phase (ruling Q6), after which the ETT copy re-points. Also the GSW hybrids through promotion P-1 (DL-50), and `statClose_of_uprob_ne` promoted to `Asymptotic/Sampling` (DL-51). After #341 merges, the `OTAnswerWords` pair is re-pointed at #324's lemmas (DL-52). Also a shared `Regev.augmentedEquiv` for the GSW augmentation equivalences (Gate 43 GS-06; `GSW/Security.lean:202–207`, `GSW/Symmetric.lean:116,136`). | Open (deferred) |
| DW-5 | **derand F-01: typed-view readers** | Seyoon, 2026-11-16: debt now, fix after | `fills/derand/final-r1/review.md` | Add the SR-02 typed-view readers (`ModuleHost` / `IterateFindHost`), then re-derive E1 `computesFunInTime_find` and `polyTimeComputable_find` through them. This clears 20 Rule-10 seal failures, 9 new and 11 pre-existing. | Open (deferred) |
| DW-6 | **Small-secret LWE equivalences** (ACPS09) | Seyoon, 2026-11-16 | `briefs/lattice-gsw/rulings.md` addendum | Small-secret LWE (A3) is assumed explicitly wherever it is used. Prove its equivalence with standard LWE later. | Open (deferred) |
| DW-7 | **Source ingests for the new campaigns** | Seyoon, 2026-11-16 (pairings Q12; GSW Q14; the Pei16 citations) | `PairingCryptographyPlan.md`; `briefs/lattice-gsw/rulings.md` | The PDFs stay uncommitted. Ingest Markdown transcriptions of only the passages used: Jou00 and BB04 (pairings); GSW13, BV14 and AP14 (GSW). Extend the approved scoped Pei16 Markdown with §5.4.3 and §6.1.2–6.1.3, which the GSW docstrings cite. | **Done** 2026-11-16 (records `6078f369`): Jou00, BB04, GSW13, AP14, BV14, BV11, Bar89 ingested as scoped `.raw.md`/`.md` pairs; Pei16 extended with §5.4.3 and §6.1.2–6.1.3; registered in `sources.json`; proofmatch runs pending. Follow-up: register `[Vad12]`, cited in `InformationTheory/` but absent from `sources.json` (Gate 43 note). |
| DW-8 | **Source ingests, never blocking** | Seyoon, 2026-11-16: "please don't let ingestion be a bottleneck; do this when and only when there are free slots, or we can even give this to an external worker" | `briefs/lattice-gsw/phase6/rulings.md` (P6-Q19), `briefs/pairings/fills/bb1-sim/rulings.md` (Q11), DW-7, task PS10 | Ingest as scoped `.raw.md`/`.md` pairs and register in `sources.json`. Run only on a free olean-tree slot or as an external job, never ahead of build, review or gate work. Every citation that waits on an ingest is a docstring-only follow-up; no Lean docstring cites a tag before its ingest. Items: [Gen09] (PDF from Seyoon; phase-6 leveled key chain); [BGZ09] and [Sho04] (PDFs from Seyoon; bb1-sim relational lemma); [Vad12] (PDF from Seyoon; already cited for Thm 6.18 in `Regev/Experiments`, `SIS/Columns`, `SIS/Universality`, unregistered); PS10 ch. 5–8 (`Pass–Shelat.pdf` is in the repository). | **Ingested** 2026-11-16 by an external worker (exchange `443df15b`); review ACCEPT WITH EDITS (`ingests/dw8-final-r1/review.md`). Open docstring-only follow-ups: (a) [Vad12] deviation notes in `Regev/Experiments.lean`, `SIS/Columns.lean` and `SIS/Universality.lean` (F6: the ½·√ bound comes from the proof of Thm 6.18 over general finite sets; F7: 2-universality is [Vad12, §3.5]); (b) [Gen09] citations in the 6b leveled statements; (c) [BGZ09]/[Sho04] in bb1-sim. BGZ09 states no adversary rule (F4), so cite its §4.1/§4.2/§5.2 lemmas with a deviation note. PS10 ch. 5–8 still to ingest (slot or external). |
| DW-9 | **Pre-existing seal failures in the two derand host files** | Seyoon, 2026-11-16 (DW-5 scope ruling: new deferred item) | `maintenance/dw5/README.md` | `ModuleHost.lean` has 10 failures (`stop_step`, `stop_clean`, `clean_install`, `clean_emit`, `pad_seam`, `pad_apply`, `pad_run`, `host_seam`, `host_call`). `IterateFindHost.lean` has 16: 6 in the `copy_*` proofs and 10 in the statements of `host_dispatch`/`host_branch`/`host_halt`, which read `hostTM`'s fields. They are identical before and after DW-5. Clearing them needs frozen-file proof edits and view versions (or statement changes) of the three `host_*` lemmas, which DW-5 left unused. | Open (deferred) |
| DW-10 | **Historical seal debt** | Seyoon, 2026-11-17: inventory now, fix in Stage 2 | the #248 seal ledger (cleanup part 2, 764 historical observations); rulings of 2026-11-10 (72 efficiency and 52 Levin provider pairs deferred); SG-F07/SY-F07 (Yao and sc-garble seal B, `PolyExpr.eval`); canonizer C-F02 (`CodeSimulator`, 177 errors in 58 pre-existing declarations, a Complexity-library file) | A fresh canonical-seal inventory of every Pass–shelat-owned file at the tip, reconciled against the #248 ledger. Open items are fixed in cleanup Stage 2 by readers and proof-only re-derivations. Seal-B-only items and files outside the campaign (`CodeSimulator`) are listed and handled by separate ruling. | Open: inventory job `dw10-seal-inventory` dispatched 2026-11-17 (records `4367db3c`, exchange `d4cfd2f8`); cryptography owners only (Q1–Q4). Complexity handoff (608 items) held until the campaign merges into `main`. |
| DW-11 | **Combined small-items gate** | Seyoon, 2026-11-17 | #351 and #352 (bb1-sim Games statements and group helpers) were merged on the maintainer review ("merge now, audit later") | One gate, later, auditing #351, #352 and any other similarly small merged changes together, instead of separate gates. #351 and #352 leave the bb1-sim gate (Q8), which keeps the reader insertions and the T2/T3 fill. Add further small items here as they arise. | Open (collecting: #351, #352) |

## ===== briefs/pass-shelat-ch5-8/duplication-ledger.md (records, at 659542ecd9413b504d30da8c937b9805e6c1f71f) =====

# Duplication ledger: Pass–shelat ch. 5–8

Accepted debt, each entry acknowledged by the user, with its scheduled resolution.

| ID | New declaration (where) | Existing copy (where) | Status | Resolution |
|---|---|---|---|---|
| DL-1 | `TCSlib.InformationTheory.abs_probTrue_sub_le_statDist` (#183, `InformationTheory/Extractors.lean`, for `main`) | `TCSlib.Cryptography.abs_sum_sub_le_statDist` (`Foundations/Experiments.lean`, Garg's concrete layer, on `cryptography/pass-shelat-ch2-4` and `cryptography/garg-ch1-3`; not on `main`) | accepted 2026-11-04 (user) | No copy on `main` today. When the concrete layer lands on `main`, its lemma becomes a one-line corollary of #183's (a `Finset` test is the `Bool` test `(· ∈ T)`) or is removed. Gate 01 pack erratum E1. |

## Inherited with ch. 2–4 (found 2026-11-05; acknowledged 2026-11-05 by the user: clean up now)

This campaign owns ch. 2–4 since 2026-11-05 (plan, decision log). These duplicates predate it.

| ID | Copies (where) | Status | Proposed resolution |
|---|---|---|---|
| DL-2 | XOR of encodings is the encoding of the Boolean sum, `zipWith xor (ofFn a) (ofFn b) = ofFn (a + b)`, stated three times: `TCSlib.Cryptography.zipWith_xor_ofFn_add` (`Asymptotic/HardCoreLoops.lean`; it was `zipWith_xor_ofFn`, renamed by the base repair to end the name clash with `Encryption.lean`'s different lemma); `TCSlib.Cryptography.zipWith_xor_ofFn_eq_add` (`Asymptotic/MultiMessage.lean`); `TCSlib.Cryptography.MultiMsg.zipWith_xor_ofFn_eq_add` (`Asymptotic/MultiMessageLemmas.lean`) | accepted; scheduled now | Keep the most upstream copy (`HardCoreLoops`) and point the other two at it, in a ch. 2–4 cleanup PR. |
| DL-3 | `pairEncode a b ≠ []`, stated four times: `GGMRed.pairEncode_ne_nil` (`Asymptotic/GGMReduction.lean`), `GI.pairEncode_ne_nil` (`ZeroKnowledge/GraphIsomorphism/Proofs.lean`), `ColMachines.pairEncode_ne_nil` (`ZeroKnowledge/ThreeColoring/Machines.lean`); and, on `main`, `Complexity.pairEncode_ne_nil` (`Complexity/SpaceComplexity/Logspace/InputAccess.lean`), the copy that made the merge's ambiguity | accepted; scheduled now | `main` is merged (#186). Remove the three local copies in favour of `Complexity.pairEncode_ne_nil`, in the same cleanup PR. |
| DL-4 | Not a copy (different carriers): the sampler-based `StatClose` (`Asymptotic/Sampling.lean`) and `main`'s `EpsClose` on `FinDist` (`InformationTheory/Extractors.lean`, #183) | accepted; scheduled now | A bridge lemma, in the same cleanup PR (user, 2026-11-05). |
| DL-5 | Not a copy (different carriers; found by the gate 02 round 2 review): `Games.guessAdv_eq_half_advantage` and `Games.accept_guessGame` (games) and the concrete layer's `predict_eq` (`Asymptotic/Ensembles.lean`, on `uprob` over seed spaces), both the identity behind [PS10, Lemma 73.8] | disclosed in the docstring (gate 02 closing commit) | Derive one from the other through bridge B2 when ch. 2–4 lands on `main`. |

## Found in the ch. 5–8 statement phase (2026-11-05)

| # | Statement | Copies | Status | Resolution |
|---|---|---|---|---|
| DL-6 | Coin-tape slices `(r.drop (j * c)).take c` in global/GI-shadow graph isomorphism, Lamport and sequential ZK, alongside the former BlockEncryptor home | historical duplicates found by the Lamport worker/maintainer | **Implemented at `e9d64158461bfe24ddc88ab885bc4017899b4c16`; final source `3f6db40e1688c4a0bb922c9575dd3bd2157a650b` is checked in draft PR #232. Native and layered Rule10 reconciliation identify zero new/touched reads; all older failures remain recorded. External gates and landing pending.** | One `TCSlib.Cryptography.coinBlock`, `coinBlock_eq` and `length_coinBlock` live in `Asymptotic/Adversary.lean`. The BlockEncryptor definition moved upstream; global/shadow `coinSlice` and sequential ZK's `phaseSlice`/unused length lemma are retired. Lamport already used the public BlockEncryptor `coinBlock`; its length lemma moved upstream. Consumers use the shared name and published reader. |
| DL-7 | Equal-length padding: Lamport's `ofFn_padFin_of_length`, and the inline step in `Composability.length_eval_of_length` (`CCA2Scheme.lean`) | General equation `Collection.ofFn_padFin_of_le` in **`Asymptotic/CollectionsHelpers.lean`**, not `Collections.lean` | **Implemented at `e9d64158461bfe24ddc88ab885bc4017899b4c16`; final source `3f6db40e1688c4a0bb922c9575dd3bd2157a650b` is checked in draft PR #232. Native and layered Rule10 reconciliation identify zero new/touched reads; all older failures remain recorded. External gates and landing pending.** | Lamport's duplicate theorem is deleted. Its uses and CCA2's two padding steps use the general equation, whose conclusion is `List.ofFn (padFin ℓ w) = w ++ List.replicate (ℓ - w.length) false`; at `w.length = ℓ`, simplify `Nat.sub_self`, `List.replicate_zero` and `List.append_nil`. |
| DL-8 | `SecureComputation.PRFOut ℓ₂` (prong B, `SpecialEncryptionSecurity.lean`): ch. 2–4's `PRF` with `ℓ₂(n)`-bit outputs; `PRF` is its case `ℓ₂ = n` | resolved 2026-11-05 | `prfOut_var_iff : PRFOut .var F ↔ PRF F` proved beside `PRFOut` (prong B). The ch. 2–4 layer is unchanged. |


## Found by gate 03 (2026-11-05; rulings G3-5 and R-03l-1: clean up in the gate 03 clean-up PR, after #195)

Most copies trace to helpers that are `private` in pack 03a's and 03l's files. The clean-up makes
one copy public in the most upstream file and re-points the rest.

| Id | Copies | Status | Payback |
|---|---|---|---|
| DL-9 | The coin-block bijection `blocks` (`Fin (m · c) → Bool ≃ Fin m → Fin c → Bool`) and its lemmas, copies and an inverse: `FunFamily.blocks`, `OneWayYao.blocksE`, `blocksEquiv`, `blocksEquivX`, `EnsembleLemmas.blocks`, `SoundnessRep.blocksEquiv`, and `Ensemble.blocks` (private, `Asymptotic/Ensembles.lean`, which calls itself a copy of `FunFamily.blocks`; added on gate 03a round 2, R2-4); with S2b's public duplicate `take_drop_ofFn_blocks` of `EnsembleLemmas.take_drop_ofFn_blocks` (gate 04 N4) | accepted; scheduled (G3-5) | One `FunFamily.blocks` in a low file; re-point 03h, 03i, 03k's statements, `Ensembles.lean` (03a) and S2b's copy. |
| DL-10 | `ptc_comp` (composition of polynomial-time functions in a convenient form), six private or public copies (`Closure`/`Repetition` helpers, `Universal*`, `ThreeColoring/Machines`, …) | accepted; scheduled (G3-5) | Public once in 03a's `Closure.lean`; delete the copies. |
| DL-11 | The state loop `stateFind` (private in `Repetition.lean`) and its copies `GI.stateFind`, `EncodingMachines.polyTimeComputable_stateFind`, `GGMRed.stateLoopFun`, and the variant `stateIterate` | accepted; **half done in [#203](https://github.com/Shilun-Allan-Li/tcslib/pull/203)** (`polyTimeComputable_stateFind` public, prose fixed); the copies are re-pointed in clean-up part 2 | `polyTimeComputable_stateFind` public in `Repetition.lean`; re-point; update the prose that calls it private (`StringLoops.lean:36–38`, `HardCoreLoops.lean:68`). |
| DL-12 | `abs_uexp_sub_le`, two copies (`PublicKeyLemmas` and a private one) | accepted; scheduled (G3-5) | One public copy. |
| DL-13 | `negligible_zero` (`Foundations/Negligible.lean` since G3-7a) and `negligible_const_zero` (`ZeroKnowledge/Defs.lean`) | accepted; scheduled (G3-5) | Delete `negligible_const_zero` (2 uses). |
| DL-14 | `forall_of_uprob_eq_one`, two copies | accepted; scheduled (G3-5) | One public copy. |
| DL-15 | `decodeFin_eq_some_iff`, a private copy in `Collections.lean` and a public one in `GGMReductionEval.lean` (`GGMRed.decodeFin_eq_some_iff`; making the `Collections.lean` copy public must avoid the namespace clash, gate 03b review #12c), and the new forward lemma `ofFn_of_decodeFin_eq_some` (`CollectionsHelpers.lean`, #198); S2b's private `eq_ofFn_of_decodeFin` | accepted; scheduled (G3-5) | One public `decodeFin_eq_some_iff` in `Asymptotic/Adversary.lean`; the forward lemma derived from it. |
| DL-16 | `IterateFindHost` (03l) copies 26 declarations of `main`'s private module layer in `Complexity/ClassNP/SAT.lean` (ten now public); the new host is missing from the policy's host registry (§14) | **done in [#203](https://github.com/Shilun-Allan-Li/tcslib/pull/203)**: one public host `Turing.ModuleHost` (`TuringMachine/Build/ModuleHost.lean`), consumed by `SAT.lean` and `IterateFindHost.lean`; registry row H14 | Make `SAT.lean`'s layer public on the ch. 2–4 branch and re-point `IterateFindHost`; register the host. |
| DL-17 | `StateLoop` (03l) restates five `main` lemmas, plus `tail_poly` and `xor_poly` (arrived with the `main` merge, #186) | accepted; scheduled (R-03l-1) | Use `main`'s lemmas. |
| DL-18 | `UnaryMul` (03l) privately copies `PairSplit`'s parser | **done in [#203](https://github.com/Shilun-Allan-Li/tcslib/pull/203)** (`Turing.PairParse` in `PairSplit.lean`) | Use `PairSplit`'s. |
| DL-19 | Not a copy yet: a latent name clash between `StateLoop.BlockLoop` and `main`'s `Complexity.BlockLoop` (nothing uses it) | **done in [#203](https://github.com/Shilun-Allan-Li/tcslib/pull/203)** (renamed `StateLoop.BlockMapLoop`) | Rename or merge in the same PR. |
| DL-20 | `main`'s `TuringMachine/Build/Loop.lean` keeps a private `loop_first_halt`, the same lemma as the new public `Turing.ModuleHost.first_halt` (found by #203's worker). `Loop.lean` is upstream of the host, so it cannot consume it | noted | Move `first_halt` and `live_prefix` down into `Loop.lean` (or the machine core) at the `main` landing, and have `Loop.lean` use them. |
| DL-21 | Elementary number theory that Mathlib already has (audit `mathlib-overlap-nt.md`, 2026-11-06, Mathlib pin `029db123`): 6 DUP (`QR` = `(powMonoidHom 2).range`, `crtUnits` (keep as alias, `rfl`), `coprime_of_ne` = `(Nat.coprime_primes hp hq).2`, `powOneSubgroup` = `(powMonoidHom m).ker`, `rsaPerm` ≈ `powCoprime` (optional), `IsGenerator` ≈ `∀ x, x ∈ zpowers g`) and 9 WRAP (shorter proofs from Mathlib: `units_val_mem`, `pow_mod_totient_modEq`, `units_pow_eq_one_iff`, `two_mul_card_le_of_ne_top`, `card_units_eq_mul_card_QR`, `card_QR_prime`, `sq_pow_div_four_succ`, `fmultNat_eq_mul_prime`; and the core of the sorried `elGamal_correct`) | accepted; scheduled (user direction 2026-11-06: Mathlib first) | Replace by Mathlib's (alias where a name is load-bearing), clean-up part 2 item M; rows in fill-owned files (`Candidates/*`) after those fills land, as landing edits. The fill briefs cite the report's Mathlib names. |
| DL-22 | TCSlib's Chebyshev lower bound (`NumberTheory/Chebyshev.lean`) and Korselt-type facts are in newer Mathlib (`Chebyshev.pi_ge`, `theta_ge`, `psi_ge`; `Nat.isCarmichael_iff_korselt`; master `94f43000`, Lean v4.36.0-rc2), not at our pin | noted | Replace at the next Mathlib bump (repository-wide, `main`'s pin). At the same bump, the hypothesis `BlumDensity` (`Rabin.lean`) can be discharged in its eventual form (`n ≥ n₀`): apply `WienerIkehara.tendsto_sum_range_div` (master only) to `vonMangoldt.residueClass 3` mod 4, with the continuation `vonMangoldt.continuousOn_LFunctionResidueClassAux` (already at our pin) and Chebyshev's `ψ(x) ≪ x` (master), to get `ψ(x; 4, 3) ~ x/2`; then `θ ≥ ψ − (ψ − θ)` (`Chebyshev.psi_sub_theta_le_mul_sqrt`) and `π(x; 4, 3) ≥ θ(x; 4, 3)/log x`. This changes the Rabin statements that take `BlumDensity` (they would take nothing, or `n ≥ n₀`); a statement gate then. |
| DL-23 | fac fill (`Candidates/Factoring.lean`, delivery review 2026-11-07): private near-copies of public lemmas: `fac_chunkEquiv` = `FunFamily.blocks`; `fac_arrowCongr` = `finCastEquiv`; `fac_ofFn_halves` repeats a private `OneWay` lemma (half is `ofFn_block_eq_take_drop`); `fac_listToNat_inj` repeats a private `Sampling` lemma; plus the REPORT's three near-duplicates and small numeral facts re-proved across the fac, rsa and dl-a fills | noted | Clean-up part 2: re-point to the public lemmas; publish the two private ones beside their files and share the numeral facts. |
| DL-24 | col-b fill (delivery review 2026-11-07): `ColZK.acceptProb_seed_to_coins` = `acceptProb_bind` reversed and `ColZK.findSome?_map_option` = core `List.map_findSome?` (removed by landing edits E3–E4); a third copy of `pushesUniform_restrict` across fill units (dl-a has one); `table_index_*` vs `finProdFinEquiv`; `polyTimeComputable_next` repeats `reply_poly`'s proof (review finding 6 has the full list) | E3–E4 at landing; rest noted | Clean-up part 2: publish one `pushesUniform_restrict`, re-point the rest. |
| DL-25 | dl-b fill (`DiscreteLogHardcore.lean`, delivery review 2026-11-07): `dlb_statClose_pi` copies the public `OneWay.statClose_pi` (removed by landing edit E1); `dlb_stateIterate_poly` (from `HardCoreLoops`), `dlb_count_ofFn` (from `HardCoreGL`; relative of `List.count_ofFn`), the `listToNat` fold lemmas, `two_pow_size_le` (dl-a and 3-col have inline `2^size m ≤ 2m` bounds), `pushesUniform_castLE` copies (review D1) | E1 at landing; rest noted | Clean-up part 2: publish one copy of each beside its source; missing equations `HardcoreBit.majority_eq` (`PairwiseIndependence.lean`) and `expSampler_coins` (`DiscreteLog.lean`) at the next shared-file window. |
| DL-26 | col-a fill (delivery review 2026-11-07): `colRep_xor_poly` = `StateLoop.xor_poly`, `eq_of_xor_eq_false` = core `bne_eq_false_iff_eq`, `pushesUniform_blockRead` rebuilds `FunFamily.blocks` (removed by landing edits E2–E4); `ColRep.exec_four_mul`'s step repeats `GI.exec_repViews`'s proof (promote `exec_four_mul`, request R-3); cross-unit near-copies with col-b's `ColZK.pushesUniform_offsetTable`, `ColZK.ofFn_drop_take` | E2–E4 at landing; rest noted | Clean-up part 2: promote `exec_four_mul`, share the col-a/col-b helpers; requests R-2 (`(decGraph x).1` equation), R-5 endorsed. Base reading for #210's next round: `R3COL_witnessRelation`'s `bounded` clause destructures `R3COL` instead of using `R3COL_iff`. |
| DL-27 | rsa fill (delivery review 2026-11-07): 151 lines copied verbatim from dl-a's private helpers (`dla_findSome?_ite`, `dla_find?_range_lt`, `dla_listToNat_append`, `dla_drop_natToList_zero_append`, `dla_ss*`); `rsa_appendEquiv` = Mathlib `Fin.appendEquiv` (landing edit E1); `rsa_comp`/`ptc_congr` copies of the private `ptc_comp` family; loop lemmas descend from Primality's private `spStep`; near-copies of `findSome?_eq_bind_find?`, `find?_range_eq_map_find?_finRange`; parallels with fac (`fac_natToList_mod`, `fac_pairDec`) | E1 at landing; shared-lemma PR planned | **Landing order:** (1) dl-a lands; (2) a shared-lemma PR publishes `PolyTimeComputable.comp'`/`.congr` (`PolyTime.lean`), `IterateFind.find?_range_and_lt` (`IterateFind.lean`), nine `listToNat`/`natToList` lemmas (`Arithmetic.lean`), `rejectBlocksL_eq_find?` (`Concrete.lean`), removing dl-a's copies; (3) rsa lands with E1–E3 and E4 (cites them; checked against stubs); (4) a statement-gated `polyTimeComputable_rejectBlocksL` retires the copied loops in dl-a, rsa, rabin (and dl-c, pending its review). |
| DL-28 | dl-c fill (delivery review 2026-11-07): near-verbatim copies of the trial loop and numeral helpers shared with dl-a and rsa (and dl-b's own modular-numeral layer); `dlc_abs_uexp_sub_le` duplicates `Sampling.lean`'s private lemma and its public copy in `PublicKeyLemmas.lean` (review D1) | noted | Folds into DL-27's shared-lemma PR. The review's D2 homes: generic `polyTimeComputable_rejectBlocksL` (`Concrete.lean`), `listToNat` lemmas, width lemmas (`Arithmetic.lean`), `find?_range` (`Repetition.lean`), `PolyTimeComputable.congr` (`PolyTime.lean`), `abs_uexp_sub_le` public in `Sampling.lean`, `finCastEquiv` to `CollectionsHelpers.lean`. Reconcile with DL-27's homes when that PR is drafted. |
| DL-29 | rabin fill (delivery review 2026-11-07): `rabin_appendEquiv` = Mathlib `Fin.appendEquiv` and `rabin_pushesUniform_prod` (re-proved from `PushesUniform.prodMap`) handled by landing edits E1–E2; undisclosed copies: `rabin_statClose_one` = dl-a's `dla_statClose_one`; `rabin_listToNat_mulStr`, `rabin_prime_poly` copy rsa helpers; `rabin_rS`/`_rQ`/`_rTest` ≈ rsa's `rsa_fS`/`_fQ`/`_fTest`; the block loop is a fourth copy (with dl-a, rsa, dl-c `dlc_ss*`); `rabin_drop_zeros_append`'s step = fac's `fac_natToList_mod` | E1–E2 at landing; rest noted | Folds into DL-27/DL-28's shared-lemma PR and the `polyTimeComputable_rejectBlocksL` host PR. Base reads `rabinCollection_index`, `rabinBlumTrapdoor_index` (through `show`; re-point via `Collection.index_eq`) go to clean-up part 2's (b) list. |

Rows from DL-30 on use a five-column layout.

| Id | New declaration (where) | Existing copy (where) | Status | Resolution |
|---|---|---|---|---|
| DL-30 | padded-cpa fill (delivery review 2026-11-11): generic `ProbComp` facts published in a public-key helper as `Composability.ChallengeSim.expect_sample_equiv`, `expect_sample_comm`, `expect_sample_unique`, `expect_sub` (`PublicKey/OracleSecurity/ChallengeSim.lean`); `expect_sample_prod` repeated `Bridge.expect_sample_pair`'s proof. | `ChallengeSim.lean` only | **Paid** ([#298](https://github.com/Shilun-Allan-Li/tcslib/pull/298), merge `d3f2290a`, 2026-11-13; Gate 20) | Landing edit re-proved `expect_sample_prod` from `Bridge.expect_sample_pair`. Promote the four lemmas to `ProbComp` in `Games/Probability.lean` and re-point their uses. |
| DL-31 | `ofFn_padFin_of_length` (`List.ofFn (padFin d w) = w` when `w.length = d`): `GGMRed.ofFn_padFin_of_length` (`GGM/Run.lean`), copy in `Asymptotic/HardCoreGLColl.lean`, private copy in `ElGamal.lean`; padded-cpa's `RecordHandler.lean` uses the GGM one through a transitive import. | 3 | **Paid** ([#298](https://github.com/Shilun-Allan-Li/tcslib/pull/298), merge `d3f2290a`, 2026-11-13; Gate 20) | Promote one public lemma beside `padFin` in `Asymptotic/Adversary.lean`; re-point all uses and delete the copies. |
| DL-32 | `List.ofFn (cast h f) = List.ofFn f` for a width equality: public `Composability.AdaptiveCPA.ofFn_cast` (`PublicKey/AdaptiveCPA/Games.lean`) and private `cca2OfFn_cast` (`PrivateKey/OracleFromPRF.lean`, #289). adaptive-cpa review also lists for promotion: `expect_sample_update` (→ `Games/Probability.lean`, with DL-30), `simulate_eq_of_abs` and the `castImpl` family (→ `Games/Simulate.lean`), `padFin_ofFn_zeroBits`, `headD_ofFn_one`, `ofFn_splitHalf_fst/_snd`; reader request `indCodec_eq_bitCodec`; new uses of `GGMRed.ofFn_padFin_of_length` join DL-31. | 2 (+ candidates) | **Paid** ([#298](https://github.com/Shilun-Allan-Li/tcslib/pull/298), merge `d3f2290a`, 2026-11-13; Gate 20) | Promote one generic `ofFn_cast` beside `padFin`/`BitCodec`; re-point both; promote the listed generic lemmas. |
| DL-33 | bitwise-cpa fill (delivery review 2026-11-11): `BitwiseSim.expect_sample_update` vs `AdaptiveCPA.expect_sample_update` (two forms, same name); generic `BitwiseSim.expect_simulate_eager` and public near-copy `BitwiseSim.expect_simulate_indImpl_cpa` of the private lemma in `PublicKey/OracleSecurity.lean`; `chRun_toCompOn_transport_list` generalizes `ChallengeSim.chRun_toCompOn_transport`; `BitwiseSim.headD_drop` = public `CommitmentLemmas.headD_drop` (and private `headD_drop_ofFn` in `Pseudorandom/NextBit.lean`); `flatten_ofFn_singleton` = private `flatten_ofFn_one` (`Yao.lean`); `decodeFin_nil_getD` (→ `Games/BitCodec`); `padded_enc_runAt/_coins` (→ beside the padded readers); `qDin/qDout` third copy of the two-oracle length vector (`recDin/recDout`, `acDin/acDout`); private `ofFn_half`, `bitwise_runAtL` re-prove published facts; reader request `HybridMachine.hybridPre_eq`. | several | **Paid** ([#298](https://github.com/Shilun-Allan-Li/tcslib/pull/298), merge `d3f2290a`, 2026-11-13; Gate 20) | One consolidation PR with DL-30–DL-32: promote to `Games/Probability`, `Games/Simulate`, `ChallengeSim`, `BitCodec`, a shared list module; re-point and delete copies. |
| DL-34 | pk-cpa-cca1 fill (delivery review 2026-11-12): `OracleFromPRF/Handler.lean` copies private AdaptiveCPA handler pieces (`ofFn_padFin_eq_padL`, round-input readers `rU`…`rCnt`, `impl_of_ret`, `replicate_one`); public `ofFn_pkTapes` re-proves `AdaptiveCPA.ofFn_acTapes` (a generic `⟦blocks q ℓ ω j⟧ = (⟦ω⟧.drop (j·ℓ)).take ℓ` belongs beside `FunFamily.blocks`, input-layout readers beside `InteractiveHandler.input`); private-key `indCodec_eq_bitCodec` (DL-32 reader request); `mem_keys_of_lookup_isSome` (core `List.lookup_isSome_iff`); promotion candidates `simulate_eq_of_abs_bounded` (generalizes `AdaptiveCPA.simulate_eq_of_abs`), `expect_simulate_congr` (→ `Games/Simulate`), `abs_expect_sub_le` (→ `Games/Probability`), `prob_bad_le`, `expect_sample_mem_le` (→ `Games/Hopping`), `padFin_nil`, `padFin_replicate_false`, `ofFn_arrowCongr_finCongr` (→ beside `padFin`), `zipWith_xor_cancel_left`, `xorPerm` (shared list/vector module); owned-file private overlaps with the `cca2*` helpers. | several | **Paid** ([#298](https://github.com/Shilun-Allan-Li/tcslib/pull/298), merge `d3f2290a`, 2026-11-13; Gate 20) | Fold into the DL-30–DL-34 consolidation PR. |
| DL-35 | Found while staging the consolidation (2026-11-12): public `blocks` in `Asymptotic/EnsemblesLemmas.lean` and private `blocks` in `Asymptotic/Ensembles.lean`, both the equivalence `(Fin (q * ℓ) → Bool) ≃ (Fin q → Fin ℓ → Bool)` of `FunFamily.blocks` (`Asymptotic/Adversary.lean`). | 2 | Open (ch. 2–4 inherited) | Re-point to `FunFamily.blocks` in a later ch. 2–4 cleanup; out of scope for `dl-consolidation`. |
| DL-36 | nm-cca2 fill (delivery review 2026-11-12): `NMCCA2.logEmit` (`PublicKey/NonMalleability/Indistinguishability/Forward.lean`) generalizes `Games.EffFill.relabelN`/`relabel` (`Games/Efficiency/OracleBridge.lean`), and its log facts `logEmit_encodeLog`, `iterate_pairSndD_encodeLog`, `flatMap_range_drop`, `length_le_length_encodeLog`, `length_iterate_pairSndD_le`, `polyTimeComputable_logEmit` mirror `relabelN_encodeHist`, `length_le_length_encodeHist` and the orbit bound of `bridgePre_poly` (undisclosed); public `finU`, `finZ`, `finW`, `finA`, `finL`, `fields_finInput` are the DL-34 round-input readers (`rU`…`rL`) again; `ofFn_nthCt` (owned file) is DL-34's generic block fact (`ofFn_acTapes`, `ofFn_pkTapes`); the private readers `rState`…`rAns` (disclosed). Promotion requests: `fwdHandler`/`fwdHandler_impl`, `exists_withAdviceOn` (→ `Games/Efficiency`), `cntRead`/`ansRead` (→ `BitCodec`), `indImpl_eq_of_msgLen_eq_zero` (→ `PublicKey/OracleSecurity`, after that file is split: it is at 999 lines). | several | **Paid** ([#299](https://github.com/Shilun-Allan-Li/tcslib/pull/299), merge `eff2dcd0`, 2026-11-14; Gate 21) | After the DL-30–DL-34 consolidation lands: put `logEmit` beside `relabelN` with `relabel x = logEmit relabelEmit x`; re-point `dCnt`/`dCt`/`dIn`/`dFin`/`eBit`/`eMsg`/`eTape`/`eCt` to R6's readers and delete `finU`…`fields_finInput`; derive `ofFn_nthCt` from the generic block lemma; promote the accepted requests. |
| DL-37 | nm-sim fill (delivery review 2026-11-13; **undisclosed**, accepted as debt by Seyoon 2026-11-13): `NMSim.chunkAt`/`chunkAt_eq`/`length_chunkAt` (`PublicKey/NonMalleability/Simulation/Hybrid.lean`) and the block lemmas `ofFn_block`, `chunkAt_flatten_append`, `map_chunkAt_flatten`; private `padFin_replicate_false` (`Simulation/Challenge.lean`); `Rounds.impl_of_ret`, `rdU`…`rdLog`/`rdState`, `rdAns`, `Simulator.finSt` (`Simulation/Rounds.lean`, `Simulator.lean`); also generic neighbours `expect_eq_until_bad`, `NMSim.expect_simulate_eager`, `expect_congr_of_allOutputs`, `chunkMap`; disclosed: `flatMap_range_drop`, `ofFn_padFin_eq_padL`, `polyTimeComputable_guessBit`, `ofFn_eq_map_range` | `coinBlock`/`coinBlock_eq`/`length_coinBlock` (`Asymptotic/Adversary.lean`), `OneWayLemmas.ofFn_block_eq_take_drop`, `NMCCA2.ofFn_nthCt`, Lamport `coinBlock_flatten`; `PRFGame.padFin_replicate_false` (`OracleFromPRF/Transfer.lean`; → `Games.padFin_replicate_false` in the consolidation); DL-34 private `impl_of_ret` (`AdaptiveCPA/Handler.lean`, `PRFGame`) and readers `rU`…`rL`/`rS`; `Games.prob_eq_until_bad`, `BitwiseSim.expect_simulate_eager`, `ProbComp.expect_mono_of_allOutputs`, `relabelN`/`logEmit` (DL-36); ZK `ofFn_eq_map_range` ×2; A4 `EnsembleLemmas.ofFn_padFin_eq_padL`; `rFwd`/`rY`/Forward `rAns` | **Paid** ([#299](https://github.com/Shilun-Allan-Li/tcslib/pull/299), merge `eff2dcd0`, 2026-11-14; Gate 21) | Landing of the consolidation (after nm-sim): delete the private `padFin_replicate_false` and use `Games.padFin_replicate_false`; re-point the nm-sim files to the moved names. Post-consolidation fold window, with DL-36: fold `chunkAt` onto `coinBlock` (58 uses) and place the block lemmas beside it; re-point `rdU`…`rdLog`, `rdState`, `finSt` to `InteractiveHandler.rU`…`rS` and `impl_of_ret` to `InteractiveHandler.impl_of_ret`; derive `prob_eq_until_bad` and `ChallengeSim.expect_simulate_eager` from the general nm-sim forms; one iterate-and-emit definition for `relabelN`/`logEmit`/`chunkMap`; merge the three `ofFn_eq_map_range` into `Foundations/BitLists`; make `NMSim.ofFn_padFin_eq_padL` the A4 lemma; fold `rdAns` with the `rFwd`/`rY`/`rAns` readers; promote the accepted requests (review r1 table). |
| DL-38 | dl-folds fill (worker REPORT §0.6, disclosed; delivery review 2026-11-14): inline re-proofs of `impl_of_query` (`acHandler_impl_forward`) and of a returning finalization (`pkHandler_finish`, `acHandler_finish`); a local `have` equal to `polyTimeComputable_ansRead` (`OracleFromPRF.lean`); further block-window restatements (`Primality.ofFn_chunk`, `ColRep.drop_take_ofFn_blockRead`, `Factoring.fac_ofFn_halves`, already corollaries); other iterate-and-emit loops (`BlockEncryptor`, `EnsembleLemmas.CopiesLoop`, `StretchMachine`, `CommitmentLemmas.ComLoop`, ZK `EncodingMachines`); the ZK pair `GI.iterate_pairSndD_encodeMsgs` / `ColMachines.iterate_pairSndD_encodeMsgs`; and the B3 `blocks` aliases (`EnsembleLemmas.blocks` and its lemmas, private `Ensembles.blocks`), escalated. | `InteractiveHandler.impl_of_query`, `finish_of_ret`; `Games.polyTimeComputable_ansRead`; `FunFamily.ofFn_blocks`; `Games.iterEmit`; `FunFamily.blocks` | Open (deferred) | Opportunistic: fold each when its file is next touched. The B3 aliases need a gate-approved restatement of `exists_copiesRed`, `ofFn_blocks_symm`, `take_drop_ofFn_blocks`, `ComLoop.emit_init_of_lt` and of the bodies of `PRFGame.pkTapes`, `Ensemble.copies` (all definitionally equal). Complexity copies of `ofFn_eq_map_range` and `flatMap_range_drop` are another campaign's. |
| DL-39 | ext-nosrc fill (worker request and delivery review 2026-11-14, disclosed): `Randomness.Rejection.tupleEquiv` restates Mathlib's `(Fin.consEquiv _).symm`; generic `FinDist` facts local to `Randomness/Extraction/Rejection.lean` (`sum_map`, `expect_map`, `probTrue_map`, `probTrue_le_one`, `probTrue_nonneg`, `map_map`, `map_prod_snd`, `uniform_prod`, `map_uniform_equiv`, `mixture`, `mixture_isSource`, `uniform_probTrue`); no exact duplicate in TCSlib (nearest: `SamplingFinDist.uprob_comp_eq_probTrue_map`, `Experiments.uprob_comp_eq_sum_map`, `ProbComp.expect_map`). | Mathlib `Fin.consEquiv`; `InformationTheory/FinDist` (to be added) | Open (deferred) | Promote the `FinDist` facts to `InformationTheory/FinDist` and use `Fin.consEquiv` in a later job (`FinDist` was frozen for the fill). The authoritative full promotion list (also `map_apply_expect`, `branch_apply`, the uniform-machine family, `take_poly`) is the delivery's `evidence/promotion-requests.md`, `rejection-review.md`, `sampler-review.md` (exchange `a5da5cc3`, `inbox/fills/ext-nosrc/`; Gate 22 observation). |
| DL-40 | cca2-ett fill (delivery review 2026-11-14): undisclosed `ETTGame.eval_toOracleAdversary_len` (`EncryptThenTag/Machines.lean`) generalizes public `PRFGame.eval_toOracleAdversary_width` (`OracleFromPRF/Reduction.lean`, its `ℓ = n` case); disclosed `ETTGame.zipWith_xor_cancel` = four private `zipWith_xor_xor_self` copies (`FromPRF`, `FromPRG`, `SpecialEncryption`, owned `zipWith_xor_xor_self'`; public relative `zipWith_xor_cancel_left`, other orientation); Gate 23 (G23-01, Seyoon 2026-11-14: debt now, fold in cleanup): private `length_le_length_encodeLog` (`EncryptThenTag/Machines.lean`) = the private copy in `NonMalleability/Indistinguishability/Forward.lean:108`; `ETTGame.prfAdv_eq_expect` re-derives private `prfAdv_prfReduction` (public relative `prfAdv_eq`, uprob form); generic forms `ETTGame.tapeImpl`/`simulate_tapeImpl_congr`/`expect_simulate_tapeImpl` (AdaptiveCPA), `recBits` family and `ovr` (PRFGame), `expect_simulate_abs` (`Games.simulate_eq_of_abs_bounded`), private `abs_expect_sub_le_expect` (`ProbComp.abs_expect_sub_le`). | `Foundations/BitLists`, `Pseudorandom/Functions`, `Games/*`, the general ETT forms | Open (deferred) | Promote the general forms (worker requested most) and re-derive the specialised copies from them; fold the private XOR copies; publish `length_le_length_encodeLog` in `Games/Efficiency/Strings.lean` beside `length_encodeLog_le` and delete both private copies (cleanup job). |
| DL-41 | dl-crh fill (delivery review 2026-11-14): **undisclosed** `FromDiscreteLog.inputWord_split` restates `ofFn_eq_init_append` (`Asymptotic/ReductionSupport.lean`, up to `Fin.init`); `ofFn_splitBits_fst/_snd` restate `ofFn_splitCoins_fst/_snd` (`CollectionsHelpers.lean`; `Authentication.splitBits` = `splitCoins`); disclosed re-derivations from public readers of private `dlb_expo_val`, `fac_listToNat_inj`, `ofFn_splitCoins_symm_cast`, `dla_statClose_expDec`; near relatives `residueFinEquiv` (Mathlib `ZMod.finEquiv`), `boundedInputEquiv` (`Fin.snocEquiv`), `expect_sample_eq_uexp` (`Games.Bridge.prob_sample_eq_uprob`). | `ofFn_eq_init_append`, `ofFn_splitCoins_*`, a `splitBits = splitCoins` bridge; worker promotion list `evidence/PROMOTION.md` (exchange `9ad236d1`) | Open (deferred) | `inputWord_take` (Gate 24 G24-01) and `inputWord_split` re-pointed to `take_ofFn_castLE` / `ofFn_eq_init_append` by LE-reuse `d356381a` (#307); the rest: re-point and promote in a later job. |
| DL-42 | hash-sign fill (delivery review 2026-11-14): `HashSignForward.roundWord`/`handler` repeats the `Games/Forwarding` `fwdRun`/`fwdHandler` pattern with a hashed query and different widths (disclosed); `splitBits_pad_concat` is a corollary of `Games.padFin_append_split`; `expect_simulate_sample_once` near `Games.expect_simulate_eager`; `MachineCodec.ext_of_fields`, `forgerCodec_eq_bitCodec`, `eq_pure_of_cost_zero` overlap the parallel lamport delivery's `lamport_codec_ext`, `lamport_forgerCodec`, `exists_pure_of_cost_zero`. | `Games/Forwarding` (a query-map `fwdHandler`), `Games/BitCodec`, `Games/Hopping`, `Games/Machines` | Open (deferred) | Generalize `fwdHandler`; promote the codec/cost facts to `Games/Machines` (no attribute) and fold the lamport copies once both units have landed. |
| DL-43 | lamport fill (delivery review 2026-11-14): **undisclosed** `LamportFill.signatureBlock σ i` = `FunFamily.blocks n n σ i` (via `blocks_apply`; DL-9 class); near relatives `Blocks.flatten_ofFn_update` (`CommitmentLemmas.ofFn_update_eq`), `Averaging.expect_favourable_of_success` (`ProbComp` counterpart of `HardcoreBit.uprob_mul_le_uexp`). Overlaps with hash-sign are DL-42. Also the follow-up (Seyoon, 2026-11-14): restate the frozen `lamport_oneTimeSecure` hypothesis `f` over `Fin (var.eval n)` with a published reader, clearing its 16 seal-B failures. | `FunFamily.blocks`; `CommitmentLemmas`; `HardcoreBit` | Open (deferred) | Re-point `signatureBlock`; promote the averaging lemma; the frozen-statement restatement needs its own gate. |
| DL-44 | prf-mac fill (delivery review 2026-11-15): F-01 local `hadv` in `MAC/FromPRF/Bound.lean` re-proves public `ETTGame.prfAdv_eq_expect` (**ruling Seyoon 2026-11-15: promote now** to the PRF layer beside `prfAdv`, re-derive the ETT copy proof-only, re-point prf-mac); F-02 `decide_fnForge`'s `hw`/`htake`/`hdrop` restate list readings of `splitBits` (`take_ofFn_castLE`, `CollectionsHelpers.ofFn_drop_take`, `FromDiscreteLog.ofFn_splitBits_fst/_snd`); F-03 `PRFMAC.blocks`/`macState`/`hits_nil_iff` near `GGMRed.tblEnc`/`lookup` (cca2-ett `tblW`). The private `prfAdv_prfReduction` (`OracleFromPRF.lean`) is the same identity specialised (DL-40). | `TCSlib.Cryptography.prfAdv_eq_expect` (published in #314, merge `59c2c1fb`); the list readers above; `GGMRed.tblEnc` | Open (F-01 paid) | F-01 **paid**: promoted in #314 (ETT re-derived, LE-gate30), prf-mac re-pointed by LE-reuse `590d1a56` (#317, Gate 33). F-02/F-03 and the private `prfAdv_prfReduction` in the deferred cleanup. |
| DL-45 | learning fill (delivery review 2026-11-15): undisclosed `LearnPRF.uprob_eq_point` = `OneWay.uprob_eq_one_div_card` (reversed); inline re-proof of `MultiMsg.abs_uexp_sub_le_uprob` in `abs_gameProb_random_sub_half_le` (both re-pointed by maintainer LE-reuse `8befc589`, #313); private `length_blk` re-proves `MultiMsg.length_histBlock` for the disclosed private copy `blk` of `histBlock`; `flip0`/`flip0_flip0` = `flipBit`/`flipBit_flipBit` (BooleanAnalysis) and `flipAt` (DeterministicCC); `foldr_pairEncode_nil` reads `Strategy.encodeMsgs`; short-name clashes `relabel`/`relabel_eq` (DL-36 family) and `flipAt`. | `OneWay.uprob_eq_one_div_card`; `MultiMsg.abs_uexp_sub_le_uprob`, `length_histBlock`; `BooleanAnalysis.flipBit` | Open | Items 1–2 by LE-reuse at landing; the rest in the deferred cleanup. |
| DL-46 | prf-long fill (delivery review 2026-11-15, disclosed): `MultiMsg.encodeList_eq_flatMap` (`FromPRF/MultiMsgOut.lean`) is a third copy of public `encodeList_eq_flatMap` (`Asymptotic/BlockEncryptor.lean`) beside the frozen private copy in `FromPRF.lean` (now unused); reuse blocked by a private/public name clash. `histBlockLen` kept beside `histBlockLenOut` (different `PolyExpr` terms); `adviceBound` now unused. Near relatives: GGM `encodeHist_eq_histEnc`/`histEnc_append_single`/`length_histEnc`, `UniformTableauEmitter.encodeList_eq_flatMap`. | `encodeList_eq_flatMap` (to move to `EnsembleSecurity`, worker's promotion request) | Open (deferred) | Promote and delete the copies; remove the unused frozen items under a frozen-file exception in the cleanup. |
| DL-47 | Gate 32 staging (2026-11-15), pre-existing: copies of `((List.ofFn f).drop i).headD d = f i` and of its getD form `(List.ofFn f).getD i d = f i`, at the tip `e9998722`. Inline chain: `Pseudorandom/NextBit.lean:454` (`headD_drop, List.getD_eq_getElem?_getD, List.getElem?_ofFn`, the remnant of NextBit's private `headD_drop_ofFn` that dl-consolidation L1 deleted). Index-0 cases: `headD_ofFn_one` (`Foundations/BitLists.lean:75`), `GIZK.headD_ofFn_block` (`ZeroKnowledge/GraphIsomorphismZK/Closeness.lean:280`), private `eq_const_headD` (`Encryption/PublicKey/NonMalleability/Simulation/SimIND.lean:88`). getD forms: `GI.getD_ofFn_lt'` (`ZeroKnowledge/GraphIsomorphism/SoundnessRep.lean:61`), `GI.getD_ofFn_lt` (`ZeroKnowledge/GraphIsomorphism/Proofs.lean:818`), `GIZK.getD_ofFn_lt` (`ZeroKnowledge/GraphIsomorphismZK/Closeness.lean:110`), `ColProofs.ofFn_getD_lt` (`ZeroKnowledge/ThreeColoring/ProtocolProofs.lean:391`), Yao's private `getD_ofFn'` (`SecureComputation/Yao.lean:611`). Inline getD chains (`List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos …`): `ZeroKnowledge/ThreeColoring/Simulator.lean:861`, `ZeroKnowledge/ThreeColoring/Language.lean:429` (in private `ofFn_getD_tape`), `ZeroKnowledge/Encoding.lean:359`; the same getD chain also inline outside the cryptography files, in `TCSlib/Complexity/ClassNP/SAT.lean:149`, `TCSlib/Complexity/ClassNP/Tautology.lean:142` and `TCSlib/Complexity/SpaceComplexity/Codec/Word.lean:135` (`getD_encChunk`). **Extended by Gate 32 G32-01 (ruling Seyoon 2026-11-15: extend DL-47 and close), at the #316 head `c18afbe6`:** exact copy of the promoted statement: GGM `Pseudorandom/Functions/Asymptotic/GGM/Run.lean:449–450` (`step_eq`, local `hbit`, replacement `TCSlib.Cryptography.headD_drop_ofFn x ⟨d.i, hi⟩ false`); headD chain `Asymptotic/HardCoreLoops.lean:278–280` (`orbit_eq`); getD/ofFn computations: `SecureComputation/Garbling.lean:193–198` (private `map_range_getD_ofFn`) and `:375–380` (`garbledValues_getD`), `SecureComputation/Yao.lean:626–627` (`yaoBobTables_yaoMsg`), `Encryption/PublicKey/BitwiseCPA.lean:107–113` (private `ofFn_half`), `Encryption/PublicKey/OracleSecurity/PaddedCPA.lean:72–78` (private `ofFn_splitHalf_bit`), `Complexity/CircuitComplexity/CircuitEvalNP.lean:68–69` (`dagCktSatLang_mem_NP`), `PSubsetPPolyGadget.lean:188–190` (`runWith_embedGates_getD`), `PSubsetPPolyProgram.lean:383–387` (`progGates_values`), `PSubsetPPolyTableau.lean:127–132` (`snapEncode_injective`), `UniformTableauCircuit.lean:427–431` (private `tabSrc_eval`), `Complexity/Randomized/RandomWalk.lean:256–259` (`decodeIdx_succ_append`), `Complexity/ClassPSPACE/TQBF.lean:857–859` (private `codecRow_realize`), optional-access form `Cryptography/Encoding/BooleanVector.lean:168–171` (`expandPoly_encode`) and `Hashing/SIS/CollisionOutput.lean:237–243` (`collisionOutputPoly_pairEncode`). **sc-garble SG-F04 (ruling Seyoon 2026-11-15, ledger):** new inline getD/`List.ofFn` chain in `SecureComputation/Garbling/CoinBlocks.lean:73–74` (`getD_eq_getElem`, `getElem_ofFn`), same as Yao's private `getD_ofFn'`. **gsw-core GC-01 (review r1, 2026-11-16; info, disclosed; ledger):** new inline getD/`List.ofFn` chain in `AdvancedEncryption/Homomorphic/GSW/Eval.lean:262–264` (`eval_encrypts`, the input vertices; `List.getD_eq_getElem`, `List.getElem_ofFn`), at the #339 head `839f36cc` (the same lines in the delivered `d4ebb0be`). The brief's F4 route prescribed these two Mathlib lemmas; the nearest public getD form, `GI.getD_ofFn_lt'`, cannot be imported there. | `TCSlib.Cryptography.headD_drop_ofFn` (#316) | Open (deferred) | Ruling Seyoon 2026-11-15: pre-existing (merged before the promotion), recorded as debt and not re-pointed in #316. Re-point NextBit:454 and the index-0 cases onto `headD_drop_ofFn`, and the getD forms onto one shared getD reader, in the deferred cleanup. Yao's `getD_ofFn'` waits for sc-garble and sc-yao to land (`Yao.lean` is shared). **Cleanup plan (G32-01):** add one generic reader `(List.ofFn f).getD i d = f ⟨i, h⟩` (any type) derived from `headD_drop_ofFn` and `List.headD_drop`, then re-point every DL-47 copy onto it or onto `headD_drop_ofFn`, proof only, headers preserved, starting with the exact GGM copy; the `Garbling.lean`/`Yao.lean` copies wait for sc-garble and sc-yao to land. |
| DL-48 | sc-ot fill (delivery review 2026-11-15): F-02 `OT.splitLen` / `splitLen_symm_ofFn` (`SecureComputation/ObliviousTransfer/Simulators.lean`) restate public `coinsEquiv` (inverted) and `ofFn_coinsEquiv` (`Asymptotic/EnsemblesLemmas.lean:141,145`), body as private ElGamal `dlc_splitEquiv`; F-04 `OT.uprob_signedPredictor_false/_true` adapt `exists_pkPredictor` (`pkPredictor` has no public reader); F-07 near-relatives `GI.pairSndD_encodeMsgs` (for `getD_one_eq`), `predict_eq`, and promotion requests `negligible_finset_sum`, `statClose_prod_of_forall`, `exec_five`, `length_runAtL_le`. **Gate 34 G34-02 (ruling Seyoon 2026-11-15, ledger):** `OT.length_ofFn_coins` (`ObliviousTransfer/Simulators.lean:210–212`) is a verbatim copy of public `Composability.NMSim.length_ofFn_coins` (`Encryption/PublicKey/NonMalleability/Simulation/Rounds.lean:41–43`); direct reuse would add 69 NM modules to the OT closure. (G34-01, `OT.getD_zero_eq`/`OT.getD_one_eq'` re-proving `headD_drop`, is fixed by LE-gate34, not debt.) | `coinsEquiv`, `ofFn_coinsEquiv`; `exists_pkPredictor` | Open (deferred) | Ruling Seyoon 2026-11-15: ledger debt, disclosed (not fixed in the landing: reuse needs a new import and a definition change). Cleanup: replace `splitLen` by `(coinsEquiv h).symm`; publish `pkPredictor_apply` and re-derive the signed predictor from `exists_pkPredictor`; decide the promotion requests. G34-02 cleanup: promote `length_ofFn_coins` to the `NUPPT` layer (`Asymptotic/Adversary` or `Randomized/NonUniform`) and re-point both copies. |
| DL-49 | sc-compose fill (delivery review 2026-11-15, SC-F01; disclosed in the checkpoint REPORTs): helpers under `SecureComputation/ComposeSecurity/` restate public lemmas because the brief's two extra imports were read as exhaustive: a third `negligible_polyExpr_mul`; `appendCoins` (= `coinsEquiv`); `ofFn_blocks_symm` (= `FunFamily.ofFn_blocks_symm`); `polyTimeComputable_flatMap_range`, `flatMap_range_ite`, `iterSnd_poly`, `encodeMsgs_eq_flatMap`, `msgAt_encodeMsgs` and the `padTo` family (from `Composability/ZeroKnowledge/ThreeColoring/Machines.lean`). | `EnsembleLemmas.negligible_polyExpr_mul` (`Asymptotic/EnsemblesLemmas.lean:377`), `coinsEquiv`, `FunFamily.ofFn_blocks_symm`, the `ThreeColoring/Machines` helpers | Open (deferred) | Ruling Seyoon 2026-11-15: ledger debt. Cleanup: import the public lemmas (or promote the ThreeColoring helpers to a shared machine layer) and re-point the sc-compose copies proof-only. **Extended 2026-11-16 (ruling Seyoon, SY-F03):** also `YaoHybridProof.encodeMsgs_eq_encWords` (sc-yao #341, `SecureComputation/Yao/HybridProof/Lengths.lean:83`) and `SequentialZK.encodeMsgs_eq_encWords` (#327, `Composability/SequentialZK/Normalization.lean:40`). These are copies of each other: statements and proofs are identical up to bound-variable names (`L`, `w` against `h`, `m`), and the docstrings differ. Each is `encodeMsgs_eq_flatMap` with `BinArith.encWords_def`. Cleanup: keep one `encodeMsgs_eq_encWords` in a common home and re-point the rest. **Extended 2026-11-17 (Seyoon, Stage 1 ruling Q1; review CS1-F01):** S1-26 `Strategy.msgAt_encodeMsgs` (`ZeroKnowledge/EncodingMachines.lean`) is the promoted form of the public copies `ColZK.field_encodeMsgs` (`ThreeColoring/ColZKMachine.lean:142`, same statement) and `ColMachines.getD_eq_pairFstD_iterate` (`ThreeColoring/Machines.lean:951`, reversed); both are re-pointed in Stage 2 (maintainer addendum `cleanup-stage1/final-r1/stage2-addendum.tsv`). |
| DL-50 | gsw-security fill (#338; delivery review 2026-11-16, GS-01 with the GS-02 erratum; disclosed in the REPORT): F5's inline column hybrid (`Hashing/SIS/Columns.lean:95–192`, the shared-parameter planting hybrid) and F6's Regev-style hybrids (`AdvancedEncryption/Homomorphic/GSW/Security.lean:197–238` and `256–279`: the `abs_sub_le` triangle chain and the relabel-into-test steps). | `Regev/Experiments.lean:254–292` and `309–327`; the nearest generic relatives are `pairTuple`/`pairHybrid`/`pairRed` (`ZeroKnowledge/Commitment.lean:148–239`) and `distAdv_multi_le_sum` (`Encryption/PublicKey/EnsembleSecurity.lean:134`) | Open (deferred) | Ruling Seyoon 2026-11-16: ledger debt; Gate 43 CLEAR. Payback is promotion P-1 as restated in GS-02: generalize `pairHybrid`/`pairRed` with a shared parameter `κ`, then re-derive `distAdv_tuple_le_sum` and the `Columns` hybrid from it. |
| DL-51 | sc-yao fill (#341; delivery review 2026-11-16, SY-F02, undisclosed): `StatisticalSwitch.statClose_of_eq_off` and `distAdv_le_of_eq_off` (`SecureComputation/Yao/HybridProof/StatisticalSwitch.lean`), re-derived through `MultiMsg.abs_uexp_sub_le_uprob`. | `statClose_of_uprob_ne` (`Candidates/DDH.lean:145`) with `StatClose.mono` and `uprob_mono` | Open (deferred) | Ruling Seyoon 2026-11-16: ledger, then promote. Cleanup: move `statClose_of_uprob_ne` to `Asymptotic/Sampling` and re-point both users proof-only. A direct re-point now would pull `Candidates/DDH` into the Yao helpers. |
| DL-52 | sc-yao fill (#341; delivery review 2026-11-16, SY-F05 remainder; disclosed in the REPORT): `YaoHybridProof.OTAnswerWords.length_answersB` and `answersA_nil` (`SecureComputation/Yao/HybridProof/OTAnswerWords.lean:41`, `:94`), the bit-transfer instances (`outB = 1`, `outA = 0`). | `HybridProtocol.length_answersB` and `length_answersA` (`SecureComputation/ComposeSecurity/Lengths.lean:60`, `:52`; #324, merged) | Open (deferred) | Ruling Seyoon 2026-11-16: ledger, then re-point. In the post-merge cleanup (after #341 merges), derive both from the #324 lemmas with `otFunctionality`'s output lengths, proof-only. |
| DL-53 | `EncodingMachines` `padTo` family and `zeros_poly` (cleanup Stage 1, S1-27 under CS1-Q8, `ZeroKnowledge/EncodingMachines.lean`; checkpoint-1 review CS1-C1-F01/F04, worker note CS1-W1) | `EnsembleLemmas.padL`, `padL_eq`, `length_padL`, `polyTimeComputable_padL`, `polyTimeComputable_zeros` (`EnsemblesLemmas.lean:191–230`); `CollectionsLemmas.padStr` and its lemmas (`CollectionsLemmas.lean:75–114`); the `padSq` copies. Each family is derivable from the others; the constants differ. | Accepted (Seyoon, 2026-11-17, ruling CS1-C1-Q1: keep S1-27 as CS1-Q8 ruled, 69 declarations; the Stage 1 final discloses every overlap) | Consolidate the four families into one after the campaign merges into `main` (deferred). |
| DL-54 | (none landed: LE-ren drops the delivered `TreeCircuit.rename`, `rename_eval`, `depth_rename` from the GSW phase 6a statements, G6A-F01) | `TreeCircuit.reidx`, `reidx_eval`, `reidx_depth` (`BooleanAnalysis/LMN/CircuitReindex.lean:24/29/46`), which the 6a formula layer uses instead | Accepted (Seyoon, 2026-11-17, 6a ruling Q1) | Move the `reidx` family into the `Complexity/` formula combinators (`Combinators`) later, so the core formula layer need not import a `BooleanAnalysis/LMN` file (deferred, out of the Pass–shelat cleanup). |
| DL-55 | T1 `BilinearGen.bdhAssumption_of_dbdhAssumption`'s inline verdict identity (`decide ([b] = [true]) = b`, specialised to the solver-success bit; #340, `Pairing/Assumptions.lean:199`; Gate 44 G44-01) | `TrapdoorPredictor.decide_singleton_eq_true` (`Encryption/PublicKey/TrapdoorPredictor.lean:144`), in the public-key layer, which the pairing closure does not import | Accepted (Seyoon, 2026-11-17, Gate 44 G44-01) | **Cleanup Stage 2:** promote `decide_singleton_eq_true` to a shared low-level home importable by both layers, re-point `TrapdoorPredictor` and T1's proof (proof-only). |
| DL-56 | `poly_rU`, `poly_rZ`, `poly_rW`, `poly_rS` (#346, `IdentityBased/BonehBoyenMachine/Words.lean:261` and neighbours; disclosed with an API obstruction; Gate 44 G44-01) | `Games.polyTimeComputable_rU`, `_rZ`, `_rW`, `_rS` for the same `InteractiveHandler` projections (`Games/Efficiency.lean:538–550`) | Accepted (Seyoon, 2026-11-17, Gate 44 G44-01) | **Cleanup Stage 2:** re-point the four to the `Games/Efficiency` facts, adding a reader there if the recorded obstruction needs one (proof-only). |
| DL-57 | `BB1Sim.sidSpec_rng_one`, `sidSpec_rng_two`, the related `sidSpec_dom_*` and `zeroBits_eq_cast` (bb1-sim fill, `IdentityBased/BonehBoyenSecurity/`; disclosed; fill review BSF-F04) | T4's private `BB1Machine.sidSpec_rng_one'`, `sidSpec_rng_two'` (#346, `BonehBoyenMachine/Oracles.lean:77`, `:84`) | Accepted (Seyoon, 2026-11-17, bb1-sim fill ruling Q1) | **Cleanup Stage 2:** promote these scheme-generic facts into `IdentityBased/Defs.lean` as `IBEScheme.*` and re-point both the fill's and T4's copies (proof-only). |
| DL-58 | `bb1_sim_real`'s local `h01` (`∀ x y : ℝ, 0 ≤ x → x ≤ 1 → 0 ≤ y → y ≤ 1 → \|x − y\| ≤ 1`; bb1-sim fill #357, `IdentityBased/BonehBoyenSecurity.lean:128–134`; undisclosed, Gate 48 G48-01) | Mathlib `abs_sub_le_of_nonneg_of_le` (`Mathlib/Algebra/Order/Group/Abs.lean:119–124`, additive form; already used in `LWE/BitNoise.lean:110`) | **Repaid** (Seyoon, 2026-11-17: first accepted as debt, then fixed before Gate 48 round 2) | **Repaid in #357 by landing edit LE-g48** (`dfdc56f2`): `h01` deleted and the bad-coin branch closed with `abs_sub_le_of_nonneg_of_le` applied to the four `ProbComp.prob_nonneg`/`prob_le_one` bounds (proof-only). Nothing left for Stage 2. |
| DL-59 | `Games.extTape`, `extTape_of_lt`, `extTape_update` (cleanup Stage 1 S1-04, #355, `Games/Tapes.lean:139/144/156`; undisclosed; found by the Gate 47 pre-dispatch sweep, B1) | `extendStream`, `extendStream_def`, `extendStream_update_of_ne` (`Pseudorandom/Functions/LazySampling.lean:196/201/235`; Garg §3.4, Gate 04): identical body, `extendStream` more general (`Type*`); DL-40's `AdaptiveCPA.extTape` is a third copy of the same function | Accepted (Seyoon, 2026-11-17, Gate 47 pre-dispatch ruling B1) | **Cleanup Stage 2, with DL-40:** keep one family in `Games/Tapes` (stated at `Type*`), re-point `LazySampling`'s `extendStream*`, `AdaptiveCPA.extTape` and #355's users to it (proof-only re-points; any public name kept as a deprecated alias only if a consumer outside the campaign needs it). |
| DL-60 | Gate 47 pre-dispatch sweep, weaker overlaps (Seyoon, 2026-11-17, ruling B2–B7): **B3** the `padTo` family (S1-27) vs Batteries `List.takeD` and Mathlib `takeD_length`/`takeD_eq_take`/`takeD_left'`, and the bridge `CollectionsLemmas.ofFn_padFin_eq_take` (= `Universal.ofFn_getD_eq_take`) — extends DL-53; **B4** public special cases `Strategy.pairFstD_encodeMsgs` (S1-26 at `i = 0`) and `GI.pairSndD_encodeMsgs` (S1-20 at `i = 1`) — extends DL-49; **B2** S1-27's proved `polyTimeComputable_flatMap_range` vs the Complexity side's `FormulaKit.polyTimeComputable_flatMap_range` (`Complexity/FormulaKit/Emit.lean:127`, still `sorry`) — Complexity handoff item; **B5–B7** analogues in other models, not duplicates: GGM `take/drop_ofFn_splitHalves` (vs S1-11), `Unary.unary_chunks` (private, vs `flatMap_range_ite`), `AdaptiveCPA.expect_tapeImpl` and LazySampling `evalLazy_congr`/`uprob_evalLazy` (vs the Tapes family) | (as listed) | Accepted and disclosed | **Stage 2:** B3 with DL-53 (state `padTo` through `List.takeD` or re-point to it); B4 with DL-49 (re-point the two special cases to S1-26/S1-20). **Complexity handoff:** B2 (the Complexity `sorry` can cite the campaign's proved twin after the campaign merge). B5–B7: disclosure only. |

## ===== briefs/pass-shelat-ch5-8/maintenance/dw5/README.md (records, at 659542ecd9413b504d30da8c937b9805e6c1f71f) =====

# DW-5 · derand F-01: typed-view readers, then E1 and `polyTimeComputable_find` re-derived through them

**Result.** F-01's 20 Rule-10 seal failures (9 in E1 `computesFunInTime_find`, 11 in `polyTimeComputable_find`) are
cleared: the `IterateFind` seals give **0 errors in all four variants** (strict and coe, A and B), against 20 in each at
the base. The readers add no seal failure. The two reader owners, however, carry **26 pre-existing seal failures**
(ModuleHost 10, IterateFindHost 16) in declarations this change does not touch. Clearing those needs frozen-file changes
beyond the readers, so they are left as a scope question (below). Build, state check, axioms, admissions, statements, lint
and name clash are clean, and `dl-oleans-2` is restored to the snapshot.

Date: 2026-11-16 UTC. `$SP` is this session's scratchpad. All evidence is in `dw5-evidence.zip` under `dw5/`. Its
SHA-256 and every entry are listed in `SHA256SUMS`.

## Branch (local only, never pushed)
- **Branch:** `cleanup/dw5-derand-readers`, made in the limited worktree `$SP/wt-dw5` from the records tip.
  - The worktree was sparse: non-cone `/*`, without `briefs/`, `dataset/`, `blueprint/`, `dep_graph.json` and the PDF.
  - The records tip was taken with `git fetch origin cryptography/pass-shelat-ch2-4` by name:
    `2da7e0f3cd65ec93ed71813b7828c3b66ba18942`.
- **Commits** (both carry an SSH signature header; the signatures cannot be verified here because no
  `allowedSignersFile` is configured; files were staged by explicit path):
  1. `1da80d9a952c3da3e406f58188cca66de94cbfaf`: the readers (ModuleHost +97, IterateFindHost +30/−2).
  2. `daa6e173cdd94cad1475b9a96eca613bce53ba61` (**head**, tree `2ae32eb3`): the re-derivations (IterateFind +126/−294).
- In total, 3 files change, with 253 insertions and 296 deletions (`branch/`).

## The readers (formula docstrings; `rfl` or the original contract as proof; no `@[simp]`)
`TCSlib/Complexity/TuringMachine/Build/ModuleHost.lean`, namespace `Turing.ModuleHost`, in a new section
"The typed view of the host":
- `abbrev hostTMView M K hk ctrl ret q₀ : FinTM Bool` is `⟨K, State C M, (hostTM M K hk ctrl ret q₀).tm⟩`.
- `hostTMView_eq : hostTMView M K hk ctrl ret q₀ = hostTM M K hk ctrl ret q₀ := rfl`.
- `hostTMView_q₀ : (hostTMView M K hk ctrl ret q₀).tm.q₀ = q₀ := rfl`.
- `hostTMView_step_inl` is `hostTM_step_inl` for the view: `cfg.state = some (.inl c) →
  (hostTMView …).tm.step cfg = (ctrl c cfg.inputSymbol cfg.workTapeSymbols).apply cfg`. Its proof is `hostTM_step_inl …`.
- `host_call_view` is `host_call` for the view, with the same hypotheses and conclusion. Its proof is `host_call …`.
- `host_clean_view` is `host_clean` for the view. Its proof is `host_clean …`.

`TCSlib/Complexity/Randomized/Build/IterateFindHost.lean`, namespace `Complexity.IterateFind`:
- `abbrev copyTMView : FinTM Bool` is `⟨1, Fin 2, ⟨0, copyTM.tm.tr⟩⟩`.
  - This view makes the start state `0` explicit as well, because `host_call_view`'s hypotheses start the module at
    `(M i).tm.q₀`.
- `copyTMView_eq : copyTMView = copyTM := rfl`.
- `copy_clean_view (x)` is `copy_clean x` for `copyTMView`. Its proof is `copy_clean x`.

These are the SR-02 proposal (`fills/derand/final-r1/review-evidence.zip`, `logs/delivery-extracts/scope-request/SR-02/`)
with one change: `copyTMView` fixes `q₀ := 0`, where SR-02's view reused `copyTM.tm`. Both modules' docstrings list the
new declarations. No existing declaration, definition, proof or attribute changes in either file.

## The re-derivations (proof-only; IterateFind)
- **E1 `computesFunInTime_find`.**
  - The host is `ModuleHost.hostTMView M (K + 1) hk (hostCtrl M K) (hostRet M) (entry M 0)`, and module 0 is
    `copyTMView`.
  - The calls go through `host_call_view` and `host_clean_view`, and the start state through `hostTMView_q₀` and
    `initCfg_ofWords`.
  - The three control steps (dispatch, branch, halt) are derived in the proof from `hostTMView_step_inl` and
    `hostCtrl_eq`. Seams are read through the published `Cfg.ofWords_*` readers and `stateWord_eq`.
  - The loop combinator's result is matched by cases on the search, which removes the 9th, matcher-transport failure.
  - The module now builds with 0 warnings; at the tip it had 12, from unused simp arguments.
- **`polyTimeComputable_find`** is re-derived **from E1**, with `init = id`, fuel `R.eval` and the same fuel machine as
  before; `final_bound` is kept as its normal form. This is derand F-03's pre-approved re-derivation, and it removes
  E1's 196-line repetition of the old assembly.
  - The theorem moves below E1, which it now uses. Its header and prose are byte-identical.
  - The frozen check (`statements/frozencheck.txt`) reports exactly that one ORDER difference, and no header, prose or
    body difference. Its control (`frozencheck-control.txt`) detects a one-character prose change.
- **Sketches.** Both proof sketches were refreshed, because the route changed. The statement paragraphs are unchanged.

## Checks (tree `$SP/dl-oleans-2` only; one Lean process at a time; no lake, no cache get)
- **Preflight.** The snapshot (`tree/snapshot-pre.txt`) has 1230 files and SHA-256
  `457ba704d26757307f14131aa534929ffd70d30a732b0c744b104ca3fc96a15f`, as required. `$SP/dl-oleans` was not touched.
- **Build** (`build/`). The sc-yao and int-tip method, with unmodified copies of the tools (`tools-used/`):
  - **Order and plan.** `downorder.py` against the snapshot base `eff2dcd0` gives changed 183, down 706 and order 1342.
    The order is the closure of root `TCSlib` and both `audits/*/Checks`.
  - **State.** `stateplan.py init` keys 1199 modules, and its `state-init.json` is byte-equal to int-tip's.
  - `plan` gives 706 to build (563 snapshot oleans and 143 new) and 636 to reuse.
  - **Mathlib.** The overlay (3346 symlinks) plus NthRootLemmas (olean `c0a9cff0…`), the only missing Mathlib root.
  - **Backup.** A hard-link copy of all 1230 snapshot files, hash-checked.
  - **Result:** 706/706 rc 0. `error:` 0, `error(` 0, combined 0, and the substring "error" 0 (`build/per-module.tsv`).
  - Sorry warnings: 91.
  - Runtime: 6417 s of module time, 19:57–21:44 UTC. Max RSS was 4.49 GB, and the lowest free disk was 1542 MB.
- **State check.** `update` took 706 modules, and `check` over the 1342-module order gives 1342/1342 OK, RESULT OK
  (`build/statecheck.txt`).
- **Rule 10** (`rule10/`, driver `tools-used/rule10_dw5.sh`; `rule10_b.sh` and the archived Gate 06/10 harness
  unmodified; `lean -DmaxErrors=0`; both error forms counted).

  | Owner | Requests (A/B) | Errors at the base (each variant) | Errors at the head: strict A, strict B, coe A, coe B | Install / EOF |
  |---|---|---|---|---|
  | IterateFind (F-01) | 595 / 596 | 20 = E1 9 + `polyTimeComputable_find` 11 | **0, 0, 0, 0** | yes |
  | ModuleHost | 241 / 241 | 10 (pre-existing) | 10, 10, 10, 10: identical to the base, none in a reader | yes |
  | IterateFindHost | 251 / 251 | 16 (pre-existing) | 16, 16, 16, 16: identical to the base, none in a reader | yes |

  - **The baseline is F-01's 20.** The tip baseline (`base-seals/`) has the same 20 messages at the same positions as
    the derand review's F-01 log.
  - **Head against base** (`compare/seals-base-vs-head.txt`):
    - Every request row is identical.
    - IterateFind: all 20 are cleared, and nothing is new.
    - The reader owners' failures are identical in declaration and message.
  - **Strict and coe** probes are byte-identical, because no projection-coercion instance is in these closures.
  - **The typed views** are reducible abbreviations. The seal excludes them as notation (`term_excluded: abbrev`),
    while `hostTM` and `copyTM` stay sealed rows.
  - **Paired controls** (`tools-used/mkctl_dw5.py`, the derand generator's harness, with one row per new reader):
    - Each harness has 8 probes and gives ALL_OK True, in strict and in coe.
    - The 29 expected sealed negatives fail exactly once each. The negatives are the `rfl`/definitional transports
      through `hostTM` or `copyTM`.
    - The readers pass, the unsealed probes give rc 0, and there are no stray errors.
  - **Explicit-unfold scan** (`scan/`):
    - Touched declarations: 128 items and **0 foreign**.
    - The three files have 27 pre-existing foreign items. They are identical at the base (`scan/scan-base-vs-head.txt`)
      and all sit in IterateFindHost's untouched `copy_*` and `host_branch` proofs.
- **Axioms** (`axioms/`, the derand census probe with the readers added).
  - The two re-derived theorems, the 9 readers, and everything F-01/derand cited downstream use only `propext`,
    `Classical.choice` and `Quot.sound`. That covers 27 printed constants, among them
    `polyTimeComputable_iterateFind`, `exists_seedMajorityTM`, `seedMajority_mem_DTIME`, `bpp_subset_dtime_subexp`,
    `inBPP_iff` and the Derand helpers.
  - The census of the three owners has 193 stored constants, all standard. `sorryAx` does not occur.
- **Admissions** (`admissions/`, `tipcensus.py`; each module's sorry count is taken from build records whose source matches
  it): 229 at the tip and 229 at the head, identical per module.
  - The three changed modules have 0 at both revisions, and none of the three files contains `sorry`.
  - The same 34 modules have no record at either revision; they lie outside the order.
- **Statements** (`statements/decls2.tsv`): 9 ADDED (exactly the readers above), 0 CHANGED, 0 REMOVED.
- **Lint** (`lint/`).
  - `campaign_style_lint.py TCSlib/Complexity` gives 25 FAIL and 338 WARN at both the base and the head; only INFO lines
    change (file sizes and declaration counts).
  - `style_lint.py --area Complexity` gives identical output.
  - All lines are within 100 characters, and there is no trailing whitespace.
- **Name clash** (`checks/nameclash.txt`): 0 exact full-name clashes. The 9 new names have no same-short-name declaration
  elsewhere.
- **Restore** (`restore/`):
  - Of the snapshot files, 41 were restored and the other 1189 were unchanged.
  - The 143 new oleans and the Mathlib overlay (3346 symlinks and 1 file) were deleted.
  - **SNAPSHOT EQUAL** (`457ba704…`). restoreplan reports extra 0, changed 0 and missing 0.
  - An independent recheck gives the same: SNAPSHOT EQUAL; 0/0/0; no symlinks, no `Mathlib/` and no empty directories.
  - Then the backup, the probes and the worktree were removed, and the branch was kept (`cleanup.txt`).

## Disclosures
- **Duplication.**
  - E1's proof derives the three control steps (`hdisp`, `hbranch`, `hhalt`, about 30 lines) at the typed view from
    `hostTMView_step_inl` and `hostCtrl_eq`. This restates the content of the public `host_dispatch`, `host_branch` and
    `host_halt`.
  - Those originals cannot be used at the view, because their statements read `hostTM`'s fields by definition.
  - The readers `host_call_view`, `host_clean_view`, `hostTMView_step_inl` and `copy_clean_view` restate `host_call`,
    `host_clean`, `hostTM_step_inl` and `copy_clean` at the typed views, by design, as in SR-02.
  - Net effect: E1's 196-line repetition of `polyTimeComputable_find` (F-03) is gone.
- **No longer used.** Nothing in the library now uses `IterateFind.host_dispatch`, `host_branch`, `host_halt`,
  `IterateFind.hostTM` or `copyTM_k`. The private `dupWord_poly` is now unused too. It is kept, because deleting it would be
  a REMOVED statement.
- **Order.** `polyTimeComputable_find` moved below E1, as described above.

## Scope question (for Seyoon)
Both reader owners became "changed owners" by gaining the readers, and their whole-file seals show 26 pre-existing
failures, unchanged by this work:
- **ModuleHost (10):** `stop_step`, `stop_clean`, `clean_install`, `clean_emit`, `pad_seam`, `pad_apply`, `pad_run`,
  `host_seam` and `host_call`.
- **IterateFindHost (16):** six in `copy_step`, `copy_turn`, `copy_rewind`, `copy_finish` and `copy_clean`, and ten in
  the **statements** of `host_dispatch`, `host_branch` and `host_halt`. Those statements type `(hostTM M K hk).tm.step`
  on `Cfg.ofWords (.inl c) …`, which needs `hostTM`'s `State` field by definition.
- The same untouched IterateFindHost proofs hold the scan's 27 foreign explicit items.

Clearing them needs proof changes in these frozen files, and for the three `host_*` statements a statement change or
their replacement by typed-view versions. That is beyond the readers, so nothing was done. Options:
- (a) **Recommended:** record them as a new deferred item, gated separately, and take DW-5 as clearing F-01's 20.
- (b) Extend DW-5 to clear them, with Seyoon's approval of the frozen proof edits and of a statement route for
  `host_dispatch`, `host_branch` and `host_halt`.

## Layout of `dw5-evidence.zip` (`dw5/`)
- `branch/`: branch facts, raw diff, per-commit diffs and the head sources of the 3 files.
- `tree/`, `order/`, `plan/`, `state/`, `build/`, `build-mathlib-extra/`: preflight, order, plan, state, build records
  and logs, and the state check.
- `base-seals/`: the tip baseline seals (collector, probes, logs, `touched-tip.json`).
- `rule10/`: head collector, axioms probe, seals strict/coe A/B, controls, ctlcheck, sealsum and probe sources.
- `compare/`, `scan/`, `axioms/`, `admissions/`, `statements/`, `lint/`, `checks/`.
- `restore/`, `restore-pre-delta/`, `cleanup.txt`.
- `dev/`: non-canonical development iterations on uncommitted sources (`devseal.py`/`devcheck.sh`). The reported
  results are the head runs above.
- `tools-used/`: every script run.
  - Unmodified copies: int-tip's build tools and gate40-seals-merged's seal suite (`seal/`).
  - New for this job: `rule10_dw5.sh`, `mkctl_dw5.py`, `run-build.sh`, `diskwatch.sh`, `restore-dw5.sh`,
    `seals_dev.sh`, `devseal.py` and `devcheck.sh`.
  - Copied from the derand review: `frozencheck.py`. Copied from sc-yao: `nameclash.py`.

## ===== briefs/pass-shelat-ch5-8/cleanup-dw10/handoff-complexity/README.md (records, at 659542ecd9413b504d30da8c937b9805e6c1f71f) =====

# DW-10 handoff: recorded seal debt in Complexity-library files

The Pass–shelat campaign's seal-debt inventory (DW-10) found recorded Rule 10 items in 21 files of the Complexity
library, outside the campaign. Seyoon ruled on 2026-11-17: "Arora–Barak material that needs fixing: send me a pasteable
prompt I can give to a different chat. You are responsible for any seals from cryptography content." This folder is
that handoff: the items (`items.tsv`), these notes, and the prompt for a separate chat (`prompt.md`). The campaign's own
inventory job (`../issued-r1/`) does not seal or scan these files; it carries their items as HANDED-OFF.

## What a Rule 10 seal is

Rule 10 (`policy.md` §1, *Definitions land with their lemmas*): a proof reads another file's TCSlib definition only
through the lemmas published beside it (its equation `_eq`, `_apply`, `_iff`, `simps` projections, case lemmas or
contract), never by unfolding it. Core and Mathlib definitions may reduce in a `rfl`, `decide` or `show` step but are
never passed to `simp`, `rw` or `unfold`. Reducible abbreviations are notation and are never sealed.

A **whole-file seal** checks this mechanically. A probe module holds the file's own source bytes behind a harness that
installs `attribute [local irreducible]` on every ordinary TCSlib definition of the file's transitive import closure
(kind `def`, a matcher or not reducible), with install and EOF records that state how many requests were installed
and verified. The probe is elaborated with `lean -DmaxErrors=0` (Lean's default cap of 100 errors once truncated a
`CodeSimulator` seal: finding C-F02). Every error is a place where the proof relied on unfolding a foreign definition.
Explicit reads (a foreign definition passed to `simp`, `rw`, `unfold` or `delta`) do not always fail under a seal, so
an **explicit-unfold scan** lists them separately; a third check lists stored proofs that reference a foreign
definition's generated equation (`eq_1`, `eq_def`).

**Variants.** **A** treats `Complexity.PolyExpr.eval` as notation (ruling of 2026-11-07); **B** seals it too. **Strict**
seals the projection-coercion instance `FinDist.instCoeFunForallReal`; **coe** treats it as notation (Q3, Seyoon
2026-11-17). **Coe-A is canonical**: a failure only under B or only under strict is recorded, not fixed (B-only items
go to Seyoon for a ruling; strict-only ones need nothing).

## The canonical tooling, by path

- `scripts/lean_check_tree.sh`: one module per `lean` process into a scratch olean tree (`lake build` is banned).
- The seal suite as the campaign's DW-5 job ran it: `briefs/pass-shelat-ch5-8/maintenance/dw5/dw5-evidence.zip`
  (SHA-256 `12abc05a61c08de7cb38b9d3bccdea5b3dd44dff6f65f036a50584a39e1dd630`), under `dw5/tools-used/`:
  `seal/rule10_b.sh` (the driver of the four variants and the controls), `seal/runner_full.py` (`lean -DmaxErrors=0`,
  no `-o`), `seal/review/mkcollect.py` with `NmCollect.template.lean` (the collector: definitions, closures, stored
  constants), `seal/review/mkseals_ab.py` (strict; `SEAL_EVAL=1` gives B), `seal/review/mkseals_coe.py` (coe),
  `seal/review/sealsum.py`, `seal/review/ctlcheck2.py`, `seal/review/touched.py`, `seal/review/archived-gate10-tools/`
  (the instrumenter, used unmodified), `seal/scan1_g40.py` and `seal/scan2.py` (the explicit-unfold scan),
  `rule10_dw5.sh` and `mkctl_dw5.py` (an owner-level driver and a paired-control generator). DW-5's
  `briefs/pass-shelat-ch5-8/maintenance/dw5/README.md` shows a complete run.
- The most recent adaptation of the same suite: branch `exchange/pass-shelat-ch5-8` at
  `d929cc21ec817b2518d57a7262e42744728f029a`, `inbox/fills/bb1-sim-statements/evidence/tools/` (`drivers/rule10_stmt.sh`
  and `seal/`).
- `SEAL_CHUNK` splits request sets above about 2,500 rows (one harness command overflows Lean's stack at 2,921).

## How items are fixed

By **readers** added next to the definition being read (an equation or case lemma, a formula docstring, no
`@[simp]`), then the failing proof re-derived through them; or by a **proof-only re-derivation** through readers that
already exist. **No statement changes**: a failure that sits in a declaration's statement is reported, not fixed.

## The items (`items.tsv`)

608 rows, one per recorded item located in the 21 files at the campaign base `f472accd5e000a53d0fbe02b5414435429ce4a70`
(Lean equal to `a6d01b1bd1a92e2ac0be9999689467fea7e4e77b`). Columns: `item_id`, `source`, `kind`, `file`,
`declaration`, `detail` (line and message or item at the record), `reads` (the definition read and its home module,
where the record gives it), `record_status`, `record_path` (the record in this repository; a `.zip:` path names the
entry). Sources:
- **#248 historical observations** (`H:<row>`, 9): the PR #248 ledger's original rows, with #248's disposition.
- **#248 current observations** (437): what the ledger retained at #248's merge: `SEAL-…` seal diagnostics (161),
  `C1-…` explicit reads (275), `C3-…` generated-equation reads (1).
- **Provider pairs** (`EFF72:`/`LEV52:`, 102): proofs in these files that two campaign fills cite (the efficiency fill
  #285 and the Levin padding proof #286) under Seyoon's 2026-11-10 provider rulings, with both ends: the failing
  declaration here and the citing fill. Each repeats a `SEAL-…` row of the current observations (53 distinct
  diagnostics).
- **SY-F07** (2): `CircuitComplexity/Uniform`'s 4 canonical-A failures in 2 declarations (readers such as
  `isFaninTwo_iff` now exist).
- **C-F02** (58): `TuringMachine/CodeSimulator`'s 177 seal errors in 58 declarations, identical in all four variants
  (1,232 requests).

The records are at #248's head or later revisions; files have moved since, and the `file` column is the static
location at the base. Line numbers are the record's.

## Counts per file

| File | #248 historical | #248 current | provider pairs | SY-F07 | C-F02 | Total |
|---|---|---|---|---|---|---|
| `Complexity/CircuitComplexity/PPoly` |  | 7 |  |  |  | 7 |
| `Complexity/CircuitComplexity/Uniform` |  |  |  | 2 |  | 2 |
| `Complexity/ClassNP/PolyTime` |  | 8 | 12 |  |  | 20 |
| `Complexity/ClassNP/PolyTimeBlockLoop` |  | 24 | 1 |  |  | 25 |
| `Complexity/ClassNP/PolyTimeBlockTests` |  | 2 |  |  |  | 2 |
| `Complexity/ClassNP/PolyTimePairing` | 9 | 4 | 7 |  |  | 20 |
| `Complexity/ClassNP/PolyTimePrefix` |  | 4 | 2 |  |  | 6 |
| `Complexity/ClassNP/Reductions` |  | 39 |  |  |  | 39 |
| `Complexity/ClassP/BinaryArith/AddSub` |  | 16 |  |  |  | 16 |
| `Complexity/ClassP/BinaryArith/Words` |  | 12 |  |  |  | 12 |
| `Complexity/ClassP/P` |  | 4 |  |  |  | 4 |
| `Complexity/Randomized/Adleman` |  | 2 |  |  |  | 2 |
| `Complexity/Randomized/PolyTimeModel` |  | 21 |  |  |  | 21 |
| `Complexity/Randomized/SipserGacs` |  | 13 |  |  |  | 13 |
| `Complexity/TuringMachine/Build/Convention` |  | 2 |  |  |  | 2 |
| `Complexity/TuringMachine/Build/Wrappers` |  | 81 | 40 |  |  | 121 |
| `Complexity/TuringMachine/CodeSimulator` |  |  |  |  | 58 | 58 |
| `Complexity/TuringMachine/Deterministic` |  | 8 | 2 |  |  | 10 |
| `Complexity/TuringMachine/Encoding` |  | 13 |  |  |  | 13 |
| `Complexity/TuringMachine/Simulation` |  | 96 | 38 |  |  | 134 |
| `Complexity/TuringMachine/UniversalBlock` |  | 81 |  |  |  | 81 |
| **Total** | 9 | 437 | 102 | 2 | 58 | 608 |


## Addendum (2026-11-17): Gate 47 pre-dispatch sweep, B2

The campaign's Stage 1 (#355, S1-27) proves `polyTimeComputable_flatMap_range` in `ZeroKnowledge/EncodingMachines.lean`;
the Complexity side's `FormulaKit.polyTimeComputable_flatMap_range` (`Complexity/FormulaKit/Emit.lean:127`) has the same
statement (pair order swapped) and is still `sorry`. After the campaign merges into `main`, the Complexity fix can cite or
re-point to the proved twin (ledger DL-60, B2).

## ===== briefs/pass-shelat-ch5-8/maintainer/olean-snapshot-6-adopt/README.md (records, at 659542ecd9413b504d30da8c937b9805e6c1f71f) =====

# Olean snapshot #6: adoption at the #357 merge (2026-11-17)

- **New T:** `8060f6b767da9e43d1c1f6d32c55b97758b80bd8` (merge of #357 into `cryptography/pass-shelat-ch2-4`).
- **Source:** LE-g48's replay `olean-replay-bb1sim-g48` of #357's head `dfdc56f21898abe2d9d6cef83b0cfe57da87d28d`, audited CLEAR in Gate 48 round 2.
  - Before adoption it rehashed against its recorded map (`mapnoml.py`, `0858dccb…`): 1463 files, 0 extra / 0 changed / 0 missing, 3346 `Mathlib/` symlinks, NthRootLemmas `c0a9cff0…` (`replay-verify.out`).
  - Its checked state (LE-g48 `state.json`, SHA-256 `78f0d483…`) at `dfdc56f2` over the 1432-module order: RESULT OK (`replay-statecheck.out`).
- **Step-3 diff** of the merge against `dfdc56f2` (`*.lean`, `lean-toolchain`, `lake-manifest.json`; `lakefile.lean` included): empty (`step3-diff.txt`).
- **Snapshot #5 at retirement:** 0/0/0 against `fca1b6a3…` (`v5-final/`).
- **Adoption:** `Mathlib/` overlay removed (3346 symlinks + the overlay NthRootLemmas olean, as at #5); map `olean-snapshot.map-8060f6b7.tsv`, SHA-256 `0858dccbee016da1da450f2b2ca0d1f5094ee42646b9496d5278f2b45cb07caf` (= the audited g48 map, byte-equal), 1463 entries (TCSlib 1430, audits 2, PFR 31); files manifest SHA-256 `1ae04ef5f80e99b331d5062546831c9a180354a88181d4233d5eacf57433c86e`, 1463 files.
- **basecheck:** init at `8060f6b7` (1432 modules; `state-init-8060f6b7.json.gz`) against g48's checked state: RESULT OK (`basecheck.out`).
- **Swap:** #5's directory deleted (no Lean process running; other replay trees keep their hard links); g48 moved to `$SP/olean-snapshot`; rehash 0/0/0 (`v6/`). `olean-replay-bb1sim` (#357's pre-LE-g48 replay) deleted (superseded). #5's map and files manifest are kept in `$SP`.
- Not adoptable any more (built on #5 without #357): `olean-replay-cs1` (TS1), `olean-replay-6a-o1`, `-6a-stmt`, `-6a-stmt-g45`, `-6a-readers`, `-6a-fill12`, `-6a-fill86` — each re-replays on #6 before merge-time adoption.

## ===== inbox/fills/cleanup-stage1/REPORT.md (exchange delivery, at 5451d3cd6fa9b8c313c9f18f5a4da3542c85f02a) =====

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

## ===== inbox/fills/cleanup-stage1/evidence/reuse/reuse-table.md (exchange delivery, at 5451d3cd6fa9b8c313c9f18f5a4da3542c85f02a) =====

# cleanup-stage1 · Overlap and reuse (check 12)

For each target: the searches run, their hits, the verdict, the brief's copy list (confirmed at the
check tree `01cc6259…`, paths under `TCSlib/Cryptography/` unless they start with `TCSlib/`) and the
further copies found (added to the Stage 2 re-point table). Searches for every target:
(1) `grep -rn` of the short name over `TCSlib/` and `audits/`; (2) `grep` for the conclusion's shape and
the proof's characteristic rewrite chain; (3) `grep` of the name and shape over Mathlib
(`.lake/packages/mathlib/Mathlib`), Batteries and the toolchain's `src/lean`; (4) `exact?` on the
statement at the **check base** (oleans of the base snapshot), importing the home(s), for every target
whose statement needs no new definition (`Probes/ReuseLead.lean`: 6 calls; `Probes/ReuseAB.lean`: 17
calls; raw logs `exact-lead/`, `exact-ab/`). Lead searches: `lead-tcslib-grep.txt`,
`lead-shape-grep.txt`; sub-agent searches: `subagents/A/NOTES.md`, `reuse-grep-1.txt`,
`copylist-check.txt`; `subagents/B/NOTES.md`.

**Result: no E-DUP.** No target exists publicly in an equal or more general form that the brief does not
already list as a Stage 2 copy, with one disclosed overlap put to Seyoon (CS1-W1, `zeros_poly`).
`exact?` closed 1 of 23 statements at the base (S1-16, by unfolding a definition; see there) and
suggested one generic core relative (S1-04 `ovr_append`).

| Target | Verdict | Copies (brief), confirmed | Further copies / relatives found |
|---|---|---|---|
| S1-01..03 `host_*_view` | fresh; no other typed-view step lemma | `TCSlib/Complexity/Randomized/Build/IterateFind.lean:373`, `:378`, `:390` (issue base); originals `IterateFindHost.lean:352`, `:364`, `:380` (DW-9's) | none |
| S1-04 `Games.expect_simulate_abs`, `_inv` | equal copies only in `ETTGame` (listed); `exact?` at base: none | `Encryption/PrivateKey/EncryptThenTag/Tools.lean:65`, `:88` | none |
| S1-04 `freshImpl`, `_apply` | listed copy | `…/EncryptThenTag/Tools.lean:116`, `:122` | consumers `…/EncryptThenTag/Games.lean:356` (`ettImpl_eq_freshImpl`), `…/EncryptThenTag/Lazy.lean:445` (`ettLazy_eq`) |
| S1-04 `tapeImpl`, `_apply`, `simulate_tapeImpl_congr`, `expect_simulate_tapeImpl` | listed copies | `…/EncryptThenTag/Tools.lean:130`, `:135`, `:145`, `:167` | near relatives (CS1-Q10, not instances): `AdaptiveCPA.tapeImpl` / `simulate_tapeImpl_congr` (`Encryption/PublicKey/AdaptiveCPA/Hybrid.lean:116`, `:170`) |
| S1-04 `extTape`, `_of_lt`, `_of_not_lt`, `_update` | listed copies (`_of_not_lt` is new: the second case reader) | `Encryption/PublicKey/AdaptiveCPA/Hybrid.lean:211`, `:215`, `:221` | consumer `Encryption/PrivateKey/EncryptThenTag/Reduction.lean:93` (`dTapes_eq`, uses `AdaptiveCPA.extTape`) |
| S1-04 `ovr` family, `expect_sample_ovr` | listed copies; `exact?` on the generic fold form of `ovr_append` suggests core `List.foldr_append` (a relative: `ovr` is a structural recursion, not syntactically a `foldr`) | `…/EncryptThenTag/Tools.lean:219`, `:224`, `:228`, `:234`, `:246`, `:262`, `:281`; `…/EncryptThenTag/Lazy.lean:175` (`ovr_append`) | consumer `Authentication/MAC/FromPRF/Random.lean:125`; private relatives `…/EncryptThenTag/Lazy.lean:271`, `:283` (`ovr_append_of_mem`/`_of_not_mem`, special forms); `PRFGame.ovr` (`…/OracleFromPRF/Lazy.lean:102`) near relative (CS1-Q10) |
| S1-05 `EffFill.length_le_length_encodeLog` | private copies only; `exact?` at base: none | `…/EncryptThenTag/Machines.lean:95`, `Encryption/PublicKey/NonMalleability/Indistinguishability/Forward.lean:108` | none |
| S1-06 `zipWith_xor_cancel_right` | other orientation `zipWith_xor_cancel_left` (equal lengths, different statement); Mathlib `List.zipWith_zipWith_left/right` are reassociations; `exact?`: none | `Encryption/PrivateKey/FromPRF.lean:174`, `FromPRG.lean:147`, `SecureComputation/SpecialEncryption.lean:101`, `Encryption/PrivateKey/EncryptThenTag.lean:338`, `…/EncryptThenTag/Lazy.lean:295` | none |
| S1-07 `recordBits` + readers | listed copies | `…/EncryptThenTag/Handler.lean:134`, `:139`, `:143`, `:147`; `…/OracleFromPRF/Handler.lean:109`, `:114`, `:117`, `:121` | near relative (an optional word, not `Fin w → Bool`): `Encryption/PublicKey/BitwiseCPA/QueryHandler.lean:266`, `:345`, `Encryption/PublicKey/BitwiseCPA.lean:270` |
| S1-08 `NUPPT.eval_toOracleAdversary_padFin` | the three listed copies are instances (ETT `a=b=ℓ`, `a'=b'=ℓ'`; PRF `a=b=n`, `a'=b'=m`; MAC `a=b=n`, `a'=m₁`, `b'=m₂`); `exact?`: none | `…/EncryptThenTag/Machines.lean:348`, `…/OracleFromPRF/Reduction.lean:228`, `Authentication/MAC/FromPRF/Bound.lean:48` | none |
| S1-09 `FunFamily.ofFn_blocks_symm_eq_flatMap` | `EnsembleLemmas.ofFn_blocks_symm` (listed, through the alias); `FunFamily.ofFn_blocks_symm` (`Asymptotic/OneWay.lean:380`, downstream, `flatten` conclusion: a different form); `exact?`: none | `Asymptotic/EnsemblesLemmas.lean:433` (+ the six/seven DL-35 changes, Stage 2) | none |
| S1-10 `Bridge.expect_sample_eq_uexp` | listed public copy; `exact?` at base: none | `Hashing/FromDiscreteLog/Probability.lean:40` | none |
| S1-11 `ofFn_splitBits_fst/_snd` | listed copies; `exact?`: none | `Hashing/FromDiscreteLog/Encoding.lean:45`, `:55`; `Authentication/MAC/FromPRF/Reduction.lean:140`, `:145`, `:147` | **further inline copies:** `Authentication/Signatures/Lamport/MachineSpec.lean:259`, `Authentication/Signatures/HashAndSign/CollisionHandler.lean:464` |
| S1-12 `OracleComp.exists_eq_pure_of_costBoundedBy_zero` | listed copies; Mathlib `eq_pure_of_*` are filter lemmas (unrelated); `exact?`: none | `Authentication/Signatures/HashAndSign/OneQuery.lean:36`, `Authentication/Signatures/Lamport/Planted.lean:226` | none |
| S1-14 `PrivateKeyScheme.encodeList_eq_flatMap` | `TCSlib.Cryptography.encodeList_eq_flatMap` (`Asymptotic/BlockEncryptor.lean:60`) is public with the equal statement, **listed by the brief as the Stage 2 copy** (DL-46: the general home is beside the definition); not a new E-DUP; `exact?`: none | `Asymptotic/BlockEncryptor.lean:60`, `Encryption/PrivateKey/FromPRF/MultiMsgOut.lean:65`, `Encryption/PrivateKey/FromPRF.lean:251` (private) | consumers of the BlockEncryptor form: `Authentication/Signatures/Lamport/MachineSpec.lean:49`, `Authentication/Signatures/Lamport.lean:582`, `Encryption/PublicKey/HybridMachine.lean:216`, `:217`, `SecureComputation/Yao/HybridProof/SliceReconstruction.lean:274`; forbidden-directory relative `TCSlib/Complexity/CircuitComplexity/UniformTableauEmitter.lean:256` |
| S1-15 `getD_ofFn` | no `List.getD_ofFn` in core/Batteries/Mathlib; `exact?`: none | all 22 lines of the brief confirmed | **further inline copy:** `SecureComputation/Yao/HybridProof/RowFromCoins.lean:416` (in `assignmentBit_of_perm`, `:408`); near relative `Yao/HybridProof/BobIO.lean:164` |
| S1-16 `NUPPT.length_ofFn_coins` | `exact?` at base closes it with core `List.length_ofFn`, **by unfolding `NUPPT.coinLen`** (Rule 10 forbids this for consumers): no equal reader-form exists; listed copies | `Encryption/PublicKey/NonMalleability/Simulation/Rounds.lean:41`, `SecureComputation/ObliviousTransfer/Simulators.lean:210` | **further inline copies:** `Asymptotic/CollectionsHelpers.lean:112`, `Hashing/FromDiscreteLog.lean:97`, `:134`, `Asymptotic/Collections.lean:796`, `:804` |
| S1-17 `pkPredictor_apply` | fresh (no reader of `pkPredictor`); near relative `owpPredictor_apply` (`Pseudorandom/GeneratorFromPermutation.lean:96`) | Stage 2 lines `SecureComputation/ObliviousTransfer/ViewB.lean:71`, `:101`; `exists_pkPredictor` `Encryption/PublicKey/Trapdoor.lean:337` (base; head `:347`); `ObliviousTransfer/Simulators.lean:52`, `:57`; `Asymptotic/EnsemblesLemmas.lean:141`, `:145` | none |
| S1-18/19 `encodeMsgs_eq`, `encodeMsgs_eq_flatMap` | listed copies; `exact?`: none | `Randomness/Learning/Sample.lean:58`, `SecureComputation/ComposeSecurity/Machines.lean:150`, `ZeroKnowledge/ThreeColoring/Machines.lean:912`, `ZeroKnowledge/ThreeColoring/SimulatorNumeric.lean:503` | relative (append form, not a copy): `CommitmentLemmas.encodeMsgs_append` |
| S1-20 `iterate_pairSndD_encodeMsgs` | listed copies; `exact?`: none | `ZeroKnowledge/ThreeColoring/Machines.lean:919`, `ZeroKnowledge/GraphIsomorphism/EfficiencyRep.lean:101` | none |
| S1-26 `msgAt_encodeMsgs` | listed copies; `exact?`: none | `SecureComputation/ComposeSecurity/Machines.lean:137`, `ZeroKnowledge/ThreeColoring/Protocol.lean:112` | none |
| S1-21 `encodeMsgs_eq_encWords` | listed copies; `exact?`: none | `SecureComputation/Yao/HybridProof/Lengths.lean:83`, `Composability/SequentialZK/Normalization.lean:40` | none |
| S1-22 `StatClose.of_uprob_ne` | listed copies; `exact?`: none | `Candidates/DDH.lean:145`; users `Encryption/PublicKey/ElGamal.lean:1154`; `SecureComputation/Yao/HybridProof/StatisticalSwitch.lean:46`, `:68` | none |
| S1-23..25 `FinDist` (14) | listed copies (all in `Randomness/Extraction/Rejection.lean`); Mathlib/`Games` short-name homonyms (`sum_map`, `map_map`, `expect_map`) are other objects; `exact?` (`map_uniform_equiv`, `map_map`): none | `Randomness/Extraction/Rejection.lean:45`, `:65`, `:81`, `:88`, `:93`, `:98`, `:104`, `:113`, `:122`, `:134`, `:343`, `:395`, `:406`, `:413` | consumers `Randomness/Extraction.lean:168`, `:221`, `:247`, `:248`, `:325`, `:328`; `Randomness/Learning/Law.lean:81`, `:82`; near-copies of `map_uniform_equiv` at `Equiv.ofBijective`: `Encoding/DyadicUniform.lean:83`, `:148`, `:216`; near relative `LWE/Sampling.lean:68` |
| S1-27 `flatMap_range_ite` | listed copies; private homonym `Complexity…QuasiPolyHierarchy.flatMap_range_ite` has another statement; `exact?`: none | `SecureComputation/ComposeSecurity/Machines.lean:61`, `ZeroKnowledge/ThreeColoring/Machines.lean:142`, `ZeroKnowledge/ThreeColoring/SimulatorMachine.lean:160` | none |
| S1-27 `polyTimeComputable_flatMap_range` | listed copies; `TCSlib/Complexity/FormulaKit/Emit.lean:127` (`Complexity.FormulaKit.polyTimeComputable_flatMap_range`) is the same statement with the pair order swapped and is **`sorry`** at the base (an admission, another layout, not in the home's closure): not an E-DUP; noted for a future Complexity fill | `ComposeSecurity/Machines.lean:81`, `ThreeColoring/Machines.lean:159` | none |
| S1-27 `iterSnd_poly` | listed copies; `exact?`: none | `ComposeSecurity/Machines.lean:117`, `ThreeColoring/Machines.lean:190` | none |
| S1-27 `zeros_poly` | **disclosed overlap, CS1-W1:** `Games.EffFill.zeros_poly` (`Games/Efficiency/Strings.lean:152`, `z ↦ 0^{|f z|}` from `f` poly) and `EnsembleLemmas.polyTimeComputable_zeros` (`Asymptotic/EnsemblesLemmas.lean:212`, `z ↦ 0^{p(|u z|)}`) are public and inter-derivable with the target by one length rewrite, but neither is in the home's import closure nor states the unary-length form that `padTo_poly` needs; kept as the brief states it; `exact?` at base: none | `ThreeColoring/Machines.lean:292` | homonyms `GI.zeros_poly`/`GIZK.zeros_poly` (`0^{|w|}`, other statements) |
| S1-27 `padTo` family | listed copies; Batteries `List.takeD L w false` gives the same lists (recursive body, different definition): relative, noted | `ComposeSecurity/Machines.lean:223`, `:226`, `:232`, `:239`, `SecureComputation/ComposeSecurity/Assembly.lean:98`; `ThreeColoring/Machines.lean:303`, `:306`, `:312`, `:316`; re-derived `ofFn_padFin` `ComposeSecurity/Machines.lean:244`, `ThreeColoring/Machines.lean:327` | none |

## ===== inbox/fills/cleanup-stage1/evidence/stage2/repoint.tsv (exchange delivery, at 5451d3cd6fa9b8c313c9f18f5a4da3542c85f02a) =====

copy (path:line; under TCSlib/Cryptography/ unless TCSlib/...)	what it is	re-points to (Stage 1 target or existing form)	source
TCSlib/Complexity/Randomized/Build/IterateFind.lean:373	hdisp (in computesFunInTime_find; issue-base line)	Complexity.IterateFind.host_dispatch_view (S1-01)	brief
TCSlib/Complexity/Randomized/Build/IterateFind.lean:378	hbranch	Complexity.IterateFind.host_branch_view (S1-02)	brief
TCSlib/Complexity/Randomized/Build/IterateFind.lean:390	hhalt	Complexity.IterateFind.host_halt_view (S1-03)	brief
TCSlib/Complexity/Randomized/Build/IterateFindHost.lean:352, :364, :380	host_dispatch, host_branch, host_halt (unused originals)	DW-9: delete or restate	brief
Encryption/PrivateKey/EncryptThenTag/Tools.lean:65	ETTGame.expect_simulate_abs	Games.expect_simulate_abs (S1-04)	brief
Encryption/PrivateKey/EncryptThenTag/Tools.lean:88	ETTGame.expect_simulate_abs_inv	Games.expect_simulate_abs_inv	brief
Encryption/PrivateKey/EncryptThenTag/Tools.lean:116, :122	ETTGame.freshImpl, freshImpl_apply	Games.freshImpl, Games.freshImpl_apply	brief
Encryption/PrivateKey/EncryptThenTag/Tools.lean:130, :135	ETTGame.tapeImpl, tapeImpl_apply	Games.tapeImpl, Games.tapeImpl_apply	brief
Encryption/PrivateKey/EncryptThenTag/Tools.lean:145	ETTGame.simulate_tapeImpl_congr	Games.simulate_tapeImpl_congr	brief
Encryption/PrivateKey/EncryptThenTag/Tools.lean:167	ETTGame.expect_simulate_tapeImpl	Games.expect_simulate_tapeImpl	brief
Encryption/PrivateKey/EncryptThenTag/Tools.lean:219, :224, :228, :234, :246, :262, :281	ETTGame.ovr, ovr_nil, ovr_cons, ovr_of_not_mem, ovr_of_mem, ovr_update, expect_sample_ovr	Games.ovr and readers, Games.expect_sample_ovr	brief
Encryption/PrivateKey/EncryptThenTag/Lazy.lean:175	ETTGame.ovr_append (at κ = Fin (2n) → Bool)	Games.ovr_append	brief
Encryption/PublicKey/AdaptiveCPA/Hybrid.lean:211, :215, :221	AdaptiveCPA.extTape, extTape_of_lt, extTape_update	Games.extTape, Games.extTape_of_lt, Games.extTape_update	brief
Authentication/MAC/FromPRF/Random.lean:125	consumer of ETTGame.expect_sample_ovr	Games.expect_sample_ovr	brief
Encryption/PrivateKey/EncryptThenTag/Games.lean:356; Encryption/PrivateKey/EncryptThenTag/Lazy.lean:445	consumers of ETTGame.freshImpl (ettImpl_eq_freshImpl, ettLazy_eq)	follow ETTGame.freshImpl -> Games.freshImpl	found (consumer)
Encryption/PrivateKey/EncryptThenTag/Reduction.lean:93	consumer of AdaptiveCPA.extTape (dTapes_eq)	follow AdaptiveCPA.extTape -> Games.extTape	found (consumer)
Encryption/PrivateKey/EncryptThenTag/Machines.lean:95	private length_le_length_encodeLog	Games.EffFill.length_le_length_encodeLog (S1-05); delete	brief
Encryption/PublicKey/NonMalleability/Indistinguishability/Forward.lean:108	private length_le_length_encodeLog	Games.EffFill.length_le_length_encodeLog; delete	brief
Encryption/PrivateKey/FromPRF.lean:174	zipWith xor cancellation	zipWith_xor_cancel_right (S1-06)	brief
Encryption/PrivateKey/FromPRG.lean:147	zipWith xor cancellation	zipWith_xor_cancel_right	brief
SecureComputation/SpecialEncryption.lean:101	private zipWith_xor_xor_self	zipWith_xor_cancel_right	brief
Encryption/PrivateKey/EncryptThenTag.lean:338	private zipWith_xor_xor_self'	zipWith_xor_cancel_right	brief
Encryption/PrivateKey/EncryptThenTag/Lazy.lean:295	ETTGame.zipWith_xor_cancel	zipWith_xor_cancel_right	brief
Encryption/PrivateKey/EncryptThenTag/Handler.lean:134, :139, :143, :147	recBits and its readers (recordBits (ettCt.eval n))	recordBits, recordBits_none/_some, length_recordBits (S1-07)	brief
Encryption/PrivateKey/OracleFromPRF/Handler.lean:109, :114, :117, :121	recBits and its readers (recordBits (ctP.eval n))	recordBits and readers	brief
Encryption/PrivateKey/EncryptThenTag/Machines.lean:348	ETTGame.eval_toOracleAdversary_len	NUPPT.eval_toOracleAdversary_padFin (S1-08), a = b = ℓ, a' = b' = ℓ'	brief
Encryption/PrivateKey/OracleFromPRF/Reduction.lean:228	PRFGame.eval_toOracleAdversary_width	NUPPT.eval_toOracleAdversary_padFin, a = b = n, a' = b' = m	brief
Authentication/MAC/FromPRF/Bound.lean:48	eval_toOracleAdversary_width₂	NUPPT.eval_toOracleAdversary_padFin, a = b = n, a' = m₁, b' = m₂	brief
Asymptotic/EnsemblesLemmas.lean:433	EnsembleLemmas.ofFn_blocks_symm (through the alias)	FunFamily.ofFn_blocks_symm_eq_flatMap (S1-09); with the seven approved DL-35 changes (Stage 2 handover 1, CS1-Q2 and the seventh, ETTGame.dTape)	brief
Hashing/FromDiscreteLog/Probability.lean:40	FromDiscreteLog.expect_sample_eq_uexp	Games.Bridge.expect_sample_eq_uexp (S1-10); needs the import of Games.Bridges.Experiments	brief
Hashing/FromDiscreteLog/Encoding.lean:45, :55	public FromDiscreteLog copies	Authentication.ofFn_splitBits_fst / _snd (S1-11)	brief
Authentication/MAC/FromPRF/Reduction.lean:140, :145, :147	decide_fnForge's hw, htake, hdrop (DL-44 F-02)	Authentication.ofFn_splitBits_fst / _snd	brief
Authentication/Signatures/Lamport/MachineSpec.lean:259	inline hs : List.ofFn (splitBits a).2 = (List.ofFn a).drop n	Authentication.ofFn_splitBits_snd	FOUND (not in brief)
Authentication/Signatures/HashAndSign/CollisionHandler.lean:464	inline hp : (List.ofFn a).take _ = List.ofFn (splitBits a).1	Authentication.ofFn_splitBits_fst	FOUND (not in brief)
Authentication/Signatures/HashAndSign/OneQuery.lean:36	HashSignFill.eq_pure_of_cost_zero	Games.OracleComp.exists_eq_pure_of_costBoundedBy_zero (S1-12)	brief
Authentication/Signatures/Lamport/Planted.lean:226	exists_pure_of_cost_zero	Games.OracleComp.exists_eq_pure_of_costBoundedBy_zero	brief
Asymptotic/BlockEncryptor.lean:60	public TCSlib.Cryptography.encodeList_eq_flatMap	PrivateKeyScheme.encodeList_eq_flatMap (S1-14); its consumers Authentication/Signatures/Lamport/MachineSpec.lean:49, Authentication/Signatures/Lamport.lean:582, Encryption/PublicKey/HybridMachine.lean:216, :217, SecureComputation/Yao/HybridProof/SliceReconstruction.lean:274 follow	brief (+ consumers found)
Encryption/PrivateKey/FromPRF/MultiMsgOut.lean:65	public MultiMsg.encodeList_eq_flatMap	PrivateKeyScheme.encodeList_eq_flatMap	brief
Encryption/PrivateKey/FromPRF.lean:251	private, unused (frozen-file exception of DL-46)	PrivateKeyScheme.encodeList_eq_flatMap	brief
Pseudorandom/NextBit.lean:454	inline	headD_drop_ofFn (existing)	brief (S1-15 list)
TCSlib/Cryptography/Foundations/BitLists.lean:88	headD_ofFn_one	headD_drop_ofFn	brief
ZeroKnowledge/GraphIsomorphismZK/Closeness.lean:280	headD_ofFn_block	headD_drop_ofFn	brief
Encryption/PublicKey/NonMalleability/Simulation/SimIND.lean:88	private eq_const_headD	headD_drop_ofFn	brief
Pseudorandom/Functions/Asymptotic/GGM/Run.lean:449	in step_eq (:435), the exact copy	headD_drop_ofFn	brief
Asymptotic/HardCoreLoops.lean:260	orbit_eq	headD_drop_ofFn	brief
ZeroKnowledge/GraphIsomorphism/SoundnessRep.lean:61	GI.getD_ofFn_lt'	getD_ofFn (S1-15)	brief
ZeroKnowledge/GraphIsomorphism/Proofs.lean:818	GI.getD_ofFn_lt	getD_ofFn	brief
ZeroKnowledge/GraphIsomorphismZK/Closeness.lean:110	GIZK.getD_ofFn_lt	getD_ofFn	brief
ZeroKnowledge/ThreeColoring/ProtocolProofs.lean:391	ColProofs.ofFn_getD_lt	getD_ofFn	brief
SecureComputation/Yao.lean:614, :620	private getD_ofFn', yaoBobTables_yaoMsg	getD_ofFn	brief
ZeroKnowledge/ThreeColoring/Simulator.lean:861	inline in statClose_colRealView (:813)	getD_ofFn	brief
ZeroKnowledge/ThreeColoring/Language.lean:423	private ofFn_getD_tape	getD_ofFn	brief
ZeroKnowledge/Encoding.lean:359	inline in coinTable_ofFn (:352)	getD_ofFn	brief
SecureComputation/Garbling.lean:202, :374	private map_range_getD_ofFn, garbledValues_getD	getD_ofFn	brief
SecureComputation/Garbling/CoinBlocks.lean:74	inline in pushesUniform_bits_of_blocks (:51)	getD_ofFn	brief
Encryption/PublicKey/BitwiseCPA.lean:98	private ofFn_half	getD_ofFn	brief
Encryption/PublicKey/OracleSecurity/PaddedCPA.lean:72	private ofFn_splitHalf_bit	getD_ofFn	brief
Encoding/BooleanVector.lean:142	expandPoly_encode	getD_ofFn	brief
Hashing/SIS/CollisionOutput.lean:188	collisionOutputPoly_pairEncode	getD_ofFn	brief
SecureComputation/Yao/HybridProof/RowFromCoins.lean:416	inline chain in assignmentBit_of_perm (:408)	getD_ofFn	FOUND (not in brief)
AdvancedEncryption/Homomorphic/GSW/Eval.lean:263; TCSlib/Complexity/CircuitComplexity/ copies; Complexity-side inline chains	forbidden now / CS1-Q12	later window; Complexity chains stay	brief
Encryption/PublicKey/NonMalleability/Simulation/Rounds.lean:41	NMSim.length_ofFn_coins	NUPPT.length_ofFn_coins (S1-16)	brief
SecureComputation/ObliviousTransfer/Simulators.lean:210	OT.length_ofFn_coins	NUPPT.length_ofFn_coins	brief
Asymptotic/CollectionsHelpers.lean:112; Hashing/FromDiscreteLog.lean:97, :134	inline have (rw [List.length_ofFn, NUPPT.coinLen_eq])	NUPPT.length_ofFn_coins	FOUND (not in brief)
Asymptotic/Collections.lean:796, :804	inline in rewrite arguments	NUPPT.length_ofFn_coins	FOUND (not in brief)
SecureComputation/ObliviousTransfer/ViewB.lean:71, :101	OT.uprob_signedPredictor_false/_true	re-derived from exists_pkPredictor (Encryption/PublicKey/Trapdoor.lean:337 base, :347 head) through pkPredictor_apply (S1-17)	brief
SecureComputation/ObliviousTransfer/Simulators.lean:52, :57	OT.splitLen, splitLen_symm_ofFn	(EnsembleLemmas.coinsEquiv h).symm, Asymptotic/EnsemblesLemmas.lean:141, :145 (no new form)	brief
Randomness/Learning/Sample.lean:58	LearnPRF.foldr_pairEncode_nil (DL-45)	Strategy.encodeMsgs_eq / encodeMsgs_eq_flatMap (S1-18/S1-19)	brief
SecureComputation/ComposeSecurity/Machines.lean:150	encodeMsgs_eq_flatMap	Strategy.encodeMsgs_eq_flatMap (S1-19)	brief
ZeroKnowledge/ThreeColoring/Machines.lean:912	encodeMsgs_eq_flatMap	Strategy.encodeMsgs_eq_flatMap	brief
ZeroKnowledge/ThreeColoring/SimulatorNumeric.lean:503	encodeMsgs_eq_flatMap	Strategy.encodeMsgs_eq_flatMap	brief
ZeroKnowledge/ThreeColoring/Machines.lean:919	iterated pairSndD on encodeMsgs	Strategy.iterate_pairSndD_encodeMsgs (S1-20)	brief
ZeroKnowledge/GraphIsomorphism/EfficiencyRep.lean:101	iterated pairSndD on encodeMsgs (DL-38 ZK pair)	Strategy.iterate_pairSndD_encodeMsgs	brief
SecureComputation/ComposeSecurity/Machines.lean:137	ComposeMachines.msgAt_encodeMsgs	Strategy.msgAt_encodeMsgs (S1-26)	brief
ZeroKnowledge/ThreeColoring/Protocol.lean:112	msgAt_encodeMsgs (instance for i < |l|, through msgAt_eq)	Strategy.msgAt_encodeMsgs	brief
SecureComputation/Yao/HybridProof/Lengths.lean:83	YaoHybridProof.encodeMsgs_eq_encWords	Strategy.encodeMsgs_eq_encWords (S1-21)	brief
Composability/SequentialZK/Normalization.lean:40	SequentialZK.encodeMsgs_eq_encWords	Strategy.encodeMsgs_eq_encWords	brief
SecureComputation/ComposeSecurity/Probability.lean:110	DL-49	EnsembleLemmas.negligible_polyExpr_mul (Asymptotic/EnsemblesLemmas.lean:377; a new import)	brief
SecureComputation/ComposeSecurity/Accept.lean:52	appendCoins (DL-49)	EnsembleLemmas.coinsEquiv	brief
SecureComputation/ComposeSecurity/Runs.lean:71	DL-49	FunFamily.ofFn_blocks_symm (Asymptotic/OneWay.lean:380)	brief
Candidates/DDH.lean:145	Candidates.statClose_of_uprob_ne	StatClose.of_uprob_ne (S1-22); user Encryption/PublicKey/ElGamal.lean:1154 follows	brief
SecureComputation/Yao/HybridProof/StatisticalSwitch.lean:46, :68	statClose_of_eq_off (re-derived with StatClose.mono, uprob_mono), distAdv_le_of_eq_off	StatClose.of_uprob_ne	brief
Randomness/Extraction/Rejection.lean:45, :65, :93, :98, :134, :343	FinDist facts	FinDist.map_uniform_equiv, sum_map, probTrue_nonneg, probTrue_le_one, uniform_prod, uniform_probTrue (S1-23)	brief
Randomness/Extraction/Rejection.lean:81, :88, :104, :113, :122	FinDist facts	FinDist.expect_map, probTrue_map, map_apply_expect, map_map, map_prod_snd (S1-24)	brief
Randomness/Extraction/Rejection.lean:395, :406, :413	mixture, mixture_apply, mixture_isSource	FinDist.mixture and readers (S1-25); consumers Randomness/Extraction.lean:168, :221, :247, :248, :325, :328 and Randomness/Learning/Law.lean:81, :82 follow	brief (+ consumers found)
Randomness/Extraction/Rejection.lean:144	Rejection.tupleEquiv	Mathlib (Fin.consEquiv _).symm (no new form)	brief
Encoding/DyadicUniform.lean:83, :148, :216	bitsToResidue_uniform, bitsToVector_uniform, bitsToMatrix_uniform (fibre count by hand)	re-provable from FinDist.map_uniform_equiv at Equiv.ofBijective (optional; near-copies)	FOUND (not in brief)
SecureComputation/ComposeSecurity/Machines.lean:61; ZeroKnowledge/ThreeColoring/Machines.lean:142; ZeroKnowledge/ThreeColoring/SimulatorMachine.lean:160	flatMap_range_ite	EncodingMachines.flatMap_range_ite (S1-27)	brief
SecureComputation/ComposeSecurity/Machines.lean:81; ZeroKnowledge/ThreeColoring/Machines.lean:159	polyTimeComputable_flatMap_range	EncodingMachines.polyTimeComputable_flatMap_range	brief
SecureComputation/ComposeSecurity/Machines.lean:117; ZeroKnowledge/ThreeColoring/Machines.lean:190	iterSnd_poly	EncodingMachines.iterSnd_poly	brief
ZeroKnowledge/ThreeColoring/Machines.lean:292	zeros_poly	EncodingMachines.zeros_poly (CS1-W1)	brief
SecureComputation/ComposeSecurity/Machines.lean:223, :226, :232, :239; SecureComputation/ComposeSecurity/Assembly.lean:98	padTo, padTo_eq, padTo_poly, length_padTo, padTo_of_length	EncodingMachines.padTo family	brief
ZeroKnowledge/ThreeColoring/Machines.lean:303, :306, :312, :316	padTo, padTo_poly, length_padTo, getD_padTo	EncodingMachines.padTo family	brief
SecureComputation/ComposeSecurity/Machines.lean:244; ZeroKnowledge/ThreeColoring/Machines.lean:327	ofFn_padFin	re-derived from ofFn_padFin_eq_take (Asymptotic/CollectionsLemmas.lean:95) and EncodingMachines.padTo_eq	brief
Authentication/Signatures/Lamport/Averaging.lean:129	LamportReduction.expect_favourable_of_success (DL-43)	ProbComp.mul_prob_le_expect, added to Games/Probability.lean in Stage 2 (CS1-Q9)	brief
Authentication/Signatures/HashAndSign/CodecReaders.lean:46; Authentication/Signatures/Lamport.lean:771	MachineCodec.ext_of_fields (moved verbatim to Games/Machines); lamport_codec_ext	the moved MachineCodec.ext_of_fields (CS1-Q3)	brief
SecureComputation/Yao/HybridProof/OTAnswerWords.lean:41, :94	DL-52	HybridProtocol.length_answersB / length_answersA (SecureComputation/ComposeSecurity/Lengths.lean:60, :52)	brief
Randomness/Learning/Sample.lean:88, :92	blk, length_blk (DL-45)	MultiMsg.histBlock, length_histBlock (Encryption/PrivateKey/FromPRF/ReductionMachine.lean:82, :91)	brief

## ===== pr347-description.md (this pack) =====

This PR resolves deferred item **DW-5** (`briefs/pass-shelat-ch5-8/deferred-work.md`), finding F-01 of the derand fill review. Seyoon ruled "debt now, fix after" on 2026-11-16.

**Head:** `daa6e173cdd94cad1475b9a96eca613bce53ba61`. **Base:** `cryptography/pass-shelat-ch2-4`. It merges cleanly onto the current tip.

## Changes (proof-only re-derivations plus 9 readers)
- **Readers** (SR-02), each with a formula docstring. None is `@[simp]`.
  - `Turing.ModuleHost`: `hostTMView` with `_eq` and `_q₀`, plus `hostTMView_step_inl`, `host_call_view` and `host_clean_view`.
  - `Complexity.IterateFind`: `copyTMView` with `_eq`, plus `copy_clean_view`. `copyTMView` fixes the start state `0`, because `host_call_view` starts the module at `q₀`.
- **E1 `computesFunInTime_find`** now runs the host and the copier through the views.
- **`polyTimeComputable_find`** is re-derived from E1, by the route pre-approved at derand F-03. This removes a 196-line copy of the old proof.
- Every header and its prose is byte-identical. Both proof sketches are refreshed because the route changed.

## Checks on the merged tree TS1 (`briefs/pass-shelat-ch5-8/cleanup-stage1/final-r1/phase2.md`, 2026-11-17)
- TS1 = records tip `e1d39836` × this PR × #355 = tree `1eaf940b938bb52e3919f5569893b58522df599b`, replayed on olean snapshot #5: **556/556 modules rc 0**, 0 errors, state **1429/1429 OK**; admissions 196 = 196 per module; axioms standard (this PR's 27 constants, census of 21 owners 1224 constants, no `sorryAx`).
- Rule 10 at TS1: `IterateFind` **20 → 0** in strict A/B and coe A/B; the 12 seal rows of this PR's owners equal DW-5's head; controls 10 probes / 30 negatives ALL_OK per variant; 0 foreign unfolds in the changed declarations.
- Since then #357 merged and olean snapshot #6 was adopted at `8060f6b7`: this PR and #355 re-replay on #6 before merge.

## Checks on its own tip (`briefs/pass-shelat-ch5-8/maintenance/dw5/`, 2026-11-16)
- **Rule 10.** F-01's **20 IterateFind seal failures go to 0** in strict A, strict B, coe A and coe B.
  - Paired controls: ALL_OK.
  - Explicit-unfold scan: 0 foreign unfolds in the changed declarations.
- **Build.** 706/706 modules give rc 0 with 0 errors, through root `TCSlib` and both `Checks`. The state check passes 1342/1342.
- **Axioms.** Both theorems, the 9 readers and everything downstream use the standard three only.
- **Statements.** Admissions are unchanged. decls2 shows +9 / 0 / 0. Lint is unchanged, and there is no name clash.

## Disclosures
- E1 restates the dispatch, branch and halt steps in-proof, because the public `host_*` lemmas read `hostTM`'s fields. The view readers restate `host_call`, `host_clean`, `hostTM_step_inl` and `copy_clean` by design (SR-02).
- `host_dispatch`, `host_branch`, `host_halt`, `IterateFind.hostTM` and `copyTM_k` are now unused.
- **Scope ruling (Seyoon, 2026-11-16):** the 26 **pre-existing** seal failures in `ModuleHost` (10) and `IterateFindHost` (16) are unchanged by this PR. They become deferred item **DW-9**.

## Gate
**Gate 47** (Codex) audits this PR together with #355. Seyoon merges.

🤖 Generated with [Claude Code](https://claude.com/claude-code)

https://claude.ai/code/session_01PqpVTiuDcjSqhyfbqnsVxA

## ===== pr355-description.md (this pack) =====

Cleanup **Stage 1** of the Pass–shelat ledger (`briefs/pass-shelat-ch5-8/cleanup-stages.md`) promotes the shared forms of the ledgered copies. It is **additive only**: nothing is re-pointed or deleted until Stage 2.

The targets are S1-01..S1-27; S1-13 is withdrawn. Together they add 69 declarations, under Seyoon's rulings CS1-Q1..Q12, CS1-C1-Q1 and the Stage 1 final rulings Q1–Q4.

**Stacked on #347** (DW-5, branch `cleanup/dw5-derand-readers`). Both PRs touch the same host files, and Gate 47 audits them together. Once #347 merges, this PR is retargeted to `cryptography/pass-shelat-ch2-4` and merged there. It is never merged into #347's branch.

**Head:** `d3c7cb000…` (`git rev-parse land/cleanup-stage1`). It consists of five maintainer-signed cherry-picks of the external Claude worker's series (`4881cf98..c8021348`, range-diff 5/5 identical) on #347's head `daa6e173`. The tree is `508f9154`, as delivered. The diff is 21 files, +1,079/−0.

## Contents
- **DW-9's view versions** of the host control steps (`IterateFindHost`).
- **Games forms:** simulation in law, coin tapes and tables. The new `Games/Tapes.lean` covers DL-40, DL-41 and DL-42.
- **Readers** for bit lists, coins, encodings and closeness (DL-35, DL-40, DL-41, DL-46, DL-47, DL-48, DL-51).
- **History encoding:** the new `ZeroKnowledge/InteractionWords.lean`, and the shared machine helpers in `ZeroKnowledge/EncodingMachines.lean` (DL-38, DL-45, DL-49; CS1-Q8).
- **Finite-distribution facts** in `InformationTheory/{FinDist,Samples,Entropy}` (DL-39).
- Every name whose short name already exists is `protected`. Each new declaration has a formula docstring and a tag or glue note.

## Review (`briefs/pass-shelat-ch5-8/cleanup-stage1/`)
- **Checkpoint 1:** proceed with notes.
- **Final, phase 1:** the code is accepted as delivered.
  - decls2 gives 69 ADDED, 0 CHANGED and 0 REMOVED, and all 69 headers match the brief.
  - It is a pure insertion with no frozen file touched. There is no `sorry` in new code, and the axioms are standard.
  - The `protected`, clash and shadow checks are clean.
  - The worker's evidence recounts: the 847-module bootstrap, the 495-module sweep, 144 seal records, 20/20 controls, 0 foreign unfolds, and lint with no new FAIL or WARN.
- **Report layer.** It is completed by the maintainer's Stage 2 addendum (`final-r1/stage2-addendum.tsv`), per ruling Q1.
- **Ledger.**
  - DL-49 is extended for `msgAt_encodeMsgs` (CS1-F01).
  - DL-53 covers the padding and zero-word families (CS1-C1-Q1).
- **Approved for Stage 2:** the seven extra `blocks`-alias changes (Q2).

## Phase 2 (`briefs/pass-shelat-ch5-8/cleanup-stage1/final-r1/phase2.md`): PASS
- TS1 = records tip `e1d39836` × #347 × this PR = tree `1eaf940b938bb52e3919f5569893b58522df599b`, clean in five merge orders, replayed on olean snapshot #5: **556/556 modules rc 0**, 0 errors, state **1429/1429 OK**, snapshot 0/0/0.
- Admissions 196 = 196 per module; the 69 axioms standard (34/12/6/4/13); census of the 21 owners 1224 constants, no `sorryAx`.
- Rule 10 on 21 owners: no failure in a touched declaration in the coe variants; strict-only failures are the `FinDist` coercion and B-only ones `PolyExpr.eval` (notation by ruling); every other failure pre-existing and identical at the tip. Controls 20/20 per variant; 0 foreign unfolds; lint 92/104 → 92/103.
- Since then #357 merged and olean snapshot #6 was adopted at `8060f6b7`: #347 and this PR re-replay on #6 (about 561 modules) before merge.

## Gate 47
- A Codex audit of #347 and this PR together. The pre-dispatch duplication sweep is ruled (Seyoon, 2026-11-17): **DL-59** (`Games.extTape` family vs `LazySampling.extendStream`, unified in Stage 2) and **DL-60** (weaker overlaps). This PR's code is unchanged.

🤖 Generated with [Claude Code](https://claude.com/claude-code)

https://claude.ai/code/session_01PqpVTiuDcjSqhyfbqnsVxA

## ===== verification-r1.zip:records/decision-log-rows.md (this pack) =====

# Decision-log rows (PassShelatChapter5-8Plan.md at records pin 659542ecd9413b504d30da8c937b9805e6c1f71f), 2026-11-16 onward, filtered

Rows whose text names DW-5, DW-9, DW-10, DW-11, #347, #355, Stage 1, cleanup-stage1, CS1, Gate 47, DL-53 to DL-60, snapshot #6 or cleanup; line numbers are the file's. Copied verbatim.

line 771: | 2026-11-16 | **Gate 34 round-2 pack** (Codex, standing ruling): `gates/34-sc-ot/pack-r2.md` for draft [PR #318](https://github.com/Shilun-Allan-Li/tcslib/pull/318) at `b0bad23ae611983e3323460bb8c564da90ad6e8c` (rebased onto `05d26fe5`, was `a334ec2e`; round 1 audited `f62a25b3`; 6 commits: 3 worker, LE-doc, LE-reuse, LE-gate34 `b0bad23a`; 7 Lean files, 2259/40). Re-audit of G34-01 (LE-gate34: `OT.getD_zero_eq`/`OT.getD_one_eq'` from the public `headD_drop`, proof only, no import; evidence `landing-r1/` `145d5574`: integration build 270/270 rc 0 against #314–#317, seals A/B and coe A/B pass with `-DmaxErrors=0`, controls ALL_OK, axioms standard, admissions 216→214, lint unchanged), the G34-02 disposition (DL-48 entry and cleanup line present, both copies unchanged), the rebase and duplication since round 1. Re-checked from git objects: range-diff `a334ec2e..f62a25b3` → `05d26fe5..e0ecdf22` 5/5 `=`, unit files identical across the rebase; 193/193 headers and every definition block identical to round 1, only the two edited docstrings changed; decls2 vs `f62a25b3` empty (141/0/0 vs the base); 6 commits signed; base delta #316 and #317 (both already in round 1's records tip `5d719839`; #314/#315 were in round 1's base), only `BitLists` in the closure (128 modules, unchanged); statement scan of the 107 new theorems against the tip delta since round 1 and every open PR: 0 hits; all 270 built sources = head blobs. `merge-tree` clean with the tip `b0ebd475` (`bd129bfa`), #319 `47daa907` (`705cab61`, = the built combined tree), #323 `8c3f3e3f` (`8cdcecbd`), #324 `a6eaebd7` (`0106b2fb`), #326 `941b5a1e` (`a69cfdb8`), #327 `e9b5ea47` (`89568060`); shared downstream: tip, #319, #327 root `TCSlib`; #324 3; #323 6 (`DAGCircuit` in the closure); #326 10 (`DTIME`, `IterateFind` in the closure): **pending merge condition, not an audit item** (combined build of all open PRs running, pending). Noted: the #318 PR description is still round 1's; `landing-r1/PROVENANCE.txt` predates the maintainer's push. `verification-r2.zip` `4fd8f8ea` (23 entries); `sources-r2.zip` `cb18319f` 128 files. Bundle and exchange staging next. |
line 787: | 2026-11-16 | **Uniformity audit returned** (Codex, HOLD against the convention; [findings](briefs/pass-shelat-ch5-8/audits/uniformity-2026-11-16/findings/uniformity-audit-findings.md), `7d398d16`). 1,160 components: 1,144 OK, 12 WEAKER, 4 equivalent through auxiliary input, 0 STRONGER. U-01: both HBC predicates allow non-uniform simulators; **PS10 Def 155.1 permits this**, so my brief's PS10 claim was wrong (U-05). The gap is against Goldreich and Seyoon's convention. U-02: `SimNMSecure`'s simulator carries advice; adding `Uniform` alone is unsatisfiable, so the repair needs a shared auxiliary input. U-03: sc-compose's simulator pairs advice (`pairEncode [] []` has length 2). The worst-instance advice stays in reductions. OT (#318) and seq-zk (#327) simulators are already uniform; Yao's are not yet built. **Ruling (Seyoon): defer all uniformity fixes, probably until after merging into `main`; record them.** Recorded as DW-1 to DW-3 in the new [deferred-work register](briefs/pass-shelat-ch5-8/deferred-work.md), with DW-4 to DW-6 (dedup cleanup, derand typed views, small-secret LWE). No note to sc-yao (retrofit later). |
line 792: | 2026-11-16 | **Gate 38 pack** (Codex, standing ruling): `gates/38-derand/` for draft [PR #326](https://github.com/Shilun-Allan-Li/tcslib/pull/326) (`land/pass-shelat-derand` at `c27005d67298f79c785a4e8ac1648da0a67d3614`, merge base `6ce4658d`, issue base `01de2d8b` (issued-r2); 5 commits: 4 Codex worker, LE-doc `c27005d6` (F-04); 15 Lean files, 1741/36). Proof audit of H17 `exists_seedMajorityTM`, `seedMajority_mem_DTIME` and Theorem 180.1 `bpp_subset_dtime_subexp`: correctness against the frozen statements and [PS10] (one machine for both clauses; the Gate 28 route, binary fuel, terminal rank, no `final_bound`; margins 7/12 and 5/12, no finite table; the edge cases), frozen integrity (53/0/0; frozen check 0 header/body, 3 target PROSE), the shared-file additions, Rule 10, duplication, docstrings and sketches, axioms. Re-checked from git objects: range-diff 4/4 `=`; src/ = the 15 files; the five pre-existing files' headers and definition blocks identical in order; **the shared files gain exactly E1 (`IterateFind` +245/−0), E2 and E3 (`DTIME` +18/−0, = the brief's drafts) and SR-01 (`Classes` +12/−0, = the scope-request patch; 1415 lines)**, each by insertion only; `polyTimeComputable_find` and `final_bound` byte-identical in whole. **F-01 (ruled debt, DW-5): the 20 `IterateFind` seal errors map to `polyTimeComputable_find` (11, pre-existing, also at the base) and `computesFunInTime_find` (9, E1); every other probe 0 in all variants.** The fourth pre-approval (re-derive `polyTimeComputable_find`) never reached the worker (review note; F-03 repetition disclosed). Statement scans of the 46 new theorems: 0 hits against the pools and the whole tree. `merge-tree` clean with the tip `c2f6adeb` (`aad4171f`), #324 (`fa624a7e`), #327 (`029cdc65`) and the merged #318/#319/#323; shared downstream 259 with the tip (DTIME is deep). Integration: the combined build `4f8cb374` = the final merged state; merge #324 last. Noted: the PR description predates LE-doc. `verification.zip` `718f373b` (153 entries, with review-evidence `ef0776d5`); `sources.zip` `743ed284` 207 files; `landing-ledoc/` (`977bbe89`) and `integration/` staged with the pack. Bundle and exchange staging next. |
line 800: | 2026-11-16 | **Gate 38 CLOSED** ([resolutions](briefs/pass-shelat-ch5-8/gates/38-derand/resolutions-r1.md)): Codex CLEAR 0/0/0/0 on #326 (derand) `c27005d6`. H17, the DTIME corollary and Thm 180.1 hold. Rule-10 failures are exactly the 20 of F-01 (DW-5). Findings `a375dfc1`. **#326 marked ready, clear to merge** (it was built alone on the tip and in the combined build). |
line 815: | 2026-11-16 | **Overnight authorization** (Seyoon): the maintainer may carry out statement prep, cleanup (deduplication etc.) and fills on its own; Codex audits everything in the morning; stop at a mission-critical audit if needed. Plan and judgment calls in `briefs/pass-shelat-ch5-8/overnight-2026-11-16.md` (DW-1/DW-2 stay deferred; pairing fills proceed before Gate 40 r2). Exchange inbox watched every 5 minutes for the `sc-yao` and `gsw-security` finals. | Overnight |
line 820: | 2026-11-16 | **sc-yao review r1 final: ACCEPT WITH LANDING EDITS** (`fills/sc-yao/final-r1/review.md`; evidence `review-evidence.zip` `d3f7c3da`, 1511 entries, `evidence-SHA256SUMS`; `landing/PROVENANCE.txt`). Landing head `e9b03c43` (12 signed commits on `f9fda8fe`: the worker's 8, LE-bullet, LE-reuse, LE-title, LE-doc). Phase 2 on `dl-oleans-2`: 718/718 rc 0, 0 errors, state 1356/1356; `yaoHybrid_polyTime`, `yaoHybrid_simulators`, `yaoHybrid_hbcSecure`, `yaoSeed_good_whp` standard; `yaoProtocol_hbcSecure` then reached `sorryAx` only via #324's `hbcSecure_compose`. Rule 10: Yao A 0, B 24 (9 new, all `PolyExpr.eval` conversions), `Uniform` 4 inherited, helpers coe-A 68/68, controls ALL_OK. Lint: no new FAIL. Tree restored (SNAPSHOT EQUAL). Findings SY-F01 (confirm 4 imports), SY-F02, SY-F03 (ledger recommended) pending Seyoon; SY-F04 fixed. **Post-merge addendum** (`post-merge-addendum.md`): merge with `201bf57a` clean, no file overlap, no name clash; SY-F03 extended (sc-yao's `encodeMsgs_eq_encWords` now copies #327's public `SequentialZK.encodeMsgs_eq_encWords`, itself unledgered DL-49 class); SY-F05's `OTAnswerWords` pair goes to the post-merge cleanup. Next: push the landing branch, draft PR, integration build on the new tip (`dl-oleans-2`), Gate 42 (Codex). | sc-yao ACCEPT WITH LE; PR + Gate 42 next |
line 821: | 2026-11-16 | **Draft PR #341 opened** (sc-yao landing, head `e9b03c43`, branch `land/pass-shelat-sc-yao` pushed). Started: the integration build of #341 × the tip `f22e0f67` on `dl-oleans-2` (merge condition; `yaoProtocol_hbcSecure` expected standard now that #324 is merged), and Gate 42 staging (Codex; records pin `f22e0f67`). DW-5/DW-4 cleanup waits for a free tree. | #341 Gate 42 staging |
line 822: | 2026-11-16 | **Rulings (Seyoon) on sc-yao (#341):** SY-F01 confirmed (the four helper imports); SY-F02 ledger then promote (DL-51; `statClose_of_uprob_ne` to `Asymptotic/Sampling` in the cleanup); SY-F03 ledger both (DL-49 extended with sc-yao's and #327's `encodeMsgs_eq_encWords`; one common copy in the cleanup). No change to #341. `fills/sc-yao/final-r1/rulings.md`. DW-4 now spans DL-38 to DL-51. Still to acknowledge: SY-F05's `OTAnswerWords` pair against #324's `HybridProtocol.length_answers*` (recommended ledger, re-point after #341 merges). | SY-F01–F03 ruled |
line 829: | 2026-11-16 | #341's description updated to head `355a0288` (Gate 42 r1 landing edits; integration PASS; `yaoProtocol_hbcSecure` standard). **Started:** Gate 42 round 2 staging (no tree), and **DW-5** (derand typed-view readers for `ModuleHost`/`IterateFindHost`, re-deriving E1 `computesFunInTime_find` and `polyTimeComputable_find` through them, targeting 0 of F-01's 20 seal failures) on the freed `dl-oleans-2`, branch `cleanup/dw5-derand-readers`. | G42 r2 staging; DW-5 running |
line 839: | 2026-11-16 | **Ruling (Seyoon): rebase the olean snapshots.** After the two running builds finish (tip × #341 × #340 on `dl-oleans`; DW-5 on `dl-oleans-2`), each tree in turn builds the current records tip from its snapshot base `eff2dcd0` (snapshot `457ba704…`), checks it (rc 0, 0 errors, state OK) and is re-snapshotted at the tip. Later jobs then recompile only a PR's downstream instead of about 700 modules (including `DetMod`, about 25 min). The restore target changes to each tree's new snapshot hash, recorded here. One tree at a time, because of disk. | snapshot rebase queued |
line 841: | 2026-11-16 | **DW-5 done** (branch `cleanup/dw5-derand-readers` at `daa6e173`, pushed; 2 signed commits on `2da7e0f3`; evidence `maintenance/dw5/`, zip `12abc05a`; moved from `cleanup/dw5/` because `.gitignore` ignores `cleanup/`). Nine typed-view readers: `hostTMView` with `_eq`, `_q₀`, `_step_inl`, `host_call_view` and `host_clean_view` in `ModuleHost`; `copyTMView` with `_eq` and `copy_clean_view` in `IterateFindHost`. E1 `computesFunInTime_find` is re-derived through them, and `polyTimeComputable_find` from E1 (the F-03 route, removing 196 copied lines). Headers and prose are unchanged. **F-01's 20 IterateFind seal failures go to 0** (strict and coe, A and B); controls ALL_OK; 0 foreign unfolds in changed declarations. Build 706/706 rc 0; state 1342/1342; axioms standard; admissions unchanged (229 base); decls2 +9 / 0 / 0; lint unchanged; no name clash; `dl-oleans-2` restored (SNAPSHOT EQUAL). Disclosed: E1 restates the dispatch/branch/halt steps in-proof (the public `host_*` lemmas read `hostTM`'s fields); `host_dispatch`, `host_branch`, `host_halt`, `IterateFind.hostTM` and `copyTM_k` become unused. **Scope question for Seyoon:** 26 pre-existing seal failures in the two host files (`ModuleHost` 10, `IterateFindHost` 16), untouched by the change. | DW-5 done; scope Q |
line 842: | 2026-11-16 | **DW-5 scope ruling (Seyoon): the 26 pre-existing host-file seal failures become new deferred item DW-9.** DW-5 counts as clearing F-01's 20. The DW-5 PR and its gate record this. | DW-9 |
line 843: | 2026-11-16 | **Draft PR #347 (DW-5) opened** at `daa6e173` (branch `cleanup/dw5-derand-readers`). It records the DW-9 ruling. A Codex gate is to be staged; the next free number is 47, since 45/46 are reserved for phase 6. | #347 opened |
line 846: | 2026-11-16 | **#341 merged** (`a6d01b1b`). The tip's Lean equals the tested tree A `c6faa7c5`. **Every Pass–shelat ch. 5–8 target is now proved** (`yaoProtocol_hbcSecure` standard; Yao's admissions 2 → 0). Run 3 (fills) is complete. Next for this campaign is Run 4 (closure): census and axiom prints, lint and screens, the completion record, the deferred items (DW-4 dedup incl. DL-49/51/52, DW-9, the PS10 ch. 5–8 ingest), then `main`. The new snapshot is being advanced to `a6d01b1b` by the procedure's first replay. | #341 merged; ch. 5–8 proved |
line 850: | 2026-11-17 | **Cleanup staging ruled (Seyoon): three stages** (`briefs/pass-shelat-ch5-8/cleanup-stages.md`): (1) promotions, additive, gated as new public API, including DW-9's host-lemma view versions; (2) re-point and prune, proof-only: all Pass–shelat ledger rows, DW-9 and `Uniform` seal fixes, dead code, nits, then a proof audit and full seal sweep; (3) closure: PS10 ch. 5–8 ingest, census, axioms, lint, completion record, closure audit, then `main`. Rebuilds and gates only between stages. Preconditions: #347 merged and the bb1-sim Games PR merged before Stage 1. DW-1/DW-2 remain after `main`. | cleanup stages |
line 851: | 2026-11-17 | **Cleanup in parallel with GSW/IBE (Seyoon).** Stage 1 starts now as an external job, owning no file the running GSW/IBE jobs edit, and is stacked on #347 (Gate 47 audits #347 and Stage 1 together). The PS10 ch. 5–8 ingest runs now as an external docs job. Stage 2 follows the merge of Stage 1 and the bb1-sim Games PR. Staging both jobs. | cleanup parallel |
line 855: | 2026-11-17 | **Cleanup Stage 1 rulings CS1-Q1 to CS1-Q12 (Seyoon)** (`cleanup-stages.md`). Nine as recommended. Changed: **Q2**, the six statement/body changes are approved and Stage 2 removes DL-35's public `blocks` alias too; **Q8**, DL-49's ThreeColoring helpers are promoted to a shared machine layer in Stage 1, and Stage 2 re-points both ThreeColoring and ComposeSecurity; **Q9**, DL-43's lemma goes to `Games/Probability.lean` in Stage 2, after bb1-sim frees it. The package is being updated (it had 25 targets and 59 declarations). | CS1 ruled |
line 856: | 2026-11-17 | **ps10-cite-check delivered** (exchange `69add654`; filed at `ingests/ps10-cite-check-final-r1/`). Of 67 locators, 48 numbered, 7 lettered, 12 § and the page/chapter locators all exist with the cited kind and page. Of 871 citing sites, 831 are OK and **40 content mismatches** (Tier A, 15 locators; 19 under Thm 180.1, mostly one wrong "step 4" label) plus 21 advisory notes. The docstring fixes go into cleanup Stage 2. Also delivered: `stmt bb1-sim: final` (`a3cb45f6`), under review. | cite check in |
line 857: | 2026-11-17 | **Historical seal debt ruled (Seyoon): inventory now, fixes in Stage 2** (deferred item DW-10). It covers the #248 ledger, the 72 + 52 provider pairs deferred on 2026-11-10, Yao/sc-garble seal B (listed) and `CodeSimulator` (listed; outside the campaign). **Stage 1 package updated to the CS1 rulings** (`cleanup-stage1/issued-r1/`; 27 targets, S1-13 withdrawn, 69 declarations; new S1-26 and S1-27, the shared machine helpers in `ZeroKnowledge/EncodingMachines.lean`; Stage 2 handover lists the six approved Q2 changes). Exchange `d929cc21` on `6a9b6e19` is pushed. A seventh Q2 change (`ETTGame.dTape` body) awaits Seyoon. | DW-10; Stage 1 staged |
line 859: | 2026-11-17 | **Cleanup Stage 1 dispatched (Seyoon)** to a Claude cloud worker (lead plus up to 2 sub-agents), pinned to exchange `d929cc21` and records `f7308a62`, on the issue base `daa6e173` (#347 head) with check tree `01cc6259`. Deliveries go to `inbox/fills/cleanup-stage1/`; checkpoint 1 is statements elaborating, with decls2, the StmtDump, the shadow scan and the reuse table. Gate 47 audits #347 together with the Stage 1 PR. | Stage 1 out |
line 860: | 2026-11-17 | **DW-10 inventory staged and ruled (Seyoon).** Job `dw10-seal-inventory` (Claude, lead + 2 sub-agents, checks only) at records `4367db3c` and exchange `d4cfd2f8` (pushed), issue base `f472accd` (Lean = snapshot T `a6d01b1b`). Rulings: **Q1** the campaign seals only cryptography content; the 21 Complexity/Arora–Barak files (608 recorded items, incl. `Uniform` SY-F07 and `CodeSimulator` C-F02) are handed off to a separate chat, and owner failures needing a Complexity reader are `STAGE2-PROVIDER-READER`; **Q2** keep the 20 adopted Garg/InformationTheory owners (434 owners); **Q3** the `FinDist` coercion is notation (strict-only failures recorded, no fix); **Q4** exclude untouched Arora–Barak files. **Handoff target: wait for the campaign merge** into `main`, then re-derive at `main`'s tip. Estimated job: about 2.1–2.5 M seal requests, 10–16 h serial Lean. | DW-10 ready |
line 861: | 2026-11-17 | **DW-10 seal inventory dispatched (Seyoon)** to a Claude cloud worker (lead + up to 2 sub-agents), pinned to exchange `d4cfd2f8` and records `4367db3c`. Deliveries go to `inbox/audits/dw10-seal-inventory/`; checkpoint 1 gives a status for every recorded item. The result feeds the cleanup Stage 2 brief. | DW-10 out |
line 862: | 2026-11-17 | **#351 merged; olean snapshot #3 adopted** at `cf7d28f7` (map `e9dfbfdd…`; `maintainer/olean-snapshot-3-adopt/`, `snapshots.md`). `ProbComp.abs_expect_sub_le_expect` is now public in `Games/Probability.lean`, which unblocks the DL-40 re-point and CS1-Q9 in cleanup Stage 2. | snapshot #3 |
line 863: | 2026-11-17 | **Olean snapshot #4 adopted** at the #352 merge `463f2244` (map `6607620d…`). **Ruling (Seyoon): small merged changes share one combined gate later** (DW-11; first members #351, #352). | snapshot #4; DW-11 |
line 867: | 2026-11-17 | **Cleanup Stage 1 checkpoint 1 reviewed: proceed with notes** (`cleanup-stage1/checkpoint1-review.md`, zip `5b2402d6…`; exchange `bc2bf64a`). Patches reproduce (head `c8021348`); check tree `01cc6259`; decls2 69 ADDED / 0 / 0; all 69 headers and pinned bodies match the brief; `protected` rule 0 exceptions; 0 clashes; shadow scan clean incl. dot notation; additive only (+1079/−0, 21 files), no frozen file touched. 0 blockers/majors; minors CS1-C1-F01 (undisclosed `padL`/`padStr` padding overlap), F02 (two copies missing from the Stage 2 table), F03 (cited evidence missing); infos F04–F11. Question CS1-C1-Q1 (zero word and padding overlap) to Seyoon. | CS1 CP1 |
line 868: | 2026-11-17 | **Ruling CS1-C1-Q1 (Seyoon): keep, disclose, ledger.** S1-27 stays as CS1-Q8 ruled (69 declarations); the Stage 1 final discloses the `padL`/`padStr`/`padSq`/zero-word overlaps; new ledger row **DL-53** consolidates the families after the campaign merges. Checkpoint feedback sent to the worker via Seyoon. | CS1-C1-Q1 |
line 869: | 2026-11-17 | **Cleanup Stage 1 final delivered** (exchange `5451d3cd`, 06:20). Phase-1 (static) maintainer review started (`cleanup-stage1/final-r1/review.md`): CS1-C1 closures, the Stage 2 re-point table, evidence recount, merges with the tip, #340/#346/#347 and the 6a landing. Then phase 2 (replays on snapshot #4), the Stage 1 PR stacked on #347, and Gate 47. | CS1 final in |
line 870: | 2026-11-17 | **Cleanup Stage 1 final: phase-1 review — code ACCEPT as delivered; report layer needs a maintainer Stage 2 addendum** (`cleanup-stage1/final-r1/review.md`, zip `37bfa750…`). Code unchanged since checkpoint 1 (head `c8021348`, tree `508f9154`); decls2 69/0/0; pure insertion; evidence recounts (847 bootstrap, 495 sweep, 144 seal records, 20/20 controls, 0 foreign unfolds, lint clean); tip × #347 × Stage 1 = `5a2e818d`, clean. Findings: **CS1-F01 major** (S1-26 `msgAt_encodeMsgs` duplicates `ColZK.field_encodeMsgs` and `ColMachines.getD_eq_pairFstD_iterate`; Stage 2 copies), **CS1-F02 major** (the final did not act on the CS1-C1 feedback; reuse table unchanged), minors F04 (removing the public `blocks` alias needs 7 more changes), F05 (Stage 2 table gaps; addendum written), F06 (signed exchange commit). Questions Q1–Q4 to Seyoon. | CS1 P1 |
line 871: | 2026-11-17 | **Stage 1 final rulings (Seyoon), all as recommended:** Q1 maintainer Stage 2 addendum, DL-49 extended (`msgAt_encodeMsgs`); Q2 the seven extra `blocks`-alias changes approved (fourteen in Stage 2); Q3 CS1-W1/W2 already answered; Q4 PR stacked on #347, then retargeted. Next: landing branch `land/cleanup-stage1`, phase-2 replay of tip × #347 × Stage 1 (551 modules) on snapshot #4, draft PR, Gate 47. | CS1 Q1–Q4 |
line 872: | 2026-11-17 | **Stage 1 draft PR #355 opened**, stacked on #347 (`cleanup/dw5-derand-readers`): head `d3c7cb00092ad5913904654d922f30fc7d5fce4a`, five signed cherry-picks (range-diff 5/5 identical), tree `508f9154`, 21 files +1079/−0. Phase 2 (≈551-module replay) waits for #340 and #346 to merge, so it runs once on snapshot #5 instead of twice (their rebuild sets overlap Stage 1's). | #355 |
line 873: | 2026-11-17 | **Olean snapshot #5 adopted** at `3f540c22` (#340 + #346 merged; map `fca1b6a3…`). Stage 1 phase 2 (tip × #347 × #355) now runs on #5. | snapshot #5 |
line 874: | 2026-11-17 | **Cleanup Stage 1 phase 2: PASS** (`cleanup-stage1/final-r1/phase2.md`, zip `854d6430…`; `review.md` final verdict appended). TS1 = tip `e1d39836` × #347 `daa6e173` × #355 `d3c7cb00` = tree `1eaf940b` (clean in 5 orders). Replay on snapshot #5 (`olean-replay-cs1`): **556/556 rc 0**, state 1429/1429 OK, link count 1, #5 0/0/0. Admissions 196 = 196 per module. Standard axioms (census of 1224 constants over 21 owners). Seals A/B strict/coe on 21 owners: Stage 1's rows equal the worker's head and #347's equal DW-5's. `IterateFind` goes 20 → 0. Strict-only failures in six new `FinDist` declarations are the coercion (notation, DW-10 Q3). Pre-existing failures are identical at the tip. Controls ALL_OK; 0 foreign unfolds. Lint: Cryptography 92/104 → 92/103. Adopt `olean-replay-cs1` only if a merge's Lean equals TS1 (both PRs merged with nothing between). Gate 47 must disclose the 7 items in `phase2.md`, including that GSW 6a is not in TS1, so whichever merges second re-replays. Next: stage Gate 47. | CS1 P2 PASS |
line 875: | 2026-11-17 | **Olean snapshot #6 adopted** at T `8060f6b7` (the #357 merge). Source: LE-g48's replay `olean-replay-bb1sim-g48`, audited CLEAR in Gate 48 round 2. Step-3 diff empty. #5 at retirement 0/0/0. `Mathlib/` overlay removed. Map `0858dccb…` (1463 entries, byte-equal to the audited map); files manifest `1ae04ef5…`. init + basecheck at `8060f6b7` RESULT OK (1432 modules). Swap done, rehash 0/0/0. `olean-replay-bb1sim` deleted (`maintainer/olean-snapshot-6-adopt/`, `snapshots.md`). No longer adoptable: `olean-replay-cs1`, `-6a-o1`, `-6a-stmt`, `-6a-stmt-g45` and `-6a-readers` (#360), and the in-house fill trees. Each PR re-replays on #6 before its merge-time adoption. | snapshot #6 |
line 876: | 2026-11-17 | **Gate 47 pre-dispatch sweep rulings (Seyoon).** The staged pack (exchange commit `937e6a55`, local only) was held after the duplication sweep. **B1: accept, unify in Stage 2 → DL-59.** #355's `Games.extTape`/`extTape_of_lt`/`extTape_update` restate LazySampling's `extendStream`/`_def`/`_update_of_ne`; DL-40's `AdaptiveCPA.extTape` is a third copy. Stage 2 keeps one family in `Games/Tapes`. **B2–B7: ledger and disclose → DL-60.** B3 extends DL-53 (`padTo` vs `List.takeD`), B4 extends DL-49, B2 goes to the Complexity handoff (a `sorry` twin in `FormulaKit/Emit`), and B5–B7 are analogues, disclosure only. #355's code is unchanged. Next: update the pack to the rulings at the new records pin, then dispatch. | G47 B1–B7 ruled |

## PairingCryptographyPlan.md at the pin, line 464 (the #357 merge)

| 2026-11-17 | **#357 merged (Seyoon)** as `8060f6b7`. **Boneh–Boyen BB1 selective-ID security is complete on the records branch.** The merge's Lean equals `dfdc56f2` (step-3 diff empty), so `olean-replay-bb1sim-g48` (map `0858dccb…`) is adoptable as **olean snapshot #6**. Adoption waits until the running LE-g45 job finishes, because it rehashes snapshot #5. The other open replays (#347/#355 TS1, the 6a trees, #360) are built on #5 without #357, so each re-replays on #6 before its merge-time adoption; the audit evidence stands. | #357 merged |

## ===== verification-r1.zip:MANIFEST.md (this pack) =====

# verification-r1.zip · Gate 47 (cleanup Stage 1 gate: #347 and #355) · manifest

Built at staging (2026-11-17) from git objects and from evidence already recorded; **nothing was re-run** except the
git-only checks under `checks/`. No Lean, no `lake`. `SHA256SUMS` lists every other entry of this zip.

| Path | Provenance |
|---|---|
| `checks/series.txt` | Pins, both PRs' commits (parent, tree, signature header, author, committer, trailers with the Co-Authored-By value elided, files), TS1 recomputation, the range-diff of the worker series `c8021348` against #355. `tools/gitchecks.py`. |
| `checks/insertion.txt` | Per-file `+/−` of #347 (from its merge base `2da7e0f3`) and #355 (from `daa6e173`), with every deleted line outside `IterateFind.lean` listed. |
| `checks/sizes.txt` | The 23 TS1 paths: lines at `e1d39836` and at TS1, maximum width of the file and of the added lines, blob and SHA-256. |
| `checks/source-head-r1.json` | Same content as the pack's `source-head-r1.json`. |
| `checks/mergetrees.txt` | `git merge-tree --write-tree` of #347/#355 with #357, #358, #359 and #360, in both orders against the records pin, and all together. `tools/mergetrees.sh` (temporary unreferenced commit objects only). |
| `checks/downstream.txt` | Import-graph overlap on each merged tree: modules downstream of TS1's 23 paths and of each other PR's paths. `tools/downstream.py` (validated: it gives 556 at TS1, equal to phase 2's `plan/queue.txt`). |
| `checks/dup-sweep.txt` | The duplication sweep over the 78 new declarations: method, classification A (in the records) and B (not in the ledger). |
| `checks/dup/` | Raw sweep outputs: same-short-name hits (TS1 and Mathlib/Batteries/core), shape hits, statement-header hits. |
| `checks/tools/` | Every script this staging ran. |
| `phase1/` | Subset of `cleanup-stage1-final-r1-phase1-evidence.zip` (records, SHA-256 `37bfa750…`), paths under its `cs1-final-r1/`; `SHA256SUMS.original` holds the original lines for the copied files. |
| `phase2/` | Subset of `cleanup-stage1-final-r1-phase2-evidence.zip` (`854d6430…`), under its `cs1-final-r1-phase2/`; `SHA256SUMS.original` likewise. |
| `dw5/` | Subset of `maintenance/dw5/dw5-evidence.zip` (`12abc05a…`), under its `dw5/`; `SHA256SUMS.original` holds the lines of the records' `maintenance/dw5/SHA256SUMS`. |
| `delivery/` | `REPORT.md`, `reuse-table.md`, `repoint.tsv` of the Stage 1 worker delivery, read at exchange `5451d3cd6fa9b8c313c9f18f5a4da3542c85f02a`. |
| `records/` | Campaign records read at the pin `659542ecd9413b504d30da8c937b9805e6c1f71f`: `cleanup-stages.md`, `deferred-work.md`, `duplication-ledger.md`, the DW-5 README, the Stage 1 checkpoint-1 review, final review, phase 2, the Stage 2 addendum, the issued brief, `snapshots.md`, the snapshot-#6 adoption README, the Complexity handoff README (DL-60 B2 addendum), `policy.md`, `workflow.md`, the Gate 44/45/48 findings, and `decision-log-rows.md` (filtered rows, verbatim). |
| `pr/` | `gh api repos/Shilun-Allan-Li/tcslib/pulls/{347,355}` at staging (REST fields, bodies). |

## ===== verification-r1.zip:POINTERS.md (this pack) =====

# verification-r1.zip · what is not copied, and where it is

All paths are on the records branch at the pin `659542ecd9413b504d30da8c937b9805e6c1f71f` unless stated.

| Evidence | Where | SHA-256 |
|---|---|---|
| Stage 1 final, phase 1 (whole) | `briefs/pass-shelat-ch5-8/cleanup-stage1/final-r1/cleanup-stage1-final-r1-phase1-evidence.zip` (66 entries) | `37bfa7506c63716b43e632c75c3af7490ffe3ffd1702f2725ec0c8b2fd0cdbd1` |
| Stage 1 final, phase 2 (whole: build records of 556 modules, all probe sources and logs at head and tip, state files) | `briefs/pass-shelat-ch5-8/cleanup-stage1/final-r1/cleanup-stage1-final-r1-phase2-evidence.zip` (2.2 MB) | `854d6430fad819e469b126565c0e3200f43b86c8ac2f83d4b133ed75c6bfd9f3` |
| Stage 1 checkpoint-1 review evidence | `briefs/pass-shelat-ch5-8/cleanup-stage1/checkpoint1-review-evidence.zip` | `5b2402d680c5d2d24f18d8cc1a960baea436a9f7f12847dd0661697a73aa06d8` |
| DW-5 (#347) evidence (whole: 706-module build, base and head seals, probes, controls, scan, restore) | `briefs/pass-shelat-ch5-8/maintenance/dw5/dw5-evidence.zip` (4.5 MB); every entry in `maintenance/dw5/SHA256SUMS` | `12abc05a61c08de7cb38b9d3bccdea5b3dd44dff6f65f036a50584a39e1dd630` |
| Stage 1 issued package | `briefs/pass-shelat-ch5-8/cleanup-stage1/issued-r1/` (`SHA256SUMS`, `SOURCE-SHA256SUMS`, closures, order) | per its `SHA256SUMS` |
| Worker delivery (whole: patches, build logs, seal records, controls, probes) | exchange branch, `inbox/fills/cleanup-stage1/` at `5451d3cd6fa9b8c313c9f18f5a4da3542c85f02a` (final) and `bc2bf64a0c8449adb61234d957acb0e737fb66d5` (checkpoint 1) | per its `SHA256SUMS` |
| The replay output itself | maintainer scratchpad `$SP/olean-replay-cs1` (not in the repository; no longer adoptable: the #357 merge voided it and snapshot #6 was adopted at `8060f6b7`; #347/#355 re-replay on #6) | phase 2's `plan/state-after-update-1eaf940b.json.gz` |

## ===== verification-r1.zip:checks/series.txt (this pack) =====

records pin (records-only advance from 95da6120, the tip fetched 2026-11-17 11:24 UTC): 659542ecd9413b504d30da8c937b9805e6c1f71f
  pin log: Records: LE-g45b on #359; Gate 47 sweep rulings (DL-59, DL-60)
  phase-2 records tip e1d39836 is an ancestor of the pin: True
  Lean paths 95da6120..pin: 0
  Lean paths e1d39836..pin: 9 (the #357 merge 8060f6b7): TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyen.lean, TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenSecurity.lean, TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenSecurity/Chain.lean, TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenSecurity/Coupling.lean, TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenSecurity/Lazy.lean, TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenSecurity/Random.lean, TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenSecurity/Real.lean, TCSlib/Cryptography/AdvancedEncryption/IdentityBased/Defs.lean, TCSlib/Cryptography/Games/Relational.lean

#347 head daa6e173cdd94cad1475b9a96eca613bce53ba61; merge base with the pin 2da7e0f3cd65ec93ed71813b7828c3b66ba18942
#355 head d3c7cb00092ad5913904654d922f30fc7d5fce4a; base branch cleanup/dw5-derand-readers = daa6e173cdd94cad1475b9a96eca613bce53ba61; #347 is an ancestor: True
#355 tree 508f915413ee8ef9f2a37b59e0012c9daf3867aa (records: 508f9154...)

#347 commits 2da7e0f3..daa6e173:
  1da80d9a952c3da3e406f58188cca66de94cbfaf parent 2da7e0f3 tree 3c2cc86e gpgsig 1 | DW-5 (derand F-01): typed-view readers for the clean-module host and the copier
    author Claude <noreply@anthropic.com> 2026-11-16T19:55:26+00:00; committer Claude <noreply@anthropic.com> 2026-11-16T19:55:26+00:00
    trailers: Co-Authored-By: (present) / Claude-Session: https://claude.ai/code/session_01PqpVTiuDcjSqhyfbqnsVxA
    files: TCSlib/Complexity/Randomized/Build/IterateFindHost.lean, TCSlib/Complexity/TuringMachine/Build/ModuleHost.lean
  daa6e173cdd94cad1475b9a96eca613bce53ba61 parent 1da80d9a tree 2ae32eb3 gpgsig 1 | DW-5 (derand F-01): re-derive computesFunInTime_find and polyTimeComputable_find through the typed views
    author Claude <noreply@anthropic.com> 2026-11-16T19:55:37+00:00; committer Claude <noreply@anthropic.com> 2026-11-16T19:55:37+00:00
    trailers: Co-Authored-By: (present) / Claude-Session: https://claude.ai/code/session_01PqpVTiuDcjSqhyfbqnsVxA
    files: TCSlib/Complexity/Randomized/Build/IterateFind.lean

#355 commits daa6e173..d3c7cb00:
  761a37031cc229abb24d0ce83edf195739e4bec2 parent daa6e173 tree 349d0215 gpgsig 1 | cleanup stage1: DW-9 view versions of the host control steps
    author Claude <noreply@anthropic.com> 2026-11-17T03:20:38+00:00; committer Claude <noreply@anthropic.com> 2026-11-17T07:37:59+00:00
    trailers: Co-Authored-By: (present) / Claude-Session: https://claude.ai/code/session_01PqpVTiMTR17aD6p7XuRrcc
    files: TCSlib/Complexity/Randomized/Build/IterateFindHost.lean
  c502027cf15d1bb539dfd9d62744347b88c359c4 parent 761a3703 tree 44cbe301 gpgsig 1 | cleanup stage1: Games forms of simulation in law, coin tapes and tables (DL-40, DL-41, DL-42)
    author Claude <noreply@anthropic.com> 2026-11-17T03:20:38+00:00; committer Claude <noreply@anthropic.com> 2026-11-17T07:37:59+00:00
    trailers: Co-Authored-By: (present) / Claude-Session: https://claude.ai/code/session_01PqpVTiMTR17aD6p7XuRrcc
    files: TCSlib/Cryptography/Games.lean, TCSlib/Cryptography/Games/Bridges/Experiments.lean, TCSlib/Cryptography/Games/Efficiency/Strings.lean, TCSlib/Cryptography/Games/Machines.lean, TCSlib/Cryptography/Games/Tapes.lean
  9b6b29ae913670d7273000cb19c8f47fbaf46994 parent c502027c tree 8b3767ff gpgsig 1 | cleanup stage1: bit-list, coin, encoding and closeness readers (DL-35, DL-40, DL-41, DL-46, DL-47, DL-48, DL-51)
    author Claude <noreply@anthropic.com> 2026-11-17T03:20:38+00:00; committer Claude <noreply@anthropic.com> 2026-11-17T07:37:59+00:00
    trailers: Co-Authored-By: (present) / Claude-Session: https://claude.ai/code/session_01PqpVTiMTR17aD6p7XuRrcc
    files: TCSlib/Complexity/Randomized/PPT.lean, TCSlib/Cryptography/Asymptotic/Adversary.lean, TCSlib/Cryptography/Asymptotic/Sampling.lean, TCSlib/Cryptography/Authentication/Encoding.lean, TCSlib/Cryptography/Encryption/PrivateKey/EnsembleSecurity.lean, TCSlib/Cryptography/Encryption/PublicKey/Trapdoor.lean, TCSlib/Cryptography/Foundations/BitLists.lean, TCSlib/Cryptography/Pseudorandom/Functions/Asymptotic/Defs.lean
  d7c02949a1f095a441eba481a8d47826ae97ffd6 parent 9b6b29ae tree 9864024e gpgsig 1 | cleanup stage1: history encoding and the shared machine helpers (DL-38, DL-45, DL-49)
    author Claude <noreply@anthropic.com> 2026-11-17T03:23:33+00:00; committer Claude <noreply@anthropic.com> 2026-11-17T07:37:59+00:00
    trailers: Co-Authored-By: (present) / Claude-Session: https://claude.ai/code/session_01PqpVTiMTR17aD6p7XuRrcc
    files: TCSlib/Cryptography/ZeroKnowledge.lean, TCSlib/Cryptography/ZeroKnowledge/EncodingMachines.lean, TCSlib/Cryptography/ZeroKnowledge/Interaction.lean, TCSlib/Cryptography/ZeroKnowledge/InteractionWords.lean
  d3c7cb00092ad5913904654d922f30fc7d5fce4a parent d7c02949 tree 508f9154 gpgsig 1 | cleanup stage1: finite-distribution facts (DL-39)
    author Claude <noreply@anthropic.com> 2026-11-17T03:23:33+00:00; committer Claude <noreply@anthropic.com> 2026-11-17T07:37:59+00:00
    trailers: Co-Authored-By: (present) / Claude-Session: https://claude.ai/code/session_01PqpVTiMTR17aD6p7XuRrcc
    files: TCSlib/InformationTheory/Entropy.lean, TCSlib/InformationTheory/FinDist.lean, TCSlib/InformationTheory/Samples.lean

TS1 recomputation: merge-tree e1d39836 x #347 = f905d841a4c2a016fc40b64e1ddbf34000d0b766; TS1 = 1eaf940b938bb52e3919f5569893b58522df599b (recorded); TS1 is a tree object: tree
TS1 vs e1d39836 Lean: 23 files changed, 1332 insertions(+), 296 deletions(-)
pin x #355 = 20d1101ade46ba26919f01e30f7ee9422495669b; Lean paths differing from TS1: 9 (exactly #357's 9, blob-equal to dfdc56f2; mergetrees.txt)

range-diff of the worker series (exchange 5451d3cd, COMMITS.tsv) against #355:
1:  4881cf98a = 1:  761a37031 cleanup stage1: DW-9 view versions of the host control steps
2:  01f6b7e90 = 2:  c502027cf cleanup stage1: Games forms of simulation in law, coin tapes and tables (DL-40, DL-41, DL-42)
3:  7b8a4d975 = 3:  9b6b29ae9 cleanup stage1: bit-list, coin, encoding and closeness readers (DL-35, DL-40, DL-41, DL-46, DL-47, DL-48, DL-51)
4:  85797b502 = 4:  d7c02949a cleanup stage1: history encoding and the shared machine helpers (DL-38, DL-45, DL-49)
5:  c8021348f = 5:  d3c7cb000 cleanup stage1: finite-distribution facts (DL-39)
worker head c8021348 tree 508f915413ee8ef9f2a37b59e0012c9daf3867aa

## ===== verification-r1.zip:checks/insertion.txt (this pack) =====

Per-file line counts (git diff --numstat); deleted lines are listed in full.

#347 2da7e0f3..daa6e173: 3 files, +253/-296
  +126   -294   TCSlib/Complexity/Randomized/Build/IterateFind.lean
  +30    -2     TCSlib/Complexity/Randomized/Build/IterateFindHost.lean
  +97    -0     TCSlib/Complexity/TuringMachine/Build/ModuleHost.lean
  deleted lines in TCSlib/Complexity/Randomized/Build/IterateFindHost.lean:
    -* `Complexity.IterateFind.copyTM` — the input copier.
    -* `Complexity.IterateFind.copy_clean` — the copier's contract.

#355 daa6e173..d3c7cb00: 21 files, +1079/-0
  +60    -0     TCSlib/Complexity/Randomized/Build/IterateFindHost.lean
  +8     -0     TCSlib/Complexity/Randomized/PPT.lean
  +30    -0     TCSlib/Cryptography/Asymptotic/Adversary.lean
  +29    -0     TCSlib/Cryptography/Asymptotic/Sampling.lean
  +19    -0     TCSlib/Cryptography/Authentication/Encoding.lean
  +14    -0     TCSlib/Cryptography/Encryption/PrivateKey/EnsembleSecurity.lean
  +10    -0     TCSlib/Cryptography/Encryption/PublicKey/Trapdoor.lean
  +52    -0     TCSlib/Cryptography/Foundations/BitLists.lean
  +3     -0     TCSlib/Cryptography/Games.lean
  +8     -0     TCSlib/Cryptography/Games/Bridges/Experiments.lean
  +11    -0     TCSlib/Cryptography/Games/Efficiency/Strings.lean
  +12    -0     TCSlib/Cryptography/Games/Machines.lean
  +346   -0     TCSlib/Cryptography/Games/Tapes.lean
  +21    -0     TCSlib/Cryptography/Pseudorandom/Functions/Asymptotic/Defs.lean
  +2     -0     TCSlib/Cryptography/ZeroKnowledge.lean
  +173   -0     TCSlib/Cryptography/ZeroKnowledge/EncodingMachines.lean
  +46    -0     TCSlib/Cryptography/ZeroKnowledge/Interaction.lean
  +44    -0     TCSlib/Cryptography/ZeroKnowledge/InteractionWords.lean
  +48    -0     TCSlib/InformationTheory/Entropy.lean
  +80    -0     TCSlib/InformationTheory/FinDist.lean
  +63    -0     TCSlib/InformationTheory/Samples.lean


## ===== verification-r1.zip:checks/sizes.txt (this pack) =====

path	lines base(e1d39836)	lines TS1	max width TS1	max width of added lines	blob TS1	sha256 TS1
TCSlib/Complexity/Randomized/Build/IterateFind.lean	801	633	99	99	30edb6037ca4	fa61bace7c54b4e995562a998221bb921119e60cb3734437eac4377cc9896cb0
TCSlib/Complexity/Randomized/Build/IterateFindHost.lean	362	450	98	98	ebe98588f374	396e4cc79d6998eb4d3ff66a82357a6a251dfa4fa02d882c21cb6192680cb069
TCSlib/Complexity/Randomized/PPT.lean	486	494	102	98	36b6d77cba1e	4bc2e2c06660a004045a30205742f908542d58ec72dded845bb842d57071dd45
TCSlib/Complexity/TuringMachine/Build/ModuleHost.lean	672	769	98	97	4670e2e5dce9	5af07b7f5e3302de04ec29dc0a35de1286daa3d30cb7554669ab253852d94b92
TCSlib/Cryptography/Asymptotic/Adversary.lean	452	482	122	98	38029707b7be	e3adb0fc860132eafbf9157b804a1add15698900f72267f064e9d299806dc686
TCSlib/Cryptography/Asymptotic/Sampling.lean	936	965	106	97	dc37bf470e8a	792a6eba7672d718f935cc720cd53aebdf512f7465739245da8910d47651143d
TCSlib/Cryptography/Authentication/Encoding.lean	47	66	95	95	e9c982c671a1	763d91b35176ca9eb4dd223ac00b4aeaf39fadac8d8c795954be2c3d1111458a
TCSlib/Cryptography/Encryption/PrivateKey/EnsembleSecurity.lean	340	354	105	94	471d15aea1df	a7c221c9fb465519df652508760adecd5608f88c6070cece14e566c1ba1b7e4c
TCSlib/Cryptography/Encryption/PublicKey/Trapdoor.lean	570	580	112	98	7b54ccf42e53	ea79e31b0f3c0333ee22cdeac63313247be1ec2f37a7b0153b9f1e983b5c58ac
TCSlib/Cryptography/Foundations/BitLists.lean	192	244	100	100	19da9109151b	a032a22e6859f0912c13f54d792a7f1bdc9646adecb7c3b30d95daf0eed625cb
TCSlib/Cryptography/Games.lean	67	70	98	98	7cccb7675728	d3fec8c9d47effe7097a67e2ad36b15af70ec70e7a47029b02d11f1fd8f85d42
TCSlib/Cryptography/Games/Bridges/Experiments.lean	136	144	98	95	bd3da1d60d12	c408c2db32ae976a443078961673493c9890c111e4b45e29ff9dcba01e153a16
TCSlib/Cryptography/Games/Efficiency/Strings.lean	570	581	100	99	a35c0a32937d	a1bade0dbe209538538524c1f0793b42d597d028f73ac7f7ee9a9cef2b590cd2
TCSlib/Cryptography/Games/Machines.lean	278	290	99	98	529f17b450d2	750fd0036b9cbac9066633d0ce541aecbc4829a23d9ab7b8beb502298df7aa09
TCSlib/Cryptography/Games/Tapes.lean	new	346	100	100	895f59a882e6	95e3a8a9b32bbb1ef0d28a563b41fde8042da9d539e72b0827438bf0aff896e2
TCSlib/Cryptography/Pseudorandom/Functions/Asymptotic/Defs.lean	480	501	109	97	826ad37fdad8	799222f7376d2696190415392e4b36330797f3189350579cea508c6b050c47c2
TCSlib/Cryptography/ZeroKnowledge.lean	67	69	98	81	a10f4e96d879	d07948677b8df4e85bbd98d418110e2cc29d7bd5e9a3dc16e1722a3fade05787
TCSlib/Cryptography/ZeroKnowledge/EncodingMachines.lean	694	867	110	98	cad8ea7d618b	acd9a7fa5d9863a524931c79919c8f2089b965f85fb35fdd822c7482afbe836d
TCSlib/Cryptography/ZeroKnowledge/Interaction.lean	565	611	101	97	44d05a506072	22fae9d4e967a45f6db03e6ea4db7f19645356e4dae8e8c8253786cf3435e73b
TCSlib/Cryptography/ZeroKnowledge/InteractionWords.lean	new	44	96	96	046627f13739	ef038993652b6bd3845366a83e204ab5dae62654f59e56b99d7468040ab9aa3e
TCSlib/InformationTheory/Entropy.lean	215	263	99	96	dccabe2cffdd	84843687e0e0e4eaaa3b2331c58442b37bf2037f0f1842fc9dbcf975190b09c7
TCSlib/InformationTheory/FinDist.lean	200	280	100	100	c0be07bdbde7	d069022465f9adf284791350bbe30fde71bd21b91d079ff5a5b77b95ff6d0273
TCSlib/InformationTheory/Samples.lean	155	218	99	99	d7cc2daa2c27	4013504e37ede623b53a0c6b70d4a712234268de7d65092dd2742ef624794176

## ===== verification-r1.zip:checks/mergetrees.txt (this pack) =====

git 2.43.0; pin 659542ecd9413b504d30da8c937b9805e6c1f71f; #347 daa6e173cdd94cad1475b9a96eca613bce53ba61; #355 d3c7cb00092ad5913904654d922f30fc7d5fce4a; TS1 1eaf940b938bb52e3919f5569893b58522df599b
#357 head dfdc56f21898abe2d9d6cef83b0cfe57da87d28d
#358 head a616adcac0760ab56b1b0a2a4869f4763843f9ab
#359 head d154c8830fc8ffc52671b41992e7dbef61e30959
#360 head cc05f76c43cd2d2f565ff0dfaec1c85b47e06d25

pin x #347                                   rc=0 tree=de193146469e7b607ca56b2eaa521a9487c2ce94 mb=2da7e0f3 
(pin x #347) x #355                          rc=0 tree=20d1101ade46ba26919f01e30f7ee9422495669b mb=daa6e173 
pin x #355                                   rc=0 tree=20d1101ade46ba26919f01e30f7ee9422495669b mb=2da7e0f3 
Lean diff (pin x #347 x #355) vs (pin x #355): 0 paths
Lean paths differing (pin x #355) vs TS1: TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyen.lean,TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenSecurity.lean,TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenSecurity/Chain.lean,TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenSecurity/Coupling.lean,TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenSecurity/Lazy.lean,TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenSecurity/Random.lean,TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenSecurity/Real.lean,TCSlib/Cryptography/AdvancedEncryption/IdentityBased/Defs.lean,TCSlib/Cryptography/Games/Relational.lean
  each blob-equal to the #357 head dfdc56f2:       9 y
Lean of pin vs e1d39836 x #357 (tree 2888323275e1): 0 paths differ

== #357 dfdc56f21898abe2d9d6cef83b0cfe57da87d28d
  #347 x #357                                rc=0 tree=96be6b543109e418631a257fb3e8eb66bd40bc2a mb=2da7e0f3 
  #355 x #357                                rc=0 tree=0eaa82e328e003d6e4e29fa898f4fe05803b8d1e mb=2da7e0f3 
  (pin x #355) x #357  [TS1 first]           rc=0 tree=20d1101ade46ba26919f01e30f7ee9422495669b mb=dfdc56f2 
  pin x #357                                 rc=0 tree=c58a0a3b25830b0649b262d4889f48904b19f961 mb=dfdc56f2 
  (pin x #357) x #355  [#357 first]          rc=0 tree=20d1101ade46ba26919f01e30f7ee9422495669b mb=2da7e0f3 
  order-independent tree: yes
  #357 paths blob-equal to its head: 0/0; TS1 paths blob-equal to TS1: 23/23
  shared paths with #347/#355: 
== #358 a616adcac0760ab56b1b0a2a4869f4763843f9ab
  #347 x #358                                rc=0 tree=95bc8e067fe6c30df463db319049cdbc64733552 mb=2da7e0f3 
  #355 x #358                                rc=0 tree=cfea883d8ce912af155e6df94d33366aada2a66b mb=2da7e0f3 
  (pin x #355) x #358  [TS1 first]           rc=0 tree=0bef1875d2aaab03d13fc59429b30cc668a812e5 mb=e1d39836 
  pin x #358                                 rc=0 tree=ae83fdc08df8a300524c53233659951370b09771 mb=e1d39836 
  (pin x #358) x #355  [#358 first]          rc=0 tree=0bef1875d2aaab03d13fc59429b30cc668a812e5 mb=2da7e0f3 
  order-independent tree: yes
  #358 paths blob-equal to its head: 4/4; TS1 paths blob-equal to TS1: 23/23
  shared paths with #347/#355: 
== #359 d154c8830fc8ffc52671b41992e7dbef61e30959
  #347 x #359                                rc=0 tree=a01d285a8ed929eb637f474b9b543f264e61cb56 mb=2da7e0f3 
  #355 x #359                                rc=0 tree=fa1a9b0b139c0cb68b41ec56c0c743c470878e01 mb=2da7e0f3 
  (pin x #355) x #359  [TS1 first]           rc=0 tree=2bce1c63d6de34ad4665d4892655b9dec49aa586 mb=e1d39836 
  pin x #359                                 rc=0 tree=b524aa5b0bcb0246a57996de3bff2c0c555050d5 mb=e1d39836 
  (pin x #359) x #355  [#359 first]          rc=0 tree=2bce1c63d6de34ad4665d4892655b9dec49aa586 mb=2da7e0f3 
  order-independent tree: yes
  #359 paths blob-equal to its head: 19/19; TS1 paths blob-equal to TS1: 23/23
  shared paths with #347/#355: 
== #360 cc05f76c43cd2d2f565ff0dfaec1c85b47e06d25
  #347 x #360                                rc=0 tree=22a2e5d4ce6007528419a1293175c5dc24b2e3a0 mb=2da7e0f3 
  #355 x #360                                rc=0 tree=883114c78036971ee74e9033198caa337614f162 mb=2da7e0f3 
  (pin x #355) x #360  [TS1 first]           rc=0 tree=1f2d91ec6370095e7cdfbf86769091f120871703 mb=8c5875fa 
  pin x #360                                 rc=0 tree=a0e492a1e4436302af7da4cbdcb2136c268bef27 mb=8c5875fa 
  (pin x #360) x #355  [#360 first]          rc=0 tree=1f2d91ec6370095e7cdfbf86769091f120871703 mb=2da7e0f3 
  order-independent tree: yes
  #360 paths blob-equal to its head: 6/6; TS1 paths blob-equal to TS1: 23/23
  shared paths with #347/#355: 

== all together: ((((pin x #355) x #357) x #359) x #360)  [#359 contains #358]
  step #357                                  rc=0 tree=20d1101ade46ba26919f01e30f7ee9422495669b mb=dfdc56f2 
  step #359                                  rc=0 tree=2bce1c63d6de34ad4665d4892655b9dec49aa586 mb=e1d39836 
  step #360                                  rc=0 tree=17fdcf1f49449522112e214e69d0ffb9c6a9c066 mb=8c5875fa 

## ===== verification-r1.zip:checks/downstream.txt (this pack) =====

TS1 PRs (S1) vs #357 (S2): tree 20d1101ade46ba26919f01e30f7ee9422495669b; modules 1468
  S1 changed modules 23, downstream (incl.) 561
  S2 changed modules 9, downstream (incl.) 19
  S2 changed modules downstream of S1: ['TCSlib.Cryptography.AdvancedEncryption.IdentityBased.BonehBoyen', 'TCSlib.Cryptography.AdvancedEncryption.IdentityBased.BonehBoyenSecurity', 'TCSlib.Cryptography.AdvancedEncryption.IdentityBased.BonehBoyenSecurity.Chain', 'TCSlib.Cryptography.AdvancedEncryption.IdentityBased.BonehBoyenSecurity.Coupling', 'TCSlib.Cryptography.AdvancedEncryption.IdentityBased.BonehBoyenSecurity.Lazy', 'TCSlib.Cryptography.AdvancedEncryption.IdentityBased.BonehBoyenSecurity.Random', 'TCSlib.Cryptography.AdvancedEncryption.IdentityBased.BonehBoyenSecurity.Real', 'TCSlib.Cryptography.AdvancedEncryption.IdentityBased.Defs', 'TCSlib.Cryptography.Games.Relational']
  S1 changed modules downstream of S2: ['TCSlib.Cryptography.Games']
  downstream of both (19): ['TCSlib', 'TCSlib.Cryptography.AdvancedEncryption', 'TCSlib.Cryptography.AdvancedEncryption.IdentityBased', 'TCSlib.Cryptography.AdvancedEncryption.IdentityBased.BonehBoyen', 'TCSlib.Cryptography.AdvancedEncryption.IdentityBased.BonehBoyenMachine', 'TCSlib.Cryptography.AdvancedEncryption.IdentityBased.BonehBoyenMachine.Draws', 'TCSlib.Cryptography.AdvancedEncryption.IdentityBased.BonehBoyenMachine.Handler', 'TCSlib.Cryptography.AdvancedEncryption.IdentityBased.BonehBoyenMachine.Oracles', 'TCSlib.Cryptography.AdvancedEncryption.IdentityBased.BonehBoyenMachine.Reduction', 'TCSlib.Cryptography.AdvancedEncryption.IdentityBased.BonehBoyenMachine.Words', 'TCSlib.Cryptography.AdvancedEncryption.IdentityBased.BonehBoyenSecurity', 'TCSlib.Cryptography.AdvancedEncryption.IdentityBased.BonehBoyenSecurity.Chain', '...']
TS1 PRs (S1) vs #358 (S2): tree 0bef1875d2aaab03d13fc59429b30cc668a812e5; modules 1470
  S1 changed modules 23, downstream (incl.) 561
  S2 changed modules 4, downstream (incl.) 9
  S2 changed modules downstream of S1: ['TCSlib.Complexity.CircuitComplexity']
  S1 changed modules downstream of S2: []
  downstream of both (3): ['TCSlib', 'TCSlib.Complexity.CircuitComplexity', 'TCSlib.ComputationalModels']
TS1 PRs (S1) vs #359 (S2): tree 2bce1c63d6de34ad4665d4892655b9dec49aa586; modules 1481
  S1 changed modules 23, downstream (incl.) 561
  S2 changed modules 18, downstream (incl.) 20
  S2 changed modules downstream of S1: ['TCSlib', 'TCSlib.Complexity.CircuitComplexity', 'TCSlib.ComputationalModels']
  S1 changed modules downstream of S2: []
  downstream of both (3): ['TCSlib', 'TCSlib.Complexity.CircuitComplexity', 'TCSlib.ComputationalModels']
TS1 PRs (S1) vs #360 (S2): tree 1f2d91ec6370095e7cdfbf86769091f120871703; modules 1468
  S1 changed modules 23, downstream (incl.) 561
  S2 changed modules 6, downstream (incl.) 566
  S2 changed modules downstream of S1: []
  S1 changed modules downstream of S2: ['TCSlib.Cryptography.Encryption.PublicKey.Trapdoor', 'TCSlib.Cryptography.Games', 'TCSlib.Cryptography.ZeroKnowledge']
  downstream of both (308): ['TCSlib', 'TCSlib.Complexity.CircuitComplexity', 'TCSlib.Complexity.CircuitComplexity.CircuitEvalNP', 'TCSlib.Complexity.CircuitComplexity.CircuitSatNPHard', 'TCSlib.Complexity.CircuitComplexity.CircuitSatReduction', 'TCSlib.Complexity.CircuitComplexity.CircuitSatReductionValid', 'TCSlib.Complexity.CircuitComplexity.DAGCircuitSatLang', 'TCSlib.Complexity.CircuitComplexity.KarpLipton', 'TCSlib.Complexity.CircuitComplexity.KarpLiptonPrefix', 'TCSlib.Complexity.CircuitComplexity.KarpLiptonSearchFamily', 'TCSlib.Complexity.CircuitComplexity.LogspaceTableau', 'TCSlib.Complexity.CircuitComplexity.Meyer', '...']

## ===== verification-r1.zip:checks/dup-sweep.txt (this pack) =====

Gate 47 staging: duplication sweep over every declaration #347 and #355 add (78 = 9 + 69)
=========================================================================================

Scope. The 9 readers of #347 (DW-5 decls2, ADDED 9/0/0) and the 69 promotions of #355 (phase-1 decls2.mine.tsv,
ADDED 69/0/0). Trees: TS1 1eaf940b938bb52e3919f5569893b58522df599b (TCSlib/ and audits/, read with git grep and
git cat-file on the tree object; no checkout); Mathlib 029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e, Batteries
(lake-manifest pin) and Lean v4.25.0 core (Init/, Std/) sources. No Lean was run: grep plus reading.

Method (tools/ in this zip):
 1. namesweep.py: every declaration with the same last name component, in TS1 and in Mathlib/Batteries/core
    (dup/shortname-hits.tsv; 239 rows). Mathlib hits: only 82 homonyms `map_map` (other objects).
 2. shapesweep.sh: 37 statement-shape regexes (33 on TS1, 4 on Mathlib/Batteries/core), one or more per
    declaration family (dup/shape-hits.txt).
 3. stmtgrep.py: declaration-header search on TS1 for the getD/headD-of-ofFn forms, the encodeMsgs equations
    and the FinDist map/probTrue/uniform forms (dup/stmt-hits.txt, dup/stmt-encodeMsgs.txt, dup/stmt-findist.txt).
 4. Every hit was read at TS1 and classified against duplication-ledger.md (records pin), the Stage 1 brief, the
    worker's reuse table and repoint.tsv (exchange 5451d3cd), the checkpoint-1 and final reviews and
    stage2-addendum.tsv.

A. Overlaps already covered by the records (no action for Gate 47 beyond disclosure)
-----------------------------------------------------------------------------------
Equal or more special public copies in TCSlib; each is the ledgered copy the promotion is for, re-pointed in
Stage 2 (repoint.tsv + stage2-addendum.tsv) unless noted.

 S1-01..03 host_dispatch_view / host_branch_view / host_halt_view (IterateFindHost.lean:399/415/437)
     = E1's in-proof hdisp/hbranch/hhalt (IterateFind.lean:373/378/390 at TS1; added by #347, disclosed there);
       view forms of the public host_dispatch/host_branch/host_halt (IterateFindHost.lean:354/366/382), which read
       hostTM's fields.                                                  DW-9 (Stage 1 scope), repoint rows 2-4
 #347 readers host_call_view, host_clean_view, hostTMView_step_inl, copy_clean_view
     = host_call, host_clean, hostTM_step_inl (ModuleHost.lean:518/622/480), copy_clean (IterateFindHost.lean:213),
       restated at the typed views by design; each proof is the original lemma.  DW-5 / SR-02 (disclosed in #347)
 S1-04 Games.expect_simulate_abs, _inv, freshImpl, _apply, tapeImpl, _apply, simulate_tapeImpl_congr,
       expect_simulate_tapeImpl, ovr, ovr_nil/_cons/_of_not_mem/_of_mem/_update/_append, expect_sample_ovr
     = public ETTGame copies, EncryptThenTag/Tools.lean:65,88,116,122,130,135,145,167,219-281; Lazy.lean:175
       (ovr_append)                                                                                       DL-40
 S1-04 Games.extTape, extTape_of_lt, extTape_update
     = public AdaptiveCPA.extTape, extTape_of_lt, extTape_update (AdaptiveCPA/Hybrid.lean:211,215,221)  DL-40
       (but see B1: an older, more general public copy is not ledgered)
 S1-05 EffFill.length_le_length_encodeLog = private copies EncryptThenTag/Machines.lean:95,
       NonMalleability/Indistinguishability/Forward.lean:108                                               DL-40
 S1-06 zipWith_xor_cancel_right = public ETTGame.zipWith_xor_cancel (EncryptThenTag/Lazy.lean:295) and the
       private copies zipWith_xor_xor_self (FromPRF:174, FromPRG:147, SpecialEncryption:101) and
       zipWith_xor_xor_self' (EncryptThenTag.lean:338)                                                      DL-40
 S1-07 recordBits, _none, _some, length_recordBits = ETTGame.recBits family (EncryptThenTag/Handler.lean:134-147),
       PRFGame.recBits family (OracleFromPRF/Handler.lean:109-121), instances at w = ettCt.eval n / ctP.eval n  DL-40
 S1-08 NUPPT.eval_toOracleAdversary_padFin generalizes ETTGame.eval_toOracleAdversary_len,
       PRFGame.eval_toOracleAdversary_width and the MAC copy (instances; phase-1 review S1-08)          DL-40, DL-44
 S1-09 FunFamily.ofFn_blocks_symm_eq_flatMap = EnsembleLemmas.ofFn_blocks_symm (EnsemblesLemmas.lean:433, via the
       public alias EnsembleLemmas.blocks); relative FunFamily.ofFn_blocks_symm (OneWay.lean:380, flatten form) and
       ComposeSecurity ofFn_blocks_symm (Runs.lean:71)                                       DL-35, DL-38, DL-49
 S1-10 Bridge.expect_sample_eq_uexp = public expect_sample_eq_uexp (Hashing/FromDiscreteLog/Probability.lean:40),
       same statement                                                                                        DL-41
 S1-11 Authentication.ofFn_splitBits_fst/_snd = public FromDiscreteLog.ofFn_splitBits_fst/_snd
       (Hashing/FromDiscreteLog/Encoding.lean:45,55), same statements; inline copies MAC/FromPRF/Reduction:145-147,
       Lamport/MachineSpec:259, HashAndSign/CollisionHandler:464                                     DL-41, DL-44
 S1-12 OracleComp.exists_eq_pure_of_costBoundedBy_zero = HashAndSign/OneQuery.lean:36, Lamport/Planted.lean:226 DL-42
 S1-14 PrivateKeyScheme.encodeList_eq_flatMap = public encodeList_eq_flatMap (Asymptotic/BlockEncryptor.lean:60,
       same statement), public MultiMsg.encodeList_eq_flatMap (FromPRF/MultiMsgOut.lean:65), private FromPRF:251;
       generic relative UniformTableauEmitter.encodeList_eq_flatMap (Complexity)                            DL-46
 S1-15 getD_ofFn = public GI.getD_ofFn_lt' (GraphIsomorphism/SoundnessRep.lean:61: the same statement, Type*);
       Bool instances GI.getD_ofFn_lt (Proofs:818), GIZK.getD_ofFn_lt (Closeness:110), ColProofs.ofFn_getD_lt
       (ProtocolProofs:391), private Yao getD_ofFn' (Yao.lean:614); the inline chains. No List.getD_ofFn in
       core/Batteries/Mathlib (searched).                                                                     DL-47
 S1-16 NUPPT.length_ofFn_coins = public NMSim.length_ofFn_coins (Rounds.lean:41), OT.length_ofFn_coins
       (Simulators.lean:210), same statement; it is core List.length_ofFn after unfolding NUPPT.coinLen, which
       Rule 10 forbids consumers (worker's exact? log).                                             DL-48 (CS1-Q6)
 S1-17 pkPredictor_apply: fresh reader (no public reader of pkPredictor); relative owpPredictor_apply.  DL-48 action
 S1-18..20 Strategy.encodeMsgs_eq (rfl reader), encodeMsgs_eq_flatMap = ComposeSecurity/Machines:150,
       ThreeColoring/Machines:912, SimulatorNumeric:503; iterate_pairSndD_encodeMsgs = GI EfficiencyRep:101,
       ThreeColoring/Machines:919                                                                     DL-38, DL-49
 S1-21 encodeMsgs_eq_encWords = SequentialZK/Normalization.lean:40, Yao/HybridProof/Lengths.lean:83 (both public),
       Yao.lean:355 inline                                                                         DL-49 (extended)
 S1-22 StatClose.of_uprob_ne = public statClose_of_uprob_ne (Candidates/DDH.lean:145), same statement   DL-51 (CS1-Q7)
 S1-26 Strategy.msgAt_encodeMsgs = public ColZK.field_encodeMsgs (ColZKMachine.lean:142, same statement),
       ColMachines.getD_eq_pairFstD_iterate (Machines.lean:951, reversed), ComposeSecurity msgAt_encodeMsgs
       (Machines.lean:137); weaker ThreeColoring/Protocol.lean:112                    DL-49 (extended, CS1-F01)
 S1-27 EncodingMachines.flatMap_range_ite, polyTimeComputable_flatMap_range, iterSnd_poly, zeros_poly, padTo,
       padTo_eq, padTo_poly, length_padTo, getD_padTo, padTo_of_length = ComposeSecurity/Machines and
       ThreeColoring/Machines copies; padTo/zeros_poly also overlap padL/padStr/padSq/zero-word families     DL-49,
       DL-53 (CS1-C1-Q1); relatives flatMap_range_ite_eq_flatten_ofFn (OneWayLemmas:245) and the private
       QuasiPolyHierarchy.flatMap_range_ite (:190) are addendum notes (CS1-F09)
 S1-23..25 the 14 FinDist facts = Randomness/Extraction/Rejection.lean:45-134, 343, 395-413 (public, same
       statements); Mathlib/Games homonyms (map_map, sum_map, expect_map) are other objects        DL-39 (CS1-Q1)

B. Overlaps found by this sweep that were not in the ledger at the first pin 95da6120; ruled before dispatch
-------------------------------------------------------------------------------------------------------------
Ruling (Seyoon, 2026-11-17; records 659542ec): B1 accepted as ledger row DL-59 (Stage 2, with DL-40: keep one
family in Games/Tapes stated at Type*, re-point LazySampling's extendStream*, AdaptiveCPA.extTape and #355's
users); B2-B7 ledgered as DL-60 (B3 extends DL-53, B4 extends DL-49, B2 goes to the Complexity handoff,
B5-B7 analogues disclosed only). #355's code is unchanged.
 B1 (DL-59). S1-04 Games.extTape (Games/Tapes.lean:139), extTape_of_lt (:144), extTape_update (:156)
     vs public extendStream (Pseudorandom/Functions/LazySampling.lean:196), extendStream_def (:201) and
     extendStream_update_of_ne (:235), Garg §3.4 (commit 736c85c8, 2026-10-14; audited at Gate 04).
     - extendStream W = fun k => if h : k < q then W ⟨k, h⟩ else Classical.arbitrary O, with {O : Type*}; extTape T m
       = if hm : m < κ then T ⟨m, hm⟩ else Classical.arbitrary C, with {C : Type}: the same function, the older one
       universe-polymorphic.
     - extTape_update (hm : m ≠ j) and extendStream_update_of_ne (hk : k ≠ j.val) are the same statement.
       extTape_of_lt / _of_not_lt are the two branches of extendStream_def (dite form).
     - Not named in DL-40, the Stage 1 brief, the worker's reuse table, repoint.tsv, stage2-addendum.tsv or either
       review. DL-40's listed copy AdaptiveCPA.extTape (2026-11-11) is itself a later copy of extendStream.
     - Neither module is in the other's import closure (git-object import scan at TS1).
     - Gate precedent: G44-01, G45-01 (an undisclosed restatement of a public TCSlib lemma graded major).
 B2 (DL-60, Complexity handoff). S1-27 EncodingMachines.polyTimeComputable_flatMap_range (EncodingMachines.lean:729) vs public
     Complexity.FormulaKit.polyTimeComputable_flatMap_range (Complexity/FormulaKit/Emit.lean:127), which is an
     admitted `sorry` at TS1: the same statement up to the order of the pair components fed to the chunk function
     (E (pairSndD w) (pairFstD w).length vs chunk (pairFstD z) (pairSndD z).length). Disclosed only in the
     worker's reuse table ("not an E-DUP; noted for a future Complexity fill"); not in the ledger, addendum or
     reviews. S1-27 proves what FormulaKit admits; no Lean proof is duplicated, but two public statements exist.
 B3 (DL-60, extends DL-53). S1-27 padTo family vs Batteries List.takeD (Batteries/Data/List/Basic.lean:159) and Mathlib takeD_length,
     takeD_eq_take, takeD_left' (Mathlib/Data/List/TakeDrop.lean:111-125): padTo L w and takeD L w false are the
     same list (different definitions), so length_padTo ~ takeD_length and padTo_of_length ~ takeD_left'-style
     facts. Noted as a relative in the worker's reuse table only. Also the public bridge
     CollectionsLemmas.ofFn_padFin_eq_take (CollectionsLemmas.lean:95: List.ofFn (padFin l w) = (w ++ replicate l
     false).take l, i.e. padL l w = padTo l w) and its public restatement Universal.ofFn_getD_eq_take
     (Universal.lean:265) make padTo literally padL; DL-53 covers padL as a family but names neither the bridge nor
     takeD. Complexity-side relative: CircuitEvalCorrect.ofFn_getD_eq_take (CircuitEvalCorrect.lean:589, the
     n <= |x| case, conclusion x.take n).
 B4 (DL-60, extends DL-49). Specializations already public: Strategy.pairFstD_encodeMsgs (Interaction.lean:146, same file as S1-26:
     pairFstD (encodeMsgs h) = h.headD []) is S1-26 at i = 0; GI.pairSndD_encodeMsgs (EfficiencyRep.lean:93) is
     S1-20 at i = 1. Pre-existing and derivable; not ledgered (the addendum lists ColZK.field_zero_encodeMsgs only).
 B5 (DL-60, disclosure only). GGM take_ofFn_splitHalves / drop_ofFn_splitHalves (GGM/Evaluator.lean:72,79): the splitHalves analogue of
     S1-11 over Fin (2 * n) (an Equiv, not splitBits; not an instance). Relative; not ledgered.
 B6 (DL-60, disclosure only). Complexity-side private unary_chunks (ClassP/BinaryArith/Unary.lean:150, [true]-chunks, replicate
     conclusion): a relative of S1-27 flatMap_range_ite of the kind the addendum records for QuasiPolyHierarchy.
 B7 (DL-60, disclosure only). Relatives of the Tapes family in other models: AdaptiveCPA.expect_tapeImpl (AdaptiveCPA/Hybrid.lean:244; the
     reuse table lists only AdaptiveCPA.tapeImpl/simulate_tapeImpl_congr as CS1-Q10 relatives) and the QueryTree
     analogues QueryTree.evalLazy_congr (LazySampling.lean:167) and uprob_evalLazy (:393). Different statements.

C. No hit
---------
 #347's hostTMView, hostTMView_eq, hostTMView_q₀, copyTMView, copyTMView_eq: no other typed-view definition or
 reader in TCSlib/Complexity (git grep); no Mathlib/Batteries/core homonym. S1-17 pkPredictor_apply, S1-25
 FinDist.mixture* (beyond Rejection), S1-23 uniform_prod/map_uniform_equiv (beyond Rejection and the optional
 DyadicUniform near-copies in repoint.tsv): nothing further.

## ===== verification-r1.zip:phase2/PROVENANCE.txt (this pack) =====

cleanup-stage1 phase 2 (merged-tree replay and checks), 2026-11-17 UTC, maintainer sub-agent. Write-up: ../phase2.md.
$SP = /tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad. Work dir $SP/cs1p2 (full logs kept there).
TS1 = 1eaf940b938bb52e3919f5569893b58522df599b = tip e1d39836 x #347 daa6e173 x #355 d3c7cb00 (merge/merge-trees.txt).
Snapshot #5 T 3f540c22, map fca1b6a3...; replay output $SP/olean-replay-cs1 (kept; snapshot candidate for Lean = TS1).
merge/      merge orders, TS1 vs tip and vs 5a2e818d, file lists
plan/       stateplan init (gz), downorder outputs, full-order (1429), queue (556), reuse (873), keys, state after update (gz)
build/      runner results.jsonl and per-module logs (556), permod, update, statecheck (after build and after probes),
            link counts, watcher log, NthRootLemmas compile log, overlay note
snapshot/   snapmap verify of $SP/olean-snapshot before, after the build, after all Lean (0/0/0 each)
admissions/ tipcensus at T and TS1 over the record sets listed, per-module comparison, source scan
axioms/     axioms probe source and log, summary
rule10/     head (TS1, olean-replay-cs1) and tip (e1d39836, snapshot #5 read only): seal/control record summaries (full
            records hashed in records/FULL-RECORDS-SHA256), sealsum TSVs, ctlcheck, touched.json, scan items/explicit, probe
            sources, run results.jsonl and diagnostics extracts (full logs hashed there; kept in $SP/cs1p2)
cmp/        head vs worker head, head vs DW-5 head, head vs tip, failure classification, controls, scan summaries
lint/       campaign_style_lint (3 areas, tip and TS1), style_lint (changed files), comparison
tools/      this job's scripts; mkctl_s1.py and controls-spec.json from the delivery (blob ids); recipe tool hashes

## ===== verification-r1.zip:phase2/build/permod.out (this pack) =====

modules 556; rc!=0 0; error: 0; error( 0; combined 0; substring 0; sorry 26; warnings 272; log/record mismatches []

## ===== verification-r1.zip:phase2/build/check.out (this pack) =====

1eaf940b order 1429; bad 0 [] | RESULT OK

## ===== verification-r1.zip:phase2/build/linkcount.txt (this pack) =====

rebuilt oleans link count 1: 556; other: 0
reused oleans hard-linked to snapshot: 873; not: 0
after seals: rebuilt oleans with link count 1: 556/556

## ===== verification-r1.zip:phase2/admissions/admcmp.out (this pack) =====

modules T 1461 TS1 1463 ; differing 2
   ('TCSlib/Cryptography/Games/Tapes', 'absent', 0)
   ('TCSlib/Cryptography/ZeroKnowledge/InteractionWords', 'absent', 0)
rebuilt set: T total 26 TS1 total 26 ; NOREC at T in rebuilt set []
tree totals T 196 TS1 196

## ===== verification-r1.zip:phase2/axioms/axsum.out (this pack) =====

Stage 1 (69) printed 69 missing [] nonstandard {}
  split {('Classical.choice', 'Quot.sound', 'propext'): 34, ('Classical.choice',): 4, (): 13, ('Quot.sound', 'propext'): 12, ('propext',): 6}
DW-5/#347 (27) printed 27 missing [] nonstandard {}
  split {('Classical.choice', 'Quot.sound', 'propext'): 27}
census constants 1224 C-COUNT 1224 owners 21 ; nonstandard 0
sorryAx anywhere in log: False ; errors: 0
touched declarations 80 ; in census 80 ; not found []

## ===== verification-r1.zip:phase2/cmp/head-classify.txt (this pack) =====

Complexity_Randomized_Build_IterateFind: errors sA/sB/cA/cB 0/0/0/0; req diff sA-cA [] sB-sA ['Complexity.PolyExpr.eval'] cA-sA []
Complexity_Randomized_Build_IterateFindHost: errors sA/sB/cA/cB 16/16/16/16; req diff sA-cA [] sB-sA [] cA-sA []
Complexity_Randomized_PPT: errors sA/sB/cA/cB 0/1/0/1; req diff sA-cA [] sB-sA ['Complexity.PolyExpr.eval'] cA-sA []
   B-only failing decls: ['Complexity.NUPPT.runAtL_ofPolyTimeUniform'] ; touched among them: []
Complexity_TuringMachine_Build_ModuleHost: errors sA/sB/cA/cB 10/10/10/10; req diff sA-cA [] sB-sA [] cA-sA []
Cryptography_Asymptotic_Adversary: errors sA/sB/cA/cB 0/0/0/0; req diff sA-cA ['TCSlib.InformationTheory.FinDist.instCoeFunForallReal'] sB-sA ['Complexity.PolyExpr.eval'] cA-sA []
Cryptography_Asymptotic_Sampling: errors sA/sB/cA/cB 0/0/0/0; req diff sA-cA ['TCSlib.InformationTheory.FinDist.instCoeFunForallReal'] sB-sA [] cA-sA []
Cryptography_Authentication_Encoding: errors sA/sB/cA/cB 0/0/0/0; req diff sA-cA [] sB-sA [] cA-sA []
Cryptography_Encryption_PrivateKey_EnsembleSecurity: errors sA/sB/cA/cB 0/2/0/2; req diff sA-cA ['TCSlib.InformationTheory.FinDist.instCoeFunForallReal'] sB-sA ['Complexity.PolyExpr.eval'] cA-sA []
   B-only failing decls: ['TCSlib.Cryptography.PrivateKeyScheme.MultiMessageSecure.singleMessageSecure'] ; touched among them: []
Cryptography_Encryption_PublicKey_Trapdoor: errors sA/sB/cA/cB 3/3/3/3; req diff sA-cA ['TCSlib.InformationTheory.FinDist.instCoeFunForallReal'] sB-sA ['Complexity.PolyExpr.eval'] cA-sA []
Cryptography_Foundations_BitLists: errors sA/sB/cA/cB 0/0/0/0; req diff sA-cA [] sB-sA [] cA-sA []
Cryptography_Games_Bridges_Experiments: errors sA/sB/cA/cB 0/0/0/0; req diff sA-cA ['TCSlib.InformationTheory.FinDist.instCoeFunForallReal'] sB-sA [] cA-sA []
Cryptography_Games_Efficiency_Strings: errors sA/sB/cA/cB 0/0/0/0; req diff sA-cA ['TCSlib.InformationTheory.FinDist.instCoeFunForallReal'] sB-sA ['Complexity.PolyExpr.eval'] cA-sA []
Cryptography_Games_Machines: errors sA/sB/cA/cB 0/0/0/0; req diff sA-cA [] sB-sA ['Complexity.PolyExpr.eval'] cA-sA []
Cryptography_Games_Tapes: errors sA/sB/cA/cB 0/0/0/0; req diff sA-cA ['TCSlib.InformationTheory.FinDist.instCoeFunForallReal'] sB-sA [] cA-sA []
Cryptography_Pseudorandom_Functions_Asymptotic_Defs: errors sA/sB/cA/cB 0/8/0/8; req diff sA-cA ['TCSlib.InformationTheory.FinDist.instCoeFunForallReal'] sB-sA ['Complexity.PolyExpr.eval'] cA-sA []
   B-only failing decls: ['TCSlib.Cryptography.OracleEnsemble.Indist.negligible_prfAdv', 'TCSlib.Cryptography.PRF', 'TCSlib.Cryptography.PRF.negligible_prfAdv', 'TCSlib.Cryptography.prfAdv_toOracleAdversary', 'TCSlib.Cryptography.prfAdv_toOracleAdversary_out'] ; touched among them: []
Cryptography_ZeroKnowledge_EncodingMachines: errors sA/sB/cA/cB 0/0/0/0; req diff sA-cA [] sB-sA ['Complexity.PolyExpr.eval'] cA-sA []
Cryptography_ZeroKnowledge_Interaction: errors sA/sB/cA/cB 0/0/0/0; req diff sA-cA [] sB-sA ['Complexity.PolyExpr.eval'] cA-sA []
Cryptography_ZeroKnowledge_InteractionWords: errors sA/sB/cA/cB 0/0/0/0; req diff sA-cA [] sB-sA ['Complexity.PolyExpr.eval'] cA-sA []
InformationTheory_Entropy: errors sA/sB/cA/cB 15/15/5/5; req diff sA-cA ['TCSlib.InformationTheory.FinDist.instCoeFunForallReal'] sB-sA [] cA-sA []
   strict-only failing decls: ['TCSlib.InformationTheory.FinDist.flat_apply', 'TCSlib.InformationTheory.FinDist.le_maxProb', 'TCSlib.InformationTheory.FinDist.maxProb_pos', 'TCSlib.InformationTheory.FinDist.mixture', 'TCSlib.InformationTheory.FinDist.mixture_apply', 'TCSlib.InformationTheory.FinDist.mixture_isSource', 'TCSlib.InformationTheory.FinDist.shannonEntropy_nonneg', 'TCSlib.InformationTheory.FinDist.shannonEntropy_uniform'] ; touched among them: ['TCSlib.InformationTheory.FinDist.mixture', 'TCSlib.InformationTheory.FinDist.mixture_apply', 'TCSlib.InformationTheory.FinDist.mixture_isSource']
   failing touched decls sA/sB/cA/cB: [['TCSlib.InformationTheory.FinDist.mixture', 'TCSlib.InformationTheory.FinDist.mixture_apply', 'TCSlib.InformationTheory.FinDist.mixture_isSource'], ['TCSlib.InformationTheory.FinDist.mixture', 'TCSlib.InformationTheory.FinDist.mixture_apply', 'TCSlib.InformationTheory.FinDist.mixture_isSource'], [], []]
InformationTheory_FinDist: errors sA/sB/cA/cB 0/0/0/0; req diff sA-cA [] sB-sA [] cA-sA []
InformationTheory_Samples: errors sA/sB/cA/cB 3/3/0/0; req diff sA-cA ['TCSlib.InformationTheory.FinDist.instCoeFunForallReal'] sB-sA [] cA-sA []
   strict-only failing decls: ['TCSlib.InformationTheory.FinDist.map_apply_expect', 'TCSlib.InformationTheory.FinDist.map_map', 'TCSlib.InformationTheory.FinDist.map_prod_snd'] ; touched among them: ['TCSlib.InformationTheory.FinDist.map_apply_expect', 'TCSlib.InformationTheory.FinDist.map_map', 'TCSlib.InformationTheory.FinDist.map_prod_snd']
   failing touched decls sA/sB/cA/cB: [['TCSlib.InformationTheory.FinDist.map_apply_expect', 'TCSlib.InformationTheory.FinDist.map_map', 'TCSlib.InformationTheory.FinDist.map_prod_snd'], ['TCSlib.InformationTheory.FinDist.map_apply_expect', 'TCSlib.InformationTheory.FinDist.map_map', 'TCSlib.InformationTheory.FinDist.map_prod_snd'], [], []]
touched declarations 80 ; failures in touched declarations: coe 0 strict 12

## ===== verification-r1.zip:phase2/cmp/tip-classify.txt (this pack) =====

Complexity_Randomized_Build_IterateFind: errors sA/sB/cA/cB 20/20/20/20; req diff sA-cA [] sB-sA ['Complexity.PolyExpr.eval'] cA-sA []
Complexity_Randomized_Build_IterateFindHost: errors sA/sB/cA/cB 16/16/16/16; req diff sA-cA [] sB-sA [] cA-sA []
Complexity_Randomized_PPT: errors sA/sB/cA/cB 0/1/0/1; req diff sA-cA [] sB-sA ['Complexity.PolyExpr.eval'] cA-sA []
   B-only failing decls: ['Complexity.NUPPT.runAtL_ofPolyTimeUniform'] ; touched among them: []
Complexity_TuringMachine_Build_ModuleHost: errors sA/sB/cA/cB 10/10/10/10; req diff sA-cA [] sB-sA [] cA-sA []
Cryptography_Asymptotic_Adversary: errors sA/sB/cA/cB 0/0/0/0; req diff sA-cA ['TCSlib.InformationTheory.FinDist.instCoeFunForallReal'] sB-sA ['Complexity.PolyExpr.eval'] cA-sA []
Cryptography_Asymptotic_Sampling: errors sA/sB/cA/cB 0/0/0/0; req diff sA-cA ['TCSlib.InformationTheory.FinDist.instCoeFunForallReal'] sB-sA [] cA-sA []
Cryptography_Authentication_Encoding: errors sA/sB/cA/cB 0/0/0/0; req diff sA-cA [] sB-sA [] cA-sA []
Cryptography_Encryption_PrivateKey_EnsembleSecurity: errors sA/sB/cA/cB 0/2/0/2; req diff sA-cA ['TCSlib.InformationTheory.FinDist.instCoeFunForallReal'] sB-sA ['Complexity.PolyExpr.eval'] cA-sA []
   B-only failing decls: ['TCSlib.Cryptography.PrivateKeyScheme.MultiMessageSecure.singleMessageSecure'] ; touched among them: []
Cryptography_Encryption_PublicKey_Trapdoor: errors sA/sB/cA/cB 3/3/3/3; req diff sA-cA ['TCSlib.InformationTheory.FinDist.instCoeFunForallReal'] sB-sA ['Complexity.PolyExpr.eval'] cA-sA []
Cryptography_Foundations_BitLists: errors sA/sB/cA/cB 0/0/0/0; req diff sA-cA [] sB-sA [] cA-sA []
Cryptography_Games_Bridges_Experiments: errors sA/sB/cA/cB 0/0/0/0; req diff sA-cA ['TCSlib.InformationTheory.FinDist.instCoeFunForallReal'] sB-sA [] cA-sA []
Cryptography_Games_Efficiency_Strings: errors sA/sB/cA/cB 0/0/0/0; req diff sA-cA ['TCSlib.InformationTheory.FinDist.instCoeFunForallReal'] sB-sA ['Complexity.PolyExpr.eval'] cA-sA []
Cryptography_Games_Machines: errors sA/sB/cA/cB 0/0/0/0; req diff sA-cA [] sB-sA ['Complexity.PolyExpr.eval'] cA-sA []
Cryptography_Pseudorandom_Functions_Asymptotic_Defs: errors sA/sB/cA/cB 0/8/0/8; req diff sA-cA ['TCSlib.InformationTheory.FinDist.instCoeFunForallReal'] sB-sA ['Complexity.PolyExpr.eval'] cA-sA []
   B-only failing decls: ['TCSlib.Cryptography.OracleEnsemble.Indist.negligible_prfAdv', 'TCSlib.Cryptography.PRF', 'TCSlib.Cryptography.PRF.negligible_prfAdv', 'TCSlib.Cryptography.prfAdv_toOracleAdversary', 'TCSlib.Cryptography.prfAdv_toOracleAdversary_out'] ; touched among them: []
Cryptography_ZeroKnowledge_EncodingMachines: errors sA/sB/cA/cB 0/0/0/0; req diff sA-cA [] sB-sA ['Complexity.PolyExpr.eval'] cA-sA []
Cryptography_ZeroKnowledge_Interaction: errors sA/sB/cA/cB 0/0/0/0; req diff sA-cA [] sB-sA ['Complexity.PolyExpr.eval'] cA-sA []
InformationTheory_Entropy: errors sA/sB/cA/cB 10/10/5/5; req diff sA-cA ['TCSlib.InformationTheory.FinDist.instCoeFunForallReal'] sB-sA [] cA-sA []
   strict-only failing decls: ['TCSlib.InformationTheory.FinDist.flat_apply', 'TCSlib.InformationTheory.FinDist.le_maxProb', 'TCSlib.InformationTheory.FinDist.maxProb_pos', 'TCSlib.InformationTheory.FinDist.shannonEntropy_nonneg', 'TCSlib.InformationTheory.FinDist.shannonEntropy_uniform'] ; touched among them: []
InformationTheory_FinDist: errors sA/sB/cA/cB 0/0/0/0; req diff sA-cA [] sB-sA [] cA-sA []
InformationTheory_Samples: errors sA/sB/cA/cB 0/0/0/0; req diff sA-cA ['TCSlib.InformationTheory.FinDist.instCoeFunForallReal'] sB-sA [] cA-sA []
touched declarations 0 ; failures in touched declarations: coe 0 strict 0

## ===== verification-r1.zip:phase2/cmp/head-vs-tip.txt (this pack) =====

DIFF seals-A SealA_Complexity_Randomized_Build_IterateFind mine ['595', '0', '0', '1', '1'] ref ['595', '1', '20', '1', '1'] 
   + [] 
   - ['Complexity.IterateFind.computesFunInTime_find', 'Complexity.IterateFind.polyTimeComputable_find']
DIFF seals-A SealA_Cryptography_Asymptotic_Adversary mine ['587', '0', '0', '1', '1'] ref ['584', '0', '0', '1', '1'] 
   + [] 
   - []
DIFF seals-A SealA_Cryptography_Pseudorandom_Functions_Asymptotic_Defs mine ['667', '0', '0', '1', '1'] ref ['664', '0', '0', '1', '1'] 
   + [] 
   - []
DIFF seals-A SealA_Cryptography_ZeroKnowledge_EncodingMachines mine ['890', '0', '0', '1', '1'] ref ['893', '0', '0', '1', '1'] 
   + [] 
   - []
DIFF seals-A SealA_InformationTheory_Entropy mine ['10', '1', '15', '1', '1'] ref ['10', '1', '10', '1', '1'] 
   + ['TCSlib.InformationTheory.FinDist.mixture', 'TCSlib.InformationTheory.FinDist.mixture_apply', 'TCSlib.InformationTheory.FinDist.mixture_isSource'] 
   - []
DIFF seals-A SealA_InformationTheory_Samples mine ['10', '1', '3', '1', '1'] ref ['10', '0', '0', '1', '1'] 
   + ['TCSlib.InformationTheory.FinDist.map_apply_expect', 'TCSlib.InformationTheory.FinDist.map_map', 'TCSlib.InformationTheory.FinDist.map_prod_snd'] 
   - []
DIFF seals-B SealB_Complexity_Randomized_Build_IterateFind mine ['596', '0', '0', '1', '1'] ref ['596', '1', '20', '1', '1'] 
   + [] 
   - ['Complexity.IterateFind.computesFunInTime_find', 'Complexity.IterateFind.polyTimeComputable_find']
DIFF seals-B SealB_Cryptography_Asymptotic_Adversary mine ['588', '0', '0', '1', '1'] ref ['585', '0', '0', '1', '1'] 
   + [] 
   - []
DIFF seals-B SealB_Cryptography_Pseudorandom_Functions_Asymptotic_Defs mine ['668', '1', '8', '1', '1'] ref ['665', '1', '8', '1', '1'] 
   + [] 
   - []
DIFF seals-B SealB_Cryptography_ZeroKnowledge_EncodingMachines mine ['891', '0', '0', '1', '1'] ref ['894', '0', '0', '1', '1'] 
   + [] 
   - []
DIFF seals-B SealB_InformationTheory_Entropy mine ['10', '1', '15', '1', '1'] ref ['10', '1', '10', '1', '1'] 
   + ['TCSlib.InformationTheory.FinDist.mixture', 'TCSlib.InformationTheory.FinDist.mixture_apply', 'TCSlib.InformationTheory.FinDist.mixture_isSource'] 
   - []
DIFF seals-B SealB_InformationTheory_Samples mine ['10', '1', '3', '1', '1'] ref ['10', '0', '0', '1', '1'] 
   + ['TCSlib.InformationTheory.FinDist.map_apply_expect', 'TCSlib.InformationTheory.FinDist.map_map', 'TCSlib.InformationTheory.FinDist.map_prod_snd'] 
   - []
DIFF seals-coe-A SealA_Complexity_Randomized_Build_IterateFind mine ['595', '0', '0', '1', '1'] ref ['595', '1', '20', '1', '1'] 
   + [] 
   - ['Complexity.IterateFind.computesFunInTime_find', 'Complexity.IterateFind.polyTimeComputable_find']
DIFF seals-coe-A SealA_Cryptography_Asymptotic_Adversary mine ['586', '0', '0', '1', '1'] ref ['583', '0', '0', '1', '1'] 
   + [] 
   - []
DIFF seals-coe-A SealA_Cryptography_Pseudorandom_Functions_Asymptotic_Defs mine ['666', '0', '0', '1', '1'] ref ['663', '0', '0', '1', '1'] 
   + [] 
   - []
DIFF seals-coe-A SealA_Cryptography_ZeroKnowledge_EncodingMachines mine ['890', '0', '0', '1', '1'] ref ['893', '0', '0', '1', '1'] 
   + [] 
   - []
DIFF seals-coe-B SealB_Complexity_Randomized_Build_IterateFind mine ['596', '0', '0', '1', '1'] ref ['596', '1', '20', '1', '1'] 
   + [] 
   - ['Complexity.IterateFind.computesFunInTime_find', 'Complexity.IterateFind.polyTimeComputable_find']
DIFF seals-coe-B SealB_Cryptography_Asymptotic_Adversary mine ['587', '0', '0', '1', '1'] ref ['584', '0', '0', '1', '1'] 
   + [] 
   - []
DIFF seals-coe-B SealB_Cryptography_Pseudorandom_Functions_Asymptotic_Defs mine ['667', '1', '8', '1', '1'] ref ['664', '1', '8', '1', '1'] 
   + [] 
   - []
DIFF seals-coe-B SealB_Cryptography_ZeroKnowledge_EncodingMachines mine ['891', '0', '0', '1', '1'] ref ['894', '0', '0', '1', '1'] 
   + [] 
   - []
compared 76; same 56; diff 20; mine-only [('seals-A', 'SealA_Cryptography_Games_Tapes'), ('seals-A', 'SealA_Cryptography_ZeroKnowledge_InteractionWords'), ('seals-B', 'SealB_Cryptography_Games_Tapes'), ('seals-B', 'SealB_Cryptography_ZeroKnowledge_InteractionWords'), ('seals-coe-A', 'SealA_Cryptography_Games_Tapes'), ('seals-coe-A', 'SealA_Cryptography_ZeroKnowledge_InteractionWords'), ('seals-coe-B', 'SealB_Cryptography_Games_Tapes'), ('seals-coe-B', 'SealB_Cryptography_ZeroKnowledge_InteractionWords')]

## ===== verification-r1.zip:phase2/cmp/head-vs-worker-head.txt (this pack) =====

compared 76; same 76; diff 0; mine-only [('seals-A', 'SealA_Complexity_Randomized_Build_IterateFind'), ('seals-A', 'SealA_Complexity_TuringMachine_Build_ModuleHost'), ('seals-B', 'SealB_Complexity_Randomized_Build_IterateFind'), ('seals-B', 'SealB_Complexity_TuringMachine_Build_ModuleHost'), ('seals-coe-A', 'SealA_Complexity_Randomized_Build_IterateFind'), ('seals-coe-A', 'SealA_Complexity_TuringMachine_Build_ModuleHost'), ('seals-coe-B', 'SealB_Complexity_Randomized_Build_IterateFind'), ('seals-coe-B', 'SealB_Complexity_TuringMachine_Build_ModuleHost')]

## ===== verification-r1.zip:phase2/cmp/head-vs-dw5-head.txt (this pack) =====

compared 12; same 12; diff 0; mine-only [('seals-A', 'SealA_Complexity_Randomized_PPT'), ('seals-A', 'SealA_Cryptography_Asymptotic_Adversary'), ('seals-A', 'SealA_Cryptography_Asymptotic_Sampling'), ('seals-A', 'SealA_Cryptography_Authentication_Encoding'), ('seals-A', 'SealA_Cryptography_Encryption_PrivateKey_EnsembleSecurity'), ('seals-A', 'SealA_Cryptography_Encryption_PublicKey_Trapdoor'), ('seals-A', 'SealA_Cryptography_Foundations_BitLists'), ('seals-A', 'SealA_Cryptography_Games_Bridges_Experiments'), ('seals-A', 'SealA_Cryptography_Games_Efficiency_Strings'), ('seals-A', 'SealA_Cryptography_Games_Machines'), ('seals-A', 'SealA_Cryptography_Games_Tapes'), ('seals-A', 'SealA_Cryptography_Pseudorandom_Functions_Asymptotic_Defs'), ('seals-A', 'SealA_Cryptography_ZeroKnowledge_EncodingMachines'), ('seals-A', 'SealA_Cryptography_ZeroKnowledge_Interaction'), ('seals-A', 'SealA_Cryptography_ZeroKnowledge_InteractionWords'), ('seals-A', 'SealA_InformationTheory_Entropy'), ('seals-A', 'SealA_InformationTheory_FinDist'), ('seals-A', 'SealA_InformationTheory_Samples'), ('seals-B', 'SealB_Complexity_Randomized_PPT'), ('seals-B', 'SealB_Cryptography_Asymptotic_Adversary'), ('seals-B', 'SealB_Cryptography_Asymptotic_Sampling'), ('seals-B', 'SealB_Cryptography_Authentication_Encoding'), ('seals-B', 'SealB_Cryptography_Encryption_PrivateKey_EnsembleSecurity'), ('seals-B', 'SealB_Cryptography_Encryption_PublicKey_Trapdoor'), ('seals-B', 'SealB_Cryptography_Foundations_BitLists'), ('seals-B', 'SealB_Cryptography_Games_Bridges_Experiments'), ('seals-B', 'SealB_Cryptography_Games_Efficiency_Strings'), ('seals-B', 'SealB_Cryptography_Games_Machines'), ('seals-B', 'SealB_Cryptography_Games_Tapes'), ('seals-B', 'SealB_Cryptography_Pseudorandom_Functions_Asymptotic_Defs'), ('seals-B', 'SealB_Cryptography_ZeroKnowledge_EncodingMachines'), ('seals-B', 'SealB_Cryptography_ZeroKnowledge_Interaction'), ('seals-B', 'SealB_Cryptography_ZeroKnowledge_InteractionWords'), ('seals-B', 'SealB_InformationTheory_Entropy'), ('seals-B', 'SealB_InformationTheory_FinDist'), ('seals-B', 'SealB_InformationTheory_Samples'), ('seals-coe-A', 'SealA_Complexity_Randomized_PPT'), ('seals-coe-A', 'SealA_Cryptography_Asymptotic_Adversary'), ('seals-coe-A', 'SealA_Cryptography_Asymptotic_Sampling'), ('seals-coe-A', 'SealA_Cryptography_Authentication_Encoding'), ('seals-coe-A', 'SealA_Cryptography_Encryption_PrivateKey_EnsembleSecurity'), ('seals-coe-A', 'SealA_Cryptography_Encryption_PublicKey_Trapdoor'), ('seals-coe-A', 'SealA_Cryptography_Foundations_BitLists'), ('seals-coe-A', 'SealA_Cryptography_Games_Bridges_Experiments'), ('seals-coe-A', 'SealA_Cryptography_Games_Efficiency_Strings'), ('seals-coe-A', 'SealA_Cryptography_Games_Machines'), ('seals-coe-A', 'SealA_Cryptography_Games_Tapes'), ('seals-coe-A', 'SealA_Cryptography_Pseudorandom_Functions_Asymptotic_Defs'), ('seals-coe-A', 'SealA_Cryptography_ZeroKnowledge_EncodingMachines'), ('seals-coe-A', 'SealA_Cryptography_ZeroKnowledge_Interaction'), ('seals-coe-A', 'SealA_Cryptography_ZeroKnowledge_InteractionWords'), ('seals-coe-A', 'SealA_InformationTheory_Entropy'), ('seals-coe-A', 'SealA_InformationTheory_FinDist'), ('seals-coe-A', 'SealA_InformationTheory_Samples'), ('seals-coe-B', 'SealB_Complexity_Randomized_PPT'), ('seals-coe-B', 'SealB_Cryptography_Asymptotic_Adversary'), ('seals-coe-B', 'SealB_Cryptography_Asymptotic_Sampling'), ('seals-coe-B', 'SealB_Cryptography_Authentication_Encoding'), ('seals-coe-B', 'SealB_Cryptography_Encryption_PrivateKey_EnsembleSecurity'), ('seals-coe-B', 'SealB_Cryptography_Encryption_PublicKey_Trapdoor'), ('seals-coe-B', 'SealB_Cryptography_Foundations_BitLists'), ('seals-coe-B', 'SealB_Cryptography_Games_Bridges_Experiments'), ('seals-coe-B', 'SealB_Cryptography_Games_Efficiency_Strings'), ('seals-coe-B', 'SealB_Cryptography_Games_Machines'), ('seals-coe-B', 'SealB_Cryptography_Games_Tapes'), ('seals-coe-B', 'SealB_Cryptography_Pseudorandom_Functions_Asymptotic_Defs'), ('seals-coe-B', 'SealB_Cryptography_ZeroKnowledge_EncodingMachines'), ('seals-coe-B', 'SealB_Cryptography_ZeroKnowledge_Interaction'), ('seals-coe-B', 'SealB_Cryptography_ZeroKnowledge_InteractionWords'), ('seals-coe-B', 'SealB_InformationTheory_Entropy'), ('seals-coe-B', 'SealB_InformationTheory_FinDist'), ('seals-coe-B', 'SealB_InformationTheory_Samples')]

## ===== verification-r1.zip:phase2/cmp/controls.txt (this pack) =====

strict: all_ok True; probes 38 (sealed 19); sealed negatives 20, failing exactly once 20; positives 40 with errors 0; unsealed rc!=0 0; stray 0; install/EOF on sealed 19
   equal to the worker's ctlcheck (labels, rc, per-control errors): True
coe: all_ok True; probes 38 (sealed 19); sealed negatives 20, failing exactly once 20; positives 40 with errors 0; unsealed rc!=0 0; stray 0; install/EOF on sealed 19
   equal to the worker's ctlcheck (labels, rc, per-control errors): True
dw5-strict: all_ok True; probes 10 (sealed 5); sealed negatives 30, failing exactly once 30; positives 60 with errors 0; unsealed rc!=0 0; stray 0; install/EOF on sealed 5
dw5-coe: all_ok True; probes 10 (sealed 5); sealed negatives 30, failing exactly once 30; positives 60 with errors 0; unsealed rc!=0 0; stray 0; install/EOF on sealed 5

## ===== verification-r1.zip:phase2/cmp/scan-head.txt (this pack) =====

items 1776 ; in touched declarations 438 {'THEOREM': 348, 'LOCAL_OR_UNRESOLVED': 88, 'OWNED_DEFINITION': 2}
  touched-declaration statuses {'ADDED': 224, 'NEW_FILE': 86, 'CHANGED': 128}
  foreign in touched 0 ; owned-definition items in touched [('TCSlib.Cryptography.Games.extTape_of_lt', 'Games.extTape'), ('TCSlib.Cryptography.Games.extTape_of_not_lt', 'Games.extTape')]
foreign total 29 by file {'IterateFindHost.lean': 27, 'Entropy.lean': 2}
foreign multiset equal to ref/head/scan/explicit.json : True ; ref-only {} ; mine-only {}
foreign multiset equal to ref/base/scan/explicit.json : True ; ref-only {} ; mine-only {}

## ===== verification-r1.zip:phase2/lint/lintcmp.out (this pack) =====

Cryptography: tip FAIL/WARN 92/104; ts1 92/103; removed 1; new 0
  removed: WARN  TCSlib/Cryptography/Encryption/PublicKey/Trapdoor.lean                                      1 public def(s) without a lemma beside them (check 8): pkPredictor
InformationTheory: tip FAIL/WARN 5/2; ts1 5/2; removed 0; new 0
Complexity: tip FAIL/WARN 25/390; ts1 25/390; removed 0; new 0

## ===== verification-r1.zip:phase2/merge/merge-trees.txt (this pack) =====

inputs (git fetch origin <branch> by name, 2026-11-17)
records tip  origin/cryptography/pass-shelat-ch2-4 = e1d39836ed4a69a34914c35f4c73c71de853dcc6
#347 head    origin/cleanup/dw5-derand-readers  = daa6e173cdd94cad1475b9a96eca613bce53ba61
#355 head    origin/land/cleanup-stage1         = d3c7cb00092ad5913904654d922f30fc7d5fce4a tree 508f915413ee8ef9f2a37b59e0012c9daf3867aa
#347 is an ancestor of #355: yes
tip vs snapshot T 3f540c22360c869069a0fba684e23ce6f3cb20db: Lean/toolchain/manifest/lakefile files differing = 0

merge orders (git merge-tree --write-tree; X*Y for an intermediate tree uses an unreferenced temporary commit object of that tree (git commit-tree; no ref, nothing pushed)):
tip x #347                        -> f905d841a4c2a016fc40b64e1ddbf34000d0b766
(tip x #347) x #355               -> 1eaf940b938bb52e3919f5569893b58522df599b
tip x #355                        -> 1eaf940b938bb52e3919f5569893b58522df599b
#355 x tip                        -> 1eaf940b938bb52e3919f5569893b58522df599b
#355 x (#347 x tip)               -> 1eaf940b938bb52e3919f5569893b58522df599b (run 07:4x)
(tip x #355) x #347               -> 1eaf940b938bb52e3919f5569893b58522df599b (run 07:4x)
all clean (rc 0, no conflict lines); TS1 = 1eaf940b938bb52e3919f5569893b58522df599b

TS1 vs tip:  23 files changed, 1332 insertions(+), 296 deletions(-)  (Lean only:  23 files changed, 1332 insertions(+), 296 deletions(-))
TS1 vs phase-1 tree 5a2e818df5a92fdf30b8dc276c4fdf32050133d6: 40 files; Lean: 9 (= #340/#346, blob-equal to T):
  TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyen.lean blob=T
  TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenMachine.lean blob=T
  TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenMachine/Draws.lean blob=T
  TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenMachine/Handler.lean blob=T
  TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenMachine/Oracles.lean blob=T
  TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenMachine/Reduction.lean blob=T
  TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenMachine/Words.lean blob=T
  TCSlib/Cryptography/AdvancedEncryption/IdentityBased/Defs.lean blob=T
  TCSlib/Cryptography/Pairing/Assumptions.lean blob=T
  non-Lean differences are records files only (briefs/, *Plan.md)
Games.lean (only file not blob-equal to #355): union of the tip's Relational import/entry and #355's Tapes import/entry

## ===== verification-r1.zip:phase1/PROVENANCE.txt (this pack) =====

cleanup-stage1 final (r1) · maintainer phase-1 (static) review evidence, 2026-11-17

Delivery: exchange/pass-shelat-ch5-8 commit 5451d3cd6fa9b8c313c9f18f5a4da3542c85f02a ("fill cleanup-stage1: final",
06:20 UTC), fetched by branch name, extracted with git archive into a fresh empty directory.
Contract: briefs/pass-shelat-ch5-8/cleanup-stage1/issued-r1/ (8/8 OK; brief 56368c13...).
Issue base daa6e173cdd94cad1475b9a96eca613bce53ba61 (#347 head). Check base tree 01cc6259480ccc9372181cd4d18d4511c87aa048.
Checkpoint-1 head c8021348f9bc2d16cfa52ca5e8ff489dc9543592.
Records tip used for landing checks: b8dfca4edeee569587f78f42256a3923cebb1159 (Lean-equal to 463f2244, snapshot #4 T).
Open PR heads: #340 916afc25c21f5e52b4b01958186ad55d2f615fd1, #346 98cb0e521a94e94c304c78348fb5d3033435a3ed,
#347 daa6e173cdd94cad1475b9a96eca613bce53ba61; GSW 6a landing branch land/gsw-6a-statements 66036926bcbffa9caf44f9e9469ca63bc555c374 (read only).

Reproduction: a sparse, detached git worktree at the issue base (only the 21 changed paths checked out);
git -c commit.gpgsign=false am --committer-date-is-author-date with committer Claude <noreply@anthropic.com>.
The worktree is removed after the review; the commits it made are unreferenced objects; no branch or ref was created
for them. Nothing was added, committed or pushed to any branch.

No Lean process was run (static review). The olean snapshot ($SP/olean-snapshot) was not touched; only its map file
olean-snapshot.map-463f2244.tsv was read (1453 entries, sha256 6607620d..., TCSlib/audits module set = the closure of
root + both audits/*/Checks at 463f2244, 1422).

Layout:
  integrity/     manifests, path sets, issued package, signing-key fingerprints of the exchange commits
  reproduction/  am hashes, equality with checkpoint 1 and src/, the -U0 diff
  statements/    decls2 (unmodified records tool fa81981a...), header check vs brief (stmtcmp; same output as at
                 checkpoint 1), docstrings, proof lengths and sketches, sizes and widths, style_lint (repo script,
                 unmodified copy from the tip) on the 21 head files, added-line scan
  clash/         same-short-name declaration hits of the 69 new names at the check base, tip, #340, #346, 6a
  recount/       bootstrap and sweep recount from raw logs (bound to git trees 01cc6259 / 985dd312), seal recount
                 (144 records: probe and source hashes, harness-only insertions, log hashes, install/EOF masks,
                 errors attributed to declarations), paired controls, explicit-unfold scan, axioms, lint line sets
  landing/       merge-tree results, file overlap with #340/#346/6a, closure lists for the phase-2 replay
  stage2/        table locations read at the check base, the maintainer Stage 2 addendum, unlisted copies, DL-35 alias uses
  tools/         every script used (python3 -I), unmodified decls2.py, stmtcmp.py/doccheck.py from the checkpoint-1 review

## ===== verification-r1.zip:phase1/statements/stmtcmp.out (this pack) =====

OK  Complexity.IterateFind.host_dispatch_view
OK  Complexity.IterateFind.host_branch_view
OK  Complexity.IterateFind.host_halt_view
OK  TCSlib.Cryptography.Games.expect_simulate_abs
OK  TCSlib.Cryptography.Games.expect_simulate_abs_inv
OK  TCSlib.Cryptography.Games.freshImpl (def, body pinned)
OK  TCSlib.Cryptography.Games.freshImpl_apply
OK  TCSlib.Cryptography.Games.extTape (def, body pinned)
OK  TCSlib.Cryptography.Games.extTape_of_lt
OK  TCSlib.Cryptography.Games.extTape_of_not_lt
OK  TCSlib.Cryptography.Games.extTape_update
OK  TCSlib.Cryptography.Games.tapeImpl (def, body pinned)
OK  TCSlib.Cryptography.Games.tapeImpl_apply
OK  TCSlib.Cryptography.Games.simulate_tapeImpl_congr
OK  TCSlib.Cryptography.Games.expect_simulate_tapeImpl
OK  TCSlib.Cryptography.Games.ovr (def, body pinned)
OK  TCSlib.Cryptography.Games.ovr_nil
OK  TCSlib.Cryptography.Games.ovr_cons
OK  TCSlib.Cryptography.Games.ovr_of_not_mem
OK  TCSlib.Cryptography.Games.ovr_of_mem
OK  TCSlib.Cryptography.Games.ovr_update
OK  TCSlib.Cryptography.Games.ovr_append
OK  TCSlib.Cryptography.Games.expect_sample_ovr
OK  TCSlib.Cryptography.Games.EffFill.length_le_length_encodeLog
DIFF TCSlib.Cryptography.zipWith_xor_cancel_right 
  brief: theorem zipWith_xor_cancel_right : ∀ (m p : List Bool), m.length ≤ p.length → List.zipWith xor (List.zipWith xor m p) p = m 
  head : theorem zipWith_xor_cancel_right : ∀ (m p : List Bool), m.length ≤ p.length → List.zipWith xor (List.zipWith xor m p) p = m | [], _, _ => rfl | _ :: _, [], h => absurd h (by rw [List.length_cons, List.length_nil]; omega) | a :: m, b :: p, h => by rw [List.zipWith_cons_cons, List.zipWith_cons_cons, zipWith_xor_cancel_right m p (by rw [List.length_cons, List.length_cons] at h; omega)] cases a <;> cases b <;> rfl
OK  TCSlib.Cryptography.recordBits (def, body pinned)
OK  TCSlib.Cryptography.recordBits_none
OK  TCSlib.Cryptography.recordBits_some
OK  TCSlib.Cryptography.length_recordBits
OK  Complexity.NUPPT.eval_toOracleAdversary_padFin
OK  TCSlib.Cryptography.FunFamily.ofFn_blocks_symm_eq_flatMap
OK  TCSlib.Cryptography.Games.Bridge.expect_sample_eq_uexp
OK  TCSlib.Cryptography.Authentication.ofFn_splitBits_fst
OK  TCSlib.Cryptography.Authentication.ofFn_splitBits_snd
OK  TCSlib.Cryptography.Games.OracleComp.exists_eq_pure_of_costBoundedBy_zero
OK  TCSlib.Cryptography.PrivateKeyScheme.encodeList_eq_flatMap
OK  TCSlib.Cryptography.getD_ofFn
OK  Complexity.NUPPT.length_ofFn_coins
OK  TCSlib.Cryptography.pkPredictor_apply
OK  TCSlib.Cryptography.StatClose.of_uprob_ne
OK  TCSlib.Cryptography.Strategy.encodeMsgs_eq
OK  TCSlib.Cryptography.Strategy.encodeMsgs_eq_flatMap
OK  TCSlib.Cryptography.Strategy.iterate_pairSndD_encodeMsgs
OK  TCSlib.Cryptography.Strategy.msgAt_encodeMsgs
OK  TCSlib.Cryptography.Strategy.encodeMsgs_eq_encWords
OK  TCSlib.Cryptography.EncodingMachines.flatMap_range_ite
OK  TCSlib.Cryptography.EncodingMachines.polyTimeComputable_flatMap_range
OK  TCSlib.Cryptography.EncodingMachines.iterSnd_poly
OK  TCSlib.Cryptography.EncodingMachines.zeros_poly
OK  TCSlib.Cryptography.EncodingMachines.padTo (def, body pinned)
OK  TCSlib.Cryptography.EncodingMachines.padTo_eq
OK  TCSlib.Cryptography.EncodingMachines.padTo_poly
OK  TCSlib.Cryptography.EncodingMachines.length_padTo
OK  TCSlib.Cryptography.EncodingMachines.getD_padTo
OK  TCSlib.Cryptography.EncodingMachines.padTo_of_length
OK  TCSlib.InformationTheory.FinDist.map_uniform_equiv
OK  TCSlib.InformationTheory.FinDist.sum_map
OK  TCSlib.InformationTheory.FinDist.probTrue_nonneg
OK  TCSlib.InformationTheory.FinDist.probTrue_le_one
OK  TCSlib.InformationTheory.FinDist.uniform_prod
OK  TCSlib.InformationTheory.FinDist.uniform_probTrue
OK  TCSlib.InformationTheory.FinDist.expect_map
OK  TCSlib.InformationTheory.FinDist.probTrue_map
OK  TCSlib.InformationTheory.FinDist.map_apply_expect
OK  TCSlib.InformationTheory.FinDist.map_map
OK  TCSlib.InformationTheory.FinDist.map_prod_snd
DIFF TCSlib.InformationTheory.FinDist.mixture 
  brief: protected noncomputable def FinDist.mixture (w : ℝ) (hw0 : 0 ≤ w) (hw1 : w ≤ 1) (p q : FinDist α) : FinDist α 
  head : protected noncomputable def FinDist.mixture (w : ℝ) (hw0 : 0 ≤ w) (hw1 : w ≤ 1) (p q : FinDist α) : FinDist α where prob a := w * p a + (1 - w) * q a nonneg a := add_nonneg (mul_nonneg hw0 (p.nonneg a)) (mul_nonneg (sub_nonneg.2 hw1) (q.nonneg a)) sum_prob := by rw [sum_add_distrib, ← mul_sum, ← mul_sum, p.sum_prob, q.sum_prob] ring
OK  TCSlib.InformationTheory.FinDist.mixture_apply
OK  TCSlib.InformationTheory.FinDist.mixture_isSource
chunks 69 ok 67 bad 2 unmatched added []

## ===== verification-r1.zip:phase1/statements/doccheck.out (this pack) =====

GLUE sk=- decl_lines=  7 Complexity.IterateFind.host_dispatch_view 
GLUE sk=- decl_lines= 14 Complexity.IterateFind.host_branch_view 
GLUE sk=- decl_lines= 12 Complexity.IterateFind.host_halt_view 
GLUE sk=- decl_lines=  3 Complexity.NUPPT.length_ofFn_coins 
GLUE sk=Y decl_lines= 18 TCSlib.Cryptography.FunFamily.ofFn_blocks_symm_eq_flatMap 
GLUE sk=Y decl_lines= 18 TCSlib.Cryptography.StatClose.of_uprob_ne 
GLUE sk=- decl_lines=  6 TCSlib.Cryptography.Authentication.ofFn_splitBits_fst 
GLUE sk=- decl_lines=  5 TCSlib.Cryptography.Authentication.ofFn_splitBits_snd 
GLUE sk=- decl_lines=  7 TCSlib.Cryptography.PrivateKeyScheme.encodeList_eq_flatMap 
TAG  sk=- decl_lines=  3 TCSlib.Cryptography.pkPredictor_apply ['[PS10, Theorem 104.4, proof]']
GLUE sk=- decl_lines=  8 TCSlib.Cryptography.zipWith_xor_cancel_right 
GLUE sk=- decl_lines=  3 TCSlib.Cryptography.recordBits 
GLUE sk=- decl_lines=  1 TCSlib.Cryptography.recordBits_none 
GLUE sk=- decl_lines=  2 TCSlib.Cryptography.recordBits_some 
GLUE sk=- decl_lines=  5 TCSlib.Cryptography.length_recordBits 
GLUE sk=- decl_lines=  4 TCSlib.Cryptography.getD_ofFn 
GLUE sk=- decl_lines=  3 TCSlib.Cryptography.Games.Bridge.expect_sample_eq_uexp 
GLUE sk=- decl_lines=  7 TCSlib.Cryptography.Games.EffFill.length_le_length_encodeLog 
GLUE sk=- decl_lines=  7 TCSlib.Cryptography.Games.OracleComp.exists_eq_pure_of_costBoundedBy_zero 
GLUE sk=- decl_lines=  3 TCSlib.Cryptography.Games.freshImpl 
GLUE sk=- decl_lines=  4 TCSlib.Cryptography.Games.freshImpl_apply 
GLUE sk=- decl_lines=  2 TCSlib.Cryptography.Games.extTape 
GLUE sk=- decl_lines=  3 TCSlib.Cryptography.Games.extTape_of_lt 
GLUE sk=- decl_lines=  3 TCSlib.Cryptography.Games.extTape_of_not_lt 
GLUE sk=- decl_lines=  6 TCSlib.Cryptography.Games.extTape_update 
GLUE sk=- decl_lines=  3 TCSlib.Cryptography.Games.tapeImpl 
GLUE sk=- decl_lines=  4 TCSlib.Cryptography.Games.tapeImpl_apply 
GLUE sk=Y decl_lines= 13 TCSlib.Cryptography.Games.simulate_tapeImpl_congr 
GLUE sk=Y decl_lines= 35 TCSlib.Cryptography.Games.expect_simulate_tapeImpl 
GLUE sk=- decl_lines=  3 TCSlib.Cryptography.Games.ovr 
GLUE sk=- decl_lines=  2 TCSlib.Cryptography.Games.ovr_nil 
GLUE sk=- decl_lines=  3 TCSlib.Cryptography.Games.ovr_cons 
GLUE sk=- decl_lines=  9 TCSlib.Cryptography.Games.ovr_of_not_mem 
GLUE sk=- decl_lines= 13 TCSlib.Cryptography.Games.ovr_of_mem 
GLUE sk=- decl_lines=  9 TCSlib.Cryptography.Games.ovr_update 
GLUE sk=- decl_lines=  7 TCSlib.Cryptography.Games.ovr_append 
GLUE sk=Y decl_lines= 13 TCSlib.Cryptography.Games.expect_sample_ovr 
GLUE sk=Y decl_lines= 16 TCSlib.Cryptography.Games.expect_simulate_abs 
GLUE sk=Y decl_lines= 17 TCSlib.Cryptography.Games.expect_simulate_abs_inv 
GLUE sk=Y decl_lines= 11 Complexity.NUPPT.eval_toOracleAdversary_padFin 
GLUE sk=- decl_lines= 12 TCSlib.Cryptography.EncodingMachines.flatMap_range_ite 
GLUE sk=Y decl_lines= 27 TCSlib.Cryptography.EncodingMachines.polyTimeComputable_flatMap_range 
GLUE sk=Y decl_lines= 41 TCSlib.Cryptography.EncodingMachines.iterSnd_poly 
GLUE sk=- decl_lines=  9 TCSlib.Cryptography.EncodingMachines.zeros_poly 
GLUE sk=- decl_lines=  1 TCSlib.Cryptography.EncodingMachines.padTo 
GLUE sk=- decl_lines=  2 TCSlib.Cryptography.EncodingMachines.padTo_eq 
GLUE sk=- decl_lines=  5 TCSlib.Cryptography.EncodingMachines.padTo_poly 
GLUE sk=- decl_lines=  4 TCSlib.Cryptography.EncodingMachines.length_padTo 
GLUE sk=- decl_lines=  9 TCSlib.Cryptography.EncodingMachines.getD_padTo 
NONE sk=- decl_lines=  4 TCSlib.Cryptography.EncodingMachines.padTo_of_length []
GLUE sk=- decl_lines=  1 TCSlib.Cryptography.Strategy.encodeMsgs_eq 
GLUE sk=- decl_lines=  7 TCSlib.Cryptography.Strategy.encodeMsgs_eq_flatMap 
GLUE sk=- decl_lines= 13 TCSlib.Cryptography.Strategy.iterate_pairSndD_encodeMsgs 
GLUE sk=- decl_lines=  4 TCSlib.Cryptography.Strategy.msgAt_encodeMsgs 
GLUE sk=- decl_lines=  3 TCSlib.Cryptography.Strategy.encodeMsgs_eq_encWords 
GLUE sk=- decl_lines=  8 TCSlib.InformationTheory.FinDist.mixture 
GLUE sk=- decl_lines=  3 TCSlib.InformationTheory.FinDist.mixture_apply 
GLUE sk=- decl_lines= 14 TCSlib.InformationTheory.FinDist.mixture_isSource 
GLUE sk=- decl_lines= 16 TCSlib.InformationTheory.FinDist.map_uniform_equiv 
GLUE sk=- decl_lines= 13 TCSlib.InformationTheory.FinDist.sum_map 
GLUE sk=- decl_lines=  3 TCSlib.InformationTheory.FinDist.probTrue_nonneg 
GLUE sk=- decl_lines=  3 TCSlib.InformationTheory.FinDist.probTrue_le_one 
GLUE sk=- decl_lines=  7 TCSlib.InformationTheory.FinDist.uniform_prod 
GLUE sk=- decl_lines=  5 TCSlib.InformationTheory.FinDist.uniform_probTrue 
GLUE sk=- decl_lines=  4 TCSlib.InformationTheory.FinDist.expect_map 
GLUE sk=- decl_lines=  3 TCSlib.InformationTheory.FinDist.probTrue_map 
GLUE sk=- decl_lines=  7 TCSlib.InformationTheory.FinDist.map_apply_expect 
GLUE sk=- decl_lines=  6 TCSlib.InformationTheory.FinDist.map_map 
GLUE sk=- decl_lines= 11 TCSlib.InformationTheory.FinDist.map_prod_snd 

## ===== verification-r1.zip:phase1/statements/prooflen.out (this pack) =====

 11	sk=-	glue	Complexity.IterateFind.host_branch_view	
  4	sk=-	glue	Complexity.IterateFind.host_dispatch_view	
  9	sk=-	glue	Complexity.IterateFind.host_halt_view	
  2	sk=-	glue	Complexity.NUPPT.length_ofFn_coins	
 16	sk=Y	gluetag	TCSlib.Cryptography.FunFamily.ofFn_blocks_symm_eq_flatMap	
 17	sk=Y	gluetag	TCSlib.Cryptography.StatClose.of_uprob_ne	
  5	sk=-	glue	TCSlib.Cryptography.Authentication.ofFn_splitBits_fst	
  4	sk=-	glue	TCSlib.Cryptography.Authentication.ofFn_splitBits_snd	
  6	sk=-	glue	TCSlib.Cryptography.PrivateKeyScheme.encodeList_eq_flatMap	
  2	sk=-	tag	TCSlib.Cryptography.pkPredictor_apply	
  3	sk=-	glue	TCSlib.Cryptography.getD_ofFn	
  4	sk=-	glue	TCSlib.Cryptography.length_recordBits	
  3	sk=-	glue	TCSlib.Cryptography.recordBits	
  1	sk=-	glue	TCSlib.Cryptography.recordBits_none	
  2	sk=-	glue	TCSlib.Cryptography.recordBits_some	
  7	sk=-	glue	TCSlib.Cryptography.zipWith_xor_cancel_right	
  2	sk=-	glue	TCSlib.Cryptography.Games.Bridge.expect_sample_eq_uexp	
  6	sk=-	glue	TCSlib.Cryptography.Games.EffFill.length_le_length_encodeLog	
  6	sk=-	glue	TCSlib.Cryptography.Games.OracleComp.exists_eq_pure_of_costBoundedBy_zero	
  9	sk=Y	glue	TCSlib.Cryptography.Games.expect_sample_ovr	
  9	sk=Y	glue	TCSlib.Cryptography.Games.expect_simulate_abs	
  9	sk=Y	glue	TCSlib.Cryptography.Games.expect_simulate_abs_inv	
 29	sk=Y	glue	TCSlib.Cryptography.Games.expect_simulate_tapeImpl	
  2	sk=-	glue	TCSlib.Cryptography.Games.extTape	
  2	sk=-	glue	TCSlib.Cryptography.Games.extTape_of_lt	
  2	sk=-	glue	TCSlib.Cryptography.Games.extTape_of_not_lt	
  5	sk=-	glue	TCSlib.Cryptography.Games.extTape_update	
  2	sk=-	glue	TCSlib.Cryptography.Games.freshImpl	
  2	sk=-	glue	TCSlib.Cryptography.Games.freshImpl_apply	
  3	sk=-	glue	TCSlib.Cryptography.Games.ovr	
  6	sk=-	glue	TCSlib.Cryptography.Games.ovr_append	
  2	sk=-	glue	TCSlib.Cryptography.Games.ovr_cons	
  2	sk=-	glue	TCSlib.Cryptography.Games.ovr_nil	
 12	sk=-	glue	TCSlib.Cryptography.Games.ovr_of_mem	
  8	sk=-	glue	TCSlib.Cryptography.Games.ovr_of_not_mem	
  8	sk=-	glue	TCSlib.Cryptography.Games.ovr_update	
 10	sk=Y	glue	TCSlib.Cryptography.Games.simulate_tapeImpl_congr	
  2	sk=-	glue	TCSlib.Cryptography.Games.tapeImpl	
  2	sk=-	glue	TCSlib.Cryptography.Games.tapeImpl_apply	
  6	sk=Y	glue	Complexity.NUPPT.eval_toOracleAdversary_padFin	
 10	sk=-	glue	TCSlib.Cryptography.EncodingMachines.flatMap_range_ite	
  8	sk=-	glue	TCSlib.Cryptography.EncodingMachines.getD_padTo	
 39	sk=Y	glue	TCSlib.Cryptography.EncodingMachines.iterSnd_poly	
  3	sk=-	glue	TCSlib.Cryptography.EncodingMachines.length_padTo	
  1	sk=-	glue	TCSlib.Cryptography.EncodingMachines.padTo	
  1	sk=-	glue	TCSlib.Cryptography.EncodingMachines.padTo_eq	
  3	sk=-		TCSlib.Cryptography.EncodingMachines.padTo_of_length	
  3	sk=-	glue	TCSlib.Cryptography.EncodingMachines.padTo_poly	
 24	sk=Y	glue	TCSlib.Cryptography.EncodingMachines.polyTimeComputable_flatMap_range	
  7	sk=-	glue	TCSlib.Cryptography.EncodingMachines.zeros_poly	
  1	sk=-	glue	TCSlib.Cryptography.Strategy.encodeMsgs_eq	
  6	sk=-	glue	TCSlib.Cryptography.Strategy.encodeMsgs_eq_flatMap	
 12	sk=-	glue	TCSlib.Cryptography.Strategy.iterate_pairSndD_encodeMsgs	
  3	sk=-	glue	TCSlib.Cryptography.Strategy.msgAt_encodeMsgs	
  2	sk=-	glue	TCSlib.Cryptography.Strategy.encodeMsgs_eq_encWords	
  7	sk=-	glue	TCSlib.InformationTheory.FinDist.mixture	
  2	sk=-	glue	TCSlib.InformationTheory.FinDist.mixture_apply	
 12	sk=-	glue	TCSlib.InformationTheory.FinDist.mixture_isSource	
 15	sk=-	glue	TCSlib.InformationTheory.FinDist.map_uniform_equiv	NEEDS-SKETCH
  3	sk=-	glue	TCSlib.InformationTheory.FinDist.probTrue_le_one	
  3	sk=-	glue	TCSlib.InformationTheory.FinDist.probTrue_nonneg	
 12	sk=-	glue	TCSlib.InformationTheory.FinDist.sum_map	
  3	sk=-	glue	TCSlib.InformationTheory.FinDist.uniform_probTrue	
  6	sk=-	glue	TCSlib.InformationTheory.FinDist.uniform_prod	
  3	sk=-	glue	TCSlib.InformationTheory.FinDist.expect_map	
  6	sk=-	glue	TCSlib.InformationTheory.FinDist.map_apply_expect	
  5	sk=-	glue	TCSlib.InformationTheory.FinDist.map_map	
  9	sk=-	glue	TCSlib.InformationTheory.FinDist.map_prod_snd	
  2	sk=-	glue	TCSlib.InformationTheory.FinDist.probTrue_map	

## ===== verification-r1.zip:phase1/statements/added-scan.txt (this pack) =====

hunks: 43; non-insertion hunks: 0
added lines: 1079
sorry/admit/@[simp]/attribute/unfold/delta/native_decide tokens in added lines: 0
tab/trailing-space/micro-sign in added lines: 0

## ===== verification-r1.zip:dw5/statements/frozencheck.txt (this pack) =====

FILE TCSlib/Complexity/Randomized/Build/IterateFind.lean: base 22 declarations (5 definition-like), head 22; differences 1
  DIFF	ORDER	-	-	0
FILE TCSlib/Complexity/Randomized/Build/IterateFindHost.lean: base 20 declarations (5 definition-like), head 23; differences 0
FILE TCSlib/Complexity/TuringMachine/Build/ModuleHost.lean: base 32 declarations (9 definition-like), head 38; differences 0
RESULT differences 1

## ===== verification-r1.zip:dw5/statements/touched.out (this pack) =====

UNCHANGED	TCSlib/Complexity/Randomized/Build/IterateFind.lean:101-107	Complexity.IterateFind.step	def
UNCHANGED	TCSlib/Complexity/Randomized/Build/IterateFind.lean:108-114	Complexity.IterateFind.step_eq	theorem
UNCHANGED	TCSlib/Complexity/Randomized/Build/IterateFind.lean:115-120	Complexity.IterateFind.Inv	def private
UNCHANGED	TCSlib/Complexity/Randomized/Build/IterateFind.lean:121-125	Complexity.IterateFind.inv_init	theorem private
UNCHANGED	TCSlib/Complexity/Randomized/Build/IterateFind.lean:126-136	Complexity.IterateFind.inv_step	theorem private
UNCHANGED	TCSlib/Complexity/Randomized/Build/IterateFind.lean:137-143	Complexity.IterateFind.inv_length	theorem private
UNCHANGED	TCSlib/Complexity/Randomized/Build/IterateFind.lean:144-148	Complexity.IterateFind.verdictWord	def private
UNCHANGED	TCSlib/Complexity/Randomized/Build/IterateFind.lean:149-155	Complexity.IterateFind.stepWord	def private
UNCHANGED	TCSlib/Complexity/Randomized/Build/IterateFind.lean:156-159	Complexity.IterateFind.outWord	def private
UNCHANGED	TCSlib/Complexity/Randomized/Build/IterateFind.lean:160-164	Complexity.IterateFind.verdictWord_head	theorem private
UNCHANGED	TCSlib/Complexity/Randomized/Build/IterateFind.lean:165-170	Complexity.IterateFind.verdictWord_length	theorem private
UNCHANGED	TCSlib/Complexity/Randomized/Build/IterateFind.lean:171-176	Complexity.IterateFind.stepWord_verdictWord	theorem private
UNCHANGED	TCSlib/Complexity/Randomized/Build/IterateFind.lean:177-181	Complexity.IterateFind.outWord_verdictWord	theorem private
UNCHANGED	TCSlib/Complexity/Randomized/Build/IterateFind.lean:182-188	Complexity.IterateFind.verdictWord_poly	theorem private
UNCHANGED	TCSlib/Complexity/Randomized/Build/IterateFind.lean:189-219	Complexity.IterateFind.stepWord_poly	theorem private
UNCHANGED	TCSlib/Complexity/Randomized/Build/IterateFind.lean:220-224	Complexity.IterateFind.outWord_poly	theorem private
UNCHANGED	TCSlib/Complexity/Randomized/Build/IterateFind.lean:225-228	Complexity.IterateFind.dupWord_poly	theorem private
UNCHANGED	TCSlib/Complexity/Randomized/Build/IterateFind.lean:231-241	Complexity.IterateFind.find?_congr_of_mem	theorem
UNCHANGED	TCSlib/Complexity/Randomized/Build/IterateFind.lean:242-262	Complexity.IterateFind.find?_range_and_lt	theorem
UNCHANGED	TCSlib/Complexity/Randomized/Build/IterateFind.lean:263-306	Complexity.IterateFind.final_bound	lemma private
CHANGED	TCSlib/Complexity/Randomized/Build/IterateFind.lean:307-589	Complexity.IterateFind.computesFunInTime_find	theorem
CHANGED	TCSlib/Complexity/Randomized/Build/IterateFind.lean:590-632	Complexity.IterateFind.polyTimeComputable_find	theorem
UNCHANGED	TCSlib/Complexity/Randomized/Build/IterateFindHost.lean:70-83	Complexity.IterateFind.copyTM	def
UNCHANGED	TCSlib/Complexity/Randomized/Build/IterateFindHost.lean:84-89	Complexity.IterateFind.copyCfg	def private
UNCHANGED	TCSlib/Complexity/Randomized/Build/IterateFindHost.lean:90-118	Complexity.IterateFind.copy_step	lemma private
UNCHANGED	TCSlib/Complexity/Randomized/Build/IterateFindHost.lean:119-145	Complexity.IterateFind.copy_turn	lemma private
UNCHANGED	TCSlib/Complexity/Randomized/Build/IterateFindHost.lean:146-183	Complexity.IterateFind.copy_rewind	lemma private
UNCHANGED	TCSlib/Complexity/Randomized/Build/IterateFindHost.lean:184-204	Complexity.IterateFind.copy_finish	lemma private
UNCHANGED	TCSlib/Complexity/Randomized/Build/IterateFindHost.lean:205-253	Complexity.IterateFind.copy_clean	lemma
ADDED	TCSlib/Complexity/Randomized/Build/IterateFindHost.lean:254-263	Complexity.IterateFind.copyTMView	abbrev
ADDED	TCSlib/Complexity/Randomized/Build/IterateFindHost.lean:264-267	Complexity.IterateFind.copyTMView_eq	theorem
ADDED	TCSlib/Complexity/Randomized/Build/IterateFindHost.lean:268-280	Complexity.IterateFind.copy_clean_view	theorem
UNCHANGED	TCSlib/Complexity/Randomized/Build/IterateFindHost.lean:283-294	Complexity.IterateFind.hostCtrl	def
UNCHANGED	TCSlib/Complexity/Randomized/Build/IterateFindHost.lean:295-307	Complexity.IterateFind.hostCtrl_eq	theorem
UNCHANGED	TCSlib/Complexity/Randomized/Build/IterateFindHost.lean:308-314	Complexity.IterateFind.hostRet	def
UNCHANGED	TCSlib/Complexity/Randomized/Build/IterateFindHost.lean:315-318	Complexity.IterateFind.hostRet_zero	theorem
UNCHANGED	TCSlib/Complexity/Randomized/Build/IterateFindHost.lean:319-322	Complexity.IterateFind.hostRet_one	theorem
UNCHANGED	TCSlib/Complexity/Randomized/Build/IterateFindHost.lean:323-326	Complexity.IterateFind.hostRet_two	theorem
UNCHANGED	TCSlib/Complexity/Randomized/Build/IterateFindHost.lean:327-330	Complexity.IterateFind.hostRet_three	theorem
UNCHANGED	TCSlib/Complexity/Randomized/Build/IterateFindHost.lean:331-334	Complexity.IterateFind.hostRet_four	theorem
UNCHANGED	TCSlib/Complexity/Randomized/Build/IterateFindHost.lean:335-342	Complexity.IterateFind.hostTM	abbrev
UNCHANGED	TCSlib/Complexity/Randomized/Build/IterateFindHost.lean:343-349	Complexity.IterateFind.hostTM_eq	theorem
UNCHANGED	TCSlib/Complexity/Randomized/Build/IterateFindHost.lean:350-360	Complexity.IterateFind.host_dispatch	theorem
UNCHANGED	TCSlib/Complexity/Randomized/Build/IterateFindHost.lean:361-377	Complexity.IterateFind.host_branch	theorem
UNCHANGED	TCSlib/Complexity/Randomized/Build/IterateFindHost.lean:378-389	Complexity.IterateFind.host_halt	theorem
UNCHANGED	TCSlib/Complexity/TuringMachine/Build/ModuleHost.lean:94-117	Turing.ModuleHost.first_halt	theorem
UNCHANGED	TCSlib/Complexity/TuringMachine/Build/ModuleHost.lean:118-128	Turing.ModuleHost.live_prefix	theorem
UNCHANGED	TCSlib/Complexity/TuringMachine/Build/ModuleHost.lean:131-142	Turing.ModuleHost.stopTM	def private
UNCHANGED	TCSlib/Complexity/TuringMachine/Build/ModuleHost.lean:143-148	Turing.ModuleHost.stopCfg	def private
UNCHANGED	TCSlib/Complexity/TuringMachine/Build/ModuleHost.lean:149-164	Turing.ModuleHost.stop_step	lemma private
UNCHANGED	TCSlib/Complexity/TuringMachine/Build/ModuleHost.lean:165-202	Turing.ModuleHost.stop_clean	lemma private
UNCHANGED	TCSlib/Complexity/TuringMachine/Build/ModuleHost.lean:203-214	Turing.ModuleHost.Clean	def
UNCHANGED	TCSlib/Complexity/TuringMachine/Build/ModuleHost.lean:215-227	Turing.ModuleHost.clean_iff	theorem
UNCHANGED	TCSlib/Complexity/TuringMachine/Build/ModuleHost.lean:228-267	Turing.ModuleHost.Clean.envelope	theorem
UNCHANGED	TCSlib/Complexity/TuringMachine/Build/ModuleHost.lean:268-288	Turing.ModuleHost.clean_stop	lemma private
UNCHANGED	TCSlib/Complexity/TuringMachine/Build/ModuleHost.lean:289-311	Turing.ModuleHost.bridge_bound	lemma private
UNCHANGED	TCSlib/Complexity/TuringMachine/Build/ModuleHost.lean:312-339	Turing.ModuleHost.clean_install	theorem
UNCHANGED	TCSlib/Complexity/TuringMachine/Build/ModuleHost.lean:340-360	Turing.ModuleHost.clean_emit	theorem
UNCHANGED	TCSlib/Complexity/TuringMachine/Build/ModuleHost.lean:361-367	Turing.ModuleHost.request_budget	theorem
UNCHANGED	TCSlib/Complexity/TuringMachine/Build/ModuleHost.lean:370-374	Turing.ModuleHost.padAction	def private
UNCHANGED	TCSlib/Complexity/TuringMachine/Build/ModuleHost.lean:375-382	Turing.ModuleHost.padTM	def private
UNCHANGED	TCSlib/Complexity/TuringMachine/Build/ModuleHost.lean:383-390	Turing.ModuleHost.padCfg	def private
UNCHANGED	TCSlib/Complexity/TuringMachine/Build/ModuleHost.lean:391-402	Turing.ModuleHost.pad_apply	lemma private
UNCHANGED	TCSlib/Complexity/TuringMachine/Build/ModuleHost.lean:403-422	Turing.ModuleHost.pad_run	lemma private
UNCHANGED	TCSlib/Complexity/TuringMachine/Build/ModuleHost.lean:423-436	Turing.ModuleHost.pad_seam	lemma private
UNCHANGED	TCSlib/Complexity/TuringMachine/Build/ModuleHost.lean:439-443	Turing.ModuleHost.State	abbrev
UNCHANGED	TCSlib/Complexity/TuringMachine/Build/ModuleHost.lean:444-448	Turing.ModuleHost.state_eq	theorem
UNCHANGED	TCSlib/Complexity/TuringMachine/Build/ModuleHost.lean:449-452	Turing.ModuleHost.entry	def
UNCHANGED	TCSlib/Complexity/TuringMachine/Build/ModuleHost.lean:453-457	Turing.ModuleHost.entry_eq	theorem
UNCHANGED	TCSlib/Complexity/TuringMachine/Build/ModuleHost.lean:465-477	Turing.ModuleHost.hostTM	def
UNCHANGED	TCSlib/Complexity/TuringMachine/Build/ModuleHost.lean:478-488	Turing.ModuleHost.hostTM_step_inl	theorem
UNCHANGED	TCSlib/Complexity/TuringMachine/Build/ModuleHost.lean:489-504	Turing.ModuleHost.host_seam	lemma private
UNCHANGED	TCSlib/Complexity/TuringMachine/Build/ModuleHost.lean:505-561	Turing.ModuleHost.host_call	theorem
UNCHANGED	TCSlib/Complexity/TuringMachine/Build/ModuleHost.lean:562-597	Turing.ModuleHost.host_call_envelope	theorem
UNCHANGED	TCSlib/Complexity/TuringMachine/Build/ModuleHost.lean:598-613	Turing.ModuleHost.guard_add	theorem
UNCHANGED	TCSlib/Complexity/TuringMachine/Build/ModuleHost.lean:614-639	Turing.ModuleHost.host_clean	theorem
UNCHANGED	TCSlib/Complexity/TuringMachine/Build/ModuleHost.lean:640-673	Turing.ModuleHost.host_clean_envelope	theorem
ADDED	TCSlib/Complexity/TuringMachine/Build/ModuleHost.lean:681-692	Turing.ModuleHost.hostTMView	abbrev
ADDED	TCSlib/Complexity/TuringMachine/Build/ModuleHost.lean:693-700	Turing.ModuleHost.hostTMView_eq	theorem
ADDED	TCSlib/Complexity/TuringMachine/Build/ModuleHost.lean:701-709	Turing.ModuleHost.hostTMView_q₀	theorem
ADDED	TCSlib/Complexity/TuringMachine/Build/ModuleHost.lean:710-722	Turing.ModuleHost.hostTMView_step_inl	theorem
ADDED	TCSlib/Complexity/TuringMachine/Build/ModuleHost.lean:723-748	Turing.ModuleHost.host_call_view	theorem
ADDED	TCSlib/Complexity/TuringMachine/Build/ModuleHost.lean:749-768	Turing.ModuleHost.host_clean_view	theorem

## ===== verification-r1.zip:dw5/compare/seals-base-vs-head.txt (this pack) =====

strict A ModuleHost       requests 241->241  errors 10->10  identical-failures True
   at: ['Turing.ModuleHost.clean_emit', 'Turing.ModuleHost.clean_install', 'Turing.ModuleHost.host_call', 'Turing.ModuleHost.host_seam', 'Turing.ModuleHost.pad_apply', 'Turing.ModuleHost.pad_run', 'Turing.ModuleHost.pad_seam', 'Turing.ModuleHost.stop_clean', 'Turing.ModuleHost.stop_step']
strict A IterateFindHost  requests 251->251  errors 16->16  identical-failures True
   at: ['Complexity.IterateFind.copy_clean', 'Complexity.IterateFind.copy_finish', 'Complexity.IterateFind.copy_rewind', 'Complexity.IterateFind.copy_step', 'Complexity.IterateFind.copy_turn', 'Complexity.IterateFind.host_branch', 'Complexity.IterateFind.host_dispatch', 'Complexity.IterateFind.host_halt']
strict A IterateFind      requests 595->595  errors 20->0  identical-failures False
   cleared: ['Complexity.IterateFind.computesFunInTime_find', 'Complexity.IterateFind.polyTimeComputable_find'] 20
   new: []
strict B ModuleHost       requests 241->241  errors 10->10  identical-failures True
   at: ['Turing.ModuleHost.clean_emit', 'Turing.ModuleHost.clean_install', 'Turing.ModuleHost.host_call', 'Turing.ModuleHost.host_seam', 'Turing.ModuleHost.pad_apply', 'Turing.ModuleHost.pad_run', 'Turing.ModuleHost.pad_seam', 'Turing.ModuleHost.stop_clean', 'Turing.ModuleHost.stop_step']
strict B IterateFindHost  requests 251->251  errors 16->16  identical-failures True
   at: ['Complexity.IterateFind.copy_clean', 'Complexity.IterateFind.copy_finish', 'Complexity.IterateFind.copy_rewind', 'Complexity.IterateFind.copy_step', 'Complexity.IterateFind.copy_turn', 'Complexity.IterateFind.host_branch', 'Complexity.IterateFind.host_dispatch', 'Complexity.IterateFind.host_halt']
strict B IterateFind      requests 596->596  errors 20->0  identical-failures False
   cleared: ['Complexity.IterateFind.computesFunInTime_find', 'Complexity.IterateFind.polyTimeComputable_find'] 20
   new: []
coe A    ModuleHost       requests 241->241  errors 10->10  identical-failures True
   at: ['Turing.ModuleHost.clean_emit', 'Turing.ModuleHost.clean_install', 'Turing.ModuleHost.host_call', 'Turing.ModuleHost.host_seam', 'Turing.ModuleHost.pad_apply', 'Turing.ModuleHost.pad_run', 'Turing.ModuleHost.pad_seam', 'Turing.ModuleHost.stop_clean', 'Turing.ModuleHost.stop_step']
coe A    IterateFindHost  requests 251->251  errors 16->16  identical-failures True
   at: ['Complexity.IterateFind.copy_clean', 'Complexity.IterateFind.copy_finish', 'Complexity.IterateFind.copy_rewind', 'Complexity.IterateFind.copy_step', 'Complexity.IterateFind.copy_turn', 'Complexity.IterateFind.host_branch', 'Complexity.IterateFind.host_dispatch', 'Complexity.IterateFind.host_halt']
coe A    IterateFind      requests 595->595  errors 20->0  identical-failures False
   cleared: ['Complexity.IterateFind.computesFunInTime_find', 'Complexity.IterateFind.polyTimeComputable_find'] 20
   new: []
coe B    ModuleHost       requests 241->241  errors 10->10  identical-failures True
   at: ['Turing.ModuleHost.clean_emit', 'Turing.ModuleHost.clean_install', 'Turing.ModuleHost.host_call', 'Turing.ModuleHost.host_seam', 'Turing.ModuleHost.pad_apply', 'Turing.ModuleHost.pad_run', 'Turing.ModuleHost.pad_seam', 'Turing.ModuleHost.stop_clean', 'Turing.ModuleHost.stop_step']
coe B    IterateFindHost  requests 251->251  errors 16->16  identical-failures True
   at: ['Complexity.IterateFind.copy_clean', 'Complexity.IterateFind.copy_finish', 'Complexity.IterateFind.copy_rewind', 'Complexity.IterateFind.copy_step', 'Complexity.IterateFind.copy_turn', 'Complexity.IterateFind.host_branch', 'Complexity.IterateFind.host_dispatch', 'Complexity.IterateFind.host_halt']
coe B    IterateFind      requests 596->596  errors 20->0  identical-failures False
   cleared: ['Complexity.IterateFind.computesFunInTime_find', 'Complexity.IterateFind.polyTimeComputable_find'] 20
   new: []

## ===== verification-r1.zip:dw5/axioms/axioms-summary.txt (this pack) =====

Complexity.exists_seedMajorityTM :: propext, Classical.choice, Quot.sound :: STANDARD
Complexity.seedMajority_mem_DTIME :: propext, Classical.choice, Quot.sound :: STANDARD
TCSlib.Cryptography.Randomness.bpp_subset_dtime_subexp :: propext, Classical.choice, Quot.sound :: STANDARD
Complexity.IterateFind.polyTimeComputable_find :: propext, Classical.choice, Quot.sound :: STANDARD
Complexity.polyTimeComputable_iterateFind :: propext, Classical.choice, Quot.sound :: STANDARD
Complexity.IterateFind.computesFunInTime_find :: propext, Classical.choice, Quot.sound :: STANDARD
Turing.FinTM.decidesInTime_iff :: propext, Classical.choice, Quot.sound :: STANDARD
Complexity.mem_DTIME_iff :: propext, Classical.choice, Quot.sound :: STANDARD
Randomized.inBPP_iff :: propext, Classical.choice, Quot.sound :: STANDARD
Complexity.SeedMajority.exists_countingTM :: propext, Classical.choice, Quot.sound :: STANDARD
Complexity.SeedMajority.envelope_of_computesInTime :: propext, Classical.choice, Quot.sound :: STANDARD
TCSlib.Cryptography.Randomness.Derand.exists_seed_majority :: propext, Classical.choice, Quot.sound :: STANDARD
TCSlib.Cryptography.Randomness.Derand.exists_coin_gap_threshold :: propext, Classical.choice, Quot.sound :: STANDARD
TCSlib.Cryptography.Randomness.Derand.exists_verifier_gap_bound :: propext, Classical.choice, Quot.sound :: STANDARD
TCSlib.Cryptography.Randomness.Derand.exists_secure_cover :: propext, Classical.choice, Quot.sound :: STANDARD
TCSlib.Cryptography.Randomness.Derand.seed_time_le_subexp :: propext, Classical.choice, Quot.sound :: STANDARD
TCSlib.Cryptography.Randomness.Derand.polyTimeComputable_ceilRoot :: propext, Classical.choice, Quot.sound :: STANDARD
TCSlib.Cryptography.Randomness.Derand.eff_mapCoins :: propext, Classical.choice, Quot.sound :: STANDARD
Turing.ModuleHost.hostTMView :: propext, Classical.choice, Quot.sound :: STANDARD
Turing.ModuleHost.hostTMView_eq :: propext, Classical.choice, Quot.sound :: STANDARD
Turing.ModuleHost.hostTMView_q₀ :: propext, Classical.choice, Quot.sound :: STANDARD
Turing.ModuleHost.hostTMView_step_inl :: propext, Classical.choice, Quot.sound :: STANDARD
Turing.ModuleHost.host_call_view :: propext, Classical.choice, Quot.sound :: STANDARD
Turing.ModuleHost.host_clean_view :: propext, Classical.choice, Quot.sound :: STANDARD
Complexity.IterateFind.copyTMView :: propext, Classical.choice, Quot.sound :: STANDARD
Complexity.IterateFind.copyTMView_eq :: propext, Classical.choice, Quot.sound :: STANDARD
Complexity.IterateFind.copy_clean_view :: propext, Classical.choice, Quot.sound :: STANDARD
printed 27 ; nonstandard 0
owner census: 193 stored constants of the three owners; nonstandard 0 []
sorryAx occurrences in log: 0

## ===== verification-r1.zip:dw5/checks/nameclash.txt (this pack) =====

Complexity.IterateFind.Inv	TCSlib/Complexity/Randomized/Build/IterateFind.lean	same-short-name 5	under-Authentication 0	EXACT 0
Complexity.IterateFind.computesFunInTime_find	TCSlib/Complexity/Randomized/Build/IterateFind.lean	same-short-name 0	under-Authentication 0	EXACT 0
Complexity.IterateFind.copyCfg	TCSlib/Complexity/Randomized/Build/IterateFindHost.lean	same-short-name 1	under-Authentication 0	EXACT 0
Complexity.IterateFind.copyTM	TCSlib/Complexity/Randomized/Build/IterateFindHost.lean	same-short-name 1	under-Authentication 0	EXACT 0
Complexity.IterateFind.copyTMView	TCSlib/Complexity/Randomized/Build/IterateFindHost.lean	same-short-name 0	under-Authentication 0	EXACT 0
Complexity.IterateFind.copyTMView_eq	TCSlib/Complexity/Randomized/Build/IterateFindHost.lean	same-short-name 0	under-Authentication 0	EXACT 0
Complexity.IterateFind.copy_clean	TCSlib/Complexity/Randomized/Build/IterateFindHost.lean	same-short-name 0	under-Authentication 0	EXACT 0
Complexity.IterateFind.copy_clean_view	TCSlib/Complexity/Randomized/Build/IterateFindHost.lean	same-short-name 0	under-Authentication 0	EXACT 0
Complexity.IterateFind.copy_finish	TCSlib/Complexity/Randomized/Build/IterateFindHost.lean	same-short-name 0	under-Authentication 0	EXACT 0
Complexity.IterateFind.copy_rewind	TCSlib/Complexity/Randomized/Build/IterateFindHost.lean	same-short-name 0	under-Authentication 0	EXACT 0
Complexity.IterateFind.copy_step	TCSlib/Complexity/Randomized/Build/IterateFindHost.lean	same-short-name 1	under-Authentication 0	EXACT 0
Complexity.IterateFind.copy_turn	TCSlib/Complexity/Randomized/Build/IterateFindHost.lean	same-short-name 0	under-Authentication 0	EXACT 0
Complexity.IterateFind.dupWord_poly	TCSlib/Complexity/Randomized/Build/IterateFind.lean	same-short-name 0	under-Authentication 0	EXACT 0
Complexity.IterateFind.final_bound	TCSlib/Complexity/Randomized/Build/IterateFind.lean	same-short-name 0	under-Authentication 0	EXACT 0
Complexity.IterateFind.find?_congr_of_mem	TCSlib/Complexity/Randomized/Build/IterateFind.lean	same-short-name 0	under-Authentication 0	EXACT 0
Complexity.IterateFind.find?_range_and_lt	TCSlib/Complexity/Randomized/Build/IterateFind.lean	same-short-name 0	under-Authentication 0	EXACT 0
Complexity.IterateFind.hostCtrl	TCSlib/Complexity/Randomized/Build/IterateFindHost.lean	same-short-name 0	under-Authentication 0	EXACT 0
Complexity.IterateFind.hostCtrl_eq	TCSlib/Complexity/Randomized/Build/IterateFindHost.lean	same-short-name 0	under-Authentication 0	EXACT 0
Complexity.IterateFind.hostRet	TCSlib/Complexity/Randomized/Build/IterateFindHost.lean	same-short-name 0	under-Authentication 0	EXACT 0
Complexity.IterateFind.hostRet_four	TCSlib/Complexity/Randomized/Build/IterateFindHost.lean	same-short-name 0	under-Authentication 0	EXACT 0
Complexity.IterateFind.hostRet_one	TCSlib/Complexity/Randomized/Build/IterateFindHost.lean	same-short-name 0	under-Authentication 0	EXACT 0
Complexity.IterateFind.hostRet_three	TCSlib/Complexity/Randomized/Build/IterateFindHost.lean	same-short-name 0	under-Authentication 0	EXACT 0
Complexity.IterateFind.hostRet_two	TCSlib/Complexity/Randomized/Build/IterateFindHost.lean	same-short-name 0	under-Authentication 0	EXACT 0
Complexity.IterateFind.hostRet_zero	TCSlib/Complexity/Randomized/Build/IterateFindHost.lean	same-short-name 0	under-Authentication 0	EXACT 0
Complexity.IterateFind.hostTM	TCSlib/Complexity/Randomized/Build/IterateFindHost.lean	same-short-name 1	under-Authentication 0	EXACT 0
Complexity.IterateFind.hostTM_eq	TCSlib/Complexity/Randomized/Build/IterateFindHost.lean	same-short-name 0	under-Authentication 0	EXACT 0
Complexity.IterateFind.host_branch	TCSlib/Complexity/Randomized/Build/IterateFindHost.lean	same-short-name 0	under-Authentication 0	EXACT 0
Complexity.IterateFind.host_dispatch	TCSlib/Complexity/Randomized/Build/IterateFindHost.lean	same-short-name 0	under-Authentication 0	EXACT 0
Complexity.IterateFind.host_halt	TCSlib/Complexity/Randomized/Build/IterateFindHost.lean	same-short-name 0	under-Authentication 0	EXACT 0
Complexity.IterateFind.inv_init	TCSlib/Complexity/Randomized/Build/IterateFind.lean	same-short-name 0	under-Authentication 0	EXACT 0
Complexity.IterateFind.inv_length	TCSlib/Complexity/Randomized/Build/IterateFind.lean	same-short-name 0	under-Authentication 0	EXACT 0
Complexity.IterateFind.inv_step	TCSlib/Complexity/Randomized/Build/IterateFind.lean	same-short-name 1	under-Authentication 0	EXACT 0
Complexity.IterateFind.outWord	TCSlib/Complexity/Randomized/Build/IterateFind.lean	same-short-name 0	under-Authentication 0	EXACT 0
Complexity.IterateFind.outWord_poly	TCSlib/Complexity/Randomized/Build/IterateFind.lean	same-short-name 0	under-Authentication 0	EXACT 0
Complexity.IterateFind.outWord_verdictWord	TCSlib/Complexity/Randomized/Build/IterateFind.lean	same-short-name 0	under-Authentication 0	EXACT 0
Complexity.IterateFind.polyTimeComputable_find	TCSlib/Complexity/Randomized/Build/IterateFind.lean	same-short-name 0	under-Authentication 0	EXACT 0
Complexity.IterateFind.step	TCSlib/Complexity/Randomized/Build/IterateFind.lean	same-short-name 31	under-Authentication 0	EXACT 0
Complexity.IterateFind.stepWord	TCSlib/Complexity/Randomized/Build/IterateFind.lean	same-short-name 0	under-Authentication 0	EXACT 0
Complexity.IterateFind.stepWord_poly	TCSlib/Complexity/Randomized/Build/IterateFind.lean	same-short-name 0	under-Authentication 0	EXACT 0
Complexity.IterateFind.stepWord_verdictWord	TCSlib/Complexity/Randomized/Build/IterateFind.lean	same-short-name 0	under-Authentication 0	EXACT 0
Complexity.IterateFind.step_eq	TCSlib/Complexity/Randomized/Build/IterateFind.lean	same-short-name 8	under-Authentication 0	EXACT 0
Complexity.IterateFind.verdictWord	TCSlib/Complexity/Randomized/Build/IterateFind.lean	same-short-name 0	under-Authentication 0	EXACT 0
Complexity.IterateFind.verdictWord_head	TCSlib/Complexity/Randomized/Build/IterateFind.lean	same-short-name 0	under-Authentication 0	EXACT 0
Complexity.IterateFind.verdictWord_length	TCSlib/Complexity/Randomized/Build/IterateFind.lean	same-short-name 0	under-Authentication 0	EXACT 0
Complexity.IterateFind.verdictWord_poly	TCSlib/Complexity/Randomized/Build/IterateFind.lean	same-short-name 0	under-Authentication 0	EXACT 0
Turing.ModuleHost.Clean	TCSlib/Complexity/TuringMachine/Build/ModuleHost.lean	same-short-name 0	under-Authentication 0	EXACT 0
Turing.ModuleHost.Clean.envelope	TCSlib/Complexity/TuringMachine/Build/ModuleHost.lean	same-short-name 0	under-Authentication 0	EXACT 0
Turing.ModuleHost.State	TCSlib/Complexity/TuringMachine/Build/ModuleHost.lean	same-short-name 3	under-Authentication 0	EXACT 0
Turing.ModuleHost.bridge_bound	TCSlib/Complexity/TuringMachine/Build/ModuleHost.lean	same-short-name 0	under-Authentication 0	EXACT 0
Turing.ModuleHost.clean_emit	TCSlib/Complexity/TuringMachine/Build/ModuleHost.lean	same-short-name 0	under-Authentication 0	EXACT 0
Turing.ModuleHost.clean_iff	TCSlib/Complexity/TuringMachine/Build/ModuleHost.lean	same-short-name 0	under-Authentication 0	EXACT 0
Turing.ModuleHost.clean_install	TCSlib/Complexity/TuringMachine/Build/ModuleHost.lean	same-short-name 0	under-Authentication 0	EXACT 0
Turing.ModuleHost.clean_stop	TCSlib/Complexity/TuringMachine/Build/ModuleHost.lean	same-short-name 0	under-Authentication 0	EXACT 0
Turing.ModuleHost.entry	TCSlib/Complexity/TuringMachine/Build/ModuleHost.lean	same-short-name 1	under-Authentication 0	EXACT 0
Turing.ModuleHost.entry_eq	TCSlib/Complexity/TuringMachine/Build/ModuleHost.lean	same-short-name 0	under-Authentication 0	EXACT 0
Turing.ModuleHost.first_halt	TCSlib/Complexity/TuringMachine/Build/ModuleHost.lean	same-short-name 0	under-Authentication 0	EXACT 0
Turing.ModuleHost.guard_add	TCSlib/Complexity/TuringMachine/Build/ModuleHost.lean	same-short-name 0	under-Authentication 0	EXACT 0
Turing.ModuleHost.hostTM	TCSlib/Complexity/TuringMachine/Build/ModuleHost.lean	same-short-name 1	under-Authentication 0	EXACT 0
Turing.ModuleHost.hostTMView	TCSlib/Complexity/TuringMachine/Build/ModuleHost.lean	same-short-name 0	under-Authentication 0	EXACT 0
Turing.ModuleHost.hostTMView_eq	TCSlib/Complexity/TuringMachine/Build/ModuleHost.lean	same-short-name 0	under-Authentication 0	EXACT 0
Turing.ModuleHost.hostTMView_q₀	TCSlib/Complexity/TuringMachine/Build/ModuleHost.lean	same-short-name 0	under-Authentication 0	EXACT 0
Turing.ModuleHost.hostTMView_step_inl	TCSlib/Complexity/TuringMachine/Build/ModuleHost.lean	same-short-name 0	under-Authentication 0	EXACT 0
Turing.ModuleHost.hostTM_step_inl	TCSlib/Complexity/TuringMachine/Build/ModuleHost.lean	same-short-name 0	under-Authentication 0	EXACT 0
Turing.ModuleHost.host_call	TCSlib/Complexity/TuringMachine/Build/ModuleHost.lean	same-short-name 0	under-Authentication 0	EXACT 0
Turing.ModuleHost.host_call_envelope	TCSlib/Complexity/TuringMachine/Build/ModuleHost.lean	same-short-name 0	under-Authentication 0	EXACT 0
Turing.ModuleHost.host_call_view	TCSlib/Complexity/TuringMachine/Build/ModuleHost.lean	same-short-name 0	under-Authentication 0	EXACT 0
Turing.ModuleHost.host_clean	TCSlib/Complexity/TuringMachine/Build/ModuleHost.lean	same-short-name 0	under-Authentication 0	EXACT 0
Turing.ModuleHost.host_clean_envelope	TCSlib/Complexity/TuringMachine/Build/ModuleHost.lean	same-short-name 0	under-Authentication 0	EXACT 0
Turing.ModuleHost.host_clean_view	TCSlib/Complexity/TuringMachine/Build/ModuleHost.lean	same-short-name 0	under-Authentication 0	EXACT 0
Turing.ModuleHost.host_seam	TCSlib/Complexity/TuringMachine/Build/ModuleHost.lean	same-short-name 0	under-Authentication 0	EXACT 0
Turing.ModuleHost.live_prefix	TCSlib/Complexity/TuringMachine/Build/ModuleHost.lean	same-short-name 0	under-Authentication 0	EXACT 0
Turing.ModuleHost.padAction	TCSlib/Complexity/TuringMachine/Build/ModuleHost.lean	same-short-name 1	under-Authentication 0	EXACT 0
Turing.ModuleHost.padCfg	TCSlib/Complexity/TuringMachine/Build/ModuleHost.lean	same-short-name 1	under-Authentication 0	EXACT 0
Turing.ModuleHost.padTM	TCSlib/Complexity/TuringMachine/Build/ModuleHost.lean	same-short-name 1	under-Authentication 0	EXACT 0
Turing.ModuleHost.pad_apply	TCSlib/Complexity/TuringMachine/Build/ModuleHost.lean	same-short-name 0	under-Authentication 0	EXACT 0
Turing.ModuleHost.pad_run	TCSlib/Complexity/TuringMachine/Build/ModuleHost.lean	same-short-name 0	under-Authentication 0	EXACT 0
Turing.ModuleHost.pad_seam	TCSlib/Complexity/TuringMachine/Build/ModuleHost.lean	same-short-name 0	under-Authentication 0	EXACT 0
Turing.ModuleHost.request_budget	TCSlib/Complexity/TuringMachine/Build/ModuleHost.lean	same-short-name 0	under-Authentication 0	EXACT 0
Turing.ModuleHost.state_eq	TCSlib/Complexity/TuringMachine/Build/ModuleHost.lean	same-short-name 2	under-Authentication 1	EXACT 0
    TCSlib.Cryptography.Authentication.LamportMachine.state_eq	TCSlib/Cryptography/Authentication/Signatures/Lamport/Machine.lean:268
Turing.ModuleHost.stopCfg	TCSlib/Complexity/TuringMachine/Build/ModuleHost.lean	same-short-name 0	under-Authentication 0	EXACT 0
Turing.ModuleHost.stopTM	TCSlib/Complexity/TuringMachine/Build/ModuleHost.lean	same-short-name 0	under-Authentication 0	EXACT 0
Turing.ModuleHost.stop_clean	TCSlib/Complexity/TuringMachine/Build/ModuleHost.lean	same-short-name 0	under-Authentication 0	EXACT 0
Turing.ModuleHost.stop_step	TCSlib/Complexity/TuringMachine/Build/ModuleHost.lean	same-short-name 0	under-Authentication 0	EXACT 0
RESULT exact full-name clashes: 0

## ===== pr347.diff.txt (this pack) =====

diff --git a/TCSlib/Complexity/Randomized/Build/IterateFind.lean b/TCSlib/Complexity/Randomized/Build/IterateFind.lean
index 27bf3615d..30edb6037 100644
--- a/TCSlib/Complexity/Randomized/Build/IterateFind.lean
+++ b/TCSlib/Complexity/Randomized/Build/IterateFind.lean
@@ -304,258 +304,6 @@ private lemma final_bound (c A D CP cP CR cR n Pn Rn : ℕ)
     _ = c * (A * (CP + 7) ^ D + 1) * (CR + 2) * (n + 1) ^ ((cP + 1) * D + cR) := by
         rw [Nat.pow_add]; ring
 
-/-- **The loop-level repetition lemma.** Let `g` be a polynomial-time step, `acc` a
-polynomial-time test, `out` a polynomial-time payload map, and `R, P` syntactic polynomials
-with `|g^[i] x| ≤ P|x|` for `i ≤ R|x|`. Then the function returning `out` of the orbit point
-of the first index `i ≤ R|x|` at which `acc` accepts the second component of the `i`-fold
-guarded step `Complexity.IterateFind.step g P x` from `⟨x, x⟩` (`[]` if none) is
-polynomial-time computable. This is the machine behind
-`Complexity.polyTimeComputable_iterateFind` [PS10, Algorithm 38.5, Theorem 35.1]; the pure
-identification of the guarded orbit with `g^[i] x` is done there.
-
-**Proof sketch.** Instance of `Turing.FinTM.exists_loopFindTM` for the host `hostTM` (the
-clean-module host `Turing.ModuleHost.hostTM` with the control table `hostCtrl`) over the five
-clean modules (the copier, and `Turing.ModuleHost.clean_install`/`clean_emit` of
-`x ↦ ⟨x, x⟩`, `verdictWord acc`, `stepWord g P`, `outWord out`), with anchor `inl 0`,
-invariant `Inv P`,
-step `step g P`, acceptance `acc ∘ snd`, payload `out ∘ snd`, start word `⟨x, x⟩`. The fuel
-machine computes `Nat.bits (R|x|)` (`polyTimeComputable_unaryPoly R` composed with
-`computesFunInTime_lengthBits`). `hstart`: the copier (`copy_clean`, `ModuleHost.host_call`)
-then the startup install (`ModuleHost.host_clean`) reach the anchor seam with `⟨x, x⟩` in
-`2|x| + 2 + t_S` steps
-with no earlier anchor visit. `hround`: from the anchor seam with an admissible word `⟨x, s⟩`,
-the dispatch step, the verdict call, the branch step (`host_branch`), then either the payload
-call and the halt step (`host_halt`) — state `none`, output `out s` — or the step call
-returning to the anchor seam with `step g P x ⟨x, s⟩` (`stepWord_verdictWord`); the anchor
-guard is `ModuleHost.guard_add` over the segments. All requests have length at most
-`2|x| + 2 + P|x| + 4`, so every call fits the common budget `T n = A (2n + 2 + P n + 5)^D`
-(`ModuleHost.request_budget`), and
-`final_bound` puts the combinator's bound `c (T n + 1)(R n + 2)` in normal form. -/
-theorem polyTimeComputable_find {g : List Bool → List Bool} (hg : PolyTimeComputable g)
-    {acc : List Bool → Bool} (hacc : PolyTimeComputable fun s => [acc s])
-    {out : List Bool → List Bool} (hout : PolyTimeComputable out)
-    (R P : PolyExpr)
-    (horbit : ∀ (x : List Bool) (i : ℕ), i ≤ R.eval x.length →
-      (g^[i] x).length ≤ P.eval x.length) :
-    PolyTimeComputable fun x =>
-      match (List.range (R.eval x.length + 1)).find?
-          (fun i => acc (pairSndD ((step g P x)^[i] (pairEncode x x)))) with
-      | some i => out (pairSndD ((step g P x)^[i] (pairEncode x x)))
-      | none => [] := by
-  obtain ⟨S, aS, dS, hS⟩ := ModuleHost.clean_install dupWord_poly
-  obtain ⟨V, aV, dV, hV⟩ := ModuleHost.clean_install (verdictWord_poly hacc)
-  obtain ⟨I, aI, dI, hI⟩ := ModuleHost.clean_install (stepWord_poly hg P)
-  obtain ⟨E, aE, dE, hE⟩ := ModuleHost.clean_emit (outWord_poly hout)
-  have hbits : PolyTimeComputable fun x => Nat.bits (R.eval x.length) := by
-    have h := (polyTimeComputable_of_linear FinTM.computesFunInTime_lengthBits).comp
-      (polyTimeComputable_unaryPoly R)
-    convert h using 1
-    funext x
-    simp
-  obtain ⟨F, aF, dF, hF⟩ := (polyTimeComputable_iff _).1 hbits
-  let M : Fin 5 → FinTM Bool := fun i => match i.val with
-    | 0 => copyTM | 1 => S | 2 => V | 3 => I | _ => E
-  let K := S.k + V.k + I.k + E.k
-  have hk : ∀ i, (M i).k ≤ K + 1 := by
-    intro i; fin_cases i <;> simp [M, K, copyTM_k] <;> omega
-  let H := hostTM M K hk
-  let anchor : H.State := .inl 0
-  have hclean := ModuleHost.host_clean M (K + 1) hk (hostCtrl M K) (hostRet M)
-    (ModuleHost.entry M 0)
-  let D := dS + dV + dI + dE + dF + 1
-  let A := aS + aV + aI + aE + aF + 5
-  let pow (n : ℕ) := (2 * n + 2 + P.eval n + 5) ^ D
-  let T (n : ℕ) := A * pow n
-  have hpow (n : ℕ) : n + 1 ≤ pow n := by
-    have h := Nat.pow_le_pow_right (show 0 < 2 * n + 2 + P.eval n + 5 by omega)
-      (show 1 ≤ D by dsimp [D]; omega)
-    simp only [Nat.pow_one] at h
-    exact (by omega : n + 1 ≤ 2 * n + 2 + P.eval n + 5).trans h
-  have hstart : ∀ x : List Bool, ∃ t ≤ T x.length,
-      (∀ v < t, (H.tm.runFrom (H.tm.initCfg x) v).state ≠ some anchor) ∧
-      H.tm.runFrom (H.tm.initCfg x) t = Cfg.ofWords anchor (stateWord H.k (pairEncode x x)) := by
-    intro x
-    obtain ⟨hcg, hce⟩ := copy_clean x
-    obtain ⟨hcGuard, hcEnd⟩ := ModuleHost.host_call M (K + 1) hk (hostCtrl M K) (hostRet M)
-      (ModuleHost.entry M 0) 0 (by simp [M, copyTM_k]) x [] x [] [] (0 : Fin 2)
-      (2 * x.length + 2) hcg (by simpa using hce)
-    have hi : H.tm.initCfg x = Cfg.ofWords (ModuleHost.entry M 0) (stateWord (K + 1) []) := by
-      refine Cfg.ext ?_ rfl ?_ rfl rfl
-      · exact congrArg some (ModuleHost.hostTM_tm_q₀ M (K + 1) hk (hostCtrl M K) (hostRet M)
-          (ModuleHost.entry M 0))
-      funext i z
-      simp [MultiTapeTM.initCfg_eq, Cfg.init_state, Cfg.init_inputPos, Cfg.init_workTapes,
-          Cfg.init_workTapePos, Cfg.init_output, Cfg.ofWords_def, stateWord_eq]
-    change H.tm.runFrom (Cfg.ofWords (input := x) (ModuleHost.entry M 0) (stateWord (K + 1) []))
-      (2 * x.length + 2) = Cfg.ofWords (hostRet M 0) (stateWord (K + 1) x) at hcEnd
-    rw [hostRet_zero] at hcEnd
-    obtain ⟨ts, hspos, hst, hsGuard, hsEnd⟩ := hclean 1
-      (fun x => pairEncode x x) (fun _ => []) (fun n => aS * (n + 1) ^ dS)
-      (by simpa [M] using hS) x x []
-    change H.tm.runFrom (Cfg.ofWords (input := x) (ModuleHost.entry M 1) (stateWord (K + 1) x))
-      ts = Cfg.ofWords (hostRet M 1) (stateWord (K + 1) (pairEncode x x)) at hsEnd
-    rw [hostRet_one] at hsEnd
-    have hsB := ModuleHost.request_budget aS dS D (2 * x.length + 2 + P.eval x.length + 5) x.length
-      (by dsimp [D]; omega) (by omega)
-    have hp := hpow x.length
-    refine ⟨2 * x.length + 2 + ts, ?_, ?_, ?_⟩
-    · dsimp only [T, A, pow]
-      simp only [Nat.add_mul]
-      dsimp only [pow] at hp
-      omega
-    · rw [hi]
-      exact ModuleHost.guard_add H.tm anchor _ _ _ ts (fun v hv => hcGuard v hv 0) hcEnd
-        (fun v hv => hsGuard v hv 0)
-    · rw [hi, MultiTapeTM.runFrom_add, hcEnd, hsEnd]
-      rfl
-  have hround : ∀ x w : List Bool, Inv P x w → ∃ t, 0 < t ∧ t ≤ T x.length ∧
-      (∀ t', 0 < t' → t' < t →
-        (H.tm.runFrom (Cfg.ofWords (input := x) anchor (stateWord H.k w)) t').state
-          ≠ some anchor) ∧
-      if acc (pairSndD w) then
-        (H.tm.runFrom (Cfg.ofWords (input := x) anchor (stateWord H.k w)) t).state = none ∧
-        (H.tm.runFrom (Cfg.ofWords (input := x) anchor (stateWord H.k w)) t).output =
-          out (pairSndD w)
-      else
-        H.tm.runFrom (Cfg.ofWords (input := x) anchor (stateWord H.k w)) t =
-          Cfg.ofWords anchor (stateWord H.k (step g P x w)) := by
-    intro x w hw
-    obtain ⟨s, rfl, hs⟩ := hw
-    have hwlen : (pairEncode x s).length ≤ 2 * x.length + 2 + P.eval x.length := by
-      rw [length_pairEncode]; omega
-    have hw'len : (verdictWord acc (pairEncode x s)).length =
-        (pairEncode x s).length + 4 := verdictWord_length acc _
-    have hpow' := hpow x.length
-    -- the dispatch, the verdict call, the branch
-    have hdisp := host_dispatch M K hk x (pairEncode x s)
-    obtain ⟨tv, hvpos, hvt, hvGuard, hvEnd⟩ := hclean 2 (verdictWord acc)
-      (fun _ => []) (fun n => aV * (n + 1) ^ dV) (by simpa [M] using hV) x (pairEncode x s) []
-    change H.tm.runFrom (Cfg.ofWords (input := x) (ModuleHost.entry M 2) (stateWord (K + 1)
-      (pairEncode x s))) tv = Cfg.ofWords (hostRet M 2) (stateWord (K + 1)
-        (verdictWord acc (pairEncode x s))) at hvEnd
-    rw [hostRet_two] at hvEnd
-    have hbr := host_branch M K hk x (acc s) (verdictWord acc (pairEncode x s))
-      (by rw [verdictWord_head, pairSndD_pairEncode])
-    have hvB := ModuleHost.request_budget aV dV D (2 * x.length + 2 + P.eval x.length + 5)
-      (pairEncode x s).length (by dsimp [D]; omega) (by omega)
-    have hseg : H.tm.runFrom (Cfg.ofWords (input := x) (ModuleHost.entry M 2)
-        (stateWord (K + 1) (pairEncode x s))) (tv + 1) =
-        Cfg.ofWords (ModuleHost.entry M (if acc s then 4 else 3))
-          (stateWord (K + 1) (verdictWord acc (pairEncode x s))) := by
-      rw [MultiTapeTM.runFrom_succ_eq_step', hvEnd, hbr]
-    have hsegGuard : ∀ v < tv + 1, (H.tm.runFrom (Cfg.ofWords (input := x) (ModuleHost.entry M 2)
-        (stateWord (K + 1) (pairEncode x s))) v).state ≠ some anchor := by
-      refine ModuleHost.guard_add H.tm anchor _ _ tv 1 (fun v hv => hvGuard v hv 0) hvEnd ?_
-      intro v hv
-      have hv0 : v = 0 := by omega
-      subst hv0
-      simp [Cfg.ofWords_def, anchor]
-    by_cases hb : acc s = true
-    · -- accepting round: the payload call, then the halt
-      rw [if_pos hb] at hseg
-      obtain ⟨te, hepos, het, heGuard, heEnd⟩ := hclean 4 id (outWord out)
-        (fun n => aE * (n + 1) ^ dE) (by simpa [M] using hE) x
-        (verdictWord acc (pairEncode x s)) []
-      change H.tm.runFrom (Cfg.ofWords (input := x) (ModuleHost.entry M 4) (stateWord (K + 1)
-        (verdictWord acc (pairEncode x s)))) te = {Cfg.ofWords (hostRet M 4) (stateWord (K + 1)
-          (verdictWord acc (pairEncode x s))) with
-            output := [] ++ outWord out (verdictWord acc (pairEncode x s))} at heEnd
-      rw [hostRet_four, List.nil_append, outWord_verdictWord] at heEnd
-      have hhalt := host_halt M K hk x (verdictWord acc (pairEncode x s)) (out s)
-      have heB := ModuleHost.request_budget aE dE D (2 * x.length + 2 + P.eval x.length + 5)
-        (verdictWord acc (pairEncode x s)).length (by dsimp [D]; omega) (by omega)
-      have hall : H.tm.runFrom (Cfg.ofWords (input := x) (ModuleHost.entry M 2)
-          (stateWord (K + 1) (pairEncode x s))) (tv + 1 + te + 1) =
-          {Cfg.ofWords (input := x) (.inl 2 : ModuleHost.State (Fin 3) M) (stateWord (K + 1)
-            (verdictWord acc (pairEncode x s))) with state := none, output := out s} := by
-        rw [MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_add, hseg, heEnd, hhalt]
-      have hallGuard : ∀ v < tv + 1 + te + 1, (H.tm.runFrom (Cfg.ofWords (input := x)
-          (ModuleHost.entry M 2) (stateWord (K + 1) (pairEncode x s))) v).state ≠ some anchor := by
-        refine ModuleHost.guard_add H.tm anchor _ {Cfg.ofWords (input := x)
-          (.inl 2 : ModuleHost.State (Fin 3) M)
-          (stateWord (K + 1) (verdictWord acc (pairEncode x s))) with output := out s}
-          (tv + 1 + te) 1 ?_ ?_ ?_
-        · exact ModuleHost.guard_add H.tm anchor _ _ (tv + 1) te hsegGuard hseg
-            (fun v hv => heGuard v hv 0)
-        · rw [MultiTapeTM.runFrom_add, hseg, heEnd]
-        · intro v hv
-          have hv0 : v = 0 := by omega
-          subst hv0
-          simp [Cfg.ofWords_def, anchor]
-      refine ⟨tv + 1 + te + 1 + 1, by omega, ?_, ?_, ?_⟩
-      · dsimp only [T, A, pow]
-        simp only [Nat.add_mul]
-        dsimp only [pow] at hpow'
-        omega
-      · intro v hv hvt
-        have hvform : v = (v - 1) + 1 := by omega
-        change (H.tm.runFrom (Cfg.ofWords (input := x) anchor (stateWord (K + 1)
-          (pairEncode x s))) v).state ≠ some anchor
-        rw [hvform, MultiTapeTM.runFrom_succ_eq_step, hdisp]
-        exact hallGuard (v - 1) (by omega)
-      · rw [pairSndD_pairEncode, if_pos hb]
-        change (H.tm.runFrom (Cfg.ofWords (input := x) anchor (stateWord (K + 1)
-            (pairEncode x s))) (tv + 1 + te + 1 + 1)).state = none ∧
-          (H.tm.runFrom (Cfg.ofWords (input := x) anchor (stateWord (K + 1)
-            (pairEncode x s))) (tv + 1 + te + 1 + 1)).output = out s
-        rw [MultiTapeTM.runFrom_succ_eq_step, hdisp, hall]
-        exact ⟨rfl, rfl⟩
-    · -- advancing round: the step call returns to the anchor
-      rw [if_neg hb] at hseg
-      obtain ⟨ti, hipos, hit, hiGuard, hiEnd⟩ := hclean 3 (stepWord g P)
-        (fun _ => []) (fun n => aI * (n + 1) ^ dI) (by simpa [M] using hI) x
-        (verdictWord acc (pairEncode x s)) []
-      change H.tm.runFrom (Cfg.ofWords (input := x) (ModuleHost.entry M 3) (stateWord (K + 1)
-        (verdictWord acc (pairEncode x s)))) ti = Cfg.ofWords (hostRet M 3) (stateWord (K + 1)
-          (stepWord g P (verdictWord acc (pairEncode x s)))) at hiEnd
-      rw [hostRet_three, stepWord_verdictWord] at hiEnd
-      have hiB := ModuleHost.request_budget aI dI D (2 * x.length + 2 + P.eval x.length + 5)
-        (verdictWord acc (pairEncode x s)).length (by dsimp [D]; omega) (by omega)
-      have hall : H.tm.runFrom (Cfg.ofWords (input := x) (ModuleHost.entry M 2)
-          (stateWord (K + 1) (pairEncode x s))) (tv + 1 + ti) =
-          Cfg.ofWords anchor (stateWord (K + 1) (step g P x (pairEncode x s))) := by
-        rw [MultiTapeTM.runFrom_add, hseg, hiEnd]
-      have hallGuard : ∀ v < tv + 1 + ti, (H.tm.runFrom (Cfg.ofWords (input := x)
-          (ModuleHost.entry M 2) (stateWord (K + 1) (pairEncode x s))) v).state ≠ some anchor :=
-        ModuleHost.guard_add H.tm anchor _ _ (tv + 1) ti hsegGuard hseg
-          (fun v hv => hiGuard v hv 0)
-      refine ⟨tv + 1 + ti + 1, by omega, ?_, ?_, ?_⟩
-      · dsimp only [T, A, pow]
-        simp only [Nat.add_mul]
-        dsimp only [pow] at hpow'
-        omega
-      · intro v hv hvt
-        have hvform : v = (v - 1) + 1 := by omega
-        change (H.tm.runFrom (Cfg.ofWords (input := x) anchor (stateWord (K + 1)
-          (pairEncode x s))) v).state ≠ some anchor
-        rw [hvform, MultiTapeTM.runFrom_succ_eq_step, hdisp]
-        exact hallGuard (v - 1) (by omega)
-      · rw [pairSndD_pairEncode, if_neg hb]
-        change H.tm.runFrom (Cfg.ofWords (input := x) anchor (stateWord (K + 1)
-            (pairEncode x s))) (tv + 1 + ti + 1) =
-          Cfg.ofWords anchor (stateWord (K + 1) (step g P x (pairEncode x s)))
-        rw [MultiTapeTM.runFrom_succ_eq_step, hdisp, hall]
-  have hFuel : F.ComputesFunInTime (fun x => Nat.bits (R.eval x.length)) T := by
-    intro x
-    apply (hF x).mono
-    have h := ModuleHost.request_budget aF dF D (2 * x.length + 2 + P.eval x.length + 5) x.length
-      (by dsimp [D]; omega) (by omega)
-    have hp := hpow x.length
-    dsimp only [T, A, pow]
-    simp only [Nat.add_mul]
-    dsimp only [pow] at hp
-    omega
-  obtain ⟨L, c, hL⟩ := FinTM.exists_loopFindTM H F anchor (Inv P) (step g P)
-    (fun _ w => acc (pairSndD w)) (fun _ w => out (pairSndD w)) (fun x => pairEncode x x)
-    (fun n => R.eval n) T hFuel
-    (fun x => inv_init P x (by simpa using horbit x 0 (Nat.zero_le _)))
-    (fun x w h => inv_step g P x w h) hstart hround
-  obtain ⟨CP, cP, hCP⟩ := P.eval_le
-  obtain ⟨CR, cR, hCR⟩ := R.eval_le
-  refine ⟨L, c * (A * (CP + 7) ^ D + 1) * (CR + 2), (cP + 1) * D + cR, fun x => (hL x).mono ?_⟩
-  exact final_bound c A D CP cP CR cR x.length (P.eval x.length) (R.eval x.length)
-    (hCP _) (hCR _)
-
 /-- A guarded search with arbitrary numerical fuel `R` and initial state `init` has a
 finite machine computing the first accepted payload (or `[]` on exhaustion) within
 `c * (A * (2 * n + 2 + P.eval n + 5) ^ D + 1) * (R n + 2)` steps, for constants
@@ -565,13 +313,27 @@ polynomial-time computable; `|init x| ≤ P.eval |x|`. A fuel machine computes
 `T n = A * (2 * n + 2 + P.eval n + 5) ^ D` is polynomial; no polynomial bound on `R`
 is assumed. [AB09, §7.1, p. 126]; [PS10, §8.2, Theorem 180.1, step 4]
 
-**Proof sketch.** Reuse the invariant and guarded-step modules of
-`polyTimeComputable_find`, installing `⟨x, init x⟩` at startup. The size guard preserves
-the invariant under every step, including steps after the search terminates. Install the
-verdict and step modules, emit the payload, and compose their clean calls through the
-same five-module host. A common polynomial budget pays for startup, each round, and the
-given binary fuel machine. The result-bearing loop combinator then supplies the stated
-bound directly, without using the polynomial-fuel normal form `final_bound`. -/
+**Proof sketch.** Instance of `Turing.FinTM.exists_loopFindTM` for the repetition machine's
+host (the clean-module host with the control table `hostCtrl` and the return states
+`hostRet`), read through its typed view `Turing.ModuleHost.hostTMView`, over five clean
+modules: the copier, through its typed view `copyTMView`, and
+`Turing.ModuleHost.clean_install`/`clean_emit` of `x ↦ ⟨x, init x⟩`, `verdictWord acc`,
+`stepWord g P` and `outWord out`. The anchor is `inl 0`; the invariant is `Inv P`, which the
+size guard preserves under every step, including steps after the search terminates; the
+step is `step g P`, the acceptance `acc ∘ snd`, the payload `out ∘ snd` and the start word
+`⟨x, init x⟩`. `hstart`: the copier call (`copy_clean_view`,
+`Turing.ModuleHost.host_call_view`) and the startup install
+(`Turing.ModuleHost.host_clean_view`) reach the anchor seam holding `⟨x, init x⟩` in
+`2|x| + 2 + t_S` steps, with no earlier anchor visit. `hround`: from the anchor seam with an
+admissible word `⟨x, s⟩`, the dispatch step, the verdict call, the branch step on the verdict
+cell, then either the payload call and the halt step (state `none`, output `out s`) or the
+step call back to the anchor seam with `step g P x ⟨x, s⟩`; the three control steps are read
+off `hostCtrl` through `Turing.ModuleHost.hostTMView_step_inl`, and the anchor guard is
+`Turing.ModuleHost.guard_add` over the segments. Every request has length at most
+`2|x| + 2 + P|x| + 4`, so every call and the given binary fuel machine fit the common budget
+`T n = A (2n + 2 + P n + 5)^D` (`Turing.ModuleHost.request_budget`). The result-bearing loop
+combinator then supplies the stated bound `c (T n + 1)(R n + 2)` directly, without the
+polynomial-fuel normal form `final_bound`; its search result is matched by cases. -/
 theorem computesFunInTime_find {g : List Bool → List Bool} (hg : PolyTimeComputable g)
     {acc : List Bool → Bool} (hacc : PolyTimeComputable fun s => [acc s])
     {out : List Bool → List Bool} (hout : PolyTimeComputable out)
@@ -588,20 +350,53 @@ theorem computesFunInTime_find {g : List Bool → List Bool} (hg : PolyTimeCompu
           | some i => out (pairSndD ((step g P x)^[i] (pairEncode x (init x))))
           | none => [])
         (fun n => c * (A * (2 * n + 2 + P.eval n + 5) ^ D + 1) * (R n + 2)) := by
-  -- Build the four clean calls and their shared host.
+  -- Build the four clean calls and their shared host, read through the typed views.
   obtain ⟨S, aS, dS, hS⟩ := ModuleHost.clean_install (polyTimeComputable_id.pairEncode hinit)
   obtain ⟨V, aV, dV, hV⟩ := ModuleHost.clean_install (verdictWord_poly hacc)
   obtain ⟨I, aI, dI, hI⟩ := ModuleHost.clean_install (stepWord_poly hg P)
   obtain ⟨E, aE, dE, hE⟩ := ModuleHost.clean_emit (outWord_poly hout)
   let M : Fin 5 → FinTM Bool := fun i => match i.val with
-    | 0 => copyTM | 1 => S | 2 => V | 3 => I | _ => E
+    | 0 => copyTMView | 1 => S | 2 => V | 3 => I | _ => E
   let K := S.k + V.k + I.k + E.k
   have hk : ∀ i, (M i).k ≤ K + 1 := by
-    intro i; fin_cases i <;> simp [M, K, copyTM_k] <;> omega
-  let H := hostTM M K hk
+    intro i; fin_cases i <;> simp [M, K] <;> omega
+  let H := ModuleHost.hostTMView M (K + 1) hk (hostCtrl M K) (hostRet M) (ModuleHost.entry M 0)
   let anchor : H.State := .inl 0
-  have hclean := ModuleHost.host_clean M (K + 1) hk (hostCtrl M K) (hostRet M)
+  have hclean := ModuleHost.host_clean_view M (K + 1) hk (hostCtrl M K) (hostRet M)
     (ModuleHost.entry M 0)
+  -- A seam with an empty output prefix is the seam.
+  have hseam (x : List Bool) (q : ModuleHost.State (Fin 3) M) (w : List Bool) :
+      ({Cfg.ofWords (input := x) q (stateWord (K + 1) w) with output := []} :
+        Cfg (K + 1) Bool (ModuleHost.State (Fin 3) M) x) = Cfg.ofWords q (stateWord (K + 1) w) :=
+    Cfg.ext rfl rfl rfl rfl (Cfg.ofWords_output q _).symm
+  -- The three control steps (the table `hostCtrl`), read through the typed view.
+  have hdisp (x w : List Bool) :
+      H.tm.step (Cfg.ofWords (input := x) anchor (stateWord (K + 1) w)) =
+        Cfg.ofWords (ModuleHost.entry M 2) (stateWord (K + 1) w) := by
+    rw [ModuleHost.hostTMView_step_inl _ _ _ _ _ _ _ 0 (Cfg.ofWords_state _ _), hostCtrl_eq,
+      if_pos rfl, FinTM.controlAction_apply, moveInputPos_zero, Cfg.ofWords_def, Cfg.ofWords_def]
+  have hbranch (x : List Bool) (b : Bool) (w : List Bool) (hw : w[0]? = some b) :
+      H.tm.step (Cfg.ofWords (input := x) (.inl 1) (stateWord (K + 1) w)) =
+        Cfg.ofWords (ModuleHost.entry M (if b then 4 else 3)) (stateWord (K + 1) w) := by
+    have hread : (Cfg.ofWords (input := x) (.inl 1 : ModuleHost.State (Fin 3) M)
+        (stateWord (K + 1) w)).workTapeSymbols 0 = some b := by
+      simp only [Cfg.workTapeSymbols_eq, Cfg.ofWords_workTapes, Cfg.ofWords_workTapePos,
+        stateWord_eq, FinTM.bufferTape_eq]
+      simpa using hw
+    rw [ModuleHost.hostTMView_step_inl _ _ _ _ _ _ _ 1 (Cfg.ofWords_state _ _), hostCtrl_eq,
+      if_neg (by decide), if_pos rfl, hread, FinTM.controlAction_apply, moveInputPos_zero,
+      Cfg.ofWords_def, Cfg.ofWords_def]
+    cases b <;> rfl
+  have hhalt (x w o : List Bool) :
+      H.tm.step {Cfg.ofWords (input := x) (.inl 2) (stateWord (K + 1) w) with output := o} =
+        {Cfg.ofWords (input := x) (.inl 2 : ModuleHost.State (Fin 3) M) (stateWord (K + 1) w)
+          with state := none, output := o} := by
+    rw [ModuleHost.hostTMView_step_inl _ _ _ _ _ _
+      ({Cfg.ofWords (input := x) (.inl 2) (stateWord (K + 1) w) with output := o} :
+        Cfg (K + 1) Bool (ModuleHost.State (Fin 3) M) x) 2
+      (Cfg.ofWords_state (input := x) (.inl 2 : ModuleHost.State (Fin 3) M) (stateWord (K + 1) w)),
+      hostCtrl_eq, if_neg (by decide), if_neg (by decide),
+      FinTM.controlAction_apply, moveInputPos_zero]
   let D := dS + dV + dI + dE + dF + 1
   let A := aS + aV + aI + aE + aF + 5
   let pow (n : ℕ) := (2 * n + 2 + P.eval n + 5) ^ D
@@ -617,25 +412,22 @@ theorem computesFunInTime_find {g : List Bool → List Bool} (hg : PolyTimeCompu
       H.tm.runFrom (H.tm.initCfg x) t =
         Cfg.ofWords anchor (stateWord H.k (pairEncode x (init x))) := by
     intro x
-    obtain ⟨hcg, hce⟩ := copy_clean x
-    obtain ⟨hcGuard, hcEnd⟩ := ModuleHost.host_call M (K + 1) hk (hostCtrl M K) (hostRet M)
-      (ModuleHost.entry M 0) 0 (by simp [M, copyTM_k]) x [] x [] [] (0 : Fin 2)
-      (2 * x.length + 2) hcg (by simpa using hce)
+    obtain ⟨hcg, hce⟩ := copy_clean_view x
+    obtain ⟨hcGuard, hcEnd⟩ := ModuleHost.host_call_view M (K + 1) hk (hostCtrl M K) (hostRet M)
+      (ModuleHost.entry M 0) 0 Nat.one_pos x [] x [] [] (0 : Fin 2) (2 * x.length + 2) hcg
+      (hce.trans (Cfg.ext rfl rfl rfl rfl
+        (Cfg.ofWords_output (input := x) (0 : Fin 2) (stateWord 1 x))))
     have hi : H.tm.initCfg x = Cfg.ofWords (ModuleHost.entry M 0) (stateWord (K + 1) []) := by
-      refine Cfg.ext ?_ rfl ?_ rfl rfl
-      · exact congrArg some (ModuleHost.hostTM_tm_q₀ M (K + 1) hk (hostCtrl M K) (hostRet M)
-          (ModuleHost.entry M 0))
-      funext i z
-      simp [MultiTapeTM.initCfg_eq, Cfg.init_state, Cfg.init_inputPos, Cfg.init_workTapes,
-          Cfg.init_workTapePos, Cfg.init_output, Cfg.ofWords_def, stateWord_eq]
-    change H.tm.runFrom (Cfg.ofWords (input := x) (ModuleHost.entry M 0) (stateWord (K + 1) []))
-      (2 * x.length + 2) = Cfg.ofWords (hostRet M 0) (stateWord (K + 1) x) at hcEnd
+      rw [initCfg_ofWords, ModuleHost.hostTMView_q₀]
+      congr 1
+      funext i
+      rw [stateWord_eq, ite_self]
+    simp only [List.nil_append, hseam] at hcGuard hcEnd
     rw [hostRet_zero] at hcEnd
     obtain ⟨ts, hspos, hst, hsGuard, hsEnd⟩ := hclean 1
       (fun x => pairEncode x (init x)) (fun _ => []) (fun n => aS * (n + 1) ^ dS)
       (by simpa [M] using hS) x x []
-    change H.tm.runFrom (Cfg.ofWords (input := x) (ModuleHost.entry M 1) (stateWord (K + 1) x))
-      ts = Cfg.ofWords (hostRet M 1) (stateWord (K + 1) (pairEncode x (init x))) at hsEnd
+    simp only [List.nil_append, hseam] at hsGuard hsEnd
     rw [hostRet_one] at hsEnd
     have hsB := ModuleHost.request_budget aS dS D (2 * x.length + 2 + P.eval x.length + 5) x.length
       (by dsimp [D]; omega) (by omega)
@@ -649,7 +441,6 @@ theorem computesFunInTime_find {g : List Bool → List Bool} (hg : PolyTimeCompu
       exact ModuleHost.guard_add H.tm anchor _ _ _ ts (fun v hv => hcGuard v hv 0) hcEnd
         (fun v hv => hsGuard v hv 0)
     · rw [hi, MultiTapeTM.runFrom_add, hcEnd, hsEnd]
-      rfl
   -- A positive round either emits its payload or advances the guarded state.
   have hround : ∀ x w : List Bool, Inv P x w → ∃ t, 0 < t ∧ t ≤ T x.length ∧
       (∀ t', 0 < t' → t' < t →
@@ -670,14 +461,12 @@ theorem computesFunInTime_find {g : List Bool → List Bool} (hg : PolyTimeCompu
         (pairEncode x s).length + 4 := verdictWord_length acc _
     have hpow' := hpow x.length
     -- the dispatch, the verdict call, the branch
-    have hdisp := host_dispatch M K hk x (pairEncode x s)
+    have hdisp := hdisp x (pairEncode x s)
     obtain ⟨tv, hvpos, hvt, hvGuard, hvEnd⟩ := hclean 2 (verdictWord acc)
       (fun _ => []) (fun n => aV * (n + 1) ^ dV) (by simpa [M] using hV) x (pairEncode x s) []
-    change H.tm.runFrom (Cfg.ofWords (input := x) (ModuleHost.entry M 2) (stateWord (K + 1)
-      (pairEncode x s))) tv = Cfg.ofWords (hostRet M 2) (stateWord (K + 1)
-        (verdictWord acc (pairEncode x s))) at hvEnd
+    simp only [List.nil_append, hseam] at hvGuard hvEnd
     rw [hostRet_two] at hvEnd
-    have hbr := host_branch M K hk x (acc s) (verdictWord acc (pairEncode x s))
+    have hbr := hbranch x (acc s) (verdictWord acc (pairEncode x s))
       (by rw [verdictWord_head, pairSndD_pairEncode])
     have hvB := ModuleHost.request_budget aV dV D (2 * x.length + 2 + P.eval x.length + 5)
       (pairEncode x s).length (by dsimp [D]; omega) (by omega)
@@ -699,12 +488,10 @@ theorem computesFunInTime_find {g : List Bool → List Bool} (hg : PolyTimeCompu
       obtain ⟨te, hepos, het, heGuard, heEnd⟩ := hclean 4 id (outWord out)
         (fun n => aE * (n + 1) ^ dE) (by simpa [M] using hE) x
         (verdictWord acc (pairEncode x s)) []
-      change H.tm.runFrom (Cfg.ofWords (input := x) (ModuleHost.entry M 4) (stateWord (K + 1)
-        (verdictWord acc (pairEncode x s)))) te = {Cfg.ofWords (hostRet M 4) (stateWord (K + 1)
-          (verdictWord acc (pairEncode x s))) with
-            output := [] ++ outWord out (verdictWord acc (pairEncode x s))} at heEnd
-      rw [hostRet_four, List.nil_append, outWord_verdictWord] at heEnd
-      have hhalt := host_halt M K hk x (verdictWord acc (pairEncode x s)) (out s)
+      simp only [List.nil_append, hseam, id_eq] at heGuard heEnd
+      rw [hostRet_four, outWord_verdictWord] at heEnd
+      have hhalt := hhalt x (verdictWord acc (pairEncode x s)) (out s)
+      simp only at hhalt
       have heB := ModuleHost.request_budget aE dE D (2 * x.length + 2 + P.eval x.length + 5)
         (verdictWord acc (pairEncode x s)).length (by dsimp [D]; omega) (by omega)
       have hall : H.tm.runFrom (Cfg.ofWords (input := x) (ModuleHost.entry M 2)
@@ -748,9 +535,7 @@ theorem computesFunInTime_find {g : List Bool → List Bool} (hg : PolyTimeCompu
       obtain ⟨ti, hipos, hit, hiGuard, hiEnd⟩ := hclean 3 (stepWord g P)
         (fun _ => []) (fun n => aI * (n + 1) ^ dI) (by simpa [M] using hI) x
         (verdictWord acc (pairEncode x s)) []
-      change H.tm.runFrom (Cfg.ofWords (input := x) (ModuleHost.entry M 3) (stateWord (K + 1)
-        (verdictWord acc (pairEncode x s)))) ti = Cfg.ofWords (hostRet M 3) (stateWord (K + 1)
-          (stepWord g P (verdictWord acc (pairEncode x s)))) at hiEnd
+      simp only [List.nil_append, hseam] at hiGuard hiEnd
       rw [hostRet_three, stepWord_verdictWord] at hiEnd
       have hiB := ModuleHost.request_budget aI dI D (2 * x.length + 2 + P.eval x.length + 5)
         (verdictWord acc (pairEncode x s)).length (by dsimp [D]; omega) (by omega)
@@ -796,6 +581,53 @@ theorem computesFunInTime_find {g : List Bool → List Bool} (hg : PolyTimeCompu
     (fun x w h => inv_step g P x w h) hstart hround
   refine ⟨L, c, A, D, (FinTM.computesFunInTime_iff _ _ _).mpr fun x => ?_⟩
   have hx := (FinTM.computesFunInTime_iff _ _ _).mp hL x
-  simpa only [T, pow] using hx
+  simp only [T, pow] at hx
+  -- The combinator states its result with its own `match`; read both by cases on the search.
+  revert hx
+  cases (List.range (R x.length + 1)).find?
+    (fun i => acc (pairSndD ((step g P x)^[i] (pairEncode x (init x))))) <;> exact id
+
+/-- **The loop-level repetition lemma.** Let `g` be a polynomial-time step, `acc` a
+polynomial-time test, `out` a polynomial-time payload map, and `R, P` syntactic polynomials
+with `|g^[i] x| ≤ P|x|` for `i ≤ R|x|`. Then the function returning `out` of the orbit point
+of the first index `i ≤ R|x|` at which `acc` accepts the second component of the `i`-fold
+guarded step `Complexity.IterateFind.step g P x` from `⟨x, x⟩` (`[]` if none) is
+polynomial-time computable. This is the machine behind
+`Complexity.polyTimeComputable_iterateFind` [PS10, Algorithm 38.5, Theorem 35.1]; the pure
+identification of the guarded orbit with `g^[i] x` is done there.
+
+**Proof sketch.** The instance of `computesFunInTime_find` with the initial state `init = id`
+(admissible, since `|x| ≤ P|x|` is the orbit bound at `i = 0`) and the fuel `R|x|`, whose
+fuel machine computes `Nat.bits (R|x|)` (`polyTimeComputable_unaryPoly R` composed with
+`computesFunInTime_lengthBits`, so that the `find?` range is exactly `R|x| + 1`).
+`final_bound` puts its bound `c (T n + 1)(R n + 2)`, with `T n = A (2n + 2 + P n + 5)^D`, in
+the normal form `C (n + 1)^e` of `Complexity.PolyTimeComputable`, once `P` and `R` are
+majorised by `CP (n+1)^cP` and `CR (n+1)^cR` (`Complexity.PolyExpr.eval_le`). -/
+theorem polyTimeComputable_find {g : List Bool → List Bool} (hg : PolyTimeComputable g)
+    {acc : List Bool → Bool} (hacc : PolyTimeComputable fun s => [acc s])
+    {out : List Bool → List Bool} (hout : PolyTimeComputable out)
+    (R P : PolyExpr)
+    (horbit : ∀ (x : List Bool) (i : ℕ), i ≤ R.eval x.length →
+      (g^[i] x).length ≤ P.eval x.length) :
+    PolyTimeComputable fun x =>
+      match (List.range (R.eval x.length + 1)).find?
+          (fun i => acc (pairSndD ((step g P x)^[i] (pairEncode x x)))) with
+      | some i => out (pairSndD ((step g P x)^[i] (pairEncode x x)))
+      | none => [] := by
+  have hbits : PolyTimeComputable fun x => Nat.bits (R.eval x.length) := by
+    have h := (polyTimeComputable_of_linear FinTM.computesFunInTime_lengthBits).comp
+      (polyTimeComputable_unaryPoly R)
+    convert h using 1
+    funext x
+    simp
+  obtain ⟨F, aF, dF, hF⟩ := (polyTimeComputable_iff _).1 hbits
+  obtain ⟨L, c, A, D, hL⟩ := computesFunInTime_find hg hacc hout polyTimeComputable_id
+    (fun n => R.eval n) P (fun x => by simpa using horbit x 0 (Nat.zero_le _)) F aF dF hF
+  obtain ⟨CP, cP, hCP⟩ := P.eval_le
+  obtain ⟨CR, cR, hCR⟩ := R.eval_le
+  refine (polyTimeComputable_iff _).2 ⟨L, c * (A * (CP + 7) ^ D + 1) * (CR + 2),
+    (cP + 1) * D + cR, (FinTM.computesFunInTime_iff _ _ _).2 fun x => ?_⟩
+  exact ((FinTM.computesFunInTime_iff _ _ _).1 hL x).mono
+    (final_bound c A D CP cP CR cR x.length (P.eval x.length) (R.eval x.length) (hCP _) (hCR _))
 
 end Complexity.IterateFind
diff --git a/TCSlib/Complexity/Randomized/Build/IterateFindHost.lean b/TCSlib/Complexity/Randomized/Build/IterateFindHost.lean
index 582b9da89..cf4597f4d 100644
--- a/TCSlib/Complexity/Randomized/Build/IterateFindHost.lean
+++ b/TCSlib/Complexity/Randomized/Build/IterateFindHost.lean
@@ -36,13 +36,15 @@ load-bearing lemma of the Pass–shelat campaign, foundation decision D11 of
 
 ## Main definitions
 
-* `Complexity.IterateFind.copyTM` — the input copier.
+* `Complexity.IterateFind.copyTM` — the input copier; `copyTMView`, the copier with its tape
+  count, state type and start state explicit (`copyTMView_eq`).
 * `Complexity.IterateFind.hostCtrl`, `hostRet`, `hostTM` — the host's control table over its
   three control states, the return states of the five modules, and the host.
 
 ## Main results
 
-* `Complexity.IterateFind.copy_clean` — the copier's contract.
+* `Complexity.IterateFind.copy_clean` — the copier's contract; `copy_clean_view`, the same for
+  `copyTMView`.
 * `Complexity.IterateFind.host_dispatch`, `host_branch`, `host_halt` — the host's control steps.
 
 ## References
@@ -249,6 +251,32 @@ lemma copy_clean (x : List Bool) :
     · funext i
       simp [copyCfg, Cfg.ofWords]
 
+/-- **The typed view of the input copier**: the finite machine with one work tape, state type
+`Fin 2`, start state `0` and the copier's transition function,
+`copyTMView = ⟨1, Fin 2, ⟨0, copyTM.tm.tr⟩⟩`. It is the copier itself (`copyTMView_eq`), with its
+tape count, state type and start state explicit, so that a consumer can type the copier's
+configurations without unfolding `copyTM`. -/
+abbrev copyTMView : FinTM Bool where
+  k := 1
+  State := Fin 2
+  tm := { q₀ := 0, tr := copyTM.tm.tr }
+
+/-- The typed view of the copier is the copier: `copyTMView = copyTM`. -/
+theorem copyTMView_eq : copyTMView = copyTM :=
+  rfl
+
+/-- **The typed copier's contract** (`copy_clean` for `copyTMView`): from the empty seam over
+native input `x`, the typed copier is live before time `2|x| + 2` and
+`copyTMView.tm.runFrom (Cfg.ofWords 0 (stateWord 1 [])) (2|x| + 2) =
+{Cfg.ofWords 0 (stateWord 1 x) with state := none}`. -/
+theorem copy_clean_view (x : List Bool) :
+    (∀ v < 2 * x.length + 2,
+      ¬(copyTMView.tm.runFrom (Cfg.ofWords (input := x) (0 : Fin 2) (stateWord 1 [])) v).Halted) ∧
+    copyTMView.tm.runFrom (Cfg.ofWords (input := x) (0 : Fin 2) (stateWord 1 []))
+        (2 * x.length + 2) =
+      {Cfg.ofWords (input := x) (0 : Fin 2) (stateWord 1 x) with state := none} :=
+  copy_clean x
+
 
 /-! ### The host -/
 
diff --git a/TCSlib/Complexity/TuringMachine/Build/ModuleHost.lean b/TCSlib/Complexity/TuringMachine/Build/ModuleHost.lean
index acd1b28ad..4670e2e5d 100644
--- a/TCSlib/Complexity/TuringMachine/Build/ModuleHost.lean
+++ b/TCSlib/Complexity/TuringMachine/Build/ModuleHost.lean
@@ -60,6 +60,8 @@ machines, the control states and their table, the return map and the start state
 * `Turing.ModuleHost.State`, `Turing.ModuleHost.entry` — the host's state type and the entry
   state of a module (`state_eq`, `entry_eq`).
 * `Turing.ModuleHost.hostTM` — the host (`hostTM_k`, `hostTM_tm_q₀`, `hostTM_step_inl`).
+* `Turing.ModuleHost.hostTMView` — the host with its tape count and state type explicit
+  (`hostTMView_eq`, `hostTMView_q₀`, `hostTMView_step_inl`, `host_call_view`, `host_clean_view`).
 
 ## Main results
 
@@ -669,4 +671,99 @@ theorem host_clean_envelope {C : Type} [Fintype C] [DecidableEq C] {n : ℕ}
   have hB : (t : ℤ) ≤ B arg.length := by exact_mod_cast ht
   exact (host_call_envelope M K hk ctrl ret q₀ i x arg pre t v hv j).trans hB
 
+/-! ### The typed view of the host
+
+A consumer that does not unfold `hostTM` cannot see that its tape count is `K` and its state
+type is `State C M`, so it cannot type the host's seam configurations. The typed view
+`hostTMView` names both fields explicitly and keeps the host's machine; the readers below
+restate the host's contracts for it, each proved by the original contract. -/
+
+/-- **The typed view of the host**: the finite machine with `K` work tapes, state type
+`State C M` and the underlying machine of `hostTM M K hk ctrl ret q₀`,
+`hostTMView M K hk ctrl ret q₀ = ⟨K, State C M, (hostTM M K hk ctrl ret q₀).tm⟩`. It is the host
+itself (`hostTMView_eq`), with its tape count and state type explicit. -/
+abbrev hostTMView {C : Type} [Fintype C] [DecidableEq C] {n : ℕ}
+    (M : Fin n → FinTM Bool) (K : ℕ) (hk : ∀ i, (M i).k ≤ K)
+    (ctrl : C → Option Bool → (Fin K → Option Bool) → Action K Bool (State C M))
+    (ret : Fin n → State C M) (q₀ : State C M) : FinTM Bool where
+  k := K
+  State := State C M
+  tm := (hostTM M K hk ctrl ret q₀).tm
+
+/-- The typed view is the host: `hostTMView M K hk ctrl ret q₀ = hostTM M K hk ctrl ret q₀`. -/
+theorem hostTMView_eq {C : Type} [Fintype C] [DecidableEq C] {n : ℕ}
+    (M : Fin n → FinTM Bool) (K : ℕ) (hk : ∀ i, (M i).k ≤ K)
+    (ctrl : C → Option Bool → (Fin K → Option Bool) → Action K Bool (State C M))
+    (ret : Fin n → State C M) (q₀ : State C M) :
+    hostTMView M K hk ctrl ret q₀ = hostTM M K hk ctrl ret q₀ :=
+  rfl
+
+/-- The typed view starts in the supplied start state:
+`(hostTMView M K hk ctrl ret q₀).tm.q₀ = q₀`. -/
+theorem hostTMView_q₀ {C : Type} [Fintype C] [DecidableEq C] {n : ℕ}
+    (M : Fin n → FinTM Bool) (K : ℕ) (hk : ∀ i, (M i).k ≤ K)
+    (ctrl : C → Option Bool → (Fin K → Option Bool) → Action K Bool (State C M))
+    (ret : Fin n → State C M) (q₀ : State C M) :
+    (hostTMView M K hk ctrl ret q₀).tm.q₀ = q₀ :=
+  rfl
+
+/-- **A control step of the typed view** (`hostTM_step_inl` for `hostTMView`): at a
+configuration in the control state `inl c`, one step applies the consumer's action,
+`(hostTMView M K hk ctrl ret q₀).tm.step cfg = (ctrl c cfg.inputSymbol cfg.workTapeSymbols).apply
+cfg`. -/
+theorem hostTMView_step_inl {C : Type} [Fintype C] [DecidableEq C] {n : ℕ}
+    (M : Fin n → FinTM Bool) (K : ℕ) (hk : ∀ i, (M i).k ≤ K)
+    (ctrl : C → Option Bool → (Fin K → Option Bool) → Action K Bool (State C M))
+    (ret : Fin n → State C M) (q₀ : State C M) {x : List Bool}
+    (cfg : Cfg K Bool (State C M) x) (c : C) (hc : cfg.state = some (.inl c)) :
+    (hostTMView M K hk ctrl ret q₀).tm.step cfg =
+      (ctrl c cfg.inputSymbol cfg.workTapeSymbols).apply cfg :=
+  hostTM_step_inl M K hk ctrl ret q₀ cfg c hc
+
+/-- **A module call inside the typed view** (`host_call` for `hostTMView`): if module `i` (with
+`0 < (M i).k`), run from the seam at its start state with argument `arg`, is live before time
+`t` and at time `t` is halted at the seam holding `result` with output `out`, then the typed
+view, run from its seam at the entry state of module `i` holding `arg` with output prefix `pre`,
+visits no control state before `t`, and
+`(hostTMView M K hk ctrl ret q₀).tm.runFrom {Cfg.ofWords (entry M i) (stateWord K arg) with
+output := pre} t = {Cfg.ofWords (ret i) (stateWord K result) with output := pre ++ out}`. -/
+theorem host_call_view {C : Type} [Fintype C] [DecidableEq C] {n : ℕ} (M : Fin n → FinTM Bool)
+    (K : ℕ) (hk : ∀ i, (M i).k ≤ K)
+    (ctrl : C → Option Bool → (Fin K → Option Bool) → Action K Bool (State C M))
+    (ret : Fin n → State C M) (q₀ : State C M)
+    (i : Fin n) (hp : 0 < (M i).k) (x arg result out pre : List Bool)
+    (q : (M i).State) (t : ℕ)
+    (hg : ∀ v < t, ¬((M i).tm.runFrom
+      (Cfg.ofWords (input := x) (M i).tm.q₀ (stateWord (M i).k arg)) v).Halted)
+    (he : (M i).tm.runFrom
+      (Cfg.ofWords (input := x) (M i).tm.q₀ (stateWord (M i).k arg)) t =
+      {Cfg.ofWords q (stateWord (M i).k result) with state := none, output := out}) :
+    (∀ v < t, ∀ c : C, ((hostTMView M K hk ctrl ret q₀).tm.runFrom
+      {Cfg.ofWords (input := x) (entry M i) (stateWord K arg) with output := pre} v).state
+        ≠ some (.inl c)) ∧
+    (hostTMView M K hk ctrl ret q₀).tm.runFrom
+      {Cfg.ofWords (input := x) (entry M i) (stateWord K arg) with output := pre} t =
+      {Cfg.ofWords (ret i) (stateWord K result) with output := pre ++ out} :=
+  host_call M K hk ctrl ret q₀ i hp x arg result out pre q t hg he
+
+/-- **A clean module call inside the typed view** (`host_clean` for `hostTMView`): if module `i`
+is `Clean` with result map `f`, emitted chunk `g` and budget `B`, then the typed view, run from
+its seam at the entry state of module `i` holding `arg` with output `pre`, reaches at some time
+`t` with `0 < t ≤ B |arg|` the seam in the return state `ret i` holding `f arg`, with output
+`pre ++ g arg`, and visits no control state before `t`. -/
+theorem host_clean_view {C : Type} [Fintype C] [DecidableEq C] {n : ℕ}
+    (M : Fin n → FinTM Bool) (K : ℕ) (hk : ∀ i, (M i).k ≤ K)
+    (ctrl : C → Option Bool → (Fin K → Option Bool) → Action K Bool (State C M))
+    (ret : Fin n → State C M) (q₀ : State C M)
+    (i : Fin n) (f g : List Bool → List Bool) (B : ℕ → ℕ)
+    (h : Clean (M i) f g B) (x arg pre : List Bool) :
+    ∃ t, 0 < t ∧ t ≤ B arg.length ∧
+      (∀ v < t, ∀ c : C, ((hostTMView M K hk ctrl ret q₀).tm.runFrom
+        {Cfg.ofWords (input := x) (entry M i) (stateWord K arg) with output := pre} v).state
+          ≠ some (.inl c)) ∧
+      (hostTMView M K hk ctrl ret q₀).tm.runFrom
+        {Cfg.ofWords (input := x) (entry M i) (stateWord K arg) with output := pre} t =
+        {Cfg.ofWords (ret i) (stateWord K (f arg)) with output := pre ++ g arg} :=
+  host_clean M K hk ctrl ret q₀ i f g B h x arg pre
+
 end Turing.ModuleHost

## ===== pr355.diff.txt (this pack) =====

diff --git a/TCSlib/Complexity/Randomized/Build/IterateFindHost.lean b/TCSlib/Complexity/Randomized/Build/IterateFindHost.lean
index cf4597f4d..ebe98588f 100644
--- a/TCSlib/Complexity/Randomized/Build/IterateFindHost.lean
+++ b/TCSlib/Complexity/Randomized/Build/IterateFindHost.lean
@@ -46,6 +46,8 @@ load-bearing lemma of the Pass–shelat campaign, foundation decision D11 of
 * `Complexity.IterateFind.copy_clean` — the copier's contract; `copy_clean_view`, the same for
   `copyTMView`.
 * `Complexity.IterateFind.host_dispatch`, `host_branch`, `host_halt` — the host's control steps.
+* `Complexity.IterateFind.host_dispatch_view`, `host_branch_view`, `host_halt_view` — the same
+  control steps for the typed view `Turing.ModuleHost.hostTMView`.
 
 ## References
 
@@ -387,4 +389,62 @@ theorem host_halt (M : Fin 5 → FinTM Bool) (K : ℕ) (hk : ∀ i, (M i).k ≤
   change (FinTM.controlAction 0 none).apply _ = _
   rw [FinTM.controlAction_apply, moveInputPos_zero]
 
+/-- **The anchor's dispatch, for the typed view** (`host_dispatch` for
+`Turing.ModuleHost.hostTMView`): from the seam at `inl 0` holding `w`, one step of the typed view
+`H = hostTMView M (K + 1) hk (hostCtrl M K) (hostRet M) (entry M 0)` reaches the seam at the
+verdict module's entry holding `w`,
+`H.tm.step (Cfg.ofWords (inl 0) (stateWord (K + 1) w)) =
+Cfg.ofWords (entry M 2) (stateWord (K + 1) w)`.
+Framework glue, no textbook counterpart (the host's control table). -/
+theorem host_dispatch_view (M : Fin 5 → FinTM Bool) (K : ℕ) (hk : ∀ i, (M i).k ≤ K + 1)
+    (x w : List Bool) :
+    (ModuleHost.hostTMView M (K + 1) hk (hostCtrl M K) (hostRet M) (ModuleHost.entry M 0)).tm.step
+        (Cfg.ofWords (input := x) (.inl 0) (stateWord (K + 1) w)) =
+      Cfg.ofWords (ModuleHost.entry M 2) (stateWord (K + 1) w) := by
+  rw [ModuleHost.hostTMView_step_inl _ _ _ _ _ _ _ 0 (Cfg.ofWords_state _ _), hostCtrl_eq,
+    if_pos rfl, FinTM.controlAction_apply, moveInputPos_zero, Cfg.ofWords_def, Cfg.ofWords_def]
+
+/-- **The branch, for the typed view** (`host_branch` for `Turing.ModuleHost.hostTMView`): the
+branch state reads the first cell of tape 0, the verdict `b` of a word `w` with `w[0]? = some b`,
+and one step of the typed view
+`H = hostTMView M (K + 1) hk (hostCtrl M K) (hostRet M) (entry M 0)` dispatches into the payload
+module (`b` true) or the step module (`b` false) at the seam holding `w`,
+`H.tm.step (Cfg.ofWords (inl 1) (stateWord (K + 1) w)) =
+Cfg.ofWords (entry M (if b then 4 else 3)) (stateWord (K + 1) w)`.
+Framework glue, no textbook counterpart (the host's control table). -/
+theorem host_branch_view (M : Fin 5 → FinTM Bool) (K : ℕ) (hk : ∀ i, (M i).k ≤ K + 1)
+    (x : List Bool) (b : Bool) (w : List Bool) (hw : w[0]? = some b) :
+    (ModuleHost.hostTMView M (K + 1) hk (hostCtrl M K) (hostRet M) (ModuleHost.entry M 0)).tm.step
+        (Cfg.ofWords (input := x) (.inl 1) (stateWord (K + 1) w)) =
+      Cfg.ofWords (ModuleHost.entry M (if b then 4 else 3)) (stateWord (K + 1) w) := by
+  have hread : (Cfg.ofWords (input := x) (.inl 1 : ModuleHost.State (Fin 3) M)
+      (stateWord (K + 1) w)).workTapeSymbols 0 = some b := by
+    simp only [Cfg.workTapeSymbols_eq, Cfg.ofWords_workTapes, Cfg.ofWords_workTapePos,
+      stateWord_eq, FinTM.bufferTape_eq]
+    simpa using hw
+  rw [ModuleHost.hostTMView_step_inl _ _ _ _ _ _ _ 1 (Cfg.ofWords_state _ _), hostCtrl_eq,
+    if_neg (by decide), if_pos rfl, hread, FinTM.controlAction_apply, moveInputPos_zero,
+    Cfg.ofWords_def, Cfg.ofWords_def]
+  cases b <;> rfl
+
+/-- **The halt, for the typed view** (`host_halt` for `Turing.ModuleHost.hostTMView`): from the
+seam at `inl 2` holding `w` with output `o`, one step of the typed view
+`H = hostTMView M (K + 1) hk (hostCtrl M K) (hostRet M) (entry M 0)` reaches the same seam with
+control `none` and output `o`,
+`H.tm.step {Cfg.ofWords (inl 2) (stateWord (K + 1) w) with output := o} =
+{Cfg.ofWords (inl 2) (stateWord (K + 1) w) with state := none, output := o}`.
+Framework glue, no textbook counterpart (the host's control table). -/
+theorem host_halt_view (M : Fin 5 → FinTM Bool) (K : ℕ) (hk : ∀ i, (M i).k ≤ K + 1)
+    (x w o : List Bool) :
+    (ModuleHost.hostTMView M (K + 1) hk (hostCtrl M K) (hostRet M) (ModuleHost.entry M 0)).tm.step
+        {Cfg.ofWords (input := x) (.inl 2) (stateWord (K + 1) w) with output := o} =
+      {Cfg.ofWords (input := x) (.inl 2 : ModuleHost.State (Fin 3) M) (stateWord (K + 1) w)
+        with state := none, output := o} := by
+  rw [ModuleHost.hostTMView_step_inl _ _ _ _ _ _
+    ({Cfg.ofWords (input := x) (.inl 2) (stateWord (K + 1) w) with output := o} :
+      Cfg (K + 1) Bool (ModuleHost.State (Fin 3) M) x) 2
+    (Cfg.ofWords_state (input := x) (.inl 2 : ModuleHost.State (Fin 3) M) (stateWord (K + 1) w)),
+    hostCtrl_eq, if_neg (by decide), if_neg (by decide),
+    FinTM.controlAction_apply, moveInputPos_zero]
+
 end Complexity.IterateFind
diff --git a/TCSlib/Complexity/Randomized/PPT.lean b/TCSlib/Complexity/Randomized/PPT.lean
index dd437f164..36b6d77cb 100644
--- a/TCSlib/Complexity/Randomized/PPT.lean
+++ b/TCSlib/Complexity/Randomized/PPT.lean
@@ -109,6 +109,7 @@ one (Definitions 26.1 and 69.4) and are related by explicit lemmas, never unifie
 * `Complexity.NUPPT.exists_uniform_computes` — every polynomial-time computable function is
   computed with probability one by a PPT [PS10, Definition 24.6, non-vacuity].
 * `Complexity.NUPPT.nonempty` — the class is inhabited.
+* `Complexity.NUPPT.length_ofFn_coins` — a coin string `r : A.Coins n` has `coins.eval n` entries.
 
 ## References
 
@@ -221,6 +222,13 @@ theorem length_advInput (n : ℕ) (y : List Bool) : (advInput n y).length = 2 *
 [PS10, Definition 23.4, "each bit of the random tape is uniformly and independently chosen"]. -/
 abbrev Coins (n : ℕ) : Type := Fin (A.coinLen n) → Bool
 
+/-- **The length of a coin string**: the list of the coins `r : A.Coins n` has length
+`coins.eval n`, `(List.ofFn r).length = A.coins.eval n`.
+Framework glue, no textbook counterpart. -/
+protected theorem length_ofFn_coins (n : ℕ) (r : A.Coins n) :
+    (List.ofFn r).length = A.coins.eval n := by
+  rw [List.length_ofFn, coinLen_eq]
+
 /-- Activation at parameter `n` on argument `y` with coins `r`: machine input
 `⟨⟨⟨1^n, y⟩, advice n⟩, r⟩`. The sampler `r ↦ runAt n y r` on the uniform coin type
 `Coins n` is the distribution `A(1^n, y)` of the text. -/
diff --git a/TCSlib/Cryptography/Asymptotic/Adversary.lean b/TCSlib/Cryptography/Asymptotic/Adversary.lean
index e2018d8af..38029707b 100644
--- a/TCSlib/Cryptography/Asymptotic/Adversary.lean
+++ b/TCSlib/Cryptography/Asymptotic/Adversary.lean
@@ -70,6 +70,8 @@ by `ifEq`).
 * `TCSlib.Cryptography.ofFn_cast`, `TCSlib.Cryptography.ofFn_arrowCongr_finCongr` — a bit vector
   read across an equality of widths keeps its string.
 * `TCSlib.Cryptography.FunFamily.ofFn_blocks` — block `j` of a string is its `j`-th window.
+* `TCSlib.Cryptography.FunFamily.ofFn_blocks_symm_eq_flatMap` — the string of a tuple of blocks is
+  the concatenation of the block strings.
 * `TCSlib.Cryptography.invProbOpt_le_invProb`, `TCSlib.Cryptography.invProbOpt_some` — the
   bridges to the concrete `invProb`.
 * `TCSlib.Cryptography.invProbOpt_nonneg`, `TCSlib.Cryptography.invProbOpt_le_one` — bounds.
@@ -292,6 +294,34 @@ theorem FunFamily.ofFn_blocks (q ℓ : ℕ) (ω : Fin (q * ℓ) → Bool) (j : F
     rw [Nat.mul_comm]
     omega
 
+/-- **The string of a tuple of blocks is the concatenation of the block strings:** for
+`V : Fin q → Fin ℓ → Bool` and any `F : ℕ → List Bool` with `F i = ⟦V i⟧` for every `i < q`,
+`⟦(FunFamily.blocks q ℓ).symm V⟧ = (List.range q).flatMap F`. Framework glue (the block encoding
+of [PS10, Theorem 35.1] is cited at `FunFamily.blocks`).
+
+**Proof sketch.** Cut the string into `q` windows of `ℓ` bits (`List.ofFn_mul`). Position `j` of
+window `i` is position `i·ℓ + j`, which the inverse bijection reads as bit `j` of block `i`
+(`FunFamily.blocks_symm_apply`: quotient `i` and remainder `j` by `ℓ`), so window `i` is
+`⟦V i⟧ = F i`, and the windows over `Fin q` are the chunks over `List.range q`. -/
+theorem FunFamily.ofFn_blocks_symm_eq_flatMap {q ℓ : ℕ} (V : Fin q → Fin ℓ → Bool)
+    (F : ℕ → List Bool) (hF : ∀ i (h : i < q), F i = List.ofFn (V ⟨i, h⟩)) :
+    List.ofFn ((FunFamily.blocks q ℓ).symm V) = (List.range q).flatMap F := by
+  rw [List.ofFn_mul, List.flatMap_def, ← List.map_coe_finRange, List.map_map, List.ofFn_eq_map]
+  congr 1
+  refine List.map_congr_left fun i _ => ?_
+  rw [Function.comp_apply, hF i i.isLt]
+  congr 1
+  funext j
+  rw [FunFamily.blocks_symm_apply]
+  have hℓ : 0 < ℓ := Nat.pos_of_ne_zero (by rintro rfl; exact j.elim0)
+  congr 1
+  · refine Fin.ext ?_
+    simp only [Fin.coe_divNat]
+    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hℓ, Nat.div_eq_of_lt j.2, Nat.zero_add]
+  · refine Fin.ext ?_
+    simp only [Fin.coe_modNat]
+    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt j.2]
+
 /-- **Block `i` of a string of `r` blocks of `k` bits and a tail** is segment `i`:
 `⟦j ↦ w (castAdd sl (finProdFinEquiv (i, j)))⟧ = coinBlock k i ⟦w⟧`.
 
diff --git a/TCSlib/Cryptography/Asymptotic/Sampling.lean b/TCSlib/Cryptography/Asymptotic/Sampling.lean
index ff030e9f4..dc37bf470 100644
--- a/TCSlib/Cryptography/Asymptotic/Sampling.lean
+++ b/TCSlib/Cryptography/Asymptotic/Sampling.lean
@@ -75,6 +75,8 @@ added for the permutation sampler, whose section moved to `Asymptotic/Permutatio
 * `TCSlib.Cryptography.StatClose.map`, `TCSlib.Cryptography.StatClose.prod`,
   `TCSlib.Cryptography.StatClose.trans`, `TCSlib.Cryptography.StatClose.comp_pushesUniform`
   — closure properties.
+* `TCSlib.Cryptography.StatClose.of_uprob_ne` — two samplers on the same seeds are close within
+  the probability that they differ (the coupling bound).
 * `TCSlib.Cryptography.pushesUniform_of_card_fiber` — equal fibres push uniform to uniform (C5).
 * `TCSlib.Cryptography.firstHit_uniform_of_some`, `TCSlib.Cryptography.uprob_firstHit_none`,
   `TCSlib.Cryptography.statClose_firstHit` — the first hit is uniform (C4).
@@ -163,6 +165,33 @@ theorem StatClose.symm {X : σ → γ} {Y : τ → γ} {δ : ℝ} (h : StatClose
 theorem StatClose.mono {X : σ → γ} {Y : τ → γ} {δ δ' : ℝ} (h : StatClose X Y δ) (hδ : δ ≤ δ') :
     StatClose X Y δ' := fun T => (h T).trans hδ
 
+/-- **Two samplers on the same seeds are statistically close within the probability that they
+differ** (the coupling bound): `StatClose X Y Pr_s[X s ≠ Y s]`, i.e.
+`|Pr_s[T (X s)] − Pr_s[T (Y s)]| ≤ Pr_s[X s ≠ Y s]` for every test set `T`. Framework glue (its
+uses are [PS10, Theorem 107.3] in DDH and [PS10, Theorem 163.7] in Yao).
+
+**Proof sketch.** On a seed where `T (X s)` holds, either `X s = Y s` and `T (Y s)` holds, or the
+samplers differ there; so `Pr[T (X)] ≤ Pr[T (Y)] + Pr[X ≠ Y]` (`uprob_mono`, `uprob_or_le`), and
+symmetrically with `Pr[Y ≠ X] = Pr[X ≠ Y]` (`OneWay.uprob_congr`). -/
+theorem StatClose.of_uprob_ne {σ γ : Type*} [Fintype σ] (X Y : σ → γ) :
+    StatClose X Y (uprob fun s => X s ≠ Y s) := by
+  rw [statClose_iff]
+  intro T
+  have key : ∀ (X Y : σ → γ), uprob (fun s => T (X s)) ≤
+      uprob (fun s => T (Y s)) + uprob (fun s => X s ≠ Y s) := by
+    intro X Y
+    refine (uprob_mono fun s h => ?_).trans (uprob_or_le (fun s => T (Y s)) (fun s => X s ≠ Y s))
+    by_cases hxy : X s = Y s
+    · exact Or.inl (hxy ▸ h)
+    · exact Or.inr hxy
+  have h1 := key X Y
+  have h2 := key Y X
+  have hsymm : uprob (fun s => Y s ≠ X s) = uprob (fun s => X s ≠ Y s) :=
+    OneWay.uprob_congr fun s => ne_comm
+  rw [hsymm] at h2
+  rw [abs_sub_le_iff]
+  constructor <;> linarith
+
 /-- Closeness bounds add along a chain (triangle inequality). -/
 theorem StatClose.trans {X : σ → γ} {Y : τ → γ} {Z : υ → γ} {δ δ' : ℝ}
     (h : StatClose X Y δ) (h' : StatClose Y Z δ') : StatClose X Z (δ + δ') := fun T =>
diff --git a/TCSlib/Cryptography/Authentication/Encoding.lean b/TCSlib/Cryptography/Authentication/Encoding.lean
index ddbe8e405..e9c982c67 100644
--- a/TCSlib/Cryptography/Authentication/Encoding.lean
+++ b/TCSlib/Cryptography/Authentication/Encoding.lean
@@ -20,6 +20,7 @@ set_option autoImplicit false
 ## Main results
 
 `splitBits_fst`, `splitBits_snd` and `atParam_eq` expose the encoded values.
+`ofFn_splitBits_fst`, `ofFn_splitBits_snd` read the two halves as the prefix and suffix words.
 
 ## References
 
@@ -37,6 +38,24 @@ def splitBits {a b : ℕ} (w : Fin (a + b) → Bool) : (Fin a → Bool) × (Fin
 
 attribute [simps (config := { isSimp := false }) fst snd] splitBits
 
+/-- The word of the first component of `splitBits w` is the first `a` bits of the word of `w`:
+`List.ofFn (splitBits w).1 = (List.ofFn w).take a`. Framework glue, no textbook counterpart. -/
+protected theorem ofFn_splitBits_fst {a b : ℕ} (w : Fin (a + b) → Bool) :
+    List.ofFn (splitBits w).1 = (List.ofFn w).take a := by
+  have hfst : (splitBits w).1 = fun i : Fin a => w (Fin.castAdd b i) :=
+    funext fun i => splitBits_fst w i
+  rw [hfst, List.ofFn_add (f := w), List.take_left' List.length_ofFn]
+  rfl
+
+/-- The word of the second component of `splitBits w` is the word of `w` after its first `a`
+bits: `List.ofFn (splitBits w).2 = (List.ofFn w).drop a`. Framework glue, no textbook
+counterpart. -/
+protected theorem ofFn_splitBits_snd {a b : ℕ} (w : Fin (a + b) → Bool) :
+    List.ofFn (splitBits w).2 = (List.ofFn w).drop a := by
+  have hsnd : (splitBits w).2 = fun j : Fin b => w (Fin.natAdd a j) :=
+    funext fun j => splitBits_snd w j
+  rw [hsnd, List.ofFn_add (f := w), List.drop_left' List.length_ofFn]
+
 /-- The parameter-tagged input `⟨1^n, w⟩` of a deterministic polynomial-time algorithm. -/
 def atParam (n : ℕ) (w : List Bool) : List Bool := pairEncode (List.replicate n true) w
 
diff --git a/TCSlib/Cryptography/Encryption/PrivateKey/EnsembleSecurity.lean b/TCSlib/Cryptography/Encryption/PrivateKey/EnsembleSecurity.lean
index 38ad023c9..471d15aea 100644
--- a/TCSlib/Cryptography/Encryption/PrivateKey/EnsembleSecurity.lean
+++ b/TCSlib/Cryptography/Encryption/PrivateKey/EnsembleSecurity.lean
@@ -33,6 +33,8 @@ polynomially many ciphertexts are encoded as nested pairs.
 * `PrivateKeyScheme.not_multiMessageSecure_of_deterministic` uses a two-message
   distinguisher to rule out security for stateless deterministic schemes
   [PS10, Theorem 94.2].
+* `PrivateKeyScheme.encodeList_eq_flatMap` writes the tuple encoding as the concatenation of
+  the blocks `⟨c, []⟩`.
 
 ## References
 
@@ -140,6 +142,18 @@ theorem encodeList_cons (m : List Bool) (ms : List (List Bool)) :
 /-- Unfolding of the list encoding on the empty list: `encodeList [] = []`. -/
 theorem encodeList_nil : encodeList [] = [] := rfl
 
+/-- **The tuple encoding is a concatenation of blocks**: the nested-pair encoding of a list of
+words is the concatenation of the self-delimiting blocks `⟨c, []⟩`,
+`encodeList l = l.flatMap fun c => pairEncode c []`.
+Framework glue, no textbook counterpart. -/
+protected theorem encodeList_eq_flatMap (l : List (List Bool)) :
+    encodeList l = l.flatMap fun c => pairEncode c [] := by
+  induction l with
+  | nil => rw [encodeList_nil, List.flatMap_nil]
+  | cons c cs ih =>
+    rw [encodeList_cons, List.flatMap_cons, ih]
+    simp only [pairEncode_eq, List.append_nil, List.append_assoc]
+
 /-- Unfolding of the multi-message ciphertext sampler: the `encodeList` of the `q + 1`
 encryptions `Enc(1^n, ⟨k, m_i⟩; s_i)` under the key `k = Gen(1^n; r.1)`, `s_i = r.2 i`. -/
 theorem multiEncDist_apply (S : PrivateKeyScheme) (n q : ℕ) (m : Fin (q + 1) → Fin n → Bool)
diff --git a/TCSlib/Cryptography/Encryption/PublicKey/Trapdoor.lean b/TCSlib/Cryptography/Encryption/PublicKey/Trapdoor.lean
index 51f7a1e7e..7b54ccf42 100644
--- a/TCSlib/Cryptography/Encryption/PublicKey/Trapdoor.lean
+++ b/TCSlib/Cryptography/Encryption/PublicKey/Trapdoor.lean
@@ -41,6 +41,7 @@ Honest sampling is the field `Collection.sample_spec`.
   security from one-wayness and a hard-core predicate.
 * `TCSlib.Cryptography.TrapdoorCollection.OneWay.exists_glPad_singleBitSecure` supplies
   the predicate and its evaluator through Goldreich–Levin under the width premise `henc`.
+* `TCSlib.Cryptography.pkPredictor_apply` reads the predictor's output on a guessed bit and coins.
 
 ## References
 
@@ -282,6 +283,15 @@ end TrapdoorCollection
 def pkPredictor {α ρ : Type*} (D : α × Bool → ρ → Bool) (flip : Bool) : α → Bool × ρ → Bool :=
   fun y c => xor (if D (y, c.1) c.2 then c.1 else !c.1) flip
 
+/-- **The predictor's output**: on `y` with coins `c = (c₁, c₂)` (the guessed bit and the
+distinguisher's coins), `pkPredictor D flip` outputs `c₁` if `D` accepts `(y, c₁)` with coins `c₂`
+and `¬c₁` otherwise, negated when `flip`,
+`pkPredictor D flip y c = xor (if D (y, c.1) c.2 then c.1 else !c.1) flip`
+[PS10, Theorem 104.4, proof]. -/
+theorem pkPredictor_apply {α ρ : Type*} (D : α × Bool → ρ → Bool) (flip : Bool) (y : α)
+    (c : Bool × ρ) : pkPredictor D flip y c = xor (if D (y, c.1) c.2 then c.1 else !c.1) flip :=
+  rfl
+
 /-- The predictor is `owpPredictor` on `α × Unit`. -/
 private theorem predProb_pkPredictor_eq {α ρ : Type*} [Fintype α] [Fintype ρ] (f : α ≃ α)
     (B : α → Bool) (D : α × Bool → ρ → Bool) (flip : Bool) :
diff --git a/TCSlib/Cryptography/Foundations/BitLists.lean b/TCSlib/Cryptography/Foundations/BitLists.lean
index 758ca630c..19da91091 100644
--- a/TCSlib/Cryptography/Foundations/BitLists.lean
+++ b/TCSlib/Cryptography/Foundations/BitLists.lean
@@ -22,6 +22,7 @@ an association list. They depend on Mathlib only.
 ## Main definitions
 
 * `TCSlib.Cryptography.xorPerm v`: exclusive-or with the vector `v`, as a permutation.
+* `TCSlib.Cryptography.recordBits w o`: the `(w + 1)`-bit record of an optional `w`-bit vector.
 
 ## Main results
 
@@ -39,6 +40,9 @@ an association list. They depend on Mathlib only.
 * `TCSlib.Cryptography.length_flatten_map_const`, `length_flatten_map_range`: the length of a
   concatenation of equal-length blocks.
 * `TCSlib.Cryptography.flatMap_range_drop`: reading the successive suffixes of a list.
+* `TCSlib.Cryptography.getD_ofFn`, `zipWith_xor_cancel_right`, `recordBits_none`,
+  `recordBits_some`, `length_recordBits`: in-range entries of a tuple's list, `(m ⊕ p) ⊕ p = m`, and
+  the readers of the record of an optional bit vector.
 
 ## References
 
@@ -63,6 +67,14 @@ theorem headD_drop_ofFn {α : Type*} {n : ℕ} (f : Fin n → α) (i : Fin n) (d
   simp only [headD_drop, List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos i.isLt,
     Option.getD_some]
 
+/-- The entry of a tuple's list at an in-range index is the tuple's entry there: for
+`f : Fin n → α`, `i < n` and any default `d`, `(List.ofFn f).getD i d = f ⟨i, hi⟩`.
+Framework glue, no textbook counterpart (`headD_drop_ofFn` read through `headD_drop`). -/
+theorem getD_ofFn {α : Type*} {n : ℕ} (f : Fin n → α) {i : ℕ} (hi : i < n) (d : α) :
+    (List.ofFn f).getD i d = f ⟨i, hi⟩ := by
+  rw [← headD_drop]
+  exact headD_drop_ofFn f ⟨i, hi⟩ d
+
 /-- **Flattening one-element blocks:** concatenating the one-bit blocks `g j` gives their bits,
 `(List.ofFn fun j => List.ofFn (g j)).flatten = List.ofFn fun j => g j 0` when the blocks have
 length `l = 1`.
@@ -97,6 +109,19 @@ theorem zipWith_xor_cancel_left {a c : List Bool} (h : a.length = c.length) :
     simp only [List.getElem_zipWith]
     cases a[i] <;> cases c[i] <;> rfl
 
+/-- Exclusive-or with the same pad twice cancels on the right: `(m ⊕ p) ⊕ p = m` for every
+message `m` and every pad `p` at least as long, `|m| ≤ |p|` (`List.zipWith` stops at the shorter
+list). Framework glue, no textbook counterpart (the decryption step of the one-time-pad style
+encryptions). -/
+theorem zipWith_xor_cancel_right : ∀ (m p : List Bool), m.length ≤ p.length →
+    List.zipWith xor (List.zipWith xor m p) p = m
+  | [], _, _ => rfl
+  | _ :: _, [], h => absurd h (by rw [List.length_cons, List.length_nil]; omega)
+  | a :: m, b :: p, h => by
+    rw [List.zipWith_cons_cons, List.zipWith_cons_cons,
+      zipWith_xor_cancel_right m p (by rw [List.length_cons, List.length_cons] at h; omega)]
+    cases a <;> cases b <;> rfl
+
 section XorPerm
 
 variable {n : ℕ}
@@ -189,4 +214,31 @@ theorem flatMap_range_drop {β γ : Type*} (F : List β → List γ) (g : β →
     exact ih (fun e' he' => hcons e' (List.mem_cons_of_mem _ he')) m'
       (by rw [List.length_cons] at hm; omega)
 
+/-! ### Records of an optional bit vector -/
+
+/-- The record of an optional `w`-bit vector, a word of `w + 1` bits: a flag bit followed by the
+vector, `recordBits w (some c) = 1 :: ⟦c⟧`, or all zeros when there is none,
+`recordBits w none = 0 :: 0^w`. Framework glue, no textbook counterpart (the challenge record of
+the encrypt-then-tag and PRF-oracle handlers). -/
+def recordBits (w : ℕ) : Option (Fin w → Bool) → List Bool
+  | none => false :: List.replicate w false
+  | some c => true :: List.ofFn c
+
+/-- The record of no vector is the zero word: `recordBits w none = 0 :: 0^w`.
+Framework glue, no textbook counterpart. -/
+theorem recordBits_none (w : ℕ) : recordBits w none = false :: List.replicate w false := rfl
+
+/-- The record of a vector is the flag `1` followed by the vector:
+`recordBits w (some c) = 1 :: ⟦c⟧`. Framework glue, no textbook counterpart. -/
+theorem recordBits_some (w : ℕ) (c : Fin w → Bool) : recordBits w (some c) = true :: List.ofFn c :=
+  rfl
+
+/-- Every record has `w + 1` bits: `|recordBits w o| = w + 1`.
+Framework glue, no textbook counterpart. -/
+theorem length_recordBits (w : ℕ) (o : Option (Fin w → Bool)) :
+    (recordBits w o).length = w + 1 := by
+  cases o with
+  | none => rw [recordBits_none, List.length_cons, List.length_replicate]
+  | some c => rw [recordBits_some, List.length_cons, List.length_ofFn]
+
 end TCSlib.Cryptography
diff --git a/TCSlib/Cryptography/Games.lean b/TCSlib/Cryptography/Games.lean
index fb3115e91..1c987715a 100644
--- a/TCSlib/Cryptography/Games.lean
+++ b/TCSlib/Cryptography/Games.lean
@@ -9,6 +9,7 @@ import TCSlib.Cryptography.Games.Advantage
 import TCSlib.Cryptography.Games.Hopping
 import TCSlib.Cryptography.Games.Protocols
 import TCSlib.Cryptography.Games.Forwarding
+import TCSlib.Cryptography.Games.Tapes
 
 set_option maxHeartbeats 0
 set_option relaxedAutoImplicit false
@@ -45,6 +46,8 @@ the interaction model `Strategy`.
   messages and coin draws.
 * `TCSlib.Cryptography.Games.Forwarding`: the forwarding handler, the call lemmas of interactive
   handlers read on lists, and hard-wiring a second input component (S2b layer).
+* `TCSlib.Cryptography.Games.Tapes`: simulation through a state abstraction in law, coins drawn in
+  advance on tapes, and functions overridden by a table.
 
 ## References
 
diff --git a/TCSlib/Cryptography/Games/Bridges/Experiments.lean b/TCSlib/Cryptography/Games/Bridges/Experiments.lean
index 5346a5a4b..bd3da1d60 100644
--- a/TCSlib/Cryptography/Games/Bridges/Experiments.lean
+++ b/TCSlib/Cryptography/Games/Bridges/Experiments.lean
@@ -34,6 +34,7 @@ The four experiments are read through their published defining equations (`invPr
 ## Main results
 
 * `Games.Bridge.prob_sample_eq_uprob`: `Pr[x ← $ α : p x] = uprob p`.
+* `Games.Bridge.expect_sample_eq_uexp`: `𝔼[x ← $ α : f x] = uexp f`.
 * `Games.Bridge.prob_sample_pair`: sampling `α` then `β` is sampling `α × β`.
 * `Games.Bridge.invProb_eq`, `predProb_eq`, `acceptProb_eq`, `distAdv_eq`: the four concrete
   experiments as games.
@@ -67,6 +68,13 @@ theorem prob_sample_eq_uprob [Fintype α] [Nonempty α] (p : α → Prop) :
   classical
   rw [prob_eq_expect, expect_sample, uprob_eq_card_filter, sum_boole, inv_mul_eq_div]
 
+/-- **Sampling and `uexp` agree:** the expectation of `f` over a uniform sample of the nonempty
+finite type `α` is the uniform average, `expect (sample α) f = uexp f`; the expectation form of
+`prob_sample_eq_uprob`. Framework glue, no textbook counterpart. -/
+protected theorem expect_sample_eq_uexp {α : Type} [Fintype α] [Nonempty α] (f : α → ℝ) :
+    expect (sample α) f = uexp f := by
+  rw [expect_sample, uexp_def, inv_mul_eq_div]
+
 /-- **Sampling a pair in sequence is sampling the product:** for every function `g` on pairs,
 its expectation over `a ← $ α; b ← $ β; (a, b)` equals its expectation over a uniform pair. -/
 theorem expect_sample_pair [Fintype α] [Nonempty α] [Fintype β] [Nonempty β] (g : α × β → ℝ) :
diff --git a/TCSlib/Cryptography/Games/Efficiency/Strings.lean b/TCSlib/Cryptography/Games/Efficiency/Strings.lean
index 0aa4831f4..a35c0a329 100644
--- a/TCSlib/Cryptography/Games/Efficiency/Strings.lean
+++ b/TCSlib/Cryptography/Games/Efficiency/Strings.lean
@@ -38,6 +38,7 @@ on strings. This file collects the string-level pieces they share (route note
 ## Main results
 
 * `EffFill.encodeLog_append_single`, `EffFill.ofFn_getD_decodeFin`.
+* `EffFill.length_le_length_encodeLog`: an encoded log has at least as many bits as entries.
 * `EffFill.canonWord_eq`: the canonical decoder is `encodeBitMove ∘ decodeBitMove`.
 * `EffFill.canonFun_poly`, `EffFill.fixLen_poly`, `EffFill.selLen_poly`, `EffFill.actLoop_poly`.
 * `EffFill.runsTo_stop`: a run that stops evaluates the loop.
@@ -81,6 +82,16 @@ theorem length_encodeLog_le {ι α : Type} {spec : OracleSpec ι} (codec : Machi
     have h2 := length_encodeLog_le codec E h fun e' he' => hE e' (List.mem_cons_of_mem e he')
     omega
 
+/-- **An encoded log has at least as many bits as entries:**
+`h.length ≤ (codec.encodeLog h).length`. Framework glue, no textbook counterpart. -/
+protected theorem length_le_length_encodeLog {ι α : Type} {spec : OracleSpec ι}
+    (codec : MachineCodec spec α) (h : QueryLog spec) : h.length ≤ (codec.encodeLog h).length := by
+  induction h with
+  | nil => rw [MachineCodec.encodeLog_nil, List.length_nil, List.length_nil]
+  | cons e h ih =>
+    rw [MachineCodec.encodeLog_cons, length_pairEncode, List.length_cons]
+    omega
+
 /-- The encoding of a log ends with the encoding of each of its suffixes, so it is at least as
 long: `|codec.encodeLog O| ≤ |codec.encodeLog (P ++ O)|`. -/
 theorem length_encodeLog_le_append {ι α : Type} {spec : OracleSpec ι} (codec : MachineCodec spec α)
diff --git a/TCSlib/Cryptography/Games/Machines.lean b/TCSlib/Cryptography/Games/Machines.lean
index d738c0ed6..529f17b45 100644
--- a/TCSlib/Cryptography/Games/Machines.lean
+++ b/TCSlib/Cryptography/Games/Machines.lean
@@ -42,6 +42,7 @@ result, stated in a later module.
 
 * `Games.buildComp_costBoundedBy`, `NUPPT.toComp_costBoundedBy`: the computation makes at most `q`
   queries.
+* `Games.OracleComp.exists_eq_pure_of_costBoundedBy_zero`: a computation of cost zero is a return.
 * `Games.buildComp_of_ret`: a final output is the computation at every budget.
 * `Games.buildComp_budget_eq`, `NUPPT.toCompOn_budget_eq`: a computation at budget `K ≥ j` that
   makes at most `j` queries is the computation at budget `j`.
@@ -175,6 +176,17 @@ theorem buildComp_costBoundedBy {spec : OracleSpec ι} (next : QueryLog spec →
       exact (OracleComp.costBoundedBy_query _ _ _ _ _).2
         ⟨Nat.le_add_left 1 q, fun y => buildComp_costBoundedBy next timeout q _⟩
 
+/-- **A computation of cost zero is a return:** if every query costs one and the budget is
+zero, `c.CostBoundedBy (fun _ => 1) 0 → ∃ a, c = pure a` (a query would need `1 ≤ 0`).
+Framework glue, no textbook counterpart. -/
+theorem OracleComp.exists_eq_pure_of_costBoundedBy_zero {ι α : Type} {spec : OracleSpec ι}
+    (c : OracleComp spec α) (h : c.CostBoundedBy (fun _ => 1) 0) : ∃ a, c = .pure a := by
+  cases c with
+  | pure a => exact ⟨a, rfl⟩
+  | query i x k =>
+    have hq := (OracleComp.costBoundedBy_query (fun _ => 1) i x k 0).1 h
+    omega
+
 /-- **Budget reduction for `buildComp`.** If the computation of `next` at budget `K` from the log
 `hist` makes at most `j ≤ K` queries on every path, it is the computation at budget `j`:
 `buildComp next t j hist = buildComp next t K hist`.
diff --git a/TCSlib/Cryptography/Games/Tapes.lean b/TCSlib/Cryptography/Games/Tapes.lean
new file mode 100644
index 000000000..895f59a88
--- /dev/null
+++ b/TCSlib/Cryptography/Games/Tapes.lean
@@ -0,0 +1,346 @@
+/-
+Copyright (c) 2026 TCSlib contributors. All rights reserved.
+Released under Apache 2.0 license as described in the file LICENSE.
+-/
+import TCSlib.Cryptography.Games.Hopping
+
+set_option maxHeartbeats 0
+set_option relaxedAutoImplicit false
+set_option autoImplicit false
+
+/-!
+# Simulation in law, coins in advance, and functions overridden by a table
+
+Generic facts on simulations of oracle computations, stated for arbitrary oracle specifications.
+They are the `Games` forms of the tools first proved for the encrypt-then-tag proof of
+[PS10, Theorem 170.4] (`Composability.ETTGame`, `EncryptThenTag/Tools.lean`), with the tape
+extension of `AdaptiveCPA.extTape` restated here.
+
+* **Simulation through a state abstraction, in law** (`Games.expect_simulate_abs`): if every
+  call of `impl₁` from the abstract image `f s` has the law of the call of `impl₂` from `s` with
+  its new state abstracted, so do whole simulations, along runs within a query budget.
+* **Coins in advance** (`Games.expect_simulate_tapeImpl`): an implementation that draws one fresh
+  coin `t` per query (`Games.freshImpl`) has the law of the implementation that reads the `j`-th
+  query's coin from a tape `T j` drawn in advance (`Games.tapeImpl`, `Games.extTape`), for
+  computations with at most `κ` queries.
+* **Functions overridden by a table** (`Games.ovr`): `ovr M R` is `R` with the values of the
+  table `M` written over it; resampling `R` at a point outside the table moves into the table
+  (`Games.expect_sample_ovr`).
+
+## Main definitions
+
+* `Games.freshImpl`, `Games.tapeImpl`: per-query coins drawn fresh, and read from tapes.
+* `Games.extTape`: a finite family of coins extended to every index.
+* `Games.ovr`: a function overridden by a finite table.
+
+## Main results
+
+* `Games.expect_simulate_abs`, `Games.expect_simulate_abs_inv`: simulation in law through a state
+  abstraction.
+* `Games.simulate_tapeImpl_congr`, `Games.expect_simulate_tapeImpl`: coins in advance.
+* `Games.extTape_of_lt`, `Games.extTape_of_not_lt`, `Games.extTape_update`: the tape extension.
+* `Games.ovr_nil`, `Games.ovr_cons`, `Games.ovr_of_not_mem`, `Games.ovr_of_mem`,
+  `Games.ovr_update`, `Games.ovr_append`, `Games.expect_sample_ovr`: tables over functions.
+
+## References
+
+* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
+  Theorem 170.4 (book p. 170): the first consumer.
+-/
+
+namespace TCSlib.Cryptography.Games
+
+open ProbComp
+
+/-! ### Simulation through a state abstraction, in law -/
+
+section Abs
+
+variable {ι : Type} {spec : OracleSpec ι} {σ₁ σ₂ α : Type}
+
+/-- **Simulation through a state abstraction, in law, along runs with a query budget.** Let every
+call of `impl₂` from a state `s` with `cnt s < κ` raise `cnt` by at most one, and give every
+function `g` of the answer and the abstracted new state the expectation that the call of `impl₁`
+from `f s` gives it. Then for a computation `c` with at most `m` queries and `cnt s + m ≤ κ`,
+`𝔼[G] (simulate impl₁ c (f s)) = 𝔼[fun p => G (p.1, f p.2)] (simulate impl₂ c s)`.
+Framework glue, no textbook counterpart.
+
+**Proof sketch.** Induction on `c`. A query costs one unit, so it is asked from a state with
+`cnt s < κ`: rewrite the call of `impl₁` by the hypothesis, and on each possible outcome of the
+call of `impl₂` (where `cnt` grew by at most one) apply the induction hypothesis
+(`expect_congr_of_allOutputs`). -/
+protected theorem expect_simulate_abs (impl₁ : QueryImpl spec σ₁ unifSpec)
+    (impl₂ : QueryImpl spec σ₂ unifSpec) (f : σ₂ → σ₁) (cnt : σ₂ → ℕ) (κ : ℕ)
+    (h : ∀ i x s, cnt s < κ → ∀ g : spec.rng i × σ₁ → ℝ,
+      expect (impl₁ i x (f s)) g = expect (impl₂ i x s) fun p => g (p.1, f p.2))
+    (hcnt : ∀ i x s, cnt s < κ → (impl₂ i x s).AllOutputs fun p => cnt p.2 ≤ cnt s + 1)
+    (c : OracleComp spec α) (m : ℕ) (hc : c.CostBoundedBy (fun _ => 1) m) (s : σ₂)
+    (hs : cnt s + m ≤ κ) (G : α × σ₁ → ℝ) :
+    expect (simulate impl₁ c (f s)) G = expect (simulate impl₂ c s) fun p => G (p.1, f p.2) := by
+  induction c generalizing m s with
+  | pure a => rw [simulate_pure, simulate_pure, expect_pure, expect_pure]
+  | query i x k ih =>
+    obtain ⟨hm, hk⟩ := (OracleComp.costBoundedBy_query _ _ _ _ _).1 hc
+    have hm1 : 1 ≤ m := hm
+    rw [simulate_query, simulate_query, expect_bind, expect_bind, h i x s (by omega)]
+    refine expect_congr_of_allOutputs (hcnt i x s (by omega)) fun p _ => ?_
+    exact ih p.1 (m - 1) (hk p.1) p.2 (by omega)
+
+/-- **Simulation through a state abstraction, in law, along runs with a query budget and an
+invariant:** as `Games.expect_simulate_abs`, with the hypotheses only on the states satisfying
+an invariant `P` that every call of `impl₂` keeps: for `c` with at most `m` queries, `P s` and
+`cnt s + m ≤ κ`, `𝔼[G | simulate impl₁ c (f s)] = 𝔼[fun p => G (p.1, f p.2) | simulate impl₂ c s]`.
+Framework glue, no textbook counterpart.
+
+**Proof sketch.** As `Games.expect_simulate_abs`, carrying `P` through the possible outcomes. -/
+protected theorem expect_simulate_abs_inv (impl₁ : QueryImpl spec σ₁ unifSpec)
+    (impl₂ : QueryImpl spec σ₂ unifSpec) (f : σ₂ → σ₁) (P : σ₂ → Prop) (cnt : σ₂ → ℕ) (κ : ℕ)
+    (h : ∀ i x s, P s → cnt s < κ → ∀ g : spec.rng i × σ₁ → ℝ,
+      expect (impl₁ i x (f s)) g = expect (impl₂ i x s) fun p => g (p.1, f p.2))
+    (hcnt : ∀ i x s, P s → cnt s < κ →
+      (impl₂ i x s).AllOutputs fun p => P p.2 ∧ cnt p.2 ≤ cnt s + 1)
+    (c : OracleComp spec α) (m : ℕ) (hc : c.CostBoundedBy (fun _ => 1) m) (s : σ₂) (hP : P s)
+    (hs : cnt s + m ≤ κ) (G : α × σ₁ → ℝ) :
+    expect (simulate impl₁ c (f s)) G = expect (simulate impl₂ c s) fun p => G (p.1, f p.2) := by
+  induction c generalizing m s with
+  | pure a => rw [simulate_pure, simulate_pure, expect_pure, expect_pure]
+  | query i x k ih =>
+    obtain ⟨hm, hk⟩ := (OracleComp.costBoundedBy_query _ _ _ _ _).1 hc
+    have hm1 : 1 ≤ m := hm
+    rw [simulate_query, simulate_query, expect_bind, expect_bind, h i x s hP (by omega)]
+    refine expect_congr_of_allOutputs (hcnt i x s hP (by omega)) fun p hp => ?_
+    exact ih p.1 (m - 1) (hk p.1) p.2 hp.1 (by omega)
+
+end Abs
+
+/-! ### Coins drawn fresh and coins in advance -/
+
+section Tapes
+
+variable {ι : Type} {spec : OracleSpec ι} {σ τ α : Type}
+
+/-- **One fresh coin per query:** the query `x` to oracle `i` in state `s` draws a uniform
+`t ∈ τ`, then runs `K i x s t`: `freshImpl K i x s = (sample τ).bind (K i x s)`.
+Framework glue, no textbook counterpart. -/
+protected noncomputable def freshImpl [Fintype τ] [Nonempty τ]
+    (K : ∀ i, spec.dom i → σ → τ → ProbComp (spec.rng i × σ)) : QueryImpl spec σ unifSpec :=
+  fun i x s => (sample τ).bind (K i x s)
+
+/-- The reader of `Games.freshImpl`: `freshImpl K i x s = (sample τ).bind (K i x s)`.
+Framework glue, no textbook counterpart. -/
+protected theorem freshImpl_apply [Fintype τ] [Nonempty τ]
+    (K : ∀ i, spec.dom i → σ → τ → ProbComp (spec.rng i × σ)) (i : ι) (x : spec.dom i) (s : σ) :
+    Games.freshImpl K i x s = (sample τ).bind (K i x s) :=
+  rfl
+
+/-- **A family of `κ` coins, extended to every index** by an arbitrary value:
+`extTape T m = T ⟨m, hm⟩` for `hm : m < κ`, and `Classical.arbitrary C` otherwise.
+Framework glue, no textbook counterpart. -/
+protected noncomputable def extTape {C : Type} [Nonempty C] {κ : ℕ} (T : Fin κ → C) (m : ℕ) : C :=
+  if hm : m < κ then T ⟨m, hm⟩ else Classical.arbitrary C
+
+/-- Below `κ` the extended family is the family: `m < κ → extTape T m = T ⟨m, hm⟩`.
+Framework glue, no textbook counterpart. -/
+protected theorem extTape_of_lt {C : Type} [Nonempty C] {κ : ℕ} (T : Fin κ → C) {m : ℕ}
+    (hm : m < κ) : Games.extTape T m = T ⟨m, hm⟩ := by
+  rw [Games.extTape, dif_pos hm]
+
+/-- From `κ` on the extended family is the arbitrary value:
+`¬ m < κ → extTape T m = Classical.arbitrary C`. Framework glue, no textbook counterpart. -/
+protected theorem extTape_of_not_lt {C : Type} [Nonempty C] {κ : ℕ} (T : Fin κ → C) {m : ℕ}
+    (hm : ¬ m < κ) : Games.extTape T m = Classical.arbitrary C := by
+  rw [Games.extTape, dif_neg hm]
+
+/-- Changing one coordinate `j` of `T` changes its extension only at `j`:
+`m ≠ j → extTape (update T j r) m = extTape T m`. Framework glue, no textbook counterpart. -/
+protected theorem extTape_update {C : Type} [Nonempty C] {κ : ℕ} (T : Fin κ → C) (j : Fin κ)
+    (r : C) {m : ℕ} (hm : m ≠ j) : Games.extTape (Function.update T j r) m = Games.extTape T m := by
+  by_cases h : m < κ
+  · rw [Games.extTape_of_lt _ h, Games.extTape_of_lt _ h, Function.update_of_ne]
+    exact fun h' => hm (congrArg Fin.val h')
+  · rw [Games.extTape_of_not_lt _ h, Games.extTape_of_not_lt _ h]
+
+/-- **One coin per query, from tapes in advance:** the query `x` to oracle `i` in state `(s, j)`
+runs `K i x s (T j)` and advances the query counter `j`,
+`tapeImpl K T i x (s, j) = (K i x s (T j)).bind fun p => pure (p.1, (p.2, j + 1))`.
+Framework glue, no textbook counterpart. -/
+protected def tapeImpl (K : ∀ i, spec.dom i → σ → τ → ProbComp (spec.rng i × σ)) (T : ℕ → τ) :
+    QueryImpl spec (σ × ℕ) unifSpec :=
+  fun i x s => (K i x s.1 (T s.2)).bind fun p => .pure (p.1, (p.2, s.2 + 1))
+
+/-- The reader of `Games.tapeImpl`:
+`tapeImpl K T i x (s, j) = (K i x s (T j)).bind fun p => pure (p.1, (p.2, j + 1))`.
+Framework glue, no textbook counterpart. -/
+protected theorem tapeImpl_apply (K : ∀ i, spec.dom i → σ → τ → ProbComp (spec.rng i × σ))
+    (T : ℕ → τ) (i : ι) (x : spec.dom i) (s : σ) (j : ℕ) :
+    Games.tapeImpl K T i x (s, j) = (K i x s (T j)).bind fun p => .pure (p.1, (p.2, j + 1)) :=
+  rfl
+
+/-- **The run from the counter `j` ignores the tapes below `j`:** if `T m = T' m` for every
+`m ≥ j`, then `simulate (tapeImpl K T) c (s, j) = simulate (tapeImpl K T') c (s, j)`.
+Framework glue, no textbook counterpart.
+
+**Proof sketch.** Induction on the computation: a query at counter `j' ≥ j` reads `T j'` and
+moves to `j' + 1`. -/
+protected theorem simulate_tapeImpl_congr
+    (K : ∀ i, spec.dom i → σ → τ → ProbComp (spec.rng i × σ))
+    (T T' : ℕ → τ) (c : OracleComp spec α) (s : σ) (j : ℕ) (hT : ∀ m, j ≤ m → T m = T' m) :
+    simulate (Games.tapeImpl K T) c (s, j) = simulate (Games.tapeImpl K T') c (s, j) := by
+  induction c generalizing s j with
+  | pure a => rw [simulate_pure, simulate_pure]
+  | query i x k ih =>
+    rw [simulate_query, simulate_query, Games.tapeImpl_apply, Games.tapeImpl_apply,
+      hT j le_rfl, OracleComp.bind_assoc, OracleComp.bind_assoc]
+    congr 1
+    funext p
+    rw [OracleComp.pure_bind, OracleComp.pure_bind]
+    exact ih p.1 p.2 (j + 1) fun m hm => hT m (by omega)
+
+/-- **Coins in advance have the law of fresh coins:** for a computation with at most `m`
+queries, a counter `j` with `j + m ≤ κ`, and every function `G` of the output,
+`𝔼_{T ← τ^κ} 𝔼[G (simulate (tapeImpl K (extTape T)) c (s, j))] = 𝔼[G (simulate (freshImpl K) c s)]`.
+Framework glue, no textbook counterpart.
+
+**Proof sketch.** Induction on `c`, generalizing the counter, the state and the budget. A query
+costs one unit, so it reads the tape `T j` with `j < κ`; the continuation runs from `j + 1`, so
+it ignores `T j` (`Games.simulate_tapeImpl_congr`, `Games.extTape_update`), and
+`ProbComp.expect_sample_coord` replaces `T j` by the fresh coin of `freshImpl`
+(`expect_expect_sample` exchanges the tape with the call). -/
+protected theorem expect_simulate_tapeImpl [Fintype τ] [Nonempty τ]
+    (K : ∀ i, spec.dom i → σ → τ → ProbComp (spec.rng i × σ))
+    (κ : ℕ) (G : α → ℝ) (c : OracleComp spec α) (m : ℕ) (hc : c.CostBoundedBy (fun _ => 1) m)
+    (s : σ) (j : ℕ) (hj : j + m ≤ κ) :
+    expect (sample (Fin κ → τ))
+        (fun T => expect (simulate (Games.tapeImpl K (Games.extTape T)) c (s, j)) fun p => G p.1) =
+      expect (simulate (Games.freshImpl K) c s) fun p => G p.1 := by
+  induction c generalizing m s j with
+  | pure a =>
+    simp only [simulate_pure, expect_pure]
+    exact expect_const _ _
+  | query i x k ih =>
+    obtain ⟨hm, hk⟩ := (OracleComp.costBoundedBy_query _ _ _ _ _).1 hc
+    have hm1 : 1 ≤ m := hm
+    have hjk : j < κ := by omega
+    let jj : Fin κ := ⟨j, hjk⟩
+    have hT : ∀ T : Fin κ → τ, Games.extTape T j = T jj :=
+      fun T => Games.extTape_of_lt T hjk
+    simp only [simulate_query, Games.tapeImpl_apply, Games.freshImpl_apply, OracleComp.bind_assoc,
+      OracleComp.pure_bind, expect_bind, hT]
+    refine (expect_sample_coord jj (fun t T => expect (K i x s t) fun p =>
+      expect (simulate (Games.tapeImpl K (Games.extTape T)) (k p.1) (p.2, j + 1))
+        fun q => G q.1) ?_).trans ?_
+    · intro t t' T
+      refine congrArg _ (funext fun p => ?_)
+      refine congrArg (fun c => expect c fun q => G q.1)
+        (Games.simulate_tapeImpl_congr K _ _ _ _ _ fun m' hm' => ?_)
+      exact Games.extTape_update T jj t' (by
+        intro h
+        have : m' = j := h
+        omega)
+    · refine congrArg _ (funext fun t => ?_)
+      rw [← expect_expect_sample]
+      refine congrArg _ (funext fun p => ?_)
+      exact ih p.1 (m - 1) (hk p.1) p.2 (j + 1) (by omega)
+
+end Tapes
+
+/-! ### Functions overridden by a table -/
+
+section Override
+
+variable {κ β : Type} [DecidableEq κ]
+
+/-- **A function overridden by a table:** `ovr M R` is `R` with the entries `(p, y)` of `M`
+written over it, the first entry of a key winning: `ovr [] R = R`,
+`ovr ((p, y) :: M) R = update (ovr M R) p y`. Framework glue, no textbook counterpart. -/
+protected def ovr : List (κ × β) → (κ → β) → κ → β
+  | [], R => R
+  | e :: M, R => Function.update (Games.ovr M R) e.1 e.2
+
+/-- The reader of `Games.ovr` on the empty table: `ovr [] R = R`.
+Framework glue, no textbook counterpart. -/
+protected theorem ovr_nil (R : κ → β) : Games.ovr ([] : List (κ × β)) R = R :=
+  rfl
+
+/-- The reader of `Games.ovr` on a nonempty table: `ovr ((p, y) :: M) R = update (ovr M R) p y`.
+Framework glue, no textbook counterpart. -/
+protected theorem ovr_cons (p : κ) (y : β) (M : List (κ × β)) (R : κ → β) :
+    Games.ovr ((p, y) :: M) R = Function.update (Games.ovr M R) p y :=
+  rfl
+
+/-- Outside the keys of the table, the overridden function is `R`:
+`p ∉ M.map Prod.fst → ovr M R p = R p`. Framework glue, no textbook counterpart. -/
+protected theorem ovr_of_not_mem {M : List (κ × β)} {p : κ} (hp : p ∉ M.map Prod.fst)
+    (R : κ → β) : Games.ovr M R p = R p := by
+  induction M with
+  | nil => rw [Games.ovr_nil]
+  | cons e M ih =>
+    obtain ⟨q, y⟩ := e
+    rw [List.map_cons, List.mem_cons, not_or] at hp
+    rw [Games.ovr_cons, Function.update_of_ne hp.1]
+    exact ih hp.2
+
+/-- On the keys of the table, the overridden function does not read `R`:
+`p ∈ M.map Prod.fst → ovr M R p = ovr M R' p`. Framework glue, no textbook counterpart. -/
+protected theorem ovr_of_mem {M : List (κ × β)} {p : κ} (hp : p ∈ M.map Prod.fst)
+    (R R' : κ → β) : Games.ovr M R p = Games.ovr M R' p := by
+  induction M with
+  | nil => rw [List.map_nil] at hp; exact absurd hp List.not_mem_nil
+  | cons e M ih =>
+    obtain ⟨q, y⟩ := e
+    rw [Games.ovr_cons, Games.ovr_cons]
+    by_cases hpq : p = q
+    · subst hpq
+      rw [Function.update_self, Function.update_self]
+    · rw [Function.update_of_ne hpq, Function.update_of_ne hpq]
+      rw [List.map_cons, List.mem_cons] at hp
+      exact ih (hp.resolve_left hpq)
+
+/-- Changing `R` at a point outside the table changes the overridden function there only:
+`p ∉ M.map Prod.fst → ovr M (update R p y) = update (ovr M R) p y`.
+Framework glue, no textbook counterpart. -/
+protected theorem ovr_update {M : List (κ × β)} {p : κ} (hp : p ∉ M.map Prod.fst) (R : κ → β)
+    (y : β) : Games.ovr M (Function.update R p y) = Function.update (Games.ovr M R) p y := by
+  induction M with
+  | nil => rw [Games.ovr_nil, Games.ovr_nil]
+  | cons e M ih =>
+    obtain ⟨q, z⟩ := e
+    rw [List.map_cons, List.mem_cons, not_or] at hp
+    rw [Games.ovr_cons, Games.ovr_cons, ih hp.2]
+    exact Function.update_comm hp.1 _ _ _
+
+/-- Writing a concatenation is writing its parts: `ovr (A ++ B) R = ovr A (ovr B R)`.
+Framework glue, no textbook counterpart. -/
+protected theorem ovr_append (A B : List (κ × β)) (R : κ → β) :
+    Games.ovr (A ++ B) R = Games.ovr A (Games.ovr B R) := by
+  induction A with
+  | nil => rw [List.nil_append, Games.ovr_nil]
+  | cons e A ih =>
+    obtain ⟨p, y⟩ := e
+    rw [List.cons_append, Games.ovr_cons, Games.ovr_cons, ih]
+
+/-- **Resampling a point outside the table moves it into the table:** for `p` not a key of `M`,
+`𝔼_R F (R p) (ovr M R) = 𝔼_y 𝔼_R F y (ovr ((p, y) :: M) R)`.
+Framework glue, no textbook counterpart.
+
+**Proof sketch.** `ProbComp.expect_sample_coord` at the coordinate `p` with
+`F' y R = F y (ovr ((p, y) :: M) R)`, which does not read `R p` (`Games.ovr_update`,
+`Function.update_idem`); at `y = R p` the new entry repeats `ovr M R p = R p`
+(`Games.ovr_of_not_mem`, `Function.update_eq_self`). -/
+protected theorem expect_sample_ovr [Fintype κ] [Fintype β] [Nonempty β] (M : List (κ × β))
+    {p : κ} (hp : p ∉ M.map Prod.fst) (F : β → (κ → β) → ℝ) :
+    expect (sample (κ → β)) (fun R => F (R p) (Games.ovr M R)) =
+      expect (sample β) fun y =>
+        expect (sample (κ → β)) fun R => F y (Games.ovr ((p, y) :: M) R) := by
+  have h := expect_sample_coord p (fun y R => F y (Games.ovr ((p, y) :: M) R)) fun y y' R => by
+    show F y (Games.ovr ((p, y) :: M) (Function.update R p y')) =
+      F y (Games.ovr ((p, y) :: M) R)
+    rw [Games.ovr_cons, Games.ovr_cons, Games.ovr_update hp, Function.update_idem]
+  refine Eq.trans ?_ h
+  refine congrArg _ (funext fun R => ?_)
+  show F (R p) (Games.ovr M R) = F (R p) (Games.ovr ((p, R p) :: M) R)
+  rw [Games.ovr_cons, ← Games.ovr_of_not_mem hp R, Function.update_eq_self]
+
+end Override
+
+end TCSlib.Cryptography.Games
diff --git a/TCSlib/Cryptography/Pseudorandom/Functions/Asymptotic/Defs.lean b/TCSlib/Cryptography/Pseudorandom/Functions/Asymptotic/Defs.lean
index 5a6bd3120..826ad37fd 100644
--- a/TCSlib/Cryptography/Pseudorandom/Functions/Asymptotic/Defs.lean
+++ b/TCSlib/Cryptography/Pseudorandom/Functions/Asymptotic/Defs.lean
@@ -40,6 +40,7 @@ also gives verdict `false` (foundation decision D7 of `PassShelatChapter2-4Plan.
 * `TCSlib.Cryptography.acceptProb_random_eq_lazy` equates the two descriptions of a
   random function, by its table and by lazy sampling [PS10, §3.8.1].
 * `Complexity.NUPPT.toOracleAdversary_boundedBy` gives the query bound.
+* `Complexity.NUPPT.eval_toOracleAdversary_padFin`: an oracle adversary read at equal widths.
 * `TCSlib.Cryptography.OracleEnsemble.indist_iff` expresses the contract through
   negligible advantage. `TCSlib.Cryptography.oracle_hybrid_lemma` gives the
   finite hybrid bound for oracle ensembles.
@@ -338,6 +339,26 @@ theorem _root_.Complexity.NUPPT.toOracleAdversary_boundedBy (D : NUPPT) (n ℓ
     rw [NUPPT.toOracleAdversary_eq]
     exact buildTree_boundedBy _ q []
 
+/-- **An oracle adversary read at equal widths:** for `a' = a` and `b' = b`, running
+`D.toOracleAdversary n a b q c` against `f` is running `D.toOracleAdversary n a' b' q c` against
+`f` with its inputs and outputs read at the widths `a'`, `b'`:
+`(D^{a,b} c).eval f = (D^{a',b'} c).eval (fun x => padFin b' ⟦f (padFin a ⟦x⟧)⟧)`, where `⟦·⟧` is
+`List.ofFn`. Framework glue, no textbook counterpart.
+
+**Proof sketch.** Substitute `a' = a` and `b' = b`; the readings are identities
+(`padFin_ofFn`). -/
+theorem _root_.Complexity.NUPPT.eval_toOracleAdversary_padFin (D : NUPPT) (n q : ℕ)
+    (c : D.Coins n) {a b a' b' : ℕ} (ha : a' = a) (hb : b' = b)
+    (f : (Fin a → Bool) → (Fin b → Bool)) :
+    (D.toOracleAdversary n a b q c).eval f =
+      (D.toOracleAdversary n a' b' q c).eval
+        (fun x => padFin b' (List.ofFn (f (padFin a (List.ofFn x))))) := by
+  subst ha hb
+  have e : (fun x => padFin b' (List.ofFn (f (padFin a' (List.ofFn x))))) = f := by
+    funext x
+    rw [padFin_ofFn, padFin_ofFn]
+  rw [e]
+
 /-! ### Oracle indistinguishability [PS10, Definition 96.1] -/
 
 /-- **Oracle indistinguishability** [PS10, Definition 96.1]: `{O_n} ≈ {O'_n}` iff for every
diff --git a/TCSlib/Cryptography/ZeroKnowledge.lean b/TCSlib/Cryptography/ZeroKnowledge.lean
index 240e07f1c..a10f4e96d 100644
--- a/TCSlib/Cryptography/ZeroKnowledge.lean
+++ b/TCSlib/Cryptography/ZeroKnowledge.lean
@@ -5,6 +5,7 @@ Authors: TCSlib contributors
 -/
 import TCSlib.Cryptography.ZeroKnowledge.Encoding
 import TCSlib.Cryptography.ZeroKnowledge.Interaction
+import TCSlib.Cryptography.ZeroKnowledge.InteractionWords
 import TCSlib.Cryptography.ZeroKnowledge.InteractiveProofs
 import TCSlib.Cryptography.ZeroKnowledge.Defs
 import TCSlib.Cryptography.ZeroKnowledge.GraphIsomorphism
@@ -39,6 +40,7 @@ zero-knowledge theorems are statistical (D8, D10).
   statements of the honest parties' string operations (Inf-4.1, Inf-4.2).
 * `Interaction` — next-message strategies, executions, views, transcripts and outputs
   [PS10, §4.4] (Def-114.a – Def-116.b).
+* `InteractionWords` — the history encoding as a word list (`BinArith.encWords`).
 * `InteractiveProofs` — interactive proof systems, soundness error, witness relations and
   interactive proofs with efficient prover [PS10, Definitions 116.1, 119.5, 191.11]; the
   one-message witness protocol as the sanity theorem (Def-116.1, Def-117.a, Def-119.5,
diff --git a/TCSlib/Cryptography/ZeroKnowledge/EncodingMachines.lean b/TCSlib/Cryptography/ZeroKnowledge/EncodingMachines.lean
index 2e01fd24c..cad8ea7d6 100644
--- a/TCSlib/Cryptography/ZeroKnowledge/EncodingMachines.lean
+++ b/TCSlib/Cryptography/ZeroKnowledge/EncodingMachines.lean
@@ -61,6 +61,10 @@ functions proved polynomial-time here.
   self-bounded updates are polynomial-time (a state loop).
 * `TCSlib.Cryptography.EncodingMachines.unarySqrt_poly`, `divNum_poly`, `modNum_poly`,
   `unarySize_poly` — `Nat.sqrt`, division, remainder and `Nat.size` in unary.
+* `TCSlib.Cryptography.EncodingMachines.flatMap_range_ite`, `polyTimeComputable_flatMap_range`,
+  `iterSnd_poly`, `zeros_poly`, `padTo_poly`, `length_padTo`, `getD_padTo`, `padTo_of_length`
+  (with the zero padding `padTo` and its equation `padTo_eq`) — concatenation loops over a unary
+  range, iterated second projections and zero padding.
 
 ## References
 
@@ -691,4 +695,173 @@ theorem unarySize_poly {f : List Bool → ℕ}
   funext x
   simp [Nat.size_eq_bits_len]
 
+/-! ### Concatenation loops, iterated projections and zero padding -/
+
+/-- **Emitting chunks below a bound:** emitting the chunk `E i` at the indices `i < L` of
+`List.range N` gives the concatenation of the `E i` over `i < min N L`:
+`(range N).flatMap (fun i => if i < L then E i else []) = (range (min N L)).flatMap E`
+(`flatMap_range_ite_eq` for arbitrary chunks). Framework glue, no textbook counterpart. -/
+protected theorem flatMap_range_ite (E : ℕ → List Bool) (L : ℕ) :
+    ∀ N, (List.range N).flatMap (fun i => if i < L then E i else []) =
+      (List.range (min N L)).flatMap E := by
+  intro N
+  induction N with
+  | zero => simp
+  | succ N ih =>
+    rw [List.range_succ, List.flatMap_append, ih, List.flatMap_singleton]
+    by_cases h : N < L
+    · rw [if_pos h, show min (N + 1) L = N + 1 by omega, show min N L = N by omega,
+        List.range_succ, List.flatMap_append, List.flatMap_singleton]
+    · rw [if_neg h, List.append_nil, show min (N + 1) L = min N L by omega]
+
+/-- **Concatenating a chunk over a unary range:** if the chunk `E z i` is a polynomial-time
+function of `⟨1^i, z⟩` and the count `n z` is a unary function, then
+`z ↦ E z 0 ++ ⋯ ++ E z (n z − 1)` is polynomial-time:
+`PolyTimeComputable fun z => (List.range (n z)).flatMap (E z)`. Framework glue, no textbook
+counterpart.
+
+**Proof sketch.** An instance of `Complexity.polyTimeComputable_iterateEmit` on the counter step
+`cstep` from `⟨[], z⟩`, whose `i`-th iterate is `⟨1^i, z⟩` (`cstep_iterate`; orbit bound
+`cstep_horbit`), emitting `E z i` while `i < n z` (`polyTimeComputable_ite` on `ltTest_poly`);
+the number of rounds is the polynomial bound `C (|z| + 1)^c` of the unary count
+(`PolyTimeComputable.output_length_le`), and the emitted chunks concatenate to the claimed list
+(`EncodingMachines.flatMap_range_ite`). -/
+protected theorem polyTimeComputable_flatMap_range {E : List Bool → ℕ → List Bool}
+    (hE : PolyTimeComputable fun w => E (pairSndD w) (pairFstD w).length)
+    {n : List Bool → ℕ} (hn : PolyTimeComputable fun z => List.replicate (n z) true) :
+    PolyTimeComputable fun z => (List.range (n z)).flatMap (E z) := by
+  obtain ⟨C, c, hC⟩ := hn.output_length_le
+  have hnP : ∀ z, n z ≤ (PolyExpr.normal C c).eval z.length := fun z => by
+    have := hC z
+    rw [List.length_replicate] at this
+    rw [PolyExpr.eval_normal]
+    exact this
+  have htest : PolyTimeComputable fun w => [decide ((pairFstD w).length < n (pairSndD w))] :=
+    ltTest_poly (unaryLength_poly polyTimeComputable_pairFstD)
+      (hn.comp' polyTimeComputable_pairSndD)
+  have hemit := polyTimeComputable_ite htest hE (polyTimeComputable_const [])
+  have hL := polyTimeComputable_iterateEmit cstep_poly hemit (PolyExpr.normal C c)
+    (cbound (PolyExpr.normal C c)) (cstep_horbit _)
+  have hpre : PolyTimeComputable fun z => pairEncode [] z :=
+    (polyTimeComputable_const []).pairEncode polyTimeComputable_id
+  refine (hL.comp' hpre).congr fun z => ?_
+  have horb : ∀ i, cstep^[i] (pairEncode [] z) = pairEncode (List.replicate i true) z :=
+    fun i => by rw [cstep_iterate, List.append_nil]
+  have hN : n z ≤ (PolyExpr.normal C c).eval (pairEncode [] z).length + 1 :=
+    ((hnP z).trans ((PolyExpr.normal C c).eval_mono
+      (by rw [length_pairEncode]; omega))).trans (Nat.le_succ _)
+  simp only [horb, pairFstD_pairEncode, pairSndD_pairEncode, List.length_replicate,
+    decide_eq_true_eq]
+  rw [EncodingMachines.flatMap_range_ite, min_eq_right hN]
+
+/-- **The iterated second projection is polynomial-time:** for a polynomial-time `s` and a unary
+count `i`, `PolyTimeComputable fun z => pairSndD^[i z] (s z)`. Framework glue, no textbook
+counterpart.
+
+**Proof sketch.** A counted loop (`polyTimeComputable_loopState`) from `s z` whose update on
+`⟨z, ⟨1^j, t⟩⟩` is the second projection of `t` truncated to `|s z|` bits
+(`truncate_poly`, `unaryLength_poly`). Peeling never lengthens a word
+(`length_pair_components_le`), so along the loop every state `pairSndD^[j] (s z)` is no longer
+than `s z` and the truncation is the identity there; every update is at most `|s z| ≤ C (|z|+1)^c`
+long (`PolyTimeComputable.output_length_le`), the self-bound the loop lemma asks for. -/
+protected theorem iterSnd_poly {s : List Bool → List Bool} (hs : PolyTimeComputable s)
+    {i : List Bool → ℕ} (hi : PolyTimeComputable fun z => List.replicate (i z) true) :
+    PolyTimeComputable fun z => pairSndD^[i z] (s z) := by
+  -- peeling never lengthens a word
+  have hlen : ∀ (w : List Bool) (j : ℕ), (pairSndD^[j] w).length ≤ w.length := by
+    intro w j
+    induction j with
+    | zero => exact le_rfl
+    | succ j ih =>
+      rw [Function.iterate_succ_apply']
+      exact ((Nat.le_add_left _ _).trans (length_pair_components_le _)).trans ih
+  -- the truncated update `⟨z, ⟨1^j, t⟩⟩ ↦ (pairSndD t).take |s z|`
+  have hupd : PolyTimeComputable fun w =>
+      (pairSndD (pairSndD (pairSndD w))).take (s (pairFstD w)).length :=
+    truncate_poly (polyTimeComputable_pairSndD.comp'
+        (polyTimeComputable_pairSndD.comp' polyTimeComputable_pairSndD))
+      (unaryLength_poly (hs.comp' polyTimeComputable_pairFstD))
+  -- the loop states are the iterated projections
+  have hclosed : ∀ (upd : List Bool → List Bool),
+      (∀ w, upd w = (pairSndD (pairSndD (pairSndD w))).take (s (pairFstD w)).length) →
+      ∀ z j, loopState upd s z j = pairSndD^[j] (s z) := by
+    intro upd hu z j
+    induction j with
+    | zero => rw [loopState_zero, Function.iterate_zero_apply]
+    | succ j ih =>
+      have hj := hlen (s z) (j + 1)
+      rw [Function.iterate_succ_apply'] at hj
+      rw [loopState_succ, hu, pairSndD_pairEncode, pairSndD_pairEncode, pairFstD_pairEncode, ih,
+        Function.iterate_succ_apply', List.take_of_length_le hj]
+  obtain ⟨C, c, hC⟩ := hs.output_length_le
+  have hsB : ∀ x, (s x).length ≤ (PolyExpr.normal C c).eval x.length := fun x => by
+    rw [PolyExpr.eval_normal]
+    exact hC x
+  have hupdB : ∀ x t, ((pairSndD (pairSndD (pairSndD (pairEncode x t)))).take
+      (s (pairFstD (pairEncode x t))).length).length ≤ (PolyExpr.normal C c).eval x.length := by
+    intro x t
+    rw [pairFstD_pairEncode]
+    exact (List.length_take_le _ _).trans (hsB x)
+  refine (polyTimeComputable_loopState hupd hs hi (PolyExpr.normal C c) hsB hupdB).congr
+    fun z => ?_
+  exact hclosed _ (fun _ => rfl) z (i z)
+
+/-- **`L` zeros from a unary length:** if `L` is a unary function, then
+`PolyTimeComputable fun x => List.replicate (L x) false` (the bit-extraction principle with the
+constant bit `0`). Framework glue, no textbook counterpart. -/
+protected theorem zeros_poly {L : List Bool → ℕ}
+    (hL : PolyTimeComputable fun x => List.replicate (L x) true) :
+    PolyTimeComputable fun x => List.replicate (L x) false := by
+  refine polyTimeComputable_of_getD (F := fun x => List.replicate (L x) false) ?_ ?_
+  · refine (polyTimeComputable_const [false]).congr fun w => ?_
+    rw [List.getD_eq_getElem?_getD, List.getElem?_replicate]
+    split_ifs <;> rfl
+  · refine hL.congr fun x => ?_
+    rw [List.length_replicate]
+
+/-- **Zero padding** to length `L` (and truncation to `L`): `padTo L w = (w ++ 0^L).take L`, the
+word `w` cut or filled with zeros to exactly `L` bits. Framework glue, no textbook counterpart. -/
+protected def padTo (L : ℕ) (w : List Bool) : List Bool := (w ++ List.replicate L false).take L
+
+/-- The defining equation of `padTo`: `padTo L w = (w ++ 0^L).take L`. Framework glue, no
+textbook counterpart. -/
+protected theorem padTo_eq (L : ℕ) (w : List Bool) :
+    EncodingMachines.padTo L w = (w ++ List.replicate L false).take L := rfl
+
+/-- **Padding to a unary length is polynomial-time:** for a polynomial-time `s` and a unary `L`,
+`PolyTimeComputable fun x => padTo (L x) (s x)` (`truncate_poly` after appending the zeros
+`EncodingMachines.zeros_poly`). Framework glue, no textbook counterpart. -/
+protected theorem padTo_poly {s : List Bool → List Bool} (hs : PolyTimeComputable s)
+    {L : List Bool → ℕ} (hL : PolyTimeComputable fun x => List.replicate (L x) true) :
+    PolyTimeComputable fun x => EncodingMachines.padTo (L x) (s x) :=
+  (truncate_poly (hs.append (EncodingMachines.zeros_poly hL)) hL).congr fun x =>
+    (EncodingMachines.padTo_eq (L x) (s x)).symm
+
+/-- The padded word has length `L`: `|padTo L w| = L`. Framework glue, no textbook
+counterpart. -/
+protected theorem length_padTo (L : ℕ) (w : List Bool) :
+    (EncodingMachines.padTo L w).length = L := by
+  rw [EncodingMachines.padTo_eq, List.length_take, List.length_append, List.length_replicate]
+  omega
+
+/-- The bits of the padded word below `L` are the bits of `w` read with default `false`:
+`(padTo L w).getD i false = w.getD i false` for `i < L`. Framework glue, no textbook
+counterpart. -/
+protected theorem getD_padTo (L : ℕ) (w : List Bool) {i : ℕ} (hi : i < L) :
+    (EncodingMachines.padTo L w).getD i false = w.getD i false := by
+  rw [EncodingMachines.padTo_eq, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hi,
+    List.getElem?_append, List.getD_eq_getElem?_getD]
+  split_ifs with h
+  · rfl
+  · have hw : w[i]? = none := List.getElem?_eq_none_iff.2 (by omega)
+    rw [hw, List.getElem?_replicate]
+    split_ifs <;> rfl
+
+/-- Padding a word of the right length is the identity: `|w| = L → padTo L w = w`. Framework
+glue, no textbook counterpart. -/
+protected theorem padTo_of_length {L : ℕ} {w : List Bool} (h : w.length = L) :
+    EncodingMachines.padTo L w = w := by
+  rw [EncodingMachines.padTo_eq, List.take_append_of_le_length (by omega),
+    List.take_of_length_le (by omega)]
+
 end TCSlib.Cryptography.EncodingMachines
diff --git a/TCSlib/Cryptography/ZeroKnowledge/Interaction.lean b/TCSlib/Cryptography/ZeroKnowledge/Interaction.lean
index 12c9c57f0..44d05a506 100644
--- a/TCSlib/Cryptography/ZeroKnowledge/Interaction.lean
+++ b/TCSlib/Cryptography/ZeroKnowledge/Interaction.lean
@@ -77,6 +77,9 @@ requires it of the verifier (run-3 audit P9-1).
 ## Main results
 
 * `TCSlib.Cryptography.exec_length` — after `k` moves exactly `k` messages have been sent.
+* `TCSlib.Cryptography.Strategy.encodeMsgs_eq`, `Strategy.encodeMsgs_eq_flatMap`,
+  `Strategy.iterate_pairSndD_encodeMsgs`, `Strategy.msgAt_encodeMsgs` — the history encoding as a
+  fold and as a concatenation, its suffixes, and its `i`-th message.
 * `TCSlib.Cryptography.Strategy.ofNUPPT_efficient` — every uniform machine is an efficient
   strategy (non-vacuity of Def-116.b).
 * `TCSlib.Cryptography.Strategy.ReadsPrefix.mono`,
@@ -147,6 +150,49 @@ theorem pairFstD_encodeMsgs (h : List (List Bool)) : pairFstD (encodeMsgs h) = h
     exact List.eq_nil_of_length_eq_zero (Nat.le_zero.1 (length_pairFstD_le []))
   | cons m h => simp
 
+/-- The defining equation of `encodeMsgs`: the encoding of a history is the right fold of
+`pairEncode` from `[]`, `encodeMsgs h = h.foldr pairEncode []`. Framework glue, no textbook
+counterpart. -/
+theorem encodeMsgs_eq (h : List (List Bool)) : encodeMsgs h = h.foldr pairEncode [] := rfl
+
+/-- **The history encoding chunk by chunk:** the encoding of a history is the concatenation of
+its self-delimiting messages, `encodeMsgs l = l.flatMap fun m => pairEncode m []`.
+Framework glue, no textbook counterpart. -/
+protected theorem encodeMsgs_eq_flatMap (l : List (List Bool)) :
+    encodeMsgs l = l.flatMap fun m => pairEncode m [] := by
+  induction l with
+  | nil => rw [encodeMsgs_nil, List.flatMap_nil]
+  | cons m l ih =>
+    rw [encodeMsgs_cons, List.flatMap_cons, ← ih, Turing.pairEncode_eq, Turing.pairEncode_eq,
+      List.append_nil]
+
+/-- **The suffixes of an encoded history:** `i` second projections of the encoding of a history
+leave the encoding of the history without its first `i` messages,
+`pairSndD^[i] (encodeMsgs hist) = encodeMsgs (hist.drop i)`. Framework glue, no textbook
+counterpart. -/
+protected theorem iterate_pairSndD_encodeMsgs (hist : List (List Bool)) (i : ℕ) :
+    pairSndD^[i] (encodeMsgs hist) = encodeMsgs (hist.drop i) := by
+  induction i generalizing hist with
+  | zero => rw [Function.iterate_zero_apply, List.drop_zero]
+  | succ i ih =>
+    cases hist with
+    | nil =>
+      rw [Function.iterate_succ_apply, encodeMsgs_nil,
+        pairSndD_of_pairDecode_eq_none Turing.pairDecode_nil, ← encodeMsgs_nil, ih,
+        List.drop_nil, List.drop_nil]
+    | cons m h =>
+      rw [Function.iterate_succ_apply, encodeMsgs_cons, pairSndD_pairEncode, ih,
+        List.drop_succ_cons]
+
+/-- **The `i`-th message of an encoded history:** the first projection after `i` second
+projections reads message `i` (`[]` beyond the history),
+`pairFstD (pairSndD^[i] (encodeMsgs hist)) = hist.getD i []`. Framework glue, no textbook
+counterpart. -/
+protected theorem msgAt_encodeMsgs (hist : List (List Bool)) (i : ℕ) :
+    pairFstD (pairSndD^[i] (encodeMsgs hist)) = hist.getD i [] := by
+  rw [Strategy.iterate_pairSndD_encodeMsgs, pairFstD_encodeMsgs, List.headD_eq_head?_getD,
+    List.head?_drop, List.getD_eq_getElem?_getD]
+
 /-- The strategy computed by a machine `A`: one activation at parameter `|x|` on
 `⟨⟨x, z⟩, messages⟩` with the whole random tape (`A.runAtL`); the coin polynomial is `A.coins`
 [PS10, §4.4, the interactive machine as a Turing machine with a random tape]. -/
diff --git a/TCSlib/Cryptography/ZeroKnowledge/InteractionWords.lean b/TCSlib/Cryptography/ZeroKnowledge/InteractionWords.lean
new file mode 100644
index 000000000..046627f13
--- /dev/null
+++ b/TCSlib/Cryptography/ZeroKnowledge/InteractionWords.lean
@@ -0,0 +1,44 @@
+/-
+Copyright (c) 2026 TCSlib contributors. All rights reserved.
+Released under Apache 2.0 license as described in the file LICENSE.
+Authors: TCSlib contributors
+-/
+import TCSlib.Cryptography.ZeroKnowledge.Interaction
+import TCSlib.Complexity.ClassP.BinaryArith.Words
+
+set_option maxHeartbeats 0
+set_option relaxedAutoImplicit false
+set_option autoImplicit false
+
+/-!
+# The history encoding as a word list
+
+The string encoding `Strategy.encodeMsgs` of the received-messages component of a view
+[PS10, §4.4] is the word-list encoding `Complexity.BinArith.encWords` of the machine layer: both
+are the concatenation of the self-delimiting messages `⟨m, []⟩`. The bridge lives in its own
+module so that `ZeroKnowledge/Interaction.lean` does not import the binary-arithmetic machines.
+
+## Main definitions
+
+None; this module proves one bridge lemma.
+
+## Main results
+
+* `TCSlib.Cryptography.Strategy.encodeMsgs_eq_encWords` — `encodeMsgs L = BinArith.encWords L`.
+
+## References
+
+* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
+  §4.4.
+-/
+
+namespace TCSlib.Cryptography.Strategy
+
+/-- **The history encoding is the word-list encoding:** for every list of words `L`,
+`encodeMsgs L = Complexity.BinArith.encWords L` (both are `L.flatMap fun m => ⟨m, []⟩`).
+Framework glue, no textbook counterpart. -/
+protected theorem encodeMsgs_eq_encWords (L : List (List Bool)) :
+    encodeMsgs L = Complexity.BinArith.encWords L := by
+  rw [Strategy.encodeMsgs_eq_flatMap, Complexity.BinArith.encWords_def]
+
+end TCSlib.Cryptography.Strategy
diff --git a/TCSlib/InformationTheory/Entropy.lean b/TCSlib/InformationTheory/Entropy.lean
index 89f050a8e..dccabe2cf 100644
--- a/TCSlib/InformationTheory/Entropy.lean
+++ b/TCSlib/InformationTheory/Entropy.lean
@@ -35,6 +35,9 @@ This file adds the min-entropy *value* that [PS10] defines and proves the two ag
 * `FinDist.IsSource k p`: `p` is a `k`-source (min-entropy at least `k`).
 * `FinDist.IsFlatSource k p`: `p` is uniform on a set of `2^k` points.
 * `FinDist.flat s`: the uniform distribution on a nonempty finite set `s`.
+* `FinDist.mixture w hw0 hw1 p q`: the mixture `w · p + (1 - w) · q` (reader
+  `FinDist.mixture_apply`); a mixture of two `k`-sources is a `k`-source
+  (`FinDist.mixture_isSource`).
 
 ## Main results
 
@@ -212,4 +215,49 @@ theorem isSource_uniform [Nonempty α] : IsSource (logb 2 (Fintype.card α)) (un
 
 end FinDist
 
+/-! ### Mixtures of sources -/
+
+section Mixture
+
+variable {α : Type*} [Fintype α]
+
+/-- The **mixture** of `p` and `q` with weight `w ∈ [0, 1]`: the distribution that gives each
+point `a` the convex combination `w · p(a) + (1 - w) · q(a)` (sample `p` with probability `w`,
+`q` otherwise). Framework glue, no textbook counterpart. -/
+protected noncomputable def FinDist.mixture (w : ℝ) (hw0 : 0 ≤ w) (hw1 : w ≤ 1)
+    (p q : FinDist α) : FinDist α where
+  prob a := w * p a + (1 - w) * q a
+  nonneg a := add_nonneg (mul_nonneg hw0 (p.nonneg a))
+    (mul_nonneg (sub_nonneg.2 hw1) (q.nonneg a))
+  sum_prob := by
+    rw [sum_add_distrib, ← mul_sum, ← mul_sum, p.sum_prob, q.sum_prob]
+    ring
+
+/-- **The point probability of a mixture** is its defining convex combination:
+`mixture w p q a = w · p(a) + (1 - w) · q(a)`. Framework glue, no textbook counterpart. -/
+protected theorem FinDist.mixture_apply (w : ℝ) (hw0 : 0 ≤ w) (hw1 : w ≤ 1) (p q : FinDist α)
+    (a : α) : FinDist.mixture w hw0 hw1 p q a = w * p a + (1 - w) * q a :=
+  rfl
+
+/-- **A mixture of two `k`-sources is a `k`-source**: if every point has probability at most
+`2^(-k)` under `p` and under `q`, then so under every mixture of them,
+`IsSource k p → IsSource k q → IsSource k (mixture w p q)`, since a convex combination preserves
+the common bound. Framework glue, no textbook counterpart. -/
+protected theorem FinDist.mixture_isSource (w : ℝ) (hw0 : 0 ≤ w) (hw1 : w ≤ 1) (p q : FinDist α)
+    (k : ℝ) (hp : FinDist.IsSource k p) (hq : FinDist.IsSource k q) :
+    FinDist.IsSource k (FinDist.mixture w hw0 hw1 p q) := by
+  have hp' := (FinDist.hasMinEntropy_iff p k).1 (FinDist.isSource_iff_hasMinEntropy.1 hp)
+  have hq' := (FinDist.hasMinEntropy_iff q k).1 (FinDist.isSource_iff_hasMinEntropy.1 hq)
+  apply FinDist.isSource_iff_hasMinEntropy.2
+  apply (FinDist.hasMinEntropy_iff _ _).2
+  intro a
+  rw [FinDist.mixture_apply]
+  calc w * p a + (1 - w) * q a
+      ≤ w * (2 : ℝ) ^ (-k) + (1 - w) * (2 : ℝ) ^ (-k) :=
+        add_le_add (mul_le_mul_of_nonneg_left (hp' a) hw0)
+          (mul_le_mul_of_nonneg_left (hq' a) (sub_nonneg.2 hw1))
+    _ = (2 : ℝ) ^ (-k) := by ring
+
+end Mixture
+
 end TCSlib.InformationTheory
diff --git a/TCSlib/InformationTheory/FinDist.lean b/TCSlib/InformationTheory/FinDist.lean
index 944d4a7e8..c0be07bdb 100644
--- a/TCSlib/InformationTheory/FinDist.lean
+++ b/TCSlib/InformationTheory/FinDist.lean
@@ -34,6 +34,9 @@ probability, the `ℓ¹`–`ℓ²` bound, the leftover hash lemma) are all diffe
   `2 ^ (-k)`.
 * `FinDist.collision_uniform`, `FinDist.inv_card_le_collision`: the uniform distribution
   minimizes collision probability.
+* `FinDist.map_uniform_equiv`, `FinDist.sum_map`, `FinDist.uniform_prod`, `FinDist.probTrue_nonneg`,
+  `FinDist.probTrue_le_one`, `FinDist.uniform_probTrue`: pushforwards and products of uniform
+  laws, and the range and uniform value of an acceptance probability.
 
 ## References
 
@@ -197,4 +200,81 @@ theorem FinDist.probTrue_eq (p : FinDist α) (D : α → Bool) :
     p.probTrue D = ∑ a ∈ univ.filter (fun a => D a = true), p a :=
   rfl
 
+/-! ### Pushforwards, products and acceptance of the uniform law -/
+
+section Pushforward
+
+variable {β : Type*} [Fintype β]
+
+/-- **The uniform law is invariant under a bijection**: pushing the uniform distribution on `α`
+through an equivalence `e : α ≃ β` gives the uniform distribution on `β`, `map e U_α = U_β`.
+Framework glue, no textbook counterpart. -/
+protected theorem FinDist.map_uniform_equiv [DecidableEq β] [Nonempty α] [Nonempty β] (e : α ≃ β) :
+    (FinDist.uniform α).map e = FinDist.uniform β := by
+  classical
+  apply FinDist.ext
+  intro b
+  rw [FinDist.map_apply]
+  have hf : (univ : Finset α).filter (fun a => e a = b) = {e.symm b} := by
+    ext a
+    simp only [mem_filter, mem_univ, true_and, mem_singleton]
+    constructor
+    · intro h
+      exact e.injective (h.trans (e.apply_symm_apply b).symm)
+    · rintro rfl
+      exact e.apply_symm_apply b
+  rw [hf, sum_singleton, FinDist.uniform_apply, FinDist.uniform_apply,
+    Fintype.card_congr e]
+
+/-- **Summing over a pushforward**: a weighted sum over the pushforward of `p` along `f` is the
+sum of the composite over `p`, `∑ b, (map f p) b · g b = ∑ a, p a · g (f a)`.
+Framework glue, no textbook counterpart. -/
+protected theorem FinDist.sum_map [DecidableEq β] (p : FinDist α) (f : α → β) (g : β → ℝ) :
+    (∑ b, (p.map f) b * g b) = ∑ a, p a * g (f a) := by
+  classical
+  simp only [FinDist.map_apply, sum_mul, sum_filter]
+  rw [sum_comm]
+  apply sum_congr rfl
+  intro a _
+  rw [sum_eq_single (f a)]
+  · simp
+  · intro b _ hba
+    simp only [if_neg (Ne.symm hba), zero_mul]
+  · intro h
+    exact False.elim (h (mem_univ _))
+
+/-- **An acceptance probability is nonnegative**: `0 ≤ Pr_{x ← p}[D x = 1]`, i.e.
+`0 ≤ p.probTrue D`. Framework glue, no textbook counterpart. -/
+protected theorem FinDist.probTrue_nonneg (p : FinDist α) (D : α → Bool) : 0 ≤ p.probTrue D := by
+  rw [FinDist.probTrue_eq]
+  exact sum_nonneg fun a _ => p.nonneg a
+
+/-- **An acceptance probability is at most one**: `Pr_{x ← p}[D x = 1] ≤ 1`, i.e.
+`p.probTrue D ≤ 1`. Framework glue, no textbook counterpart. -/
+protected theorem FinDist.probTrue_le_one (p : FinDist α) (D : α → Bool) : p.probTrue D ≤ 1 := by
+  rw [FinDist.probTrue_eq, ← p.sum_prob]
+  exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun a _ _ => p.nonneg a)
+
+/-- **The product of two uniform laws is uniform**: the independent pair of uniform samples of
+`α` and `β` is the uniform distribution on `α × β`, `U_α × U_β = U_{α × β}`.
+Framework glue, no textbook counterpart. -/
+protected theorem FinDist.uniform_prod [Nonempty α] [Nonempty β] :
+    (FinDist.uniform α).prod (FinDist.uniform β) = FinDist.uniform (α × β) := by
+  apply FinDist.ext
+  intro z
+  rw [FinDist.prod_apply, FinDist.uniform_apply, FinDist.uniform_apply,
+    FinDist.uniform_apply, Fintype.card_prod, Nat.cast_mul, mul_inv_rev]
+  ring
+
+/-- **Acceptance under the uniform law is a count**: the probability that `D` accepts a uniform
+sample of `α` is the number of accepted points divided by `|α|`,
+`Pr_{U_α}[D = 1] = |{a : D a = 1}| · |α|⁻¹`. Framework glue, no textbook counterpart. -/
+protected theorem FinDist.uniform_probTrue [Nonempty α] (D : α → Bool) :
+    (FinDist.uniform α).probTrue D =
+      ((Finset.univ.filter (fun a => D a = true)).card : ℝ) * (Fintype.card α : ℝ)⁻¹ := by
+  rw [FinDist.probTrue_eq]
+  simp only [FinDist.uniform_apply, sum_const, nsmul_eq_mul]
+
+end Pushforward
+
 end TCSlib.InformationTheory
diff --git a/TCSlib/InformationTheory/Samples.lean b/TCSlib/InformationTheory/Samples.lean
index 35f4df3e6..d7cc2daa2 100644
--- a/TCSlib/InformationTheory/Samples.lean
+++ b/TCSlib/InformationTheory/Samples.lean
@@ -30,6 +30,8 @@ an iterated expectation.
 * `FinDist.probTrue_not`: the complement rule `Pr[¬D] = 1 − Pr[D]`.
 * `FinDist.expect_le_add_of_le_one`: a function with values at most `1` has expectation at most
   `ε + Pr[f > ε]`, for `ε ≥ 0`.
+* `FinDist.expect_map`, `FinDist.probTrue_map`, `FinDist.map_apply_expect`, `FinDist.map_map`,
+  `FinDist.map_prod_snd`: expectations, probabilities and point masses under a pushforward.
 
 ## References
 
@@ -152,4 +154,65 @@ theorem iid_apply (p : FinDist α) (m : ℕ) (s : Fin m → α) :
 
 end FinDist
 
+/-! ### Expectations and probabilities under a pushforward -/
+
+section Pushforward
+
+variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
+
+/-- **Expectation under a pushforward composes the function**: the expectation of `g` under the
+pushforward of `p` along `f` is the expectation of `g ∘ f` under `p`,
+`E_{map f p}[g] = E_p[g ∘ f]`. Framework glue, no textbook counterpart. -/
+protected theorem FinDist.expect_map [DecidableEq β] (p : FinDist α) (f : α → β) (g : β → ℝ) :
+    (p.map f).expect g = p.expect (fun a => g (f a)) := by
+  rw [FinDist.expect_eq, FinDist.expect_eq]
+  exact FinDist.sum_map p f g
+
+/-- **Acceptance under a pushforward composes the test**: the probability that `D` accepts a
+sample of the pushforward of `p` along `f` is the probability that `D ∘ f` accepts a sample of
+`p`, `Pr_{map f p}[D = 1] = Pr_p[D ∘ f = 1]`. Framework glue, no textbook counterpart. -/
+protected theorem FinDist.probTrue_map [DecidableEq β] (p : FinDist α) (f : α → β) (D : β → Bool) :
+    (p.map f).probTrue D = p.probTrue (fun a => D (f a)) := by
+  rw [FinDist.probTrue_eq_expect, FinDist.expect_map, FinDist.probTrue_eq_expect]
+
+/-- **A pushforward's mass is the expectation of an indicator**: the pushforward of `p` along
+`f` gives `b` the expectation under `p` of the indicator of `f a = b`,
+`map f p b = E_p[1_{f a = b}]`. Framework glue, no textbook counterpart. -/
+protected theorem FinDist.map_apply_expect [DecidableEq β] (p : FinDist α) (f : α → β) (b : β) :
+    (p.map f) b = p.expect (fun a => if f a = b then 1 else 0) := by
+  classical
+  rw [FinDist.map_apply, FinDist.expect_eq, sum_filter]
+  apply sum_congr rfl
+  intro a _
+  split_ifs <;> simp
+
+/-- **Successive pushforwards compose**: pushing `p` forward along `f` and then along `g` is
+pushing it forward along `g ∘ f`, `map g (map f p) = map (g ∘ f) p`.
+Framework glue, no textbook counterpart. -/
+protected theorem FinDist.map_map [DecidableEq β] [DecidableEq γ] (p : FinDist α) (f : α → β)
+    (g : β → γ) : (p.map f).map g = p.map (fun a => g (f a)) := by
+  classical
+  apply FinDist.ext
+  intro c
+  rw [FinDist.map_apply_expect, FinDist.expect_map, FinDist.map_apply_expect]
+
+/-- **A pushforward of the second coordinate commutes with pairing**: mapping the second
+coordinate of an independent pair by `f` before pairing, and then mapping the pair by `g`, is
+mapping the pair by `(x, y) ↦ g (x, f y)`,
+`map g (p × map f q) = map (fun z => g (z.1, f z.2)) (p × q)`.
+Framework glue, no textbook counterpart. -/
+protected theorem FinDist.map_prod_snd [DecidableEq β] [DecidableEq γ] {δ : Type*} [Fintype δ]
+    [DecidableEq δ] (p : FinDist α) (q : FinDist β) (f : β → γ) (g : α × γ → δ) :
+    (p.prod (q.map f)).map g = (p.prod q).map (fun z => g (z.1, f z.2)) := by
+  classical
+  apply FinDist.ext
+  intro d
+  rw [FinDist.map_apply_expect, FinDist.map_apply_expect, FinDist.expect_prod,
+    FinDist.expect_prod]
+  congr 1
+  funext a
+  exact FinDist.expect_map q f (fun c => if g (a, c) = d then 1 else 0)
+
+end Pushforward
+
 end TCSlib.InformationTheory

## ===== TCSlib/Complexity/TuringMachine/Build/ModuleHost.lean (Lean, TS1 tree 1eaf940b938bb52e3919f5569893b58522df599b) =====

/-
Copyright (c) 2026 Seyoon Ragavan, TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan, TCSlib contributors
-/
import Mathlib.Data.Fintype.Sigma
import Mathlib.Tactic.Ring
import TCSlib.Complexity.TuringMachine.Build.Loop
import TCSlib.Complexity.ClassNP.PolyTime

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The clean-module host

A host (`machine-library-design.md` §14, row H14) that runs a finite family of *clean modules*
inside one finite machine.

* **Clean modules.** A clean module (`Turing.ModuleHost.Clean`) is a finite machine with at least
  one work tape that, started at the canonical seam with an argument word as its only
  tape-resident word, halts for the first time at a positive time within a budget of the argument
  length, at the seam holding a result word, having emitted exactly a declared chunk. Every
  polynomial-time word function has a clean **install** module (the value installed as the
  tape-resident word, nothing emitted) and a clean **emit** module (the argument kept, the value
  emitted), each with a polynomial budget (`clean_install`, `clean_emit`). They come from the
  clean-call bridges `Turing.FinTM.exists_installCallTM`/`exists_emitCallTM`, whose modules exit
  at their first positive visit of an exit state: a release flag halts such a module one silent
  step after that visit, and cutting the run at its first halt (`first_halt`) gives the uniform
  contract.
* **The host.** `Turing.ModuleHost.hostTM` pads `n` modules to a shared bank of `K` work tapes
  (all modules share tape 0) and embeds them, through the forwarding transformer
  `Turing.emitAction`, into one finite machine whose states are the host's own control states `C`
  and the modules' states (`Turing.ModuleHost.State C M = C ⊕ Σ i, (M i).State`). When module `i`
  halts, control passes to its return state `ret i`; the control states run a table `ctrl`
  supplied by the consumer (`hostTM_step_inl`). `host_call` and `host_clean` run one module inside
  the host: from the host seam at the module's entry state, with any output prefix, the host
  reaches the seam at the module's return state with the module's result word, forwarding exactly
  the module's output, and visits no control state meanwhile; `guard_add` chains such segments.
* **Head envelopes.** A clean module's heads stay within its budget `B |arg|` of the origin at
  every time (`Clean.envelope`), and the host's heads stay within `t` cells of the origin up to
  time `t` of a call (`host_call_envelope`), hence within `B |arg|` during a clean call
  (`host_clean_envelope`). These are the coarse envelopes from the time bounds and the unit head
  moves of `Turing.MultiTapeTM.workTapePos_step_le` (gate 03l round 2, finding 1).

## Origin

Harvested on 2026-11-05 (gate 03l, ruling R-03l-1) from two copies of one private layer: the
module-gluing layer of `TCSlib.Complexity.ClassNP.SAT` on `main` (the streaming emitter behind
`Complexity.SAT_reducible_SAT3` [AB09, Lemma 2.14]: six modules, one control state), and its copy
in pack 03l's `TCSlib.Complexity.Randomized.Build.IterateFindHost` (the repetition machine behind
`Complexity.polyTimeComputable_iterateFind`: five modules, three control states). Both now
instantiate this file; what they vary is a parameter here: the number of modules and their
machines, the control states and their table, the return map and the start state.

## Main definitions

* `Turing.ModuleHost.Clean` — the first-halting clean-module contract (read through `clean_iff`).
* `Turing.ModuleHost.State`, `Turing.ModuleHost.entry` — the host's state type and the entry
  state of a module (`state_eq`, `entry_eq`).
* `Turing.ModuleHost.hostTM` — the host (`hostTM_k`, `hostTM_tm_q₀`, `hostTM_step_inl`).
* `Turing.ModuleHost.hostTMView` — the host with its tape count and state type explicit
  (`hostTMView_eq`, `hostTMView_q₀`, `hostTMView_step_inl`, `host_call_view`, `host_clean_view`).

## Main results

* `Turing.ModuleHost.clean_install`, `clean_emit` — every polynomial-time word function has a
  clean install and a clean emit module with a polynomial budget on the argument length.
* `Turing.ModuleHost.host_call`, `host_clean` — one module call inside the host, with the guard
  that no control state is visited; `guard_add` — chaining guarded segments.
* `Turing.ModuleHost.Clean.envelope`, `host_call_envelope`, `host_clean_envelope` — the head
  envelopes of a clean module and of a host call.
* `Turing.ModuleHost.first_halt`, `live_prefix` — cutting a halting run at its first halt, and
  liveness of the prefix of a live run.
* `Turing.ModuleHost.request_budget` — a polynomial budget on a bounded request fits a common
  power.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.2–1.3, time-bounded multi-tape machines; §2.2, the class
  FP; Lemma 2.14, the reduction of the first consumer.)
* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (Algorithm 38.5 and Theorem 35.1: the repeated-adversary machine of the second consumer.)
-/

namespace Turing.ModuleHost

open Complexity

/-! ### Runs: the first halt and the live prefix -/

/-- **The first halt.** If the run of `tm` from a live configuration `cfg` has halted by time
`t`, then it halts for the first time at some time `u` with `0 < u ≤ t`: the configurations
before `u` are live, and the configuration at `u` is the one at `t`.

**Proof sketch.** Take the least halting time `u` (`Nat.find`). It is positive because `cfg` is
live, and since halting is absorbing (`runFrom_of_halt`), the configuration at `t = u + (t - u)`
is the one at `u`. -/
theorem first_halt {k : ℕ} {S : Type} {x : List Bool}
    (tm : MultiTapeTM k Bool S) (cfg : Cfg k Bool S x) (t : ℕ)
    (hstart : cfg.state ≠ none) (hhalt : (tm.runFrom cfg t).state = none) :
    ∃ u, 0 < u ∧ u ≤ t ∧ (∀ v < u, ¬(tm.runFrom cfg v).Halted) ∧
      tm.runFrom cfg u = tm.runFrom cfg t := by
  classical
  let h : ∃ u, (tm.runFrom cfg u).state = none := ⟨t, hhalt⟩
  have hu := Nat.find_spec h
  have hle := Nat.find_min' h hhalt
  refine ⟨Nat.find h, ?_, hle, fun v hv => Nat.find_min h hv, ?_⟩
  · by_contra hn
    have hz : Nat.find h = 0 := by omega
    rw [hz, MultiTapeTM.runFrom_zero] at hu
    exact hstart hu
  · symm
    rw [← Nat.add_sub_of_le hle, MultiTapeTM.runFrom_add, MultiTapeTM.runFrom_of_halt _ hu]

/-- **The live prefix.** If the run of `tm` from `c` is live at time `t`, it is live at every
time `u ≤ t` (halting is absorbing, `runFrom_of_halt`). -/
theorem live_prefix {k : ℕ} {S : Type} {x : List Bool}
    (tm : MultiTapeTM k Bool S) (c : Cfg k Bool S x) (t : ℕ)
    (ht : (tm.runFrom c t).state ≠ none) :
    ∀ u ≤ t, (tm.runFrom c u).state ≠ none := by
  intro u hu hh
  have he : tm.runFrom c t = tm.runFrom c u := by
    rw [← Nat.add_sub_of_le hu, MultiTapeTM.runFrom_add, MultiTapeTM.runFrom_of_halt _ hh]
  exact ht (by rw [he]; exact hh)

/-! ### Clean modules -/

/-- Convert a first-positive-exit module into a halting source: a release flag, raised after
the first step, makes the module halt silently when it is at `exit` — so an entry equal to the
exit still executes once. -/
private def stopTM (C : FinTM Bool) (entry exit : C.State) : FinTM Bool where
  k := C.k
  State := Bool × C.State
  tm := { q₀ := (false, entry)
          tr := fun q inp work =>
            if q.1 = true ∧ q.2 = exit then FinTM.controlAction 0 none
            else {C.tm.tr q.2 inp work with
              state := (C.tm.tr q.2 inp work).state.map (true, ·)} }

/-- The release-flag embedding of a module configuration: the flag `b` joins the state, and
every physical field is kept. -/
private def stopCfg {k : ℕ} {S : Type} {x : List Bool}
    (b : Bool) (c : Cfg k Bool S x) : Cfg k Bool (Bool × S) x :=
  ⟨c.state.map (b, ·), c.inputPos, c.workTapes, c.workTapePos, c.output⟩

/-- Before the designated positive exit, the stopped source takes the same physical step as the
module and raises the release flag. -/
private lemma stop_step (C : FinTM Bool) (entry exit : C.State)
    {x : List Bool} (b : Bool) (c : Cfg C.k Bool C.State x)
    (hlive : c.state ≠ none) (hg : b = true → c.state ≠ some exit) :
    (stopTM C entry exit).tm.step (stopCfg b c) = stopCfg true (C.tm.step c) := by
  cases hs : c.state with
  | none => exact False.elim (hlive hs)
  | some q =>
    have hq : ¬(b = true ∧ q = exit) := by
      rintro ⟨hb, rfl⟩; exact hg hb hs
    have hs' : (stopCfg b c).state = some (b, q) := by simp [stopCfg, hs]
    rw [MultiTapeTM.step_of_some hs', MultiTapeTM.step_of_some hs]
    simp only [stopTM, hq, ↓reduceIte]
    rfl

/-- Stop a clean call one silent step after its certified first positive exit.

**Proof sketch.** Induct on prefixes, keeping the release flag false only at time zero; the
guard prevents an early stop; the final silent halt keeps every seam field and every emitted
bit. -/
private lemma stop_clean (C : FinTM Bool) (entry exit : C.State)
    (x arg result out : List Bool) (t : ℕ) (ht : 0 < t)
    (hg : ∀ v, 0 < v → v < t → (C.tm.runFrom
      (Cfg.ofWords (input := x) entry (stateWord C.k arg)) v).state ≠ some exit)
    (he : C.tm.runFrom (Cfg.ofWords (input := x) entry (stateWord C.k arg)) t =
      {Cfg.ofWords exit (stateWord C.k result) with output := out}) :
    (stopTM C entry exit).tm.runFrom
      (Cfg.ofWords (input := x) (false, entry) (stateWord C.k arg)) (t + 1) =
      {Cfg.ofWords (true, exit) (stateWord C.k result) with state := none, output := out} := by
  let c := Cfg.ofWords (input := x) entry (stateWord C.k arg)
  have hl := live_prefix C.tm c t
    (by rw [show C.tm.runFrom c t = _ from he]; simp [Cfg.ofWords_def])
  have hp : ∀ v, v ≤ t → (stopTM C entry exit).tm.runFrom (stopCfg false c) v =
      stopCfg (decide (v ≠ 0)) (C.tm.runFrom c v) := by
    intro v
    induction v with
    | zero => intro _; rfl
    | succ v ih =>
      intro hv
      rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega),
        stop_step C entry exit _ _ (hl v (by omega)) (by
          intro hn
          exact hg v (Nat.pos_of_ne_zero (of_decide_eq_true hn)) (by omega)),
        MultiTapeTM.runFrom_succ_eq_step']
      rfl
  have hi : Cfg.ofWords (input := x) (false, entry) (stateWord C.k arg) = stopCfg false c := rfl
  rw [hi, MultiTapeTM.runFrom_succ_eq_step', hp t (Nat.le_refl _)]
  have hflag : decide (t ≠ 0) = true := by simp [Nat.ne_of_gt ht]
  rw [hflag, show C.tm.runFrom c t = _ from he]
  rw [MultiTapeTM.step_of_some (q := (true, exit)) (by simp [stopCfg, Cfg.ofWords_def])]
  simp [stopTM, stopCfg, Cfg.ofWords_def, FinTM.controlAction_def, Action.apply_state,
    Action.apply_output, Action.apply_workTapes, Action.apply_workTapePos, Action.apply_inputPos]

/-- **The clean-module contract.** `Clean M result emit B` says: the module `M` has at least one
work tape (`0 < M.k`), and for every native input `x` and argument `arg`, the run of `M` from the
seam at its start state with `arg` as the only tape-resident word halts for the first time at
some time `t` with `0 < t ≤ B |arg|` (every configuration before `t` is live), and the
configuration at `t` is the seam holding the result word `result arg`, with output exactly
`emit arg`. -/
def Clean (M : FinTM Bool) (result emit : List Bool → List Bool) (B : ℕ → ℕ) : Prop :=
  0 < M.k ∧ ∀ x arg : List Bool, ∃ t, 0 < t ∧ t ≤ B arg.length ∧
    (∀ v < t, ¬(M.tm.runFrom (Cfg.ofWords (input := x) M.tm.q₀ (stateWord M.k arg)) v).Halted) ∧
    M.tm.runFrom (Cfg.ofWords (input := x) M.tm.q₀ (stateWord M.k arg)) t =
      {Cfg.ofWords M.tm.q₀ (stateWord M.k (result arg)) with state := none, output := emit arg}

/-- `Clean M result emit B` holds iff `0 < M.k` and, for every native input `x` and argument
`arg`, some time `t` with `0 < t ≤ B |arg|` is the first halt of `M` from the seam
`Cfg.ofWords M.tm.q₀ (stateWord M.k arg)`, at the seam holding `result arg` with output
`emit arg`. -/
theorem clean_iff (M : FinTM Bool) (result emit : List Bool → List Bool) (B : ℕ → ℕ) :
    Clean M result emit B ↔ 0 < M.k ∧ ∀ x arg : List Bool, ∃ t, 0 < t ∧ t ≤ B arg.length ∧
      (∀ v < t,
        ¬(M.tm.runFrom (Cfg.ofWords (input := x) M.tm.q₀ (stateWord M.k arg)) v).Halted) ∧
      M.tm.runFrom (Cfg.ofWords (input := x) M.tm.q₀ (stateWord M.k arg)) t =
        {Cfg.ofWords M.tm.q₀ (stateWord M.k (result arg)) with
          state := none, output := emit arg} :=
  Iff.rfl

/-- **The head envelope of a clean module** (H14's space clause): if `Clean M result emit B`,
then for every native input `x` and argument `arg`, at every time `v` of the run of `M` from the
seam at its start state holding `arg` (before, at and after its first halt), every work head is
within `B |arg|` cells of the origin, where all heads start (`Cfg.ofWords_workTapePos`).

This is the coarse envelope from the time bound: one step moves each head by at most one cell
(`Turing.MultiTapeTM.workTapePos_step_le`; over a run,
`Turing.MultiTapeTM.workTapePos_runFrom_mem_Icc`), the first halt comes at a time `t ≤ B |arg|`,
and the run is constant from `t` on. The theorem intentionally publishes this coarse
time-derived bound. A sharper one does hold: every head starts at the origin and the terminal
seam (`Cfg.ofWords`) puts it back there, so a head that reaches distance `d` spends at least
`2d ≤ t` steps going out and back, and `|position| ≤ B |arg| / 2`; that factor-two bound is not
stated here (gate 03l round 2, finding 1).

**Proof sketch.** Take the first halt `t ≤ B |arg|` of `Clean`. At a time `v ≤ t` each head is
within `v` cells of its start (`MultiTapeTM.workTapePos_runFrom_mem_Icc`); at `v > t` the run
is halted, so its configuration is the one at `t` (`MultiTapeTM.runFrom_add`,
`MultiTapeTM.runFrom_of_halt`). -/
theorem Clean.envelope {M : FinTM Bool} {result emit : List Bool → List Bool} {B : ℕ → ℕ}
    (h : Clean M result emit B) (x arg : List Bool) (v : ℕ) (j : Fin M.k) :
    |(M.tm.runFrom (Cfg.ofWords (input := x) M.tm.q₀ (stateWord M.k arg)) v).workTapePos j| ≤
      (B arg.length : ℤ) := by
  obtain ⟨t, -, htB, -, hend⟩ := ((clean_iff M result emit B).1 h).2 x arg
  have hhalt : (M.tm.runFrom (Cfg.ofWords (input := x) M.tm.q₀ (stateWord M.k arg)) t).state =
      none := by
    rw [hend]
  obtain ⟨u, hut, hu⟩ : ∃ u ≤ t,
      M.tm.runFrom (Cfg.ofWords (input := x) M.tm.q₀ (stateWord M.k arg)) v =
        M.tm.runFrom (Cfg.ofWords (input := x) M.tm.q₀ (stateWord M.k arg)) u := by
    rcases le_total v t with hvt | htv
    · exact ⟨v, hvt, rfl⟩
    · refine ⟨t, le_rfl, ?_⟩
      rw [← Nat.add_sub_of_le htv, MultiTapeTM.runFrom_add, MultiTapeTM.runFrom_of_halt _ hhalt]
  obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 (M.tm.workTapePos_runFrom_mem_Icc
    (Cfg.ofWords (input := x) M.tm.q₀ (stateWord M.k arg)) u j)
  rw [Cfg.ofWords_workTapePos] at h1 h2
  have hB : (u : ℤ) ≤ B arg.length := by exact_mod_cast hut.trans htB
  rw [hu, abs_le]
  constructor <;> omega

/-- Turn a clean-call bridge contract into the uniform first-halting form.

**Proof sketch.** The release wrapper stops one step after the positive exit (`stop_clean`);
cutting the run at its first halt (`first_halt`) keeps the whole clean configuration. -/
private lemma clean_stop (C : FinTM Bool) (entry exit : C.State)
    (result emit : List Bool → List Bool) (B : ℕ → ℕ) (hk : 0 < C.k)
    (h : ∀ x arg : List Bool, ∃ t ≤ B arg.length, 0 < t ∧
      (∀ v, 0 < v → v < t → (C.tm.runFrom
        (Cfg.ofWords (input := x) entry (stateWord C.k arg)) v).state ≠ some exit) ∧
      C.tm.runFrom (Cfg.ofWords (input := x) entry (stateWord C.k arg)) t =
        {Cfg.ofWords exit (stateWord C.k (result arg)) with output := emit arg}) :
    Clean (stopTM C entry exit) result emit (fun n => B n + 1) := by
  refine ⟨hk, fun x arg => ?_⟩
  obtain ⟨t, hb, ht, hg, he⟩ := h x arg
  have hs := stop_clean C entry exit x arg (result arg) (emit arg) t ht hg he
  obtain ⟨u, hu, hut, hguard, hend⟩ := first_halt (stopTM C entry exit).tm
    (Cfg.ofWords (input := x) (false, entry) (stateWord C.k arg)) (t + 1)
    (by simp [Cfg.ofWords_def]) (by rw [hs])
  refine ⟨u, hu, by dsimp only; omega, hguard, ?_⟩
  simpa only [stopTM, Cfg.ofWords_def] using hend.trans hs

/-- The bridge overhead `c (A (n+1)^d + n + len + 1) + 1`, with the output length
`len ≤ A (n+1)^d`, fits the single monomial `(c (2A + 1) + 1)(n+1)^{d+1}`.

**Proof sketch.** `n + 1` and both source-time terms are at most multiples of `(n+1)^{d+1}`; the
last unit, which pays for the stop, is at most `(n+1)^{d+1}`. -/
private lemma bridge_bound (c A d n len : ℕ) (hlen : len ≤ A * (n + 1) ^ d) :
    c * (A * (n + 1) ^ d + n + len + 1) + 1 ≤
      (c * (2 * A + 1) + 1) * (n + 1) ^ (d + 1) := by
  have hd := Nat.mul_le_mul_left A
    (Nat.pow_le_pow_right (Nat.succ_pos n) (show d ≤ d + 1 by omega))
  simp only [Nat.succ_eq_add_one] at hd
  have hn : n + 1 ≤ (n + 1) ^ (d + 1) := by
    simpa using Nat.pow_le_pow_right (Nat.succ_pos n) (show 1 ≤ d + 1 by omega)
  have h1 : 1 ≤ (n + 1) ^ (d + 1) := by omega
  calc
    _ ≤ c * ((2 * A + 1) * (n + 1) ^ (d + 1)) + 1 := by
      apply Nat.add_le_add_right
      apply Nat.mul_le_mul_left
      simp only [Nat.add_mul, Nat.one_mul, two_mul]
      omega
    _ ≤ c * ((2 * A + 1) * (n + 1) ^ (d + 1)) + (n + 1) ^ (d + 1) := Nat.add_le_add_left h1 _
    _ = _ := by ring

/-- **Clean install modules.** Every polynomial-time word function `f` has a clean module that
installs `f arg` as the tape-resident word and emits nothing, with a budget `A (|arg| + 1)^d`.

**Proof sketch.** `Turing.FinTM.exists_installCallTM` gives a module that exits at its first
positive visit of an exit state, within `c (T + |arg| + |f arg| + 1)` steps for the source time
`T = A (|arg|+1)^d`; the output length is at most the source time
(`Turing.MultiTapeTM.output_length_le`). The release wrapper and the first-halt cut
(`clean_stop`) give the uniform contract one step later, and `bridge_bound` puts the budget in
the form `A' (|arg| + 1)^{d+1}`. -/
theorem clean_install {f : List Bool → List Bool} (hf : PolyTimeComputable f) :
    ∃ M A d, Clean M f (fun _ => []) (fun n => A * (n + 1) ^ d) := by
  obtain ⟨F, A, d, hF⟩ := hf
  obtain ⟨C, entry, exit, c, hk, hc⟩ := FinTM.exists_installCallTM F f _ hF
  -- The bridge's result length depends on the word, so enlarge it pointwise to the source
  -- time before putting it in the uniform argument-length budget.
  have hlen (arg : List Bool) : (f arg).length ≤ A * (arg.length + 1) ^ d := by
    have ho := ((FinTM.computesInTime_iff _ _ _ _).mp (hF arg)).2
    simpa only [ho] using F.tm.output_length_le arg (A * (arg.length + 1) ^ d)
  have hstop := clean_stop C entry exit f (fun _ => [])
    (fun n => c * (A * (n + 1) ^ d + n + A * (n + 1) ^ d + 1)) hk (by
      intro x arg
      obtain ⟨t, ht, hp, hg, he⟩ := hc x arg
      refine ⟨t, ht.trans (Nat.mul_le_mul_left c (by have := hlen arg; omega)), hp, hg, ?_⟩
      exact he)
  refine ⟨stopTM C entry exit, c * (2 * A + 1) + 1, d + 1, hk, fun x arg => ?_⟩
  obtain ⟨t, hp, ht, hg, he⟩ := hstop.2 x arg
  exact ⟨t, hp, ht.trans (bridge_bound c A d arg.length _ (Nat.le_refl _)), hg, he⟩

/-- **Clean emit modules.** Every polynomial-time word function `f` has a clean module that
keeps its argument as the tape-resident word and emits exactly `f arg`, with a budget
`A (|arg| + 1)^d`.

**Proof sketch.** As `clean_install`, from `Turing.FinTM.exists_emitCallTM`. -/
theorem clean_emit {f : List Bool → List Bool} (hf : PolyTimeComputable f) :
    ∃ M A d, Clean M id f (fun n => A * (n + 1) ^ d) := by
  obtain ⟨F, A, d, hF⟩ := hf
  obtain ⟨C, entry, exit, c, hk, hc⟩ := FinTM.exists_emitCallTM F f _ hF
  have hlen (arg : List Bool) : (f arg).length ≤ A * (arg.length + 1) ^ d := by
    have ho := ((FinTM.computesInTime_iff _ _ _ _).mp (hF arg)).2
    simpa only [ho] using F.tm.output_length_le arg (A * (arg.length + 1) ^ d)
  have hstop := clean_stop C entry exit id f
    (fun n => c * (A * (n + 1) ^ d + n + A * (n + 1) ^ d + 1)) hk (by
      intro x arg
      obtain ⟨t, ht, hp, hg, he⟩ := hc x arg
      exact ⟨t, ht.trans (Nat.mul_le_mul_left c (by have := hlen arg; omega)), hp, hg, he⟩)
  refine ⟨stopTM C entry exit, c * (2 * A + 1) + 1, d + 1, hk, fun x arg => ?_⟩
  obtain ⟨t, hp, ht, hg, he⟩ := hstop.2 x arg
  exact ⟨t, hp, ht.trans (bridge_bound c A d arg.length _ (Nat.le_refl _)), hg, he⟩

/-- **A common budget.** A polynomial budget `A (m + 1)^d` on a request of length `m` with
`m + 1 ≤ N` is at most `A N^D` for every `D ≥ d` (monotonicity of powers, `0 < N`). -/
theorem request_budget (A d D N m : ℕ) (hd : d ≤ D) (hm : m + 1 ≤ N) :
    A * (m + 1) ^ d ≤ A * N ^ D := by
  apply Nat.mul_le_mul_left
  exact (Nat.pow_le_pow_left hm d).trans (Nat.pow_le_pow_right (by omega) hd)

/-! ### Padding a module into the shared tape bank -/

/-- Pad an action to a larger tape count, keeping the extra tapes stationary. -/
private def padAction {k K : ℕ} {S : Type} (a : Action k Bool S) : Action K Bool S :=
  ⟨a.inputTape, fun i => if h : i.val < k then a.workTapes ⟨i.val, h⟩ else (none, 0),
    a.output, a.state⟩

/-- A module padded into a shared bank of `K` tapes; all modules share tape zero. -/
private def padTM (M : FinTM Bool) (K : ℕ) (hk : M.k ≤ K) : FinTM Bool where
  k := K
  State := M.State
  tm := { q₀ := M.tm.q₀
          tr := fun q inp work => padAction (M.tm.tr q inp
            (fun i => work ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩)) }

/-- The configuration embedding for the shared bank: the padding tapes are blank, with their
heads at the origin. -/
private def padCfg {k K : ℕ} {S : Type} {x : List Bool}
    (c : Cfg k Bool S x) : Cfg K Bool S x :=
  ⟨c.state, c.inputPos,
    fun i => if h : i.val < k then c.workTapes ⟨i.val, h⟩ else fun _ => none,
    fun i => if h : i.val < k then c.workTapePos ⟨i.val, h⟩ else 0, c.output⟩

/-- Padding commutes with applying an action (the inactive tapes neither write nor move). -/
private lemma pad_apply {k K : ℕ} {S : Type} {x : List Bool}
    (a : Action k Bool S) (c : Cfg k Bool S x) :
    (padAction (K := K) a).apply (padCfg c) = padCfg (a.apply c) := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · funext i z
    by_cases h : i.val < k <;> simp [padAction, padCfg, Action.apply_state, Action.apply_output,
        Action.apply_workTapes, Action.apply_workTapePos, Action.apply_inputPos, h]
  · funext i
    by_cases h : i.val < k <;> simp [padAction, padCfg, Action.apply_state, Action.apply_output,
        Action.apply_workTapes, Action.apply_workTapePos, Action.apply_inputPos, h]

/-- The padded module runs in lockstep with the module. -/
private lemma pad_run (M : FinTM Bool) (K : ℕ) (hk : M.k ≤ K)
    {x : List Bool} (c : Cfg M.k Bool M.State x) (t : ℕ) :
    (padTM M K hk).tm.runFrom (padCfg c) t = padCfg (M.tm.runFrom c t) := by
  apply MultiTapeTM.runFrom_comm_of_step
  intro c
  cases hs : c.state with
  | none =>
    have hs' : (padCfg (K := K) c).state = none := hs
    rw [MultiTapeTM.step_of_halt hs', MultiTapeTM.step_of_halt hs]
  | some q =>
    have hw : (fun i : Fin M.k => (padCfg (K := K) c).workTapeSymbols
        ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩) = c.workTapeSymbols := by
      funext i; simp [padCfg, Cfg.workTapeSymbols_eq, i.isLt]
    have hstate : (padCfg (K := K) c).state = some q := hs
    rw [MultiTapeTM.step_of_some hstate, MultiTapeTM.step_of_some hs]
    change (padAction (M.tm.tr q c.inputSymbol _)).apply _ = _
    rw [hw]
    exact pad_apply _ _

/-- With a positive tape count, padding a seam gives the seam with the same state word. -/
private lemma pad_seam {k K : ℕ} {S : Type} {x : List Bool}
    (hk : 0 < k) (q : S) (w out : List Bool) :
    padCfg (K := K) ({Cfg.ofWords (input := x) q (stateWord k w) with output := out}) =
      {Cfg.ofWords (input := x) q (stateWord K w) with output := out} := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · funext i z
    by_cases hi : i.val < k
    · simp [padCfg, Cfg.ofWords_def, stateWord_eq, hi]
    · have hn : i.val ≠ 0 := by omega
      simp [padCfg, Cfg.ofWords_def, stateWord_eq, hi, hn, FinTM.bufferTape_eq]
  · funext i
    simp [padCfg, Cfg.ofWords_def]

/-! ### The host -/

/-- The states of the host over the modules `M : Fin n → FinTM Bool` with control states `C`:
`C ⊕ Σ i, (M i).State`, a control state or module `i` in one of its states. -/
abbrev State (C : Type) {n : ℕ} (M : Fin n → FinTM Bool) : Type :=
  C ⊕ Σ i, (M i).State

/-- The host's state type is `C ⊕ Σ i, (M i).State`. -/
theorem state_eq (C : Type) {n : ℕ} (M : Fin n → FinTM Bool) :
    State C M = (C ⊕ Σ i, (M i).State) :=
  rfl

/-- The entry state of module `i` inside the host: module `i` at its start state. -/
def entry {C : Type} {n : ℕ} (M : Fin n → FinTM Bool) (i : Fin n) : State C M :=
  .inr ⟨i, (M i).tm.q₀⟩

/-- The entry state of module `i` is `inr ⟨i, (M i).tm.q₀⟩`. -/
theorem entry_eq {C : Type} {n : ℕ} (M : Fin n → FinTM Bool) (i : Fin n) :
    entry (C := C) M i = .inr ⟨i, (M i).tm.q₀⟩ :=
  rfl

/-- **The clean-module host** over the modules `M : Fin n → FinTM Bool`: a finite machine with
`K` work tapes (`hk`: every module fits, all modules sharing tape 0), states `State C M`, start
state `q₀`. At a control state `inl c` it applies the consumer's table `ctrl c`; at a module
state `inr ⟨i, s⟩` it applies module `i`'s transition, padded to the `K` tapes and forwarded by
`Turing.emitAction`: the module's emission is the host's, a live successor stays in module `i`,
and a halt passes control to the return state `ret i`. -/
@[simps (config := { isSimp := false }) k tm_q₀]
def hostTM {C : Type} [Fintype C] [DecidableEq C] {n : ℕ} (M : Fin n → FinTM Bool) (K : ℕ)
    (hk : ∀ i, (M i).k ≤ K)
    (ctrl : C → Option Bool → (Fin K → Option Bool) → Action K Bool (State C M))
    (ret : Fin n → State C M) (q₀ : State C M) : FinTM Bool where
  k := K
  State := State C M
  tm := {
    q₀ := q₀
    tr := fun q inp work => match q with
      | .inl c => ctrl c inp work
      | .inr ⟨i, s⟩ => emitAction (fun s => .inr ⟨i, s⟩) (ret i)
          ((padTM (M i) K (hk i)).tm.tr s inp work) }

/-- **A control step.** At a configuration in the control state `inl c`, one step of the host
applies the consumer's action `ctrl c` for the scanned input and work symbols. -/
theorem hostTM_step_inl {C : Type} [Fintype C] [DecidableEq C] {n : ℕ}
    (M : Fin n → FinTM Bool) (K : ℕ) (hk : ∀ i, (M i).k ≤ K)
    (ctrl : C → Option Bool → (Fin K → Option Bool) → Action K Bool (State C M))
    (ret : Fin n → State C M) (q₀ : State C M) {x : List Bool}
    (cfg : Cfg K Bool (State C M) x) (c : C) (hc : cfg.state = some (.inl c)) :
    (hostTM M K hk ctrl ret q₀).tm.step cfg =
      (ctrl c cfg.inputSymbol cfg.workTapeSymbols).apply cfg :=
  MultiTapeTM.step_of_some hc

/-- Forwarding a padded clean seam produces the host's seam with the supplied output prefix (a
positive tape count identifies the tape-zero word). -/
private lemma host_seam {C : Type} {n : ℕ} (M : Fin n → FinTM Bool) (K : ℕ)
    (ret : Fin n → State C M) (i : Fin n)
    (hp : 0 < (M i).k) (x w pre out : List Bool) (q : (M i).State)
    (state : Option (M i).State) :
    emitCfg (fun s => (Sum.inr ⟨i, s⟩ : State C M)) (ret i) pre
      (padCfg (K := K) {Cfg.ofWords (input := x) q (stateWord (M i).k w)
        with state := state, output := out}) =
      {Cfg.ofWords (((state.map (fun s => (Sum.inr ⟨i, s⟩ : State C M))).getD (ret i)))
        (stateWord K w) with output := pre ++ out} := by
  have h := pad_seam (K := K) (x := x) hp q w out
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · exact congrArg (fun c : Cfg K Bool (M i).State x => c.workTapes) h
  · exact congrArg (fun c : Cfg K Bool (M i).State x => c.workTapePos) h

/-- **A module call inside the host.** Suppose module `i` (with `0 < (M i).k`), run from the seam
at its start state with argument `arg`, is live before time `t` and at time `t` is halted at the
seam holding `result`, with output `out`. Then the host, run from its seam at the entry state of
module `i` holding `arg` with output prefix `pre`, visits no control state before time `t`, and
at time `t` is at the seam in the return state `ret i` holding `result`, with output
`pre ++ out`.

**Proof sketch.** The host seam is the forwarded image (`Turing.emitCfg`) of the padded module
seam (`host_seam`). The module's live run is transferred to the padded machine (`pad_run`) and
then to the host by `Turing.emit_run`, whose agreement hypothesis holds by the definition of
`hostTM`. Every live configuration of the module has a state in module `i`'s summand, hence is
not a control state; the halting endpoint is the forwarded image of the module's terminal seam,
i.e. the host seam at `ret i` (`host_seam` again). -/
theorem host_call {C : Type} [Fintype C] [DecidableEq C] {n : ℕ} (M : Fin n → FinTM Bool)
    (K : ℕ) (hk : ∀ i, (M i).k ≤ K)
    (ctrl : C → Option Bool → (Fin K → Option Bool) → Action K Bool (State C M))
    (ret : Fin n → State C M) (q₀ : State C M)
    (i : Fin n) (hp : 0 < (M i).k) (x arg result out pre : List Bool)
    (q : (M i).State) (t : ℕ)
    (hg : ∀ v < t, ¬((M i).tm.runFrom
      (Cfg.ofWords (input := x) (M i).tm.q₀ (stateWord (M i).k arg)) v).Halted)
    (he : (M i).tm.runFrom
      (Cfg.ofWords (input := x) (M i).tm.q₀ (stateWord (M i).k arg)) t =
      {Cfg.ofWords q (stateWord (M i).k result) with state := none, output := out}) :
    (∀ v < t, ∀ c : C, ((hostTM M K hk ctrl ret q₀).tm.runFrom
      {Cfg.ofWords (input := x) (entry M i) (stateWord K arg) with output := pre} v).state
        ≠ some (.inl c)) ∧
    (hostTM M K hk ctrl ret q₀).tm.runFrom
      {Cfg.ofWords (input := x) (entry M i) (stateWord K arg) with output := pre} t =
      {Cfg.ofWords (ret i) (stateWord K result) with output := pre ++ out} := by
  let c := Cfg.ofWords (input := x) (M i).tm.q₀ (stateWord (M i).k arg)
  let emb : (M i).State → State C M := fun s => .inr ⟨i, s⟩
  have hinit : emitCfg emb (ret i) pre (padCfg (K := K) c) =
      {Cfg.ofWords (input := x) (entry M i) (stateWord K arg) with output := pre} := by
    simpa [emb, c, entry] using
      host_seam M K ret i hp x arg pre [] (M i).tm.q₀ (some (M i).tm.q₀)
  have hrun (v : ℕ) (hv : v ≤ t) :
      (hostTM M K hk ctrl ret q₀).tm.runFrom
        {Cfg.ofWords (input := x) (entry M i) (stateWord K arg) with output := pre} v =
        emitCfg emb (ret i) pre (padCfg ((M i).tm.runFrom c v)) := by
    rw [← hinit]
    rw [emit_run (padTM (M i) K (hk i)).tm (hostTM M K hk ctrl ret q₀).tm emb (ret i)
      (by intros; rfl) pre _ v (by
        intro u hu
        rw [pad_run]
        exact hg u (by omega))]
    rw [pad_run]
  constructor
  · intro v hv a
    rw [hrun v (Nat.le_of_lt hv)]
    have hl := hg v hv
    cases hs : ((M i).tm.runFrom c v).state with
    | none => exact False.elim (hl hs)
    | some s => simp [emitCfg_state, padCfg, hs, emb]
  · rw [hrun t (Nat.le_refl _), show (M i).tm.runFrom c t = _ from he]
    exact host_seam M K ret i hp x result pre out q none

/-- **The head envelope of a host call** (H14's space clause for one call, inclusive of its
endpoint): run from its seam at the entry state of module `i` holding `arg` with output prefix
`pre`, the host has, at every time `v ≤ t`, every work head within `t` cells of the origin,
where all heads start (`Cfg.ofWords_workTapePos`). Under the hypotheses of `host_call`, `t` is
the duration of the call, so this bounds the heads throughout the call.

This is the coarse envelope from the time bound: one step moves each head by at most one cell
(`Turing.MultiTapeTM.workTapePos_step_le`; over a run,
`Turing.MultiTapeTM.workTapePos_runFrom_mem_Icc`). A sharper envelope follows from the proof of
`host_call` and is not stated here: before the return, the host's tape `j` is module `i`'s
tape `j` for `j < (M i).k` (the padded module runs in lockstep and the forwarding keeps every
physical field, `Turing.emit_run`), and every other tape stays blank with its head at the
origin, so the host's heads obey any head envelope of the module.

**Proof sketch.** `MultiTapeTM.workTapePos_runFrom_mem_Icc` from the host seam, whose heads are
at the origin, and `v ≤ t`. -/
theorem host_call_envelope {C : Type} [Fintype C] [DecidableEq C] {n : ℕ}
    (M : Fin n → FinTM Bool) (K : ℕ) (hk : ∀ i, (M i).k ≤ K)
    (ctrl : C → Option Bool → (Fin K → Option Bool) → Action K Bool (State C M))
    (ret : Fin n → State C M) (q₀ : State C M) (i : Fin n) (x arg pre : List Bool) (t : ℕ) :
    ∀ v ≤ t, ∀ j : Fin K, |((hostTM M K hk ctrl ret q₀).tm.runFrom
      {Cfg.ofWords (input := x) (entry M i) (stateWord K arg) with output := pre} v).workTapePos
        j| ≤ (t : ℤ) := by
  intro v hv j
  have key : ∀ c : Cfg K Bool (State C M) x, c.workTapePos j = 0 →
      |((hostTM M K hk ctrl ret q₀).tm.runFrom c v).workTapePos j| ≤ (t : ℤ) := by
    intro c hc
    obtain ⟨h1, h2⟩ :=
      Finset.mem_Icc.1 ((hostTM M K hk ctrl ret q₀).tm.workTapePos_runFrom_mem_Icc c v j)
    rw [hc] at h1 h2
    have hvt : (v : ℤ) ≤ t := by exact_mod_cast hv
    rw [abs_le]
    constructor <;> omega
  exact key {Cfg.ofWords (input := x) (entry M i) (stateWord K arg) with output := pre}
    (Cfg.ofWords_workTapePos (input := x) (entry (C := C) M i) (stateWord K arg) j)

/-- **Chaining guarded segments.** If the run from `c` avoids the state `anchor` before time `a`
and is at `d` at time `a`, and the run from `d` avoids `anchor` before time `b`, then the run
from `c` avoids `anchor` before time `a + b`. -/
theorem guard_add {k : ℕ} {S : Type} {x : List Bool}
    (tm : MultiTapeTM k Bool S) (anchor : S) (c d : Cfg k Bool S x) (a b : ℕ)
    (ha : ∀ v < a, (tm.runFrom c v).state ≠ some anchor)
    (he : tm.runFrom c a = d)
    (hb : ∀ v < b, (tm.runFrom d v).state ≠ some anchor) :
    ∀ v < a + b, (tm.runFrom c v).state ≠ some anchor := by
  intro v hv
  by_cases h : v < a
  · exact ha v h
  · have hva : a ≤ v := by omega
    rw [← Nat.add_sub_of_le hva, MultiTapeTM.runFrom_add, he]
    exact hb (v - a) (by omega)

/-- **A clean module call inside the host.** If module `i` is `Clean` with result map `f`,
emitted chunk `g` and budget `B`, then for every native input `x`, argument `arg` and output
prefix `pre`, the host, run from its seam at the entry state of module `i` holding `arg` with
output `pre`, reaches at some time `t` with `0 < t ≤ B |arg|` the seam in the return state
`ret i` holding `f arg`, with output `pre ++ g arg`, and visits no control state before `t`.

**Proof sketch.** Unfold `Clean` for `x` and `arg` and apply `host_call` with the result word
`f arg` and the output `g arg`. -/
theorem host_clean {C : Type} [Fintype C] [DecidableEq C] {n : ℕ} (M : Fin n → FinTM Bool)
    (K : ℕ) (hk : ∀ i, (M i).k ≤ K)
    (ctrl : C → Option Bool → (Fin K → Option Bool) → Action K Bool (State C M))
    (ret : Fin n → State C M) (q₀ : State C M)
    (i : Fin n) (f g : List Bool → List Bool) (B : ℕ → ℕ)
    (h : Clean (M i) f g B) (x arg pre : List Bool) :
    ∃ t, 0 < t ∧ t ≤ B arg.length ∧
      (∀ v < t, ∀ c : C, ((hostTM M K hk ctrl ret q₀).tm.runFrom
        {Cfg.ofWords (input := x) (entry M i) (stateWord K arg) with output := pre} v).state
          ≠ some (.inl c)) ∧
      (hostTM M K hk ctrl ret q₀).tm.runFrom
        {Cfg.ofWords (input := x) (entry M i) (stateWord K arg) with output := pre} t =
        {Cfg.ofWords (ret i) (stateWord K (f arg)) with output := pre ++ g arg} := by
  obtain ⟨t, hp, ht, hg, he⟩ := h.2 x arg
  obtain ⟨hguard, hend⟩ :=
    host_call M K hk ctrl ret q₀ i h.1 x arg (f arg) (g arg) pre (M i).tm.q₀ t hg he
  exact ⟨t, hp, ht, hguard, hend⟩

/-- **A clean module call inside the host, with its head envelope** (the bounded call of
`host_clean` together with H14's space clause): if module `i` is `Clean` with result map `f`,
emitted chunk `g` and budget `B`, then for every native input `x`, argument `arg` and output
prefix `pre`, the host, run from its seam at the entry state of module `i` holding `arg` with
output `pre`, reaches at some time `t` with `0 < t ≤ B |arg|` the seam in the return state
`ret i` holding `f arg`, with output `pre ++ g arg`, visits no control state before `t`, and at
every time `v ≤ t` has every work head within `B |arg|` cells of the origin.

The envelope is the coarse one from the time bound (`host_call_envelope`, which also describes
the sharper envelope inherited from the module).

**Proof sketch.** `host_clean` gives `t` and the call; `host_call_envelope` at `t`, with
`t ≤ B |arg|`, gives the envelope. -/
theorem host_clean_envelope {C : Type} [Fintype C] [DecidableEq C] {n : ℕ}
    (M : Fin n → FinTM Bool) (K : ℕ) (hk : ∀ i, (M i).k ≤ K)
    (ctrl : C → Option Bool → (Fin K → Option Bool) → Action K Bool (State C M))
    (ret : Fin n → State C M) (q₀ : State C M)
    (i : Fin n) (f g : List Bool → List Bool) (B : ℕ → ℕ)
    (h : Clean (M i) f g B) (x arg pre : List Bool) :
    ∃ t, 0 < t ∧ t ≤ B arg.length ∧
      (∀ v < t, ∀ c : C, ((hostTM M K hk ctrl ret q₀).tm.runFrom
        {Cfg.ofWords (input := x) (entry M i) (stateWord K arg) with output := pre} v).state
          ≠ some (.inl c)) ∧
      (hostTM M K hk ctrl ret q₀).tm.runFrom
        {Cfg.ofWords (input := x) (entry M i) (stateWord K arg) with output := pre} t =
        {Cfg.ofWords (ret i) (stateWord K (f arg)) with output := pre ++ g arg} ∧
      ∀ v ≤ t, ∀ j : Fin K, |((hostTM M K hk ctrl ret q₀).tm.runFrom
        {Cfg.ofWords (input := x) (entry M i) (stateWord K arg) with output := pre}
          v).workTapePos j| ≤ (B arg.length : ℤ) := by
  obtain ⟨t, hp, ht, hguard, hend⟩ := host_clean M K hk ctrl ret q₀ i f g B h x arg pre
  refine ⟨t, hp, ht, hguard, hend, fun v hv j => ?_⟩
  have hB : (t : ℤ) ≤ B arg.length := by exact_mod_cast ht
  exact (host_call_envelope M K hk ctrl ret q₀ i x arg pre t v hv j).trans hB

/-! ### The typed view of the host

A consumer that does not unfold `hostTM` cannot see that its tape count is `K` and its state
type is `State C M`, so it cannot type the host's seam configurations. The typed view
`hostTMView` names both fields explicitly and keeps the host's machine; the readers below
restate the host's contracts for it, each proved by the original contract. -/

/-- **The typed view of the host**: the finite machine with `K` work tapes, state type
`State C M` and the underlying machine of `hostTM M K hk ctrl ret q₀`,
`hostTMView M K hk ctrl ret q₀ = ⟨K, State C M, (hostTM M K hk ctrl ret q₀).tm⟩`. It is the host
itself (`hostTMView_eq`), with its tape count and state type explicit. -/
abbrev hostTMView {C : Type} [Fintype C] [DecidableEq C] {n : ℕ}
    (M : Fin n → FinTM Bool) (K : ℕ) (hk : ∀ i, (M i).k ≤ K)
    (ctrl : C → Option Bool → (Fin K → Option Bool) → Action K Bool (State C M))
    (ret : Fin n → State C M) (q₀ : State C M) : FinTM Bool where
  k := K
  State := State C M
  tm := (hostTM M K hk ctrl ret q₀).tm

/-- The typed view is the host: `hostTMView M K hk ctrl ret q₀ = hostTM M K hk ctrl ret q₀`. -/
theorem hostTMView_eq {C : Type} [Fintype C] [DecidableEq C] {n : ℕ}
    (M : Fin n → FinTM Bool) (K : ℕ) (hk : ∀ i, (M i).k ≤ K)
    (ctrl : C → Option Bool → (Fin K → Option Bool) → Action K Bool (State C M))
    (ret : Fin n → State C M) (q₀ : State C M) :
    hostTMView M K hk ctrl ret q₀ = hostTM M K hk ctrl ret q₀ :=
  rfl

/-- The typed view starts in the supplied start state:
`(hostTMView M K hk ctrl ret q₀).tm.q₀ = q₀`. -/
theorem hostTMView_q₀ {C : Type} [Fintype C] [DecidableEq C] {n : ℕ}
    (M : Fin n → FinTM Bool) (K : ℕ) (hk : ∀ i, (M i).k ≤ K)
    (ctrl : C → Option Bool → (Fin K → Option Bool) → Action K Bool (State C M))
    (ret : Fin n → State C M) (q₀ : State C M) :
    (hostTMView M K hk ctrl ret q₀).tm.q₀ = q₀ :=
  rfl

/-- **A control step of the typed view** (`hostTM_step_inl` for `hostTMView`): at a
configuration in the control state `inl c`, one step applies the consumer's action,
`(hostTMView M K hk ctrl ret q₀).tm.step cfg = (ctrl c cfg.inputSymbol cfg.workTapeSymbols).apply
cfg`. -/
theorem hostTMView_step_inl {C : Type} [Fintype C] [DecidableEq C] {n : ℕ}
    (M : Fin n → FinTM Bool) (K : ℕ) (hk : ∀ i, (M i).k ≤ K)
    (ctrl : C → Option Bool → (Fin K → Option Bool) → Action K Bool (State C M))
    (ret : Fin n → State C M) (q₀ : State C M) {x : List Bool}
    (cfg : Cfg K Bool (State C M) x) (c : C) (hc : cfg.state = some (.inl c)) :
    (hostTMView M K hk ctrl ret q₀).tm.step cfg =
      (ctrl c cfg.inputSymbol cfg.workTapeSymbols).apply cfg :=
  hostTM_step_inl M K hk ctrl ret q₀ cfg c hc

/-- **A module call inside the typed view** (`host_call` for `hostTMView`): if module `i` (with
`0 < (M i).k`), run from the seam at its start state with argument `arg`, is live before time
`t` and at time `t` is halted at the seam holding `result` with output `out`, then the typed
view, run from its seam at the entry state of module `i` holding `arg` with output prefix `pre`,
visits no control state before `t`, and
`(hostTMView M K hk ctrl ret q₀).tm.runFrom {Cfg.ofWords (entry M i) (stateWord K arg) with
output := pre} t = {Cfg.ofWords (ret i) (stateWord K result) with output := pre ++ out}`. -/
theorem host_call_view {C : Type} [Fintype C] [DecidableEq C] {n : ℕ} (M : Fin n → FinTM Bool)
    (K : ℕ) (hk : ∀ i, (M i).k ≤ K)
    (ctrl : C → Option Bool → (Fin K → Option Bool) → Action K Bool (State C M))
    (ret : Fin n → State C M) (q₀ : State C M)
    (i : Fin n) (hp : 0 < (M i).k) (x arg result out pre : List Bool)
    (q : (M i).State) (t : ℕ)
    (hg : ∀ v < t, ¬((M i).tm.runFrom
      (Cfg.ofWords (input := x) (M i).tm.q₀ (stateWord (M i).k arg)) v).Halted)
    (he : (M i).tm.runFrom
      (Cfg.ofWords (input := x) (M i).tm.q₀ (stateWord (M i).k arg)) t =
      {Cfg.ofWords q (stateWord (M i).k result) with state := none, output := out}) :
    (∀ v < t, ∀ c : C, ((hostTMView M K hk ctrl ret q₀).tm.runFrom
      {Cfg.ofWords (input := x) (entry M i) (stateWord K arg) with output := pre} v).state
        ≠ some (.inl c)) ∧
    (hostTMView M K hk ctrl ret q₀).tm.runFrom
      {Cfg.ofWords (input := x) (entry M i) (stateWord K arg) with output := pre} t =
      {Cfg.ofWords (ret i) (stateWord K result) with output := pre ++ out} :=
  host_call M K hk ctrl ret q₀ i hp x arg result out pre q t hg he

/-- **A clean module call inside the typed view** (`host_clean` for `hostTMView`): if module `i`
is `Clean` with result map `f`, emitted chunk `g` and budget `B`, then the typed view, run from
its seam at the entry state of module `i` holding `arg` with output `pre`, reaches at some time
`t` with `0 < t ≤ B |arg|` the seam in the return state `ret i` holding `f arg`, with output
`pre ++ g arg`, and visits no control state before `t`. -/
theorem host_clean_view {C : Type} [Fintype C] [DecidableEq C] {n : ℕ}
    (M : Fin n → FinTM Bool) (K : ℕ) (hk : ∀ i, (M i).k ≤ K)
    (ctrl : C → Option Bool → (Fin K → Option Bool) → Action K Bool (State C M))
    (ret : Fin n → State C M) (q₀ : State C M)
    (i : Fin n) (f g : List Bool → List Bool) (B : ℕ → ℕ)
    (h : Clean (M i) f g B) (x arg pre : List Bool) :
    ∃ t, 0 < t ∧ t ≤ B arg.length ∧
      (∀ v < t, ∀ c : C, ((hostTMView M K hk ctrl ret q₀).tm.runFrom
        {Cfg.ofWords (input := x) (entry M i) (stateWord K arg) with output := pre} v).state
          ≠ some (.inl c)) ∧
      (hostTMView M K hk ctrl ret q₀).tm.runFrom
        {Cfg.ofWords (input := x) (entry M i) (stateWord K arg) with output := pre} t =
        {Cfg.ofWords (ret i) (stateWord K (f arg)) with output := pre ++ g arg} :=
  host_clean M K hk ctrl ret q₀ i f g B h x arg pre

end Turing.ModuleHost

## ===== TCSlib/Complexity/Randomized/Build/IterateFindHost.lean (Lean, TS1 tree 1eaf940b938bb52e3919f5569893b58522df599b) =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import Mathlib.Tactic.Ring
import TCSlib.Complexity.TuringMachine.Build.ModuleHost

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The host of the repetition machine

The repetition machine's instance of the clean-module host `Turing.ModuleHost.hostTM`
(`TCSlib.Complexity.TuringMachine.Build.ModuleHost`, host H14 of `machine-library-design.md` §14),
for `Complexity.polyTimeComputable_iterateFind` (`TCSlib.Complexity.Randomized.Build.IterateFind`
assembles the machine; the theorem itself lives in `TCSlib.Complexity.Randomized.Repetition`, the
load-bearing lemma of the Pass–shelat campaign, foundation decision D11 of
`PassShelatChapter2-4Plan.md`). Nothing here mentions the repetition lemma's data.

## Construction (DESIGN.md §2.6, steps 2–5, as built; see its as-built erratum)

* **The copier.** A one-tape, two-state machine (`copyTM`) writes the native input on tape 0 and
  returns both heads (`copy_clean`): the startup module of the loop body, since a clean call sees
  only its tape-resident argument. It re-derives, as a parallel routine and not a copy, the input
  copier of the private emit-iteration body `TCSlib.Complexity.TuringMachine.Build.EmitIterBody`.
* **The host.** Five modules (copier, startup install, verdict install, step install, payload
  emit) run in the clean-module host with three control states (`hostTM`): the loop **anchor**
  `inl 0` (never a module-internal state, the panel repair J2-16/J3-6), which dispatches into the
  verdict module (`host_dispatch`); the **branch** `inl 1`, which reads the first cell of tape 0
  and dispatches into the payload or the step module (`host_branch`); and the **halt** state
  `inl 2` (`host_halt`). Each module's halt passes control to its fixed return state (`hostRet`).
  Module calls inside the host are `Turing.ModuleHost.host_call` and `host_clean`.

## Main definitions

* `Complexity.IterateFind.copyTM` — the input copier; `copyTMView`, the copier with its tape
  count, state type and start state explicit (`copyTMView_eq`).
* `Complexity.IterateFind.hostCtrl`, `hostRet`, `hostTM` — the host's control table over its
  three control states, the return states of the five modules, and the host.

## Main results

* `Complexity.IterateFind.copy_clean` — the copier's contract; `copy_clean_view`, the same for
  `copyTMView`.
* `Complexity.IterateFind.host_dispatch`, `host_branch`, `host_halt` — the host's control steps.
* `Complexity.IterateFind.host_dispatch_view`, `host_branch_view`, `host_halt_view` — the same
  control steps for the typed view `Turing.ModuleHost.hostTMView`.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (Algorithm 38.5 and Theorem 35.1: the repeated-adversary machine this host realizes.)
* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.2–1.3, time-bounded multi-tape machines.)
-/

namespace Complexity.IterateFind

open Turing

/-! ### The input copier -/

/-- The input copier: a one-tape, two-state machine that writes the native input on tape 0
and returns both heads to their seam positions. State `0` copies (read a bit, write it,
advance both heads; at the right blank move both heads left into state `1`); state `1`
walks both heads left while the input head reads a bit, and at the left blank moves both
heads right and halts. -/
@[simps (config := { isSimp := false }) k]
def copyTM : FinTM Bool where
  k := 1
  State := Fin 2
  tm := { q₀ := 0
          tr := fun q inp _ =>
            if q = 0 then
              match inp with
              | some b => ⟨.pos, fun _ => (some (some b), .pos), none, some 0⟩
              | none => ⟨.neg, fun _ => (none, .neg), none, some 1⟩
            else
              match inp with
              | some _ => ⟨.neg, fun _ => (none, .neg), none, some 1⟩
              | none => ⟨.pos, fun _ => (none, .pos), none, none⟩ }

/-- Configurations of the copier: control `q`, input head at position `i`, tape 0 holding
`w` from the origin with its head at cell `z`, nothing emitted. -/
private def copyCfg (x : List Bool) (q : Option (Fin 2)) (i : ℕ) (hi : i < x.length + 2)
    (w : List Bool) (z : ℤ) : Cfg 1 Bool (Fin 2) x :=
  ⟨q, ⟨i, hi⟩, fun _ => FinTM.bufferTape w, fun _ => z, []⟩

/-- One copying step: bit `j` is read, written at cell `j`, and both heads advance.

**Proof sketch.** The input head at position `j + 1` reads `x[j]` (`inputSymbolInner`); the
action writes it at cell `j`, which turns `bufferTape (x.take j)` into
`bufferTape (x.take (j + 1))` (`List.take_succ_eq_append_getElem`, `bufferTape_append`), and
both heads move right (`moveInputPos_pos_of_ne_right`). -/
private lemma copy_step (x : List Bool) (j : ℕ) (hj : j < x.length) :
    copyTM.tm.step (copyCfg x (some 0) (j + 1) (by omega) (x.take j) j) =
      copyCfg x (some 0) (j + 1 + 1) (by omega) (x.take (j + 1)) ((j + 1 : ℕ) : ℤ) := by
  have hsym : (copyCfg x (some 0) (j + 1) (by omega) (x.take j) j).inputSymbol = some x[j] :=
    inputSymbolInner j (by simp [copyCfg]; omega) hj
  have hs : (copyCfg x (some 0) (j + 1) (by omega) (x.take j) j).state = some 0 := rfl
  unfold MultiTapeTM.step
  rw [hs]
  dsimp only
  rw [hsym]
  show (⟨.pos, fun _ => (some (some x[j]), .pos), none, some 0⟩ :
    Action 1 Bool (Fin 2)).apply _ = _
  refine Cfg.ext rfl ?_ ?_ ?_ rfl
  · apply Fin.ext
    simp only [Action.apply, copyCfg]
    rw [moveInputPos_pos_of_ne_right _ (by simp; omega)]
  · funext i
    simp only [Action.apply, copyCfg]
    rw [List.take_succ_eq_append_getElem hj, FinTM.bufferTape_append, List.length_take,
      Nat.min_eq_left hj.le]
  · funext i
    simp [Action.apply, copyCfg]

/-- At the right blank the copier turns: both heads move left and the control becomes `1`.

**Proof sketch.** At position `|x| + 1` the input symbol is the right blank
(`inputSymbol_at`); the action writes nothing, moves the input head left
(`moveInputPos_neg_val`) and the work head to `|x| - 1`. -/
private lemma copy_turn (x : List Bool) :
    copyTM.tm.step (copyCfg x (some 0) (x.length + 1) (by omega) x x.length) =
      copyCfg x (some 1) x.length (by omega) x (x.length - 1) := by
  have hsym : (copyCfg x (some 0) (x.length + 1) (by omega) x x.length).inputSymbol = none := by
    rw [FinTM.inputSymbol_at _ x.length le_rfl rfl]
    simp
  have hs : (copyCfg x (some 0) (x.length + 1) (by omega) x x.length).state = some 0 := rfl
  unfold MultiTapeTM.step
  rw [hs]
  dsimp only
  rw [hsym]
  show (⟨.neg, fun _ => (none, .neg), none, some 1⟩ : Action 1 Bool (Fin 2)).apply _ = _
  refine Cfg.ext rfl ?_ ?_ ?_ rfl
  · apply Fin.ext
    simp only [Action.apply, copyCfg]
    rw [FinTM.moveInputPos_neg_val]
    simp
  · funext i
    simp [Action.apply, copyCfg]
  · funext i
    simp [Action.apply, copyCfg, sub_eq_add_neg]

/-- The rewind: from input position `p ≤ |x|` in control `1`, `p` left moves of both heads
reach input position `0`.

**Proof sketch.** Induction on `p`, generalizing the work head: at position `p + 1 ≤ |x|` the
input head reads `x[p]`, so one step moves both heads left without writing, and the
induction hypothesis finishes the remaining `p` steps. -/
private lemma copy_rewind (x : List Bool) (p : ℕ) (hp : p ≤ x.length) (z : ℤ) :
    copyTM.tm.runFrom (copyCfg x (some 1) p (by omega) x z) p =
      copyCfg x (some 1) 0 (by omega) x (z - p) := by
  induction p generalizing z with
  | zero => simp [copyCfg]
  | succ p ih =>
    rw [MultiTapeTM.runFrom_succ_eq_step]
    have hstep : copyTM.tm.step (copyCfg x (some 1) (p + 1) (by omega) x z) =
        copyCfg x (some 1) p (by omega) x (z - 1) := by
      have hsym : (copyCfg x (some 1) (p + 1) (by omega) x z).inputSymbol = some x[p] :=
        inputSymbolInner p (by simp [copyCfg]; omega) (by omega)
      have hs : (copyCfg x (some 1) (p + 1) (by omega) x z).state = some 1 := rfl
      unfold MultiTapeTM.step
      rw [hs]
      dsimp only
      rw [hsym]
      show (⟨.neg, fun _ => (none, .neg), none, some 1⟩ : Action 1 Bool (Fin 2)).apply _ = _
      refine Cfg.ext rfl ?_ ?_ ?_ rfl
      · apply Fin.ext
        simp only [Action.apply, copyCfg]
        rw [FinTM.moveInputPos_neg_val]
        simp
      · funext i
        simp [Action.apply, copyCfg]
      · funext i
        simp [Action.apply, copyCfg, sub_eq_add_neg]
    rw [hstep, ih (by omega)]
    simp only [copyCfg, Nat.cast_succ]
    congr 1
    funext _
    ring

/-- At the left blank the copier moves both heads right and halts. -/
private lemma copy_finish (x : List Bool) (z : ℤ) :
    copyTM.tm.step (copyCfg x (some 1) 0 (by omega) x z) =
      copyCfg x none 1 (by omega) x (z + 1) := by
  have hsym : (copyCfg x (some 1) 0 (by omega) x z).inputSymbol = none := by
    simp [Cfg.inputSymbol, copyCfg]
  have hs : (copyCfg x (some 1) 0 (by omega) x z).state = some 1 := rfl
  unfold MultiTapeTM.step
  rw [hs]
  dsimp only
  rw [hsym]
  show (⟨.pos, fun _ => (none, .pos), none, none⟩ : Action 1 Bool (Fin 2)).apply _ = _
  refine Cfg.ext rfl ?_ ?_ ?_ rfl
  · apply Fin.ext
    simp only [Action.apply, copyCfg]
    rw [moveInputPos_pos_of_ne_right _ (by simp)]
  · funext i
    simp [Action.apply, copyCfg]
  · funext i
    simp [Action.apply, copyCfg]

/-- **The copier's contract.** From the empty seam over native input `x`, the copier halts
after exactly `2|x| + 2` steps at the seam holding `x` on tape 0, never halting earlier.

**Proof sketch.** `|x|` copying steps (`copy_step`), the turn (`copy_turn`), `|x|` rewind
steps (`copy_rewind`), the final right move and halt (`copy_finish`); liveness before the
end from the live configuration at time `2|x| + 1` (`Turing.ModuleHost.live_prefix`). -/
lemma copy_clean (x : List Bool) :
    (∀ v < 2 * x.length + 2,
      ¬(copyTM.tm.runFrom (Cfg.ofWords (input := x) (0 : Fin 2) (stateWord 1 [])) v).Halted) ∧
    copyTM.tm.runFrom (Cfg.ofWords (input := x) (0 : Fin 2) (stateWord 1 []))
        (2 * x.length + 2) =
      {Cfg.ofWords (input := x) (0 : Fin 2) (stateWord 1 x) with state := none} := by
  have hi : Cfg.ofWords (input := x) (0 : Fin 2) (stateWord 1 []) =
      copyCfg x (some 0) 1 (by omega) [] 0 := by
    refine Cfg.ext rfl rfl ?_ rfl rfl
    funext i
    simp [Cfg.ofWords, copyCfg, stateWord]
  have hcopy : ∀ j (hj : j ≤ x.length),
      copyTM.tm.runFrom (copyCfg x (some 0) 1 (by omega) [] 0) j =
        copyCfg x (some 0) (j + 1) (by omega) (x.take j) j := by
    intro j
    induction j with
    | zero => intro _; simp [copyCfg]
    | succ j ih =>
      intro hj
      rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega), copy_step x j (by omega)]
  have hmid : copyTM.tm.runFrom (copyCfg x (some 0) 1 (by omega) [] 0) (2 * x.length + 1) =
      copyCfg x (some 1) 0 (by omega) x (-1) := by
    rw [show 2 * x.length + 1 = x.length + 1 + x.length by ring, MultiTapeTM.runFrom_add,
      MultiTapeTM.runFrom_succ_eq_step', hcopy x.length le_rfl]
    simp only [List.take_length]
    rw [copy_turn, copy_rewind x x.length le_rfl]
    simp only [copyCfg]
    congr 1
    funext _
    ring
  refine ⟨?_, ?_⟩
  · intro v hv
    rw [hi]
    exact ModuleHost.live_prefix copyTM.tm _ (2 * x.length + 1) (by rw [hmid]; simp [copyCfg]) v
      (by omega)
  · rw [hi, MultiTapeTM.runFrom_succ_eq_step', hmid, copy_finish]
    refine Cfg.ext rfl ?_ ?_ ?_ rfl
    · apply Fin.ext; simp [copyCfg, Cfg.ofWords]
    · funext i
      simp [copyCfg, Cfg.ofWords, stateWord]
    · funext i
      simp [copyCfg, Cfg.ofWords]

/-- **The typed view of the input copier**: the finite machine with one work tape, state type
`Fin 2`, start state `0` and the copier's transition function,
`copyTMView = ⟨1, Fin 2, ⟨0, copyTM.tm.tr⟩⟩`. It is the copier itself (`copyTMView_eq`), with its
tape count, state type and start state explicit, so that a consumer can type the copier's
configurations without unfolding `copyTM`. -/
abbrev copyTMView : FinTM Bool where
  k := 1
  State := Fin 2
  tm := { q₀ := 0, tr := copyTM.tm.tr }

/-- The typed view of the copier is the copier: `copyTMView = copyTM`. -/
theorem copyTMView_eq : copyTMView = copyTM :=
  rfl

/-- **The typed copier's contract** (`copy_clean` for `copyTMView`): from the empty seam over
native input `x`, the typed copier is live before time `2|x| + 2` and
`copyTMView.tm.runFrom (Cfg.ofWords 0 (stateWord 1 [])) (2|x| + 2) =
{Cfg.ofWords 0 (stateWord 1 x) with state := none}`. -/
theorem copy_clean_view (x : List Bool) :
    (∀ v < 2 * x.length + 2,
      ¬(copyTMView.tm.runFrom (Cfg.ofWords (input := x) (0 : Fin 2) (stateWord 1 [])) v).Halted) ∧
    copyTMView.tm.runFrom (Cfg.ofWords (input := x) (0 : Fin 2) (stateWord 1 []))
        (2 * x.length + 2) =
      {Cfg.ofWords (input := x) (0 : Fin 2) (stateWord 1 x) with state := none} :=
  copy_clean x


/-! ### The host -/

/-- The control table of the repetition machine's host over its three control states, each step
stationary and silent: the loop anchor `0` dispatches into the verdict module (`2`); the branch
state `1` reads the first cell of tape 0 and dispatches into the payload module (`4`) if it holds
`true`, into the step module (`3`) otherwise; the halt state `2` halts. -/
def hostCtrl (M : Fin 5 → FinTM Bool) (K : ℕ) (c : Fin 3) (_inp : Option Bool)
    (work : Fin (K + 1) → Option Bool) : Action (K + 1) Bool (ModuleHost.State (Fin 3) M) :=
  if c = 0 then FinTM.controlAction 0 (some (ModuleHost.entry M 2))
  else if c = 1 then
    FinTM.controlAction 0
      (some (if work 0 = some true then ModuleHost.entry M 4 else ModuleHost.entry M 3))
  else FinTM.controlAction 0 none

/-- The control table: `hostCtrl M K c inp work` is the stationary silent action into the
verdict module's entry if `c = 0`, into the payload module's entry (`work 0 = some true`) or the
step module's entry (otherwise) if `c = 1`, and the halting action if `c = 2`. -/
theorem hostCtrl_eq (M : Fin 5 → FinTM Bool) (K : ℕ) (c : Fin 3) (inp : Option Bool)
    (work : Fin (K + 1) → Option Bool) :
    hostCtrl M K c inp work =
      if c = 0 then FinTM.controlAction 0 (some (ModuleHost.entry M 2))
      else if c = 1 then
        FinTM.controlAction 0
          (some (if work 0 = some true then ModuleHost.entry M 4 else ModuleHost.entry M 3))
      else FinTM.controlAction 0 none :=
  rfl

/-- The return states of the five modules: copier (`0`) → startup install's entry; startup
install (`1`) → anchor `inl 0`; verdict (`2`) → branch `inl 1`; step (`3`) → anchor `inl 0`;
payload emit (`4`) → halt state `inl 2`. -/
def hostRet (M : Fin 5 → FinTM Bool) (i : Fin 5) : ModuleHost.State (Fin 3) M :=
  if i = 0 then ModuleHost.entry M 1 else if i = 2 then .inl 1 else if i = 4 then .inl 2
  else .inl 0

/-- The copier returns to the startup install's entry: `hostRet M 0 = entry M 1`. -/
theorem hostRet_zero (M : Fin 5 → FinTM Bool) : hostRet M 0 = ModuleHost.entry M 1 :=
  rfl

/-- The startup install returns to the anchor: `hostRet M 1 = inl 0`. -/
theorem hostRet_one (M : Fin 5 → FinTM Bool) : hostRet M 1 = .inl 0 :=
  rfl

/-- The verdict module returns to the branch state: `hostRet M 2 = inl 1`. -/
theorem hostRet_two (M : Fin 5 → FinTM Bool) : hostRet M 2 = .inl 1 :=
  rfl

/-- The step module returns to the anchor: `hostRet M 3 = inl 0`. -/
theorem hostRet_three (M : Fin 5 → FinTM Bool) : hostRet M 3 = .inl 0 :=
  rfl

/-- The payload module returns to the halt state: `hostRet M 4 = inl 2`. -/
theorem hostRet_four (M : Fin 5 → FinTM Bool) : hostRet M 4 = .inl 2 :=
  rfl

/-- The finite host of the repetition machine: the clean-module host
`Turing.ModuleHost.hostTM` over the five modules `M` with `K + 1` shared tapes (tape 0 carries
the state word), the three control states of `hostCtrl`, the return states `hostRet`, and the
copier's entry as start state. A reducible abbreviation, so the host's lemmas
(`Turing.ModuleHost.host_call`, `host_clean`, `hostTM_step_inl`, …) apply to it directly. -/
abbrev hostTM (M : Fin 5 → FinTM Bool) (K : ℕ) (hk : ∀ i, (M i).k ≤ K + 1) : FinTM Bool :=
  ModuleHost.hostTM M (K + 1) hk (hostCtrl M K) (hostRet M) (ModuleHost.entry M 0)

/-- The repetition machine's host is
`Turing.ModuleHost.hostTM M (K + 1) hk (hostCtrl M K) (hostRet M) (entry M 0)`. -/
theorem hostTM_eq (M : Fin 5 → FinTM Bool) (K : ℕ) (hk : ∀ i, (M i).k ≤ K + 1) :
    hostTM M K hk =
      ModuleHost.hostTM M (K + 1) hk (hostCtrl M K) (hostRet M) (ModuleHost.entry M 0) :=
  rfl

/-- The anchor dispatches into the verdict module in one stationary step: from the seam at
`inl 0` holding `w`, one step reaches the seam at the verdict module's entry holding `w`. -/
theorem host_dispatch (M : Fin 5 → FinTM Bool) (K : ℕ) (hk : ∀ i, (M i).k ≤ K + 1)
    (x w : List Bool) :
    (hostTM M K hk).tm.step (Cfg.ofWords (input := x) (.inl 0) (stateWord (K + 1) w)) =
      Cfg.ofWords (ModuleHost.entry M 2) (stateWord (K + 1) w) := by
  rw [ModuleHost.hostTM_step_inl _ _ _ _ _ _ _ 0 rfl]
  change (FinTM.controlAction 0 (some (ModuleHost.entry M 2))).apply _ = _
  rw [FinTM.controlAction_apply, moveInputPos_zero]
  rfl

/-- The branch state reads the first cell of tape 0 — the verdict `b` of a verdict word `w`
with `w[0]? = some b` — and dispatches, in one stationary step, into the payload module (`b`
true) or the step module (`b` false), at the seam holding `w`. -/
theorem host_branch (M : Fin 5 → FinTM Bool) (K : ℕ) (hk : ∀ i, (M i).k ≤ K + 1)
    (x : List Bool) (b : Bool) (w : List Bool) (hw : w[0]? = some b) :
    (hostTM M K hk).tm.step (Cfg.ofWords (input := x) (.inl 1) (stateWord (K + 1) w)) =
      Cfg.ofWords (ModuleHost.entry M (if b then 4 else 3)) (stateWord (K + 1) w) := by
  have hread : (Cfg.ofWords (input := x) (.inl 1 : ModuleHost.State (Fin 3) M)
      (stateWord (K + 1) w)).workTapeSymbols 0 = some b := by
    simp [Cfg.ofWords, Cfg.workTapeSymbols, stateWord, FinTM.bufferTape, hw]
  rw [ModuleHost.hostTM_step_inl _ _ _ _ _ _ _ 1 rfl]
  show (FinTM.controlAction 0 (some (if (Cfg.ofWords (input := x)
    (.inl 1 : ModuleHost.State (Fin 3) M) (stateWord (K + 1) w)).workTapeSymbols 0 = some true
      then ModuleHost.entry M 4 else ModuleHost.entry M 3))).apply _ = _
  rw [hread, FinTM.controlAction_apply, moveInputPos_zero]
  cases b <;> rfl

/-- The halt state halts without emitting: from the seam at `inl 2` holding `w` with output `o`,
one step reaches the same seam with control `none` and output `o`. -/
theorem host_halt (M : Fin 5 → FinTM Bool) (K : ℕ) (hk : ∀ i, (M i).k ≤ K + 1)
    (x w o : List Bool) :
    (hostTM M K hk).tm.step
        {Cfg.ofWords (input := x) (.inl 2) (stateWord (K + 1) w) with output := o} =
      {Cfg.ofWords (input := x) (.inl 2 : ModuleHost.State (Fin 3) M) (stateWord (K + 1) w)
        with state := none, output := o} := by
  rw [ModuleHost.hostTM_step_inl _ _ _ _ _ _ _ 2 rfl]
  change (FinTM.controlAction 0 none).apply _ = _
  rw [FinTM.controlAction_apply, moveInputPos_zero]

/-- **The anchor's dispatch, for the typed view** (`host_dispatch` for
`Turing.ModuleHost.hostTMView`): from the seam at `inl 0` holding `w`, one step of the typed view
`H = hostTMView M (K + 1) hk (hostCtrl M K) (hostRet M) (entry M 0)` reaches the seam at the
verdict module's entry holding `w`,
`H.tm.step (Cfg.ofWords (inl 0) (stateWord (K + 1) w)) =
Cfg.ofWords (entry M 2) (stateWord (K + 1) w)`.
Framework glue, no textbook counterpart (the host's control table). -/
theorem host_dispatch_view (M : Fin 5 → FinTM Bool) (K : ℕ) (hk : ∀ i, (M i).k ≤ K + 1)
    (x w : List Bool) :
    (ModuleHost.hostTMView M (K + 1) hk (hostCtrl M K) (hostRet M) (ModuleHost.entry M 0)).tm.step
        (Cfg.ofWords (input := x) (.inl 0) (stateWord (K + 1) w)) =
      Cfg.ofWords (ModuleHost.entry M 2) (stateWord (K + 1) w) := by
  rw [ModuleHost.hostTMView_step_inl _ _ _ _ _ _ _ 0 (Cfg.ofWords_state _ _), hostCtrl_eq,
    if_pos rfl, FinTM.controlAction_apply, moveInputPos_zero, Cfg.ofWords_def, Cfg.ofWords_def]

/-- **The branch, for the typed view** (`host_branch` for `Turing.ModuleHost.hostTMView`): the
branch state reads the first cell of tape 0, the verdict `b` of a word `w` with `w[0]? = some b`,
and one step of the typed view
`H = hostTMView M (K + 1) hk (hostCtrl M K) (hostRet M) (entry M 0)` dispatches into the payload
module (`b` true) or the step module (`b` false) at the seam holding `w`,
`H.tm.step (Cfg.ofWords (inl 1) (stateWord (K + 1) w)) =
Cfg.ofWords (entry M (if b then 4 else 3)) (stateWord (K + 1) w)`.
Framework glue, no textbook counterpart (the host's control table). -/
theorem host_branch_view (M : Fin 5 → FinTM Bool) (K : ℕ) (hk : ∀ i, (M i).k ≤ K + 1)
    (x : List Bool) (b : Bool) (w : List Bool) (hw : w[0]? = some b) :
    (ModuleHost.hostTMView M (K + 1) hk (hostCtrl M K) (hostRet M) (ModuleHost.entry M 0)).tm.step
        (Cfg.ofWords (input := x) (.inl 1) (stateWord (K + 1) w)) =
      Cfg.ofWords (ModuleHost.entry M (if b then 4 else 3)) (stateWord (K + 1) w) := by
  have hread : (Cfg.ofWords (input := x) (.inl 1 : ModuleHost.State (Fin 3) M)
      (stateWord (K + 1) w)).workTapeSymbols 0 = some b := by
    simp only [Cfg.workTapeSymbols_eq, Cfg.ofWords_workTapes, Cfg.ofWords_workTapePos,
      stateWord_eq, FinTM.bufferTape_eq]
    simpa using hw
  rw [ModuleHost.hostTMView_step_inl _ _ _ _ _ _ _ 1 (Cfg.ofWords_state _ _), hostCtrl_eq,
    if_neg (by decide), if_pos rfl, hread, FinTM.controlAction_apply, moveInputPos_zero,
    Cfg.ofWords_def, Cfg.ofWords_def]
  cases b <;> rfl

/-- **The halt, for the typed view** (`host_halt` for `Turing.ModuleHost.hostTMView`): from the
seam at `inl 2` holding `w` with output `o`, one step of the typed view
`H = hostTMView M (K + 1) hk (hostCtrl M K) (hostRet M) (entry M 0)` reaches the same seam with
control `none` and output `o`,
`H.tm.step {Cfg.ofWords (inl 2) (stateWord (K + 1) w) with output := o} =
{Cfg.ofWords (inl 2) (stateWord (K + 1) w) with state := none, output := o}`.
Framework glue, no textbook counterpart (the host's control table). -/
theorem host_halt_view (M : Fin 5 → FinTM Bool) (K : ℕ) (hk : ∀ i, (M i).k ≤ K + 1)
    (x w o : List Bool) :
    (ModuleHost.hostTMView M (K + 1) hk (hostCtrl M K) (hostRet M) (ModuleHost.entry M 0)).tm.step
        {Cfg.ofWords (input := x) (.inl 2) (stateWord (K + 1) w) with output := o} =
      {Cfg.ofWords (input := x) (.inl 2 : ModuleHost.State (Fin 3) M) (stateWord (K + 1) w)
        with state := none, output := o} := by
  rw [ModuleHost.hostTMView_step_inl _ _ _ _ _ _
    ({Cfg.ofWords (input := x) (.inl 2) (stateWord (K + 1) w) with output := o} :
      Cfg (K + 1) Bool (ModuleHost.State (Fin 3) M) x) 2
    (Cfg.ofWords_state (input := x) (.inl 2 : ModuleHost.State (Fin 3) M) (stateWord (K + 1) w)),
    hostCtrl_eq, if_neg (by decide), if_neg (by decide),
    FinTM.controlAction_apply, moveInputPos_zero]

end Complexity.IterateFind

## ===== TCSlib/Complexity/Randomized/Build/IterateFind.lean (Lean, TS1 tree 1eaf940b938bb52e3919f5569893b58522df599b) =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import Mathlib.Data.Nat.Bits
import Mathlib.Tactic.FinCases
import TCSlib.Complexity.TuringMachine.Build.Primitives
import TCSlib.Complexity.Randomized.Build.IterateFindHost
import TCSlib.Complexity.Randomized.Primitives

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The machine behind the repetition lemma

The finite machine behind `Complexity.polyTimeComputable_iterateFind`
(`TCSlib.Complexity.Randomized.Repetition`, the load-bearing lemma of the Pass–shelat campaign,
foundation decision D11 of `PassShelatChapter2-4Plan.md`): iterate a polynomial-time step `g`
at most `R(|x|)` times on a polynomially bounded orbit and return the payload `out` of the first
orbit point accepted by `acc` (`[]` on exhaustion). Every theorem of [PS10, ch. 2–4] that
repeats an adversary — Algorithm 38.5's `2nm²p(n)` attempts with first success
[PS10, Theorem 35.1], the `n(2^k − 1)` calls of Goldreich–Levin [PS10, Theorem 87.3], the
truncated simulators [PS10, Algorithms 123.4 and 128.7] — reduces to this machine.

## Construction (DESIGN.md §2.6, the three panel repairs built in)

The machine is an instance of the result-bearing loop combinator
`Turing.FinTM.exists_loopFindTM` (`TCSlib.Complexity.TuringMachine.Build.Loop`).

1. *State word.* The loop state is the pair `⟨x, s⟩` (`Turing.pairEncode x s`) of the input
   and the current orbit point; the loop invariant `Inv` says the word *is* such a pair with
   `|s| ≤ P|x|`; the step is the length-guarded `Complexity.IterateFind.step`
   (`⟨x, g s⟩` if `|g s| ≤ P|x|`, else unchanged), under which the invariant is closed for
   every admissible word; on the orbit the guard never fires (the pure lemmas of
   `TCSlib.Complexity.Randomized.Repetition`).
2. *Modules.* Three clean-call modules over the state word, from
   `Turing.FinTM.exists_installCallTM`/`exists_emitCallTM` applied to FP functions: the
   **verdict** install `w ↦ ⟨[acc (snd w)], w⟩` (the verdict as the first cell of the installed
   word), the **step** install `w' ↦ step` on the pair carried by `w'`, and the **payload** emit
   `w' ↦ out (snd (snd w'))`; plus the startup module `x ↦ ⟨x, x⟩`
   (`Turing.FinTM.computesFunInTime_pairDup`) and a two-state copier that puts the native
   input on tape 0 first.
3. *Gluing.* Each module is converted into a first-halting source (a release flag stops it one
   silent step after its first positive exit), padded to the common tape count, and embedded
   into one finite host through the forwarding transformer `Turing.emitAction`; the host's own
   control has three fresh states — the loop **anchor** (never a module-internal state), a
   **branch** state reading the verdict cell of tape 0, and a **halt** state. Modules return
   to fixed host states: copier → startup install → anchor; verdict → branch; branch → payload
   emit (verdict `true`) or step install (verdict `false`); payload emit → halt; step → anchor.
4. *Budgets.* All requests are state words of length at most `Q n + 4` with
   `Q n = 2n + 2 + P n`; every module's polynomial budget on its argument is majorised by one
   common `A · (Q n + 5)^D`, which also pays for the fuel machine `x ↦ Nat.bits (R|x|)`
   (`Complexity.polyTimeComputable_unaryPoly R` composed with
   `Turing.FinTM.computesFunInTime_lengthBits`, so that the `find?` range is exactly
   `R|x| + 1`). The loop combinator returns a machine within `c (T n + 1)(R n + 2)`, which
   `PolyExpr.eval_le` puts in the normal form of `Complexity.PolyTimeComputable`.

The clean modules and the finite host (steps 2–3: release-flag stop, padding, forwarding host,
first-halt cutting) are the public clean-module host
`TCSlib.Complexity.TuringMachine.Build.ModuleHost` (host H14 of `machine-library-design.md` §14);
its instance for this machine (the copier, the control table, the return states) lives in
`TCSlib.Complexity.Randomized.Build.IterateFindHost`.
This file supplies the pure step, the FP functions of the modules, the budget arithmetic, and the
assembly through `Turing.FinTM.exists_loopFindTM`.

## Main definitions

* `Complexity.IterateFind.step` — the length-guarded step on the state word (definitionally
  `Complexity.guardedStep`).

## Main results

* `Complexity.IterateFind.computesFunInTime_find` — the finite machine with arbitrary
  numerical fuel supplied in binary, a chosen initial state, and an explicit polynomial
  per-round budget.
* `Complexity.IterateFind.polyTimeComputable_find` — the loop-level form of the repetition
  lemma: the first accepted orbit point's payload along the guarded orbit of `⟨x, x⟩` is
  polynomial-time computable.
* `Complexity.IterateFind.find?_congr_of_mem` — `List.find?` depends only on the predicate's
  values on the list (used to identify the guarded orbit with `g^[i] x`).
* `Complexity.IterateFind.find?_range_and_lt` — a search over `[0, L)` whose test also demands
  `i < N` is the search over `[0, N)`, for `N ≤ L`.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (Algorithm 38.5 and Theorem 35.1; Theorem 87.3; Algorithms 123.4 and 128.7.)
* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.2–1.3, time-bounded machines.)
-/

namespace Complexity.IterateFind

open Turing

/-! ### The guarded step on the state word and its FP pieces -/

/-- The length-guarded step on the state word `w = ⟨x, s⟩`: advance to `⟨x, g s⟩` if the new
orbit point fits the bound `P|x|`, else stay (DESIGN.md §2.6, step 1). This is definitionally
`Complexity.guardedStep g P x w`; it is restated here because this file is imported by the
file defining `guardedStep`. -/
def step (g : List Bool → List Bool) (P : PolyExpr) (x w : List Bool) : List Bool :=
  if (g (pairSndD w)).length ≤ P.eval x.length then pairEncode x (g (pairSndD w)) else w

/-- The guarded step: `step g P x w = ⟨x, g (snd w)⟩` if `|g (snd w)| ≤ P|x|`, and `w`
otherwise. -/
theorem step_eq (g : List Bool → List Bool) (P : PolyExpr) (x w : List Bool) :
    step g P x w =
      if (g (pairSndD w)).length ≤ P.eval x.length then pairEncode x (g (pairSndD w)) else w :=
  rfl

/-- The loop invariant used by the machine: the state word *is* a pair `⟨x, s⟩` with
`|s| ≤ P|x|` (stronger than the pure `Complexity.LoopInv`, which also admits malformed
words; the machine needs the well-formedness to bound the word's length). -/
private def Inv (P : PolyExpr) (x w : List Bool) : Prop :=
  ∃ s, w = pairEncode x s ∧ s.length ≤ P.eval x.length

/-- The initial word `⟨x, x⟩` is admissible when `|x| ≤ P|x|`. -/
private theorem inv_init (P : PolyExpr) (x : List Bool) (h0 : x.length ≤ P.eval x.length) :
    Inv P x (pairEncode x x) :=
  ⟨x, rfl, h0⟩

/-- The invariant is closed under the guarded step (the guard keeps the word unchanged when
the new point would be too long). -/
private theorem inv_step (g : List Bool → List Bool) (P : PolyExpr) (x w : List Bool)
    (h : Inv P x w) : Inv P x (step g P x w) := by
  obtain ⟨s, rfl, hs⟩ := h
  unfold step
  rw [pairSndD_pairEncode]
  split_ifs with hg
  · exact ⟨g s, rfl, hg⟩
  · exact ⟨s, rfl, hs⟩

/-- The length of an admissible state word is at most `2|x| + 2 + P|x|`. -/
private theorem inv_length (P : PolyExpr) (x w : List Bool) (h : Inv P x w) :
    w.length ≤ 2 * x.length + 2 + P.eval x.length := by
  obtain ⟨s, rfl, hs⟩ := h
  rw [length_pairEncode]
  omega

/-- The verdict word: `w ↦ ⟨[acc (snd w)], w⟩` (the verdict as the first cell, since
`pairEncode [b] w = [b, b, false, true] ++ w`). -/
private def verdictWord (acc : List Bool → Bool) (w : List Bool) : List Bool :=
  pairEncode [acc (pairSndD w)] w

/-- The step on a verdict word: strip the verdict, then take the guarded step on the pair
`⟨x, s⟩` carried by the word, with `x` recovered from the word itself. -/
private def stepWord (g : List Bool → List Bool) (P : PolyExpr) (w' : List Bool) : List Bool :=
  if (g (pairSndD (pairSndD w'))).length ≤ P.eval (pairFstD (pairSndD w')).length then
    pairEncode (pairFstD (pairSndD w')) (g (pairSndD (pairSndD w')))
  else pairSndD w'

/-- The payload of a verdict word: `out` of the orbit point `snd (snd w')`. -/
private def outWord (out : List Bool → List Bool) (w' : List Bool) : List Bool :=
  out (pairSndD (pairSndD w'))

/-- The first cell of a verdict word is the verdict. -/
private theorem verdictWord_head (acc : List Bool → Bool) (w : List Bool) :
    (verdictWord acc w)[0]? = some (acc (pairSndD w)) := by
  simp [verdictWord, pairEncode_eq]

/-- The length of a verdict word. -/
private theorem verdictWord_length (acc : List Bool → Bool) (w : List Bool) :
    (verdictWord acc w).length = w.length + 4 := by
  simp [verdictWord, length_pairEncode]
  omega

/-- On the verdict word of a pair `⟨x, s⟩`, `stepWord` is the guarded step. -/
private theorem stepWord_verdictWord (g : List Bool → List Bool) (P : PolyExpr)
    (acc : List Bool → Bool) (x s : List Bool) :
    stepWord g P (verdictWord acc (pairEncode x s)) = step g P x (pairEncode x s) := by
  simp [stepWord, verdictWord, step]

/-- On the verdict word of a pair, `outWord` is `out` of the orbit point. -/
private theorem outWord_verdictWord (out : List Bool → List Bool) (acc : List Bool → Bool)
    (x s : List Bool) : outWord out (verdictWord acc (pairEncode x s)) = out s := by
  simp [outWord, verdictWord]

/-- The verdict word is polynomial-time computable (`PolyTimeComputable.pairEncode` of the
test composed with the projection and the identity). -/
private theorem verdictWord_poly {acc : List Bool → Bool}
    (hacc : PolyTimeComputable fun s => [acc s]) : PolyTimeComputable (verdictWord acc) := by
  have h := (hacc.comp polyTimeComputable_pairSndD).pairEncode polyTimeComputable_id
  exact h

/-- The step on verdict words is polynomial-time computable.

**Proof sketch.** `Complexity.polyTimeComputable_ite`: the test
`|g (snd (snd w'))| ≤ P|fst (snd w')|` is `Complexity.polyTimeComputable_lenLe` on the pair
`⟨1^{P|fst (snd w')|}, g (snd (snd w'))⟩`, built with the unary evaluator
`Complexity.polyTimeComputable_unaryPoly P` and `PolyTimeComputable.pairEncode`; the `then`
branch is the pairing of the two projections (with `g`), the `else` branch the projection
`snd`; the Boolean test is identified with the propositional `if` by `decide_eq_true_eq`. -/
private theorem stepWord_poly {g : List Bool → List Bool} (hg : PolyTimeComputable g)
    (P : PolyExpr) : PolyTimeComputable (stepWord g P) := by
  have hs2 : PolyTimeComputable fun w' => pairSndD (pairSndD w') :=
    polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD
  have hf1 : PolyTimeComputable fun w' => pairFstD (pairSndD w') :=
    polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD
  have hgg : PolyTimeComputable fun w' => g (pairSndD (pairSndD w')) := hg.comp hs2
  have hun : PolyTimeComputable fun w' =>
      List.replicate (P.eval (pairFstD (pairSndD w')).length) true :=
    (polyTimeComputable_unaryPoly P).comp hf1
  have htest : PolyTimeComputable fun w' =>
      [decide ((g (pairSndD (pairSndD w'))).length ≤ P.eval (pairFstD (pairSndD w')).length)] := by
    have h := polyTimeComputable_lenLe.comp (hun.pairEncode hgg)
    convert h using 1
    funext w'
    simp
  have hthen : PolyTimeComputable fun w' =>
      pairEncode (pairFstD (pairSndD w')) (g (pairSndD (pairSndD w'))) := hf1.pairEncode hgg
  have h := polyTimeComputable_ite htest hthen polyTimeComputable_pairSndD
  convert h using 1
  funext w'
  simp [stepWord]

/-- The payload map on verdict words is polynomial-time computable. -/
private theorem outWord_poly {out : List Bool → List Bool} (hout : PolyTimeComputable out) :
    PolyTimeComputable (outWord out) :=
  hout.comp (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD)

/-- The duplication `x ↦ ⟨x, x⟩` is polynomial-time computable. -/
private theorem dupWord_poly : PolyTimeComputable fun x => pairEncode x x :=
  polyTimeComputable_of_linear FinTM.computesFunInTime_pairDup

/-! ### Assembly -/

/-- `List.find?` depends only on the values of the predicate on the list's elements. -/
theorem find?_congr_of_mem {α : Type*} {p q : α → Bool} :
    ∀ l : List α, (∀ a ∈ l, p a = q a) → l.find? p = l.find? q
  | [], _ => rfl
  | a :: l, h => by
    have ha : p a = q a := h a (List.mem_cons_self ..)
    by_cases hq : q a = true
    · rw [List.find?_cons_of_pos (by rw [ha]; exact hq), List.find?_cons_of_pos hq]
    · rw [List.find?_cons_of_neg (by rw [ha]; exact hq), List.find?_cons_of_neg hq]
      exact find?_congr_of_mem l (fun b hb => h b (List.mem_cons_of_mem a hb))

/-- **A bounded search is a search over a shorter range**: for `N ≤ L`, searching `[0, L)` for
the first `i` with `i < N` and `p i` is searching `[0, N)` for the first `i` with `p i`:
`(List.range L).find? (fun i => decide (i < N) && p i) = (List.range N).find? p`.

**Proof sketch.** Write `L = N + d` (`List.range_add`, `List.find?_append`). On `[0, N)` the guard
`i < N` holds, so the two predicates agree (`find?_congr_of_mem`). On the shifted tail `N + [0, d)`
it fails, so that search is `none` (`List.find?_eq_none`), and `o <|> none = o`. -/
theorem find?_range_and_lt (p : ℕ → Bool) {N L : ℕ} (hNL : N ≤ L) :
    (List.range L).find? (fun i => decide (i < N) && p i) = (List.range N).find? p := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hNL
  rw [List.range_add, List.find?_append,
    find?_congr_of_mem _ (fun i hi => by rw [decide_eq_true (List.mem_range.1 hi), Bool.true_and])]
  have hnone : (List.map (fun x => N + x) (List.range d)).find?
      (fun i => decide (i < N) && p i) = none := by
    rw [List.find?_eq_none]
    intro x hx
    obtain ⟨y, -, rfl⟩ := List.mem_map.1 hx
    rw [decide_eq_false (by omega), Bool.false_and]
    exact Bool.false_ne_true
  rw [hnone, Option.or_none]

/-- The final budget arithmetic: the loop combinator's bound `c (T n + 1)(R n + 2)` with
`T n = A (2n + 2 + P n + 5)^D` is in the normal form `C (n + 1)^e` once `P` and `R` are
majorised by `CP (n+1)^cP` and `CR (n+1)^cR`.

**Proof sketch.** `2n + 7 + P n ≤ (CP + 7)(n+1)^{cP+1}` (both `7(n+1)` and `CP (n+1)^{cP}`
are at most the corresponding multiples of `(n+1)^{cP+1}`); raise to the `D`-th power
(`Nat.pow_le_pow_left`, `Nat.mul_pow`, `Nat.pow_mul`), absorb the `+ 1` with
`1 ≤ (n+1)^{(cP+1)D}`, bound `R n + 2 ≤ (CR + 2)(n+1)^{cR}` likewise, and multiply
(`Nat.mul_le_mul`, `Nat.pow_add`). -/
private lemma final_bound (c A D CP cP CR cR n Pn Rn : ℕ)
    (hP : Pn ≤ CP * (n + 1) ^ cP) (hR : Rn ≤ CR * (n + 1) ^ cR) :
    c * (A * (2 * n + 2 + Pn + 5) ^ D + 1) * (Rn + 2) ≤
      c * (A * (CP + 7) ^ D + 1) * (CR + 2) * (n + 1) ^ ((cP + 1) * D + cR) := by
  have hpos : 0 < n + 1 := Nat.succ_pos n
  have h1 : 2 * n + 2 + Pn + 5 ≤ (CP + 7) * (n + 1) ^ (cP + 1) := by
    have ha : n + 1 ≤ (n + 1) ^ (cP + 1) := by
      simpa using Nat.pow_le_pow_right hpos (show 1 ≤ cP + 1 by omega)
    have hb : (n + 1) ^ cP ≤ (n + 1) ^ (cP + 1) := Nat.pow_le_pow_right hpos (by omega)
    have hc := Nat.mul_le_mul_left CP hb
    calc 2 * n + 2 + Pn + 5 ≤ 7 * (n + 1) + CP * (n + 1) ^ cP := by omega
      _ ≤ 7 * (n + 1) ^ (cP + 1) + CP * (n + 1) ^ (cP + 1) :=
          Nat.add_le_add (Nat.mul_le_mul_left 7 ha) hc
      _ = (CP + 7) * (n + 1) ^ (cP + 1) := by ring
  have h2 : (2 * n + 2 + Pn + 5) ^ D ≤ (CP + 7) ^ D * (n + 1) ^ ((cP + 1) * D) := by
    calc (2 * n + 2 + Pn + 5) ^ D ≤ ((CP + 7) * (n + 1) ^ (cP + 1)) ^ D :=
          Nat.pow_le_pow_left h1 D
      _ = (CP + 7) ^ D * (n + 1) ^ ((cP + 1) * D) := by rw [Nat.mul_pow, ← Nat.pow_mul]
  have hone : 1 ≤ (n + 1) ^ ((cP + 1) * D) := Nat.one_le_pow _ _ hpos
  have h3 : A * (2 * n + 2 + Pn + 5) ^ D + 1 ≤
      (A * (CP + 7) ^ D + 1) * (n + 1) ^ ((cP + 1) * D) := by
    calc A * (2 * n + 2 + Pn + 5) ^ D + 1
        ≤ A * ((CP + 7) ^ D * (n + 1) ^ ((cP + 1) * D)) + (n + 1) ^ ((cP + 1) * D) :=
          Nat.add_le_add (Nat.mul_le_mul_left A h2) hone
      _ = (A * (CP + 7) ^ D + 1) * (n + 1) ^ ((cP + 1) * D) := by ring
  have h4 : Rn + 2 ≤ (CR + 2) * (n + 1) ^ cR := by
    have hone' : 1 ≤ (n + 1) ^ cR := Nat.one_le_pow _ _ hpos
    calc Rn + 2 ≤ CR * (n + 1) ^ cR + 2 * (n + 1) ^ cR := by omega
      _ = (CR + 2) * (n + 1) ^ cR := by ring
  calc c * (A * (2 * n + 2 + Pn + 5) ^ D + 1) * (Rn + 2)
      ≤ c * ((A * (CP + 7) ^ D + 1) * (n + 1) ^ ((cP + 1) * D)) * ((CR + 2) * (n + 1) ^ cR) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left c h3) h4
    _ = c * (A * (CP + 7) ^ D + 1) * (CR + 2) * (n + 1) ^ ((cP + 1) * D + cR) := by
        rw [Nat.pow_add]; ring

/-- A guarded search with arbitrary numerical fuel `R` and initial state `init` has a
finite machine computing the first accepted payload (or `[]` on exhaustion) within
`c * (A * (2 * n + 2 + P.eval n + 5) ^ D + 1) * (R n + 2)` steps, for constants
`c, A, D`. The step `g`, acceptance word `[acc s]`, payload `out s`, and initial state are
polynomial-time computable; `|init x| ≤ P.eval |x|`. A fuel machine computes
`Nat.bits (R |x|)` within `aF * (|x| + 1) ^ dF`. The displayed common per-round budget
`T n = A * (2 * n + 2 + P.eval n + 5) ^ D` is polynomial; no polynomial bound on `R`
is assumed. [AB09, §7.1, p. 126]; [PS10, §8.2, Theorem 180.1, step 4]

**Proof sketch.** Instance of `Turing.FinTM.exists_loopFindTM` for the repetition machine's
host (the clean-module host with the control table `hostCtrl` and the return states
`hostRet`), read through its typed view `Turing.ModuleHost.hostTMView`, over five clean
modules: the copier, through its typed view `copyTMView`, and
`Turing.ModuleHost.clean_install`/`clean_emit` of `x ↦ ⟨x, init x⟩`, `verdictWord acc`,
`stepWord g P` and `outWord out`. The anchor is `inl 0`; the invariant is `Inv P`, which the
size guard preserves under every step, including steps after the search terminates; the
step is `step g P`, the acceptance `acc ∘ snd`, the payload `out ∘ snd` and the start word
`⟨x, init x⟩`. `hstart`: the copier call (`copy_clean_view`,
`Turing.ModuleHost.host_call_view`) and the startup install
(`Turing.ModuleHost.host_clean_view`) reach the anchor seam holding `⟨x, init x⟩` in
`2|x| + 2 + t_S` steps, with no earlier anchor visit. `hround`: from the anchor seam with an
admissible word `⟨x, s⟩`, the dispatch step, the verdict call, the branch step on the verdict
cell, then either the payload call and the halt step (state `none`, output `out s`) or the
step call back to the anchor seam with `step g P x ⟨x, s⟩`; the three control steps are read
off `hostCtrl` through `Turing.ModuleHost.hostTMView_step_inl`, and the anchor guard is
`Turing.ModuleHost.guard_add` over the segments. Every request has length at most
`2|x| + 2 + P|x| + 4`, so every call and the given binary fuel machine fit the common budget
`T n = A (2n + 2 + P n + 5)^D` (`Turing.ModuleHost.request_budget`). The result-bearing loop
combinator then supplies the stated bound `c (T n + 1)(R n + 2)` directly, without the
polynomial-fuel normal form `final_bound`; its search result is matched by cases. -/
theorem computesFunInTime_find {g : List Bool → List Bool} (hg : PolyTimeComputable g)
    {acc : List Bool → Bool} (hacc : PolyTimeComputable fun s => [acc s])
    {out : List Bool → List Bool} (hout : PolyTimeComputable out)
    {init : List Bool → List Bool} (hinit : PolyTimeComputable init)
    (R : ℕ → ℕ) (P : PolyExpr)
    (hbound : ∀ x : List Bool, (init x).length ≤ P.eval x.length)
    (F : FinTM Bool) (aF dF : ℕ)
    (hF : F.ComputesFunInTime (fun x => Nat.bits (R x.length))
      (fun n => aF * (n + 1) ^ dF)) :
    ∃ (M : FinTM Bool) (c A D : ℕ),
      M.ComputesFunInTime
        (fun x => match (List.range (R x.length + 1)).find?
            (fun i => acc (pairSndD ((step g P x)^[i] (pairEncode x (init x))))) with
          | some i => out (pairSndD ((step g P x)^[i] (pairEncode x (init x))))
          | none => [])
        (fun n => c * (A * (2 * n + 2 + P.eval n + 5) ^ D + 1) * (R n + 2)) := by
  -- Build the four clean calls and their shared host, read through the typed views.
  obtain ⟨S, aS, dS, hS⟩ := ModuleHost.clean_install (polyTimeComputable_id.pairEncode hinit)
  obtain ⟨V, aV, dV, hV⟩ := ModuleHost.clean_install (verdictWord_poly hacc)
  obtain ⟨I, aI, dI, hI⟩ := ModuleHost.clean_install (stepWord_poly hg P)
  obtain ⟨E, aE, dE, hE⟩ := ModuleHost.clean_emit (outWord_poly hout)
  let M : Fin 5 → FinTM Bool := fun i => match i.val with
    | 0 => copyTMView | 1 => S | 2 => V | 3 => I | _ => E
  let K := S.k + V.k + I.k + E.k
  have hk : ∀ i, (M i).k ≤ K + 1 := by
    intro i; fin_cases i <;> simp [M, K] <;> omega
  let H := ModuleHost.hostTMView M (K + 1) hk (hostCtrl M K) (hostRet M) (ModuleHost.entry M 0)
  let anchor : H.State := .inl 0
  have hclean := ModuleHost.host_clean_view M (K + 1) hk (hostCtrl M K) (hostRet M)
    (ModuleHost.entry M 0)
  -- A seam with an empty output prefix is the seam.
  have hseam (x : List Bool) (q : ModuleHost.State (Fin 3) M) (w : List Bool) :
      ({Cfg.ofWords (input := x) q (stateWord (K + 1) w) with output := []} :
        Cfg (K + 1) Bool (ModuleHost.State (Fin 3) M) x) = Cfg.ofWords q (stateWord (K + 1) w) :=
    Cfg.ext rfl rfl rfl rfl (Cfg.ofWords_output q _).symm
  -- The three control steps (the table `hostCtrl`), read through the typed view.
  have hdisp (x w : List Bool) :
      H.tm.step (Cfg.ofWords (input := x) anchor (stateWord (K + 1) w)) =
        Cfg.ofWords (ModuleHost.entry M 2) (stateWord (K + 1) w) := by
    rw [ModuleHost.hostTMView_step_inl _ _ _ _ _ _ _ 0 (Cfg.ofWords_state _ _), hostCtrl_eq,
      if_pos rfl, FinTM.controlAction_apply, moveInputPos_zero, Cfg.ofWords_def, Cfg.ofWords_def]
  have hbranch (x : List Bool) (b : Bool) (w : List Bool) (hw : w[0]? = some b) :
      H.tm.step (Cfg.ofWords (input := x) (.inl 1) (stateWord (K + 1) w)) =
        Cfg.ofWords (ModuleHost.entry M (if b then 4 else 3)) (stateWord (K + 1) w) := by
    have hread : (Cfg.ofWords (input := x) (.inl 1 : ModuleHost.State (Fin 3) M)
        (stateWord (K + 1) w)).workTapeSymbols 0 = some b := by
      simp only [Cfg.workTapeSymbols_eq, Cfg.ofWords_workTapes, Cfg.ofWords_workTapePos,
        stateWord_eq, FinTM.bufferTape_eq]
      simpa using hw
    rw [ModuleHost.hostTMView_step_inl _ _ _ _ _ _ _ 1 (Cfg.ofWords_state _ _), hostCtrl_eq,
      if_neg (by decide), if_pos rfl, hread, FinTM.controlAction_apply, moveInputPos_zero,
      Cfg.ofWords_def, Cfg.ofWords_def]
    cases b <;> rfl
  have hhalt (x w o : List Bool) :
      H.tm.step {Cfg.ofWords (input := x) (.inl 2) (stateWord (K + 1) w) with output := o} =
        {Cfg.ofWords (input := x) (.inl 2 : ModuleHost.State (Fin 3) M) (stateWord (K + 1) w)
          with state := none, output := o} := by
    rw [ModuleHost.hostTMView_step_inl _ _ _ _ _ _
      ({Cfg.ofWords (input := x) (.inl 2) (stateWord (K + 1) w) with output := o} :
        Cfg (K + 1) Bool (ModuleHost.State (Fin 3) M) x) 2
      (Cfg.ofWords_state (input := x) (.inl 2 : ModuleHost.State (Fin 3) M) (stateWord (K + 1) w)),
      hostCtrl_eq, if_neg (by decide), if_neg (by decide),
      FinTM.controlAction_apply, moveInputPos_zero]
  let D := dS + dV + dI + dE + dF + 1
  let A := aS + aV + aI + aE + aF + 5
  let pow (n : ℕ) := (2 * n + 2 + P.eval n + 5) ^ D
  let T (n : ℕ) := A * pow n
  have hpow (n : ℕ) : n + 1 ≤ pow n := by
    have h := Nat.pow_le_pow_right (show 0 < 2 * n + 2 + P.eval n + 5 by omega)
      (show 1 ≤ D by dsimp [D]; omega)
    simp only [Nat.pow_one] at h
    exact (by omega : n + 1 ≤ 2 * n + 2 + P.eval n + 5).trans h
  -- Startup copies the input and installs the chosen initial state.
  have hstart : ∀ x : List Bool, ∃ t ≤ T x.length,
      (∀ v < t, (H.tm.runFrom (H.tm.initCfg x) v).state ≠ some anchor) ∧
      H.tm.runFrom (H.tm.initCfg x) t =
        Cfg.ofWords anchor (stateWord H.k (pairEncode x (init x))) := by
    intro x
    obtain ⟨hcg, hce⟩ := copy_clean_view x
    obtain ⟨hcGuard, hcEnd⟩ := ModuleHost.host_call_view M (K + 1) hk (hostCtrl M K) (hostRet M)
      (ModuleHost.entry M 0) 0 Nat.one_pos x [] x [] [] (0 : Fin 2) (2 * x.length + 2) hcg
      (hce.trans (Cfg.ext rfl rfl rfl rfl
        (Cfg.ofWords_output (input := x) (0 : Fin 2) (stateWord 1 x))))
    have hi : H.tm.initCfg x = Cfg.ofWords (ModuleHost.entry M 0) (stateWord (K + 1) []) := by
      rw [initCfg_ofWords, ModuleHost.hostTMView_q₀]
      congr 1
      funext i
      rw [stateWord_eq, ite_self]
    simp only [List.nil_append, hseam] at hcGuard hcEnd
    rw [hostRet_zero] at hcEnd
    obtain ⟨ts, hspos, hst, hsGuard, hsEnd⟩ := hclean 1
      (fun x => pairEncode x (init x)) (fun _ => []) (fun n => aS * (n + 1) ^ dS)
      (by simpa [M] using hS) x x []
    simp only [List.nil_append, hseam] at hsGuard hsEnd
    rw [hostRet_one] at hsEnd
    have hsB := ModuleHost.request_budget aS dS D (2 * x.length + 2 + P.eval x.length + 5) x.length
      (by dsimp [D]; omega) (by omega)
    have hp := hpow x.length
    refine ⟨2 * x.length + 2 + ts, ?_, ?_, ?_⟩
    · dsimp only [T, A, pow]
      simp only [Nat.add_mul]
      dsimp only [pow] at hp
      omega
    · rw [hi]
      exact ModuleHost.guard_add H.tm anchor _ _ _ ts (fun v hv => hcGuard v hv 0) hcEnd
        (fun v hv => hsGuard v hv 0)
    · rw [hi, MultiTapeTM.runFrom_add, hcEnd, hsEnd]
  -- A positive round either emits its payload or advances the guarded state.
  have hround : ∀ x w : List Bool, Inv P x w → ∃ t, 0 < t ∧ t ≤ T x.length ∧
      (∀ t', 0 < t' → t' < t →
        (H.tm.runFrom (Cfg.ofWords (input := x) anchor (stateWord H.k w)) t').state
          ≠ some anchor) ∧
      if acc (pairSndD w) then
        (H.tm.runFrom (Cfg.ofWords (input := x) anchor (stateWord H.k w)) t).state = none ∧
        (H.tm.runFrom (Cfg.ofWords (input := x) anchor (stateWord H.k w)) t).output =
          out (pairSndD w)
      else
        H.tm.runFrom (Cfg.ofWords (input := x) anchor (stateWord H.k w)) t =
          Cfg.ofWords anchor (stateWord H.k (step g P x w)) := by
    intro x w hw
    obtain ⟨s, rfl, hs⟩ := hw
    have hwlen : (pairEncode x s).length ≤ 2 * x.length + 2 + P.eval x.length := by
      rw [length_pairEncode]; omega
    have hw'len : (verdictWord acc (pairEncode x s)).length =
        (pairEncode x s).length + 4 := verdictWord_length acc _
    have hpow' := hpow x.length
    -- the dispatch, the verdict call, the branch
    have hdisp := hdisp x (pairEncode x s)
    obtain ⟨tv, hvpos, hvt, hvGuard, hvEnd⟩ := hclean 2 (verdictWord acc)
      (fun _ => []) (fun n => aV * (n + 1) ^ dV) (by simpa [M] using hV) x (pairEncode x s) []
    simp only [List.nil_append, hseam] at hvGuard hvEnd
    rw [hostRet_two] at hvEnd
    have hbr := hbranch x (acc s) (verdictWord acc (pairEncode x s))
      (by rw [verdictWord_head, pairSndD_pairEncode])
    have hvB := ModuleHost.request_budget aV dV D (2 * x.length + 2 + P.eval x.length + 5)
      (pairEncode x s).length (by dsimp [D]; omega) (by omega)
    have hseg : H.tm.runFrom (Cfg.ofWords (input := x) (ModuleHost.entry M 2)
        (stateWord (K + 1) (pairEncode x s))) (tv + 1) =
        Cfg.ofWords (ModuleHost.entry M (if acc s then 4 else 3))
          (stateWord (K + 1) (verdictWord acc (pairEncode x s))) := by
      rw [MultiTapeTM.runFrom_succ_eq_step', hvEnd, hbr]
    have hsegGuard : ∀ v < tv + 1, (H.tm.runFrom (Cfg.ofWords (input := x) (ModuleHost.entry M 2)
        (stateWord (K + 1) (pairEncode x s))) v).state ≠ some anchor := by
      refine ModuleHost.guard_add H.tm anchor _ _ tv 1 (fun v hv => hvGuard v hv 0) hvEnd ?_
      intro v hv
      have hv0 : v = 0 := by omega
      subst hv0
      simp [Cfg.ofWords_def, anchor]
    by_cases hb : acc s = true
    · -- accepting round: the payload call, then the halt
      rw [if_pos hb] at hseg
      obtain ⟨te, hepos, het, heGuard, heEnd⟩ := hclean 4 id (outWord out)
        (fun n => aE * (n + 1) ^ dE) (by simpa [M] using hE) x
        (verdictWord acc (pairEncode x s)) []
      simp only [List.nil_append, hseam, id_eq] at heGuard heEnd
      rw [hostRet_four, outWord_verdictWord] at heEnd
      have hhalt := hhalt x (verdictWord acc (pairEncode x s)) (out s)
      simp only at hhalt
      have heB := ModuleHost.request_budget aE dE D (2 * x.length + 2 + P.eval x.length + 5)
        (verdictWord acc (pairEncode x s)).length (by dsimp [D]; omega) (by omega)
      have hall : H.tm.runFrom (Cfg.ofWords (input := x) (ModuleHost.entry M 2)
          (stateWord (K + 1) (pairEncode x s))) (tv + 1 + te + 1) =
          {Cfg.ofWords (input := x) (.inl 2 : ModuleHost.State (Fin 3) M) (stateWord (K + 1)
            (verdictWord acc (pairEncode x s))) with state := none, output := out s} := by
        rw [MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_add, hseg, heEnd, hhalt]
      have hallGuard : ∀ v < tv + 1 + te + 1, (H.tm.runFrom (Cfg.ofWords (input := x)
          (ModuleHost.entry M 2) (stateWord (K + 1) (pairEncode x s))) v).state ≠ some anchor := by
        refine ModuleHost.guard_add H.tm anchor _ {Cfg.ofWords (input := x)
          (.inl 2 : ModuleHost.State (Fin 3) M)
          (stateWord (K + 1) (verdictWord acc (pairEncode x s))) with output := out s}
          (tv + 1 + te) 1 ?_ ?_ ?_
        · exact ModuleHost.guard_add H.tm anchor _ _ (tv + 1) te hsegGuard hseg
            (fun v hv => heGuard v hv 0)
        · rw [MultiTapeTM.runFrom_add, hseg, heEnd]
        · intro v hv
          have hv0 : v = 0 := by omega
          subst hv0
          simp [Cfg.ofWords_def, anchor]
      refine ⟨tv + 1 + te + 1 + 1, by omega, ?_, ?_, ?_⟩
      · dsimp only [T, A, pow]
        simp only [Nat.add_mul]
        dsimp only [pow] at hpow'
        omega
      · intro v hv hvt
        have hvform : v = (v - 1) + 1 := by omega
        change (H.tm.runFrom (Cfg.ofWords (input := x) anchor (stateWord (K + 1)
          (pairEncode x s))) v).state ≠ some anchor
        rw [hvform, MultiTapeTM.runFrom_succ_eq_step, hdisp]
        exact hallGuard (v - 1) (by omega)
      · rw [pairSndD_pairEncode, if_pos hb]
        change (H.tm.runFrom (Cfg.ofWords (input := x) anchor (stateWord (K + 1)
            (pairEncode x s))) (tv + 1 + te + 1 + 1)).state = none ∧
          (H.tm.runFrom (Cfg.ofWords (input := x) anchor (stateWord (K + 1)
            (pairEncode x s))) (tv + 1 + te + 1 + 1)).output = out s
        rw [MultiTapeTM.runFrom_succ_eq_step, hdisp, hall]
        exact ⟨rfl, rfl⟩
    · -- advancing round: the step call returns to the anchor
      rw [if_neg hb] at hseg
      obtain ⟨ti, hipos, hit, hiGuard, hiEnd⟩ := hclean 3 (stepWord g P)
        (fun _ => []) (fun n => aI * (n + 1) ^ dI) (by simpa [M] using hI) x
        (verdictWord acc (pairEncode x s)) []
      simp only [List.nil_append, hseam] at hiGuard hiEnd
      rw [hostRet_three, stepWord_verdictWord] at hiEnd
      have hiB := ModuleHost.request_budget aI dI D (2 * x.length + 2 + P.eval x.length + 5)
        (verdictWord acc (pairEncode x s)).length (by dsimp [D]; omega) (by omega)
      have hall : H.tm.runFrom (Cfg.ofWords (input := x) (ModuleHost.entry M 2)
          (stateWord (K + 1) (pairEncode x s))) (tv + 1 + ti) =
          Cfg.ofWords anchor (stateWord (K + 1) (step g P x (pairEncode x s))) := by
        rw [MultiTapeTM.runFrom_add, hseg, hiEnd]
      have hallGuard : ∀ v < tv + 1 + ti, (H.tm.runFrom (Cfg.ofWords (input := x)
          (ModuleHost.entry M 2) (stateWord (K + 1) (pairEncode x s))) v).state ≠ some anchor :=
        ModuleHost.guard_add H.tm anchor _ _ (tv + 1) ti hsegGuard hseg
          (fun v hv => hiGuard v hv 0)
      refine ⟨tv + 1 + ti + 1, by omega, ?_, ?_, ?_⟩
      · dsimp only [T, A, pow]
        simp only [Nat.add_mul]
        dsimp only [pow] at hpow'
        omega
      · intro v hv hvt
        have hvform : v = (v - 1) + 1 := by omega
        change (H.tm.runFrom (Cfg.ofWords (input := x) anchor (stateWord (K + 1)
          (pairEncode x s))) v).state ≠ some anchor
        rw [hvform, MultiTapeTM.runFrom_succ_eq_step, hdisp]
        exact hallGuard (v - 1) (by omega)
      · rw [pairSndD_pairEncode, if_neg hb]
        change H.tm.runFrom (Cfg.ofWords (input := x) anchor (stateWord (K + 1)
            (pairEncode x s))) (tv + 1 + ti + 1) =
          Cfg.ofWords anchor (stateWord (K + 1) (step g P x (pairEncode x s)))
        rw [MultiTapeTM.runFrom_succ_eq_step, hdisp, hall]
  -- Pay for binary fuel in the same polynomial budget, then apply the host.
  have hFuel : F.ComputesFunInTime (fun x => Nat.bits (R x.length)) T := by
    apply (FinTM.computesFunInTime_iff _ _ _).2
    intro x
    apply ((FinTM.computesFunInTime_iff _ _ _).1 hF x).mono
    have h := ModuleHost.request_budget aF dF D (2 * x.length + 2 + P.eval x.length + 5) x.length
      (by dsimp [D]; omega) (by omega)
    have hp := hpow x.length
    dsimp only [T, A, pow]
    simp only [Nat.add_mul]
    dsimp only [pow] at hp
    omega
  obtain ⟨L, c, hL⟩ := FinTM.exists_loopFindTM H F anchor (Inv P) (step g P)
    (fun _ w => acc (pairSndD w)) (fun _ w => out (pairSndD w)) (fun x => pairEncode x (init x))
    R T hFuel (fun x => ⟨init x, rfl, hbound x⟩)
    (fun x w h => inv_step g P x w h) hstart hround
  refine ⟨L, c, A, D, (FinTM.computesFunInTime_iff _ _ _).mpr fun x => ?_⟩
  have hx := (FinTM.computesFunInTime_iff _ _ _).mp hL x
  simp only [T, pow] at hx
  -- The combinator states its result with its own `match`; read both by cases on the search.
  revert hx
  cases (List.range (R x.length + 1)).find?
    (fun i => acc (pairSndD ((step g P x)^[i] (pairEncode x (init x))))) <;> exact id

/-- **The loop-level repetition lemma.** Let `g` be a polynomial-time step, `acc` a
polynomial-time test, `out` a polynomial-time payload map, and `R, P` syntactic polynomials
with `|g^[i] x| ≤ P|x|` for `i ≤ R|x|`. Then the function returning `out` of the orbit point
of the first index `i ≤ R|x|` at which `acc` accepts the second component of the `i`-fold
guarded step `Complexity.IterateFind.step g P x` from `⟨x, x⟩` (`[]` if none) is
polynomial-time computable. This is the machine behind
`Complexity.polyTimeComputable_iterateFind` [PS10, Algorithm 38.5, Theorem 35.1]; the pure
identification of the guarded orbit with `g^[i] x` is done there.

**Proof sketch.** The instance of `computesFunInTime_find` with the initial state `init = id`
(admissible, since `|x| ≤ P|x|` is the orbit bound at `i = 0`) and the fuel `R|x|`, whose
fuel machine computes `Nat.bits (R|x|)` (`polyTimeComputable_unaryPoly R` composed with
`computesFunInTime_lengthBits`, so that the `find?` range is exactly `R|x| + 1`).
`final_bound` puts its bound `c (T n + 1)(R n + 2)`, with `T n = A (2n + 2 + P n + 5)^D`, in
the normal form `C (n + 1)^e` of `Complexity.PolyTimeComputable`, once `P` and `R` are
majorised by `CP (n+1)^cP` and `CR (n+1)^cR` (`Complexity.PolyExpr.eval_le`). -/
theorem polyTimeComputable_find {g : List Bool → List Bool} (hg : PolyTimeComputable g)
    {acc : List Bool → Bool} (hacc : PolyTimeComputable fun s => [acc s])
    {out : List Bool → List Bool} (hout : PolyTimeComputable out)
    (R P : PolyExpr)
    (horbit : ∀ (x : List Bool) (i : ℕ), i ≤ R.eval x.length →
      (g^[i] x).length ≤ P.eval x.length) :
    PolyTimeComputable fun x =>
      match (List.range (R.eval x.length + 1)).find?
          (fun i => acc (pairSndD ((step g P x)^[i] (pairEncode x x)))) with
      | some i => out (pairSndD ((step g P x)^[i] (pairEncode x x)))
      | none => [] := by
  have hbits : PolyTimeComputable fun x => Nat.bits (R.eval x.length) := by
    have h := (polyTimeComputable_of_linear FinTM.computesFunInTime_lengthBits).comp
      (polyTimeComputable_unaryPoly R)
    convert h using 1
    funext x
    simp
  obtain ⟨F, aF, dF, hF⟩ := (polyTimeComputable_iff _).1 hbits
  obtain ⟨L, c, A, D, hL⟩ := computesFunInTime_find hg hacc hout polyTimeComputable_id
    (fun n => R.eval n) P (fun x => by simpa using horbit x 0 (Nat.zero_le _)) F aF dF hF
  obtain ⟨CP, cP, hCP⟩ := P.eval_le
  obtain ⟨CR, cR, hCR⟩ := R.eval_le
  refine (polyTimeComputable_iff _).2 ⟨L, c * (A * (CP + 7) ^ D + 1) * (CR + 2),
    (cP + 1) * D + cR, (FinTM.computesFunInTime_iff _ _ _).2 fun x => ?_⟩
  exact ((FinTM.computesFunInTime_iff _ _ _).1 hL x).mono
    (final_bound c A D CP cP CR cR x.length (P.eval x.length) (R.eval x.length) (hCP _) (hCR _))

end Complexity.IterateFind

## ===== TCSlib/Cryptography/Games/Tapes.lean (Lean, TS1 tree 1eaf940b938bb52e3919f5569893b58522df599b) =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Games.Hopping

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Simulation in law, coins in advance, and functions overridden by a table

Generic facts on simulations of oracle computations, stated for arbitrary oracle specifications.
They are the `Games` forms of the tools first proved for the encrypt-then-tag proof of
[PS10, Theorem 170.4] (`Composability.ETTGame`, `EncryptThenTag/Tools.lean`), with the tape
extension of `AdaptiveCPA.extTape` restated here.

* **Simulation through a state abstraction, in law** (`Games.expect_simulate_abs`): if every
  call of `impl₁` from the abstract image `f s` has the law of the call of `impl₂` from `s` with
  its new state abstracted, so do whole simulations, along runs within a query budget.
* **Coins in advance** (`Games.expect_simulate_tapeImpl`): an implementation that draws one fresh
  coin `t` per query (`Games.freshImpl`) has the law of the implementation that reads the `j`-th
  query's coin from a tape `T j` drawn in advance (`Games.tapeImpl`, `Games.extTape`), for
  computations with at most `κ` queries.
* **Functions overridden by a table** (`Games.ovr`): `ovr M R` is `R` with the values of the
  table `M` written over it; resampling `R` at a point outside the table moves into the table
  (`Games.expect_sample_ovr`).

## Main definitions

* `Games.freshImpl`, `Games.tapeImpl`: per-query coins drawn fresh, and read from tapes.
* `Games.extTape`: a finite family of coins extended to every index.
* `Games.ovr`: a function overridden by a finite table.

## Main results

* `Games.expect_simulate_abs`, `Games.expect_simulate_abs_inv`: simulation in law through a state
  abstraction.
* `Games.simulate_tapeImpl_congr`, `Games.expect_simulate_tapeImpl`: coins in advance.
* `Games.extTape_of_lt`, `Games.extTape_of_not_lt`, `Games.extTape_update`: the tape extension.
* `Games.ovr_nil`, `Games.ovr_cons`, `Games.ovr_of_not_mem`, `Games.ovr_of_mem`,
  `Games.ovr_update`, `Games.ovr_append`, `Games.expect_sample_ovr`: tables over functions.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  Theorem 170.4 (book p. 170): the first consumer.
-/

namespace TCSlib.Cryptography.Games

open ProbComp

/-! ### Simulation through a state abstraction, in law -/

section Abs

variable {ι : Type} {spec : OracleSpec ι} {σ₁ σ₂ α : Type}

/-- **Simulation through a state abstraction, in law, along runs with a query budget.** Let every
call of `impl₂` from a state `s` with `cnt s < κ` raise `cnt` by at most one, and give every
function `g` of the answer and the abstracted new state the expectation that the call of `impl₁`
from `f s` gives it. Then for a computation `c` with at most `m` queries and `cnt s + m ≤ κ`,
`𝔼[G] (simulate impl₁ c (f s)) = 𝔼[fun p => G (p.1, f p.2)] (simulate impl₂ c s)`.
Framework glue, no textbook counterpart.

**Proof sketch.** Induction on `c`. A query costs one unit, so it is asked from a state with
`cnt s < κ`: rewrite the call of `impl₁` by the hypothesis, and on each possible outcome of the
call of `impl₂` (where `cnt` grew by at most one) apply the induction hypothesis
(`expect_congr_of_allOutputs`). -/
protected theorem expect_simulate_abs (impl₁ : QueryImpl spec σ₁ unifSpec)
    (impl₂ : QueryImpl spec σ₂ unifSpec) (f : σ₂ → σ₁) (cnt : σ₂ → ℕ) (κ : ℕ)
    (h : ∀ i x s, cnt s < κ → ∀ g : spec.rng i × σ₁ → ℝ,
      expect (impl₁ i x (f s)) g = expect (impl₂ i x s) fun p => g (p.1, f p.2))
    (hcnt : ∀ i x s, cnt s < κ → (impl₂ i x s).AllOutputs fun p => cnt p.2 ≤ cnt s + 1)
    (c : OracleComp spec α) (m : ℕ) (hc : c.CostBoundedBy (fun _ => 1) m) (s : σ₂)
    (hs : cnt s + m ≤ κ) (G : α × σ₁ → ℝ) :
    expect (simulate impl₁ c (f s)) G = expect (simulate impl₂ c s) fun p => G (p.1, f p.2) := by
  induction c generalizing m s with
  | pure a => rw [simulate_pure, simulate_pure, expect_pure, expect_pure]
  | query i x k ih =>
    obtain ⟨hm, hk⟩ := (OracleComp.costBoundedBy_query _ _ _ _ _).1 hc
    have hm1 : 1 ≤ m := hm
    rw [simulate_query, simulate_query, expect_bind, expect_bind, h i x s (by omega)]
    refine expect_congr_of_allOutputs (hcnt i x s (by omega)) fun p _ => ?_
    exact ih p.1 (m - 1) (hk p.1) p.2 (by omega)

/-- **Simulation through a state abstraction, in law, along runs with a query budget and an
invariant:** as `Games.expect_simulate_abs`, with the hypotheses only on the states satisfying
an invariant `P` that every call of `impl₂` keeps: for `c` with at most `m` queries, `P s` and
`cnt s + m ≤ κ`, `𝔼[G | simulate impl₁ c (f s)] = 𝔼[fun p => G (p.1, f p.2) | simulate impl₂ c s]`.
Framework glue, no textbook counterpart.

**Proof sketch.** As `Games.expect_simulate_abs`, carrying `P` through the possible outcomes. -/
protected theorem expect_simulate_abs_inv (impl₁ : QueryImpl spec σ₁ unifSpec)
    (impl₂ : QueryImpl spec σ₂ unifSpec) (f : σ₂ → σ₁) (P : σ₂ → Prop) (cnt : σ₂ → ℕ) (κ : ℕ)
    (h : ∀ i x s, P s → cnt s < κ → ∀ g : spec.rng i × σ₁ → ℝ,
      expect (impl₁ i x (f s)) g = expect (impl₂ i x s) fun p => g (p.1, f p.2))
    (hcnt : ∀ i x s, P s → cnt s < κ →
      (impl₂ i x s).AllOutputs fun p => P p.2 ∧ cnt p.2 ≤ cnt s + 1)
    (c : OracleComp spec α) (m : ℕ) (hc : c.CostBoundedBy (fun _ => 1) m) (s : σ₂) (hP : P s)
    (hs : cnt s + m ≤ κ) (G : α × σ₁ → ℝ) :
    expect (simulate impl₁ c (f s)) G = expect (simulate impl₂ c s) fun p => G (p.1, f p.2) := by
  induction c generalizing m s with
  | pure a => rw [simulate_pure, simulate_pure, expect_pure, expect_pure]
  | query i x k ih =>
    obtain ⟨hm, hk⟩ := (OracleComp.costBoundedBy_query _ _ _ _ _).1 hc
    have hm1 : 1 ≤ m := hm
    rw [simulate_query, simulate_query, expect_bind, expect_bind, h i x s hP (by omega)]
    refine expect_congr_of_allOutputs (hcnt i x s hP (by omega)) fun p hp => ?_
    exact ih p.1 (m - 1) (hk p.1) p.2 hp.1 (by omega)

end Abs

/-! ### Coins drawn fresh and coins in advance -/

section Tapes

variable {ι : Type} {spec : OracleSpec ι} {σ τ α : Type}

/-- **One fresh coin per query:** the query `x` to oracle `i` in state `s` draws a uniform
`t ∈ τ`, then runs `K i x s t`: `freshImpl K i x s = (sample τ).bind (K i x s)`.
Framework glue, no textbook counterpart. -/
protected noncomputable def freshImpl [Fintype τ] [Nonempty τ]
    (K : ∀ i, spec.dom i → σ → τ → ProbComp (spec.rng i × σ)) : QueryImpl spec σ unifSpec :=
  fun i x s => (sample τ).bind (K i x s)

/-- The reader of `Games.freshImpl`: `freshImpl K i x s = (sample τ).bind (K i x s)`.
Framework glue, no textbook counterpart. -/
protected theorem freshImpl_apply [Fintype τ] [Nonempty τ]
    (K : ∀ i, spec.dom i → σ → τ → ProbComp (spec.rng i × σ)) (i : ι) (x : spec.dom i) (s : σ) :
    Games.freshImpl K i x s = (sample τ).bind (K i x s) :=
  rfl

/-- **A family of `κ` coins, extended to every index** by an arbitrary value:
`extTape T m = T ⟨m, hm⟩` for `hm : m < κ`, and `Classical.arbitrary C` otherwise.
Framework glue, no textbook counterpart. -/
protected noncomputable def extTape {C : Type} [Nonempty C] {κ : ℕ} (T : Fin κ → C) (m : ℕ) : C :=
  if hm : m < κ then T ⟨m, hm⟩ else Classical.arbitrary C

/-- Below `κ` the extended family is the family: `m < κ → extTape T m = T ⟨m, hm⟩`.
Framework glue, no textbook counterpart. -/
protected theorem extTape_of_lt {C : Type} [Nonempty C] {κ : ℕ} (T : Fin κ → C) {m : ℕ}
    (hm : m < κ) : Games.extTape T m = T ⟨m, hm⟩ := by
  rw [Games.extTape, dif_pos hm]

/-- From `κ` on the extended family is the arbitrary value:
`¬ m < κ → extTape T m = Classical.arbitrary C`. Framework glue, no textbook counterpart. -/
protected theorem extTape_of_not_lt {C : Type} [Nonempty C] {κ : ℕ} (T : Fin κ → C) {m : ℕ}
    (hm : ¬ m < κ) : Games.extTape T m = Classical.arbitrary C := by
  rw [Games.extTape, dif_neg hm]

/-- Changing one coordinate `j` of `T` changes its extension only at `j`:
`m ≠ j → extTape (update T j r) m = extTape T m`. Framework glue, no textbook counterpart. -/
protected theorem extTape_update {C : Type} [Nonempty C] {κ : ℕ} (T : Fin κ → C) (j : Fin κ)
    (r : C) {m : ℕ} (hm : m ≠ j) : Games.extTape (Function.update T j r) m = Games.extTape T m := by
  by_cases h : m < κ
  · rw [Games.extTape_of_lt _ h, Games.extTape_of_lt _ h, Function.update_of_ne]
    exact fun h' => hm (congrArg Fin.val h')
  · rw [Games.extTape_of_not_lt _ h, Games.extTape_of_not_lt _ h]

/-- **One coin per query, from tapes in advance:** the query `x` to oracle `i` in state `(s, j)`
runs `K i x s (T j)` and advances the query counter `j`,
`tapeImpl K T i x (s, j) = (K i x s (T j)).bind fun p => pure (p.1, (p.2, j + 1))`.
Framework glue, no textbook counterpart. -/
protected def tapeImpl (K : ∀ i, spec.dom i → σ → τ → ProbComp (spec.rng i × σ)) (T : ℕ → τ) :
    QueryImpl spec (σ × ℕ) unifSpec :=
  fun i x s => (K i x s.1 (T s.2)).bind fun p => .pure (p.1, (p.2, s.2 + 1))

/-- The reader of `Games.tapeImpl`:
`tapeImpl K T i x (s, j) = (K i x s (T j)).bind fun p => pure (p.1, (p.2, j + 1))`.
Framework glue, no textbook counterpart. -/
protected theorem tapeImpl_apply (K : ∀ i, spec.dom i → σ → τ → ProbComp (spec.rng i × σ))
    (T : ℕ → τ) (i : ι) (x : spec.dom i) (s : σ) (j : ℕ) :
    Games.tapeImpl K T i x (s, j) = (K i x s (T j)).bind fun p => .pure (p.1, (p.2, j + 1)) :=
  rfl

/-- **The run from the counter `j` ignores the tapes below `j`:** if `T m = T' m` for every
`m ≥ j`, then `simulate (tapeImpl K T) c (s, j) = simulate (tapeImpl K T') c (s, j)`.
Framework glue, no textbook counterpart.

**Proof sketch.** Induction on the computation: a query at counter `j' ≥ j` reads `T j'` and
moves to `j' + 1`. -/
protected theorem simulate_tapeImpl_congr
    (K : ∀ i, spec.dom i → σ → τ → ProbComp (spec.rng i × σ))
    (T T' : ℕ → τ) (c : OracleComp spec α) (s : σ) (j : ℕ) (hT : ∀ m, j ≤ m → T m = T' m) :
    simulate (Games.tapeImpl K T) c (s, j) = simulate (Games.tapeImpl K T') c (s, j) := by
  induction c generalizing s j with
  | pure a => rw [simulate_pure, simulate_pure]
  | query i x k ih =>
    rw [simulate_query, simulate_query, Games.tapeImpl_apply, Games.tapeImpl_apply,
      hT j le_rfl, OracleComp.bind_assoc, OracleComp.bind_assoc]
    congr 1
    funext p
    rw [OracleComp.pure_bind, OracleComp.pure_bind]
    exact ih p.1 p.2 (j + 1) fun m hm => hT m (by omega)

/-- **Coins in advance have the law of fresh coins:** for a computation with at most `m`
queries, a counter `j` with `j + m ≤ κ`, and every function `G` of the output,
`𝔼_{T ← τ^κ} 𝔼[G (simulate (tapeImpl K (extTape T)) c (s, j))] = 𝔼[G (simulate (freshImpl K) c s)]`.
Framework glue, no textbook counterpart.

**Proof sketch.** Induction on `c`, generalizing the counter, the state and the budget. A query
costs one unit, so it reads the tape `T j` with `j < κ`; the continuation runs from `j + 1`, so
it ignores `T j` (`Games.simulate_tapeImpl_congr`, `Games.extTape_update`), and
`ProbComp.expect_sample_coord` replaces `T j` by the fresh coin of `freshImpl`
(`expect_expect_sample` exchanges the tape with the call). -/
protected theorem expect_simulate_tapeImpl [Fintype τ] [Nonempty τ]
    (K : ∀ i, spec.dom i → σ → τ → ProbComp (spec.rng i × σ))
    (κ : ℕ) (G : α → ℝ) (c : OracleComp spec α) (m : ℕ) (hc : c.CostBoundedBy (fun _ => 1) m)
    (s : σ) (j : ℕ) (hj : j + m ≤ κ) :
    expect (sample (Fin κ → τ))
        (fun T => expect (simulate (Games.tapeImpl K (Games.extTape T)) c (s, j)) fun p => G p.1) =
      expect (simulate (Games.freshImpl K) c s) fun p => G p.1 := by
  induction c generalizing m s j with
  | pure a =>
    simp only [simulate_pure, expect_pure]
    exact expect_const _ _
  | query i x k ih =>
    obtain ⟨hm, hk⟩ := (OracleComp.costBoundedBy_query _ _ _ _ _).1 hc
    have hm1 : 1 ≤ m := hm
    have hjk : j < κ := by omega
    let jj : Fin κ := ⟨j, hjk⟩
    have hT : ∀ T : Fin κ → τ, Games.extTape T j = T jj :=
      fun T => Games.extTape_of_lt T hjk
    simp only [simulate_query, Games.tapeImpl_apply, Games.freshImpl_apply, OracleComp.bind_assoc,
      OracleComp.pure_bind, expect_bind, hT]
    refine (expect_sample_coord jj (fun t T => expect (K i x s t) fun p =>
      expect (simulate (Games.tapeImpl K (Games.extTape T)) (k p.1) (p.2, j + 1))
        fun q => G q.1) ?_).trans ?_
    · intro t t' T
      refine congrArg _ (funext fun p => ?_)
      refine congrArg (fun c => expect c fun q => G q.1)
        (Games.simulate_tapeImpl_congr K _ _ _ _ _ fun m' hm' => ?_)
      exact Games.extTape_update T jj t' (by
        intro h
        have : m' = j := h
        omega)
    · refine congrArg _ (funext fun t => ?_)
      rw [← expect_expect_sample]
      refine congrArg _ (funext fun p => ?_)
      exact ih p.1 (m - 1) (hk p.1) p.2 (j + 1) (by omega)

end Tapes

/-! ### Functions overridden by a table -/

section Override

variable {κ β : Type} [DecidableEq κ]

/-- **A function overridden by a table:** `ovr M R` is `R` with the entries `(p, y)` of `M`
written over it, the first entry of a key winning: `ovr [] R = R`,
`ovr ((p, y) :: M) R = update (ovr M R) p y`. Framework glue, no textbook counterpart. -/
protected def ovr : List (κ × β) → (κ → β) → κ → β
  | [], R => R
  | e :: M, R => Function.update (Games.ovr M R) e.1 e.2

/-- The reader of `Games.ovr` on the empty table: `ovr [] R = R`.
Framework glue, no textbook counterpart. -/
protected theorem ovr_nil (R : κ → β) : Games.ovr ([] : List (κ × β)) R = R :=
  rfl

/-- The reader of `Games.ovr` on a nonempty table: `ovr ((p, y) :: M) R = update (ovr M R) p y`.
Framework glue, no textbook counterpart. -/
protected theorem ovr_cons (p : κ) (y : β) (M : List (κ × β)) (R : κ → β) :
    Games.ovr ((p, y) :: M) R = Function.update (Games.ovr M R) p y :=
  rfl

/-- Outside the keys of the table, the overridden function is `R`:
`p ∉ M.map Prod.fst → ovr M R p = R p`. Framework glue, no textbook counterpart. -/
protected theorem ovr_of_not_mem {M : List (κ × β)} {p : κ} (hp : p ∉ M.map Prod.fst)
    (R : κ → β) : Games.ovr M R p = R p := by
  induction M with
  | nil => rw [Games.ovr_nil]
  | cons e M ih =>
    obtain ⟨q, y⟩ := e
    rw [List.map_cons, List.mem_cons, not_or] at hp
    rw [Games.ovr_cons, Function.update_of_ne hp.1]
    exact ih hp.2

/-- On the keys of the table, the overridden function does not read `R`:
`p ∈ M.map Prod.fst → ovr M R p = ovr M R' p`. Framework glue, no textbook counterpart. -/
protected theorem ovr_of_mem {M : List (κ × β)} {p : κ} (hp : p ∈ M.map Prod.fst)
    (R R' : κ → β) : Games.ovr M R p = Games.ovr M R' p := by
  induction M with
  | nil => rw [List.map_nil] at hp; exact absurd hp List.not_mem_nil
  | cons e M ih =>
    obtain ⟨q, y⟩ := e
    rw [Games.ovr_cons, Games.ovr_cons]
    by_cases hpq : p = q
    · subst hpq
      rw [Function.update_self, Function.update_self]
    · rw [Function.update_of_ne hpq, Function.update_of_ne hpq]
      rw [List.map_cons, List.mem_cons] at hp
      exact ih (hp.resolve_left hpq)

/-- Changing `R` at a point outside the table changes the overridden function there only:
`p ∉ M.map Prod.fst → ovr M (update R p y) = update (ovr M R) p y`.
Framework glue, no textbook counterpart. -/
protected theorem ovr_update {M : List (κ × β)} {p : κ} (hp : p ∉ M.map Prod.fst) (R : κ → β)
    (y : β) : Games.ovr M (Function.update R p y) = Function.update (Games.ovr M R) p y := by
  induction M with
  | nil => rw [Games.ovr_nil, Games.ovr_nil]
  | cons e M ih =>
    obtain ⟨q, z⟩ := e
    rw [List.map_cons, List.mem_cons, not_or] at hp
    rw [Games.ovr_cons, Games.ovr_cons, ih hp.2]
    exact Function.update_comm hp.1 _ _ _

/-- Writing a concatenation is writing its parts: `ovr (A ++ B) R = ovr A (ovr B R)`.
Framework glue, no textbook counterpart. -/
protected theorem ovr_append (A B : List (κ × β)) (R : κ → β) :
    Games.ovr (A ++ B) R = Games.ovr A (Games.ovr B R) := by
  induction A with
  | nil => rw [List.nil_append, Games.ovr_nil]
  | cons e A ih =>
    obtain ⟨p, y⟩ := e
    rw [List.cons_append, Games.ovr_cons, Games.ovr_cons, ih]

/-- **Resampling a point outside the table moves it into the table:** for `p` not a key of `M`,
`𝔼_R F (R p) (ovr M R) = 𝔼_y 𝔼_R F y (ovr ((p, y) :: M) R)`.
Framework glue, no textbook counterpart.

**Proof sketch.** `ProbComp.expect_sample_coord` at the coordinate `p` with
`F' y R = F y (ovr ((p, y) :: M) R)`, which does not read `R p` (`Games.ovr_update`,
`Function.update_idem`); at `y = R p` the new entry repeats `ovr M R p = R p`
(`Games.ovr_of_not_mem`, `Function.update_eq_self`). -/
protected theorem expect_sample_ovr [Fintype κ] [Fintype β] [Nonempty β] (M : List (κ × β))
    {p : κ} (hp : p ∉ M.map Prod.fst) (F : β → (κ → β) → ℝ) :
    expect (sample (κ → β)) (fun R => F (R p) (Games.ovr M R)) =
      expect (sample β) fun y =>
        expect (sample (κ → β)) fun R => F y (Games.ovr ((p, y) :: M) R) := by
  have h := expect_sample_coord p (fun y R => F y (Games.ovr ((p, y) :: M) R)) fun y y' R => by
    show F y (Games.ovr ((p, y) :: M) (Function.update R p y')) =
      F y (Games.ovr ((p, y) :: M) R)
    rw [Games.ovr_cons, Games.ovr_cons, Games.ovr_update hp, Function.update_idem]
  refine Eq.trans ?_ h
  refine congrArg _ (funext fun R => ?_)
  show F (R p) (Games.ovr M R) = F (R p) (Games.ovr ((p, R p) :: M) R)
  rw [Games.ovr_cons, ← Games.ovr_of_not_mem hp R, Function.update_eq_self]

end Override

end TCSlib.Cryptography.Games

## ===== TCSlib/Cryptography/ZeroKnowledge/InteractionWords.lean (Lean, TS1 tree 1eaf940b938bb52e3919f5569893b58522df599b) =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.ZeroKnowledge.Interaction
import TCSlib.Complexity.ClassP.BinaryArith.Words

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The history encoding as a word list

The string encoding `Strategy.encodeMsgs` of the received-messages component of a view
[PS10, §4.4] is the word-list encoding `Complexity.BinArith.encWords` of the machine layer: both
are the concatenation of the self-delimiting messages `⟨m, []⟩`. The bridge lives in its own
module so that `ZeroKnowledge/Interaction.lean` does not import the binary-arithmetic machines.

## Main definitions

None; this module proves one bridge lemma.

## Main results

* `TCSlib.Cryptography.Strategy.encodeMsgs_eq_encWords` — `encodeMsgs L = BinArith.encWords L`.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  §4.4.
-/

namespace TCSlib.Cryptography.Strategy

/-- **The history encoding is the word-list encoding:** for every list of words `L`,
`encodeMsgs L = Complexity.BinArith.encWords L` (both are `L.flatMap fun m => ⟨m, []⟩`).
Framework glue, no textbook counterpart. -/
protected theorem encodeMsgs_eq_encWords (L : List (List Bool)) :
    encodeMsgs L = Complexity.BinArith.encWords L := by
  rw [Strategy.encodeMsgs_eq_flatMap, Complexity.BinArith.encWords_def]

end TCSlib.Cryptography.Strategy

## ===== TCSlib/Cryptography/Pseudorandom/Functions/LazySampling.lean (Lean, TS1 tree 1eaf940b938bb52e3919f5569893b58522df599b) =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Pseudorandom.Functions.OracleAdversary
import Mathlib.Data.Fintype.Pi

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Lazy sampling of a random oracle

A random function `R : I → O` has `|O|^|I|` values, far too many for an efficient
reduction to sample. An oracle algorithm making at most `q` queries only ever looks at
`q` of them, and the standard remedy [Gar26, footnote 9 of §3.4] is *lazy sampling*: keep
a list of the distinct queries seen so far, answer a repeated query consistently, and
answer the `k`-th new query with a fresh value `W k`. This file proves that lazy
sampling with `q` uniform values `W : Fin q → O` produces exactly the same output
distribution as a uniform random function.

The lazy run is stated for an arbitrary answer stream `a : ℕ → O` (the answer to the
`k`-th distinct query is `a k`), so that hybrids can mix fresh values with other
answers index by index.

## Main definitions

* `QueryTree.noteQuery L x`: the list of distinct queries after querying `x`.
* `QueryTree.evalLazy a t L`: run `t`, answering the `k`-th distinct query by `a k`.
* `extendStream W`: a finite list of values `W : Fin q → O` as an answer stream.
* `lazyDist A` evaluates the oracle adversary against an answer stream.

## Main results

* `QueryTree.evalLazy_congr`: a run making at most `m` more queries only reads the first
  `L.length + m` entries of the answer stream.
* `QueryTree.uprob_evalLazy`: lazy sampling with `q` uniform fresh values has the same
  output distribution as a uniform random function, for trees making at most `q`
  queries.
* Probability helpers: `uprob_congr`, `uprob_prod_comm`, `uprob_snd`,
  `uprob_sections_congr`, `uprob_update_absorb`, `uprob_update_split`.

## References

* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, §3.4.2, footnote 9 (lazy sampling of random functions).
-/

namespace TCSlib.Cryptography

open Function

section Helpers

variable {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]

/-- Events that are equivalent pointwise have the same probability. -/
theorem uprob_congr {p p' : α → Prop} (h : ∀ a, p a ↔ p' a) : uprob p = uprob p' :=
  congrArg uprob (funext fun a => propext (h a))

/-- Swapping the two coordinates of a product does not change probabilities. -/
theorem uprob_prod_comm (p : α → β → Prop) :
    uprob (fun z : α × β => p z.1 z.2) = uprob (fun z : β × α => p z.2 z.1) :=
  (uprob_comp_equiv (Equiv.prodComm β α) (fun z : α × β => p z.1 z.2)).symm

/-- An event depending only on the second coordinate has the same probability on the
product. -/
theorem uprob_snd [Nonempty α] (p : β → Prop) :
    uprob (fun z : α × β => p z.2) = uprob p := by
  rw [uprob_prod_comm (fun _ b => p b)]
  exact uprob_fst p

/-- Two events on products with the same first factor have the same probability when
every section has the same probability. -/
theorem uprob_sections_congr (p : α → β → Prop) (p' : α → γ → Prop)
    (h : ∀ a, uprob (p a) = uprob (p' a)) :
    uprob (fun z : α × β => p z.1 z.2) = uprob (fun z : α × γ => p' z.1 z.2) := by
  rw [uprob_prod, uprob_prod]
  exact congrArg uexp (funext h)

variable [DecidableEq α]

/-- Overwriting one entry of a uniform table by an independent uniform value leaves the
table uniform: the overwritten entry is absorbed. -/
theorem uprob_update_absorb [Nonempty β] (i : α) (f : (α → β) → γ → Prop) :
    uprob (fun z : β × ((α → β) × γ) => f (update z.2.1 i z.1) z.2.2) =
      uprob (fun z : (α → β) × γ => f z.1 z.2) := by
  let e : β × ((α → β) × γ) ≃ ((α → β) × γ) × β :=
    { toFun := fun z => ((update z.2.1 i z.1, z.2.2), z.2.1 i)
      invFun := fun w => (w.1.1 i, (update w.1.1 i w.2, w.1.2))
      left_inv := fun z => by simp
      right_inv := fun w => by simp }
  exact (uprob_comp_equiv e (fun w => f w.1.1 w.1.2)).trans
    (uprob_fst (fun w : (α → β) × γ => f w.1 w.2))

/-- Overwriting one entry of a uniform table by an independent uniform value leaves the
table uniform (version without extra coordinates). -/
theorem uprob_update_absorb' [Nonempty β] (i : α) (f : (α → β) → Prop) :
    uprob (fun z : β × (α → β) => f (update z.2 i z.1)) = uprob f := by
  let e : β × (α → β) ≃ (α → β) × β :=
    { toFun := fun z => (update z.2 i z.1, z.2 i)
      invFun := fun w => (w.1 i, update w.1 i w.2)
      left_inv := fun z => by simp
      right_inv := fun w => by simp }
  exact (uprob_comp_equiv e (fun w => f w.1)).trans (uprob_fst f)

/-- If an event on a uniform table `W` depends on the entry `W i` only through a
parameter `v` (it does not otherwise read position `i`), its probability is the average
over `v` of the probability with `v` fixed. -/
theorem uprob_update_split [Nonempty β] (i : α) (g : β → (α → β) → Prop)
    (hg : ∀ v W u, g v (update W i u) ↔ g v W) :
    uprob (fun W => g (W i) W) = uexp (fun v => uprob (fun W => g v W)) := by
  rw [← uprob_prod (fun z : β × (α → β) => g z.1 z.2),
    ← uprob_update_absorb' i (fun W => g (W i) W)]
  exact uprob_congr fun z => by simp [hg]

end Helpers

namespace QueryTree

variable {I O α : Type} [DecidableEq I]

/-- The list of distinct queries after the query `x`, given the list `L` of distinct
queries so far: `x` is appended if it is new. -/
def noteQuery (L : List I) (x : I) : List I := if x ∈ L then L else L ++ [x]

/-- A repeated query leaves the list of distinct queries unchanged. -/
theorem noteQuery_of_mem {L : List I} {x : I} (h : x ∈ L) : noteQuery L x = L := if_pos h

/-- A new query is appended to the list of distinct queries. -/
theorem noteQuery_of_not_mem {L : List I} {x : I} (h : x ∉ L) : noteQuery L x = L ++ [x] :=
  if_neg h

/-- The index of the current query in the updated list is below its length. -/
theorem idxOf_noteQuery_lt (L : List I) (x : I) :
    (noteQuery L x).idxOf x < (noteQuery L x).length := by
  rw [List.idxOf_lt_length_iff]
  unfold noteQuery; split_ifs with h <;> simp [h]

/-- Querying adds at most one entry to the list of distinct queries. -/
theorem length_noteQuery_le (L : List I) (x : I) :
    (noteQuery L x).length ≤ L.length + 1 := by
  unfold noteQuery; split_ifs <;> simp

/-- Run `t` against a lazily sampled oracle: with `L` the list of distinct queries so
far, the query `x` is answered by `a k`, where `k` is the position of `x` among the
distinct queries in order of first appearance. A repeated query gets the same answer as
before. [Gar26, §3.4.2, footnote 9]. -/
def evalLazy (a : ℕ → O) : QueryTree I O α → List I → α
  | ret y, _ => y
  | query x k, L =>
      evalLazy a (k (a ((noteQuery L x).idxOf x))) (noteQuery L x)

/-- A leaf returns its output whatever the answers. -/
@[simp] theorem evalLazy_ret (a : ℕ → O) (y : α) (L : List I) :
    evalLazy a (ret y) L = y := rfl

/-- A query is recorded and answered by the stream entry at its position. -/
theorem evalLazy_query (a : ℕ → O) (x : I) (k : O → QueryTree I O α) (L : List I) :
    evalLazy a (query x k) L =
      evalLazy a (k (a ((noteQuery L x).idxOf x))) (noteQuery L x) := rfl

/-- A run making at most `m` further queries, started with `L` distinct queries already
seen, only reads the answer stream below `L.length + m`. -/
theorem evalLazy_congr {a b : ℕ → O} {t : QueryTree I O α} {m : ℕ} (ht : t.BoundedBy m)
    (L : List I) (hab : ∀ k < L.length + m, a k = b k) :
    evalLazy a t L = evalLazy b t L := by
  induction t using QueryTree.induct generalizing m L with
  | ret y => rfl
  | query x k ih =>
    cases m with
    | zero => exact absurd ht (boundedBy_query_zero x k)
    | succ m =>
      have h1 := idxOf_noteQuery_lt L x
      have h2 := length_noteQuery_le L x
      rw [evalLazy_query, evalLazy_query, hab _ (by omega)]
      exact ih _ ((boundedBy_query_succ x k m).1 ht _) _ fun j hj => hab j (by omega)

/-- Post-processing every lazy answer by `g` is the same as running the tree whose
answers are post-processed by `g`. -/
theorem evalLazy_comp {O' : Type} (g : O' → O) (a : ℕ → O') (t : QueryTree I O α)
    (L : List I) :
    evalLazy (g ∘ a) t L = evalLazy a (t.simulate id (fun _ => g)) L := by
  induction t using QueryTree.induct generalizing L with
  | ret y => rw [simulate_ret, evalLazy_ret, evalLazy_ret]
  | query x k ih =>
    rw [simulate_query, evalLazy_query, evalLazy_query]
    exact ih _ _

end QueryTree

/-- A finite list `W : Fin q → O` of values as an answer stream; entries beyond `q` are
an arbitrary fixed value and are never read by trees making at most `q` queries. -/
noncomputable def extendStream {O : Type*} [Nonempty O] {q : ℕ} (W : Fin q → O) : ℕ → O :=
  fun k => if h : k < q then W ⟨k, h⟩ else Classical.arbitrary O

/-- The defining equation of `extendStream`: `extendStream W = fun k => if h : k < q then W ⟨k, h⟩
else Classical.arbitrary O`. -/
theorem extendStream_def {O : Type*} [Nonempty O] {q : ℕ} (W : Fin q → O) :
    (extendStream W : ℕ → O) =
      (fun k => if h : k < q then W ⟨k, h⟩ else Classical.arbitrary O :
        ℕ → O) := rfl

namespace QueryTree

variable {I : Type*} {O : Type*} {α : Type*} [DecidableEq I]

/-- A constant event has the same probability on any two nonempty finite types. -/
private theorem uprob_const_eq {β γ : Type*} [Fintype β] [Fintype γ] [Nonempty β]
    [Nonempty γ] (P : Prop) : uprob (fun _ : β => P) = uprob (fun _ : γ => P) := by
  by_cases h : P
  · rw [uprob_congr (p' := fun _ : β => True) (fun _ => iff_true_intro h),
      uprob_congr (p' := fun _ : γ => True) (fun _ => iff_true_intro h), uprob_true,
      uprob_true]
  · rw [uprob_congr (p' := fun _ : β => False) (fun _ => iff_false_intro h),
      uprob_congr (p' := fun _ : γ => False) (fun _ => iff_false_intro h), uprob_false,
      uprob_false]

/-- Keep the first `ℓ` entries of `W₀` and take the remaining entries from `W`. -/
private def combine {q : ℕ} (ℓ : ℕ) (W₀ W : Fin q → O) : Fin q → O :=
  fun i => if i.val < ℓ then W₀ i else W i

/-- The table answering a recorded query `x ∈ L` from the stream `a` at the position of `x`
in `L`, and every other query from `R`. -/
private def mergeTable (L : List I) (a : ℕ → O) (R : I → O) : I → O :=
  fun x => if x ∈ L then a (L.idxOf x) else R x

section Streams

variable [Nonempty O] {q : ℕ}

/-- Overwriting entry `j` of a value list does not change the stream at other positions. -/
theorem extendStream_update_of_ne (W : Fin q → O) (j : Fin q) (v : O) {k : ℕ}
    (hk : k ≠ j.val) : extendStream (update W j v) k = extendStream W k := by
  unfold extendStream
  split_ifs with h
  · exact update_of_ne (fun e => hk (by rw [← e])) _ _
  · rfl

/-- Overwriting entry `j` of a value list by `v` makes the stream read `v` at `j`. -/
theorem extendStream_update_self (W : Fin q → O) (j : Fin q) (v : O) :
    extendStream (update W j v) j.val = v := by
  simp [extendStream]

private theorem extendStream_combine_of_lt (W₀ W : Fin q → O) {ℓ k : ℕ} (hk : k < ℓ) :
    extendStream (combine ℓ W₀ W) k = extendStream W₀ k := by
  unfold extendStream combine
  split_ifs <;> simp_all

private theorem extendStream_combine_self (W₀ W : Fin q → O) {ℓ : ℕ} (hℓ : ℓ < q) :
    extendStream (combine ℓ W₀ W) ℓ = W ⟨ℓ, hℓ⟩ := by
  simp [extendStream, combine, hℓ]

omit [Nonempty O] in
private theorem combine_succ (W₀ W : Fin q → O) {ℓ : ℕ} (hℓ : ℓ < q) :
    combine ℓ W₀ W = combine (ℓ + 1) (update W₀ ⟨ℓ, hℓ⟩ (W ⟨ℓ, hℓ⟩)) W := by
  funext i
  unfold combine
  by_cases h1 : i.val < ℓ
  · have : i ≠ ⟨ℓ, hℓ⟩ := fun e => by rw [e] at h1; exact lt_irrefl _ h1
    simp [h1, Nat.lt_succ_of_lt h1, this]
  · by_cases h2 : i.val = ℓ
    · have : i = ⟨ℓ, hℓ⟩ := Fin.ext h2
      subst this; simp
    · have : ¬ i.val < ℓ + 1 := by omega
      simp [h1, this]

omit [Nonempty O] in
private theorem combine_update (W₁ W : Fin q → O) {ℓ : ℕ} (hℓ : ℓ < q) (u : O) :
    combine (ℓ + 1) W₁ (update W ⟨ℓ, hℓ⟩ u) = combine (ℓ + 1) W₁ W := by
  funext i
  unfold combine
  by_cases h : i.val < ℓ + 1
  · simp [h]
  · have : i ≠ ⟨ℓ, hℓ⟩ := fun e => by rw [e] at h; exact h (Nat.lt_succ_self _)
    simp [h, this]

private theorem mergeTable_append (W₀ : Fin q → O) (R : I → O) {L : List I} {x : I}
    (hx : x ∉ L) (hℓ : L.length < q) :
    mergeTable L (extendStream W₀) R =
      mergeTable (L ++ [x]) (extendStream (update W₀ ⟨L.length, hℓ⟩ (R x))) R := by
  funext y
  unfold mergeTable
  by_cases hy : y ∈ L
  · have hlt := List.idxOf_lt_length_of_mem hy
    rw [if_pos hy, if_pos (List.mem_append_left _ hy), List.idxOf_append_of_mem hy,
      extendStream_update_of_ne _ _ _ (by simp; omega)]
  · by_cases hyx : y = x
    · subst hyx
      rw [if_neg hy, if_pos (by simp), List.idxOf_append_of_notMem hy]
      simpa using (extendStream_update_self W₀ ⟨L.length, hℓ⟩ (R y)).symm
    · rw [if_neg hy, if_neg (by simp [hy, hyx])]

omit [Nonempty O] in
private theorem mergeTable_update (L : List I) (a : ℕ → O) (R : I → O) {x : I} (hx : x ∈ L)
    (u : O) : mergeTable L a (update R x u) = mergeTable L a R := by
  funext y
  unfold mergeTable
  by_cases hy : y ∈ L
  · simp [hy]
  · have : y ≠ x := fun e => hy (e ▸ hx)
    simp [hy, this]

end Streams

end QueryTree

namespace QueryTree

variable {I O α : Type} [DecidableEq I]

/-- The generalized lazy-sampling invariant: started with `L` already recorded, with
answers `W₀` on `L`, the lazy run with fresh values beyond `L` and the run against a
random function agreeing with `W₀` on `L` have the same output distribution.

**Proof sketch.** Induction on the tree. A repeated query is answered by the recorded
value on both sides. For a new query `x`, the lazy side answers with the fresh entry at
position `|L|` and the table side with `R x`; record this answer `v` in `W₀`. Neither
continuation reads the entry again, so both probabilities are averages over `v` of the
continuation probabilities (`uprob_update_split`), which agree by induction. -/
private theorem uprob_evalLazy_aux [Fintype I] [Fintype O] [Nonempty O] (φ : α → Prop)
    {q : ℕ} (t : QueryTree I O α) : ∀ (m : ℕ) (L : List I) (W₀ : Fin q → O),
    t.BoundedBy m → L.length + m ≤ q →
    uprob (fun W : Fin q → O => φ (evalLazy (extendStream (combine L.length W₀ W)) t L)) =
      uprob (fun R : I → O => φ (t.eval (mergeTable L (extendStream W₀) R))) := by
  induction t using QueryTree.induct with
  | ret y =>
    intro _ _ _ _ _
    simp only [evalLazy_ret, eval_ret]
    exact uprob_const_eq (β := Fin q → O) (γ := I → O) (φ y)
  | query x k ih =>
    intro m L W₀ ht hm
    cases m with
    | zero => exact absurd ht (boundedBy_query_zero x k)
    | succ m =>
    by_cases hx : x ∈ L
    · -- a repeated query: both sides answer with the recorded value
      have hi : L.idxOf x < L.length := List.idxOf_lt_length_of_mem hx
      have hl : ∀ W, evalLazy (extendStream (combine L.length W₀ W)) (query x k) L =
          evalLazy (extendStream (combine L.length W₀ W)) (k (extendStream W₀ (L.idxOf x)))
            L := by
        intro W
        rw [evalLazy_query, noteQuery_of_mem hx, extendStream_combine_of_lt _ _ hi]
      have hr : ∀ R, (query x k).eval (mergeTable L (extendStream W₀) R) =
          (k (extendStream W₀ (L.idxOf x))).eval (mergeTable L (extendStream W₀) R) := by
        intro R; simp [mergeTable, hx]
      simp only [hl, hr]
      exact ih _ m L W₀ ((boundedBy_query_succ x k m).1 ht _) (by omega)
    · -- a new query: split off the fresh value on both sides
      have hℓ : L.length < q := by omega
      have hidx : (L ++ [x]).idxOf x = L.length := by
        rw [List.idxOf_append_of_notMem hx]; simp
      have hlen : (L ++ [x]).length = L.length + 1 := by simp
      let j : Fin q := ⟨L.length, hℓ⟩
      let g : O → (Fin q → O) → Prop := fun v W =>
        φ (evalLazy (extendStream (combine (L ++ [x]).length (update W₀ j v) W)) (k v)
          (L ++ [x]))
      let h : O → (I → O) → Prop := fun v R =>
        φ ((k v).eval (mergeTable (L ++ [x]) (extendStream (update W₀ j v)) R))
      have hl : ∀ W, φ (evalLazy (extendStream (combine L.length W₀ W)) (query x k) L) ↔
          g (W j) W := by
        intro W
        simp only [g, evalLazy_query, noteQuery_of_not_mem hx, hidx, hlen,
          extendStream_combine_self _ _ hℓ, ← combine_succ _ _ hℓ, j]
      have hr : ∀ R, φ ((query x k).eval (mergeTable L (extendStream W₀) R)) ↔
          h (R x) R := by
        intro R
        simp only [h, eval_query, ← mergeTable_append W₀ R hx hℓ, j]
        simp [mergeTable, hx]
      rw [uprob_congr hl, uprob_congr hr,
        uprob_update_split j g (fun v W u => by simp only [g, hlen, j, combine_update]),
        uprob_update_split x h (fun v R u => by
          simp only [h, mergeTable_update _ _ _ (List.mem_append_right L
            (List.mem_singleton_self x))])]
      exact congrArg uexp (funext fun v =>
        ih v m (L ++ [x]) (update W₀ j v) ((boundedBy_query_succ x k m).1 ht v)
          (by rw [hlen]; omega))

/-- **Lazy sampling.** For a query tree making at most `q` queries, answering the `k`-th
distinct query by the `k`-th of `q` independent uniform values gives the same output
distribution as answering by a uniform random function. [Gar26, §3.4.2, footnote 9],
stated as an exact equality of probabilities for every event on the output.

**Proof sketch.** Generalize to a run started with a list `L` of `ℓ` distinct queries
whose answers are fixed values `W₀`, against a random function that agrees with `W₀` on
`L`. A repeated query is answered by the fixed value on both sides. A new query is
answered by the fresh value `W ℓ` on the lazy side and by `R x` on the table side; in
both cases the rest of the run does not read this entry again except through the
recorded answer, so both probabilities are the average over the answer `v` of the
probability of the continuation with `v` recorded, which agree by induction. -/
theorem uprob_evalLazy [Fintype I] [Fintype O] [Nonempty O] (φ : α → Prop)
    {t : QueryTree I O α} {q : ℕ} (ht : t.BoundedBy q) :
    uprob (fun W : Fin q → O => φ (evalLazy (extendStream W) t [])) =
      uprob (fun R : I → O => φ (t.eval R)) := by
  have h := uprob_evalLazy_aux (q := q) φ t q [] (fun _ => Classical.arbitrary O) ht (by simp)
  have h1 : ∀ W : Fin q → O, combine ([] : List I).length (fun _ => Classical.arbitrary O) W = W :=
    fun W => funext fun i => by simp [combine]
  have h2 : ∀ R : I → O, mergeTable [] (extendStream fun _ : Fin q => Classical.arbitrary O)
      R = R := fun R => funext fun y => by simp [mergeTable]
  simpa only [h1, h2] using h

end QueryTree

section LazyDistinguisher

variable {P V : Type} {ρ : Type*} [DecidableEq P]

/-- The oracle adversary `A` run with lazily sampled answers given by an answer stream. -/
def lazyDist (A : OracleAdversary ρ P V) : (ℕ → V) → ρ → Bool :=
  fun a r => (A r).evalLazy a []

/-- On the answer stream `a` and coins `r`, `lazyDist A` is the lazy run of `A r` from the empty
list of distinct queries: `lazyDist A a r = (A r).evalLazy a []`. -/
theorem lazyDist_apply (A : OracleAdversary ρ P V) (a : ℕ → V) (r : ρ) :
    lazyDist A a r = (A r).evalLazy a [] :=
  rfl

end LazyDistinguisher

end TCSlib.Cryptography

## ===== policy.md (records, at 659542ecd9413b504d30da8c937b9805e6c1f71f) =====

# TCSlib Contribution Policy

Standards for all Lean contributions to this repository, whether written by humans or by
agents. This document covers three things: **modularity** (how code is organized),
**attribution** (how every result is traced to a source), and **proof sketches** (how every
formal proof is accompanied by readable mathematics).

It complements, and does not replace:

- `workflow.md` — the campaign formalization process (phases, audit gates, fill epochs)
  that produces code meeting these standards.
- `.github/copilot-instructions.md` — build workflows, import rules, CI integration points.
- `AGENTS.md` / `.claude/CLAUDE.md` — the sorry-ladder proof workflow and agent roster.
- `blueprint/BLUEPRINT_PIPELINE.md` — how blueprint entries are generated and validated.

Where this document names an existing mechanism (blueprint macros, hygiene scripts), the
policy is to *use that mechanism*, not to invent a parallel one.

## 1. Modularity

**Layout.** Content lives at `TCSlib/<Area>/<Topic>/<Piece>.lean`, one coherent concept or
lemma cluster per file, with a facade file `TCSlib/<Area>/<Topic>.lean` that imports every
child and carries a `/-! -/` module docstring with a `## Contents` list (one line per child).
See `TCSlib/Complexity/NPReductions.lean` for the reference example.

**File size.** Target 150–600 lines per math file. A file approaching 1000 lines should be
split unless there is a positive reason not to (e.g. a single long proof that cannot be
usefully decomposed).

**Exports.** Every new topic facade must be imported from `TCSlib.lean`. CI only builds what
is reachable from `TCSlib.lean`; an unexported file is invisible to CI, docs, and the
blueprint.

**Imports.** Precise module imports only. A bare `import Mathlib` fails CI. Import only what
the file uses.

**Namespaces.** Namespaces are area-local: pick one namespace root per topic and use it
consistently within that topic. Do not leak auxiliary definitions into the root namespace;
mark internal helpers `private` or put them in a dedicated inner namespace.
*Model registry exception*: a model-defining **type** (a machine, circuit, formula, or
decision-tree model) may live at the root namespace, Mathlib-style, provided it is
registered in the catalog facade `TCSlib/ComputationalModels.lean`; its operations and
lemmas still live in the type's own namespace. Anything else at root is a leak.

**Layering.** Keep definition files separate from heavyweight theorem files, so that
downstream work can import a model or a class definition without pulling in every proof about
it. When a development has both a "raw/general" layer and a "bundled" layer (e.g. a machine
model that is parametric in its types, plus a bundled version carrying finiteness instances),
headline definitions and theorems are stated against the bundled layer; the raw layer is
internal plumbing.

**Helpers.** Foundational helper lemmas that serve a whole area belong in that area's
`Basic.lean`, not in the file that first needed them.

**Definitions land with their lemmas** (user, 2026-10-16). Every new public `def` is published,
in the same PR and beside the definition, with the lemmas that let a consumer read it without
unfolding:
- a structure-valued definition (a contract, a configuration, zone contents): its field
  equations, generated by `simps` with `(config := { isSimp := false })` and explicit
  projections (`simps!` where the body is another constructor's result);
- any other definition: an equation lemma `<name>_eq` (by `rfl` where that holds), or case
  lemmas that together cover every input (`_of_lt`/`_of_le`, `_true`/`_false`, one per
  constructor);
- a predicate: an `_iff` characterization;
- a machine: its run or contract lemma, the only way consumers read a machine.

None carries `@[simp]` unless a gate approves it, and each docstring states its formula. Consumers
never unfold another file's definition (the no-unfolding rule of the briefs, user 2026-10-16). The
rule binds TCSlib's own definitions: core and Mathlib definitions may reduce in a `rfl`, `decide`
or `show` step, but are never passed to `simp`, `rw` or `unfold`; use their equation lemmas
(`Bool.toNat_true`, not `simp [Bool.toNat]`) (user, 2026-10-23).
**Reducible abbreviations are notation** (user, 2026-10-26). Lean unfolds a TCSlib `abbrev` (such
as `Turing.Cfg.Halted`, `cfg.state = none`) at every step, and the standard seal cannot cover it:
under Lean's default reducibility validation, `attribute [local irreducible]` fails on a reducible
declaration (only the unsafe override `set_option allowUnsafeReducibility true`, which the
campaign's seals do not use, lifts the check). So reading an abbreviation through its body,
for example `¬ c.Halted` as `c.state ≠ none`, is allowed and is not a definitional closure. A
consumer names it in `simp`, `rw` or `unfold` only through a published lemma where one exists, and
a new public `abbrev` still lands with its `_iff` or `_eq` lemma.
They read the machine model's primitives (`MultiTapeTM.step`, `runFrom`, `Action.apply`,
`Cfg.mapState`) through the existing lemmas. The style lint's check 8 reports, per file, every
public `def` with no lemma named after it and no `simps` attribute, so a head-against-base diff
of the lint shows any new definition that lacks one. Definitions that predate the rule are listed
by the same check and covered as consumers need them.

**Construction reuse.** Machines are built from the verified construction layers, not from
scratch: the combinators and routine catalog of `TCSlib/Complexity/TuringMachine/Build/`
(conventions, wrappers, loops, primitives, embeddings, seams, and the catalog rows —
`machine-library-design.md` is the registry), the registered hosts (**Hosts come first**,
below), and the program layers (`LogProg.ARM`, `CounterProg`, and the general programming
layer of `machine-library-design.md` §15 once it lands) where a program-level description
suffices. Before writing a transition
table by hand, check the registry; a routine that exists is cited, not re-derived. A routine
that *almost* exists is the interesting case: do not write a third private variant — either
consume the general form, or commission the missing form into the shared layer (during a
fill batch: a `private` local copy plus a "requested shared lemma" in the report, promoted
at the next shared-file window). A hand-built machine is acceptable only when no layer
covers the need, and its docstring must say so and name what was missing — that sentence is
what turns the gap into the next catalog row. The chapter-1/2 files that predate this layer
re-derived the same bank/relocation/dispatch/frame families four times over (`emitterBank*`,
`clBank*`, `clSlot*`, …); the retrofit paying that debt back is the standing cautionary
tale. The same discipline applies to circuit construction once `CircuitComplexity`'s gadget
layer exists: gadgets, wiring combinators, and size/depth ledgers get one shared home and a
registry, and new circuits are assembled from it.

**Hosts come first.** A *host* is a control structure that drives other routines rather than
computing one value: a search or traversal (BFS, DFS, backtracking, an odometer over
assignments), a recursion or evaluation scheme (AND/OR evaluation, Savitch's midpoint
recursion), an interpreter or simulation step block, a clocked or windowed runner, a dispatcher
over a data structure (tables, records), or an input device. Any routine whose natural contract
does not depend on its first consumer counts as a host; leaf rows (copy, compare, seek,
arithmetic) do not. **A host is never built `private` inside the proof that first needs it.**
Its public contract is designed, statement-gated and placed in the shared construction layer
first, generic in the parts its consumers vary (the leaf test, the step relation, the data
domain), with time and space (head-envelope) clauses. Consumers cite it, under the campaign's
proved-modulo rule while its own fill is still running. The host registry is
`machine-library-design.md` §14. A private host already in the tree is harvested into the
shared layer before a second consumer is briefed against it. The rule exists because private
hosts were the main way the library overfitted to single proofs: four configuration encodings,
three reachability notions and a private search host per theorem, each to be re-derived by the
next consumer (assessment of 2026-10-12, recorded in the design document). (User, binding,
2026-10-12.)

**Duplication.** Some duplication is mechanically forced by the campaign discipline —
exclusive file ownership, the statement freeze, and `private` visibility leave a fill batch
no other legal way to use another file's unexported machinery — and occasionally it is the
right engineering call. It is never silently acceptable: **every instance of duplicated
proved material must be human-approved.** A fill batch discloses each copy in its report;
the maintainer's integration ledger totals copied material per file (`workflow.md` §4); and
the audit template treats accumulated duplication as a major finding that a gate cannot
close over without the human maintainer explicitly accepting the debt and naming where and
when it is paid back (the registry's dedup/refactor queue). Duplication that was never
disclosed is a freeze violation, not debt.

**File header.** Every math file begins with the Mathlib-style copyright block, its imports,
the repo-standard options

```
set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false
```

then a module docstring containing `# Title`, `## Main definitions`, `## Main results`, and
`## References` (see §2).

## 2. Attribution

Every mathematical statement in the library must be traceable to a source, at the level of
precision of a textbook theorem number or a paper section.

**File-level.** Every math file's module docstring contains a `## References` section giving
full citations with short tags, e.g.

```
## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.
```

**Declaration-level.** Every definition, theorem, and lemma that corresponds to a result in
a source carries the tag with a precise location in its docstring: `[AB09, Claim 1.6]`,
`[AB09, §1.7]`, `[GRS25, Thm 4.2.1]`. Purely technical glue lemmas with no textbook
counterpart may omit the tag; anything a reader would recognize as "a result" may not.

**Deviations.** If the formal statement deviates from the source — different constants,
strengthened or weakened hypotheses, a reformulation — the docstring must say so and briefly
say why (e.g. "stated with explicit constant 5k rather than O(·), following the proof").

**Statement prose.** Every public declaration's docstring begins with a natural-language
statement of what it asserts (for a definition: what it is), precise enough that a reader
could judge the formalization's fidelity without parsing the Lean. The `[Tag, location]`
citation and any deviation note attach to that statement; the proof sketch (§3) follows it.
A bare label ("Unfolding lemma", "Helper for X") is not a statement. Instances are exempt,
as are vendored files (which follow upstream style). `private` declarations should carry
docstrings too, but at reviewer discretion rather than as a hard requirement. The blueprint
remains the cross-referenced informal layer for dependency structure (see **Blueprint**);
the docstring statement is what external audits compare blind restatements against, so it
is part of the trusted surface.

**Blueprint.** When an ingested reference exists under `blueprint/src/references/`, blueprint
entries use `\statementsource{<ref>}{<anchor>}` and `\proofsource{<ref>}{<anchor>}` to cite
it, subject to the existing rule that these are written only after an approved proofmatch
run. When starting a new chapter or paper, ingest it as a reference pair
(`<name>.raw.md` + `<name>.md`) so these citations are possible: put the PDF under
`blueprint/src/references/` in the change that formalizes it and run
`python3 scripts/dataset_pipeline.py --yes`, which ingests it, matches every text the
blueprint does not cite yet, and carries the new statements into the dataset
(`python3 scripts/sources.py add TAG=<pdf or md>` does the ingest and match alone, with
the docstring tag above; `python3 scripts/sources.py` shows which texts are attached and
which are still missing; see `dataset/INSTRUCTIONS.md`). The dataset builder does not
search outside that directory for sources; an unattached text leaves the theorems with
informalized proof notes instead of citations.

**Vendored code.** Lean code adapted from another project keeps the original copyright
header and license notice, and its file docstring names the source project, the commit it
was taken from, and a summary of local modifications.

**Design adaptation.** When a construction, proof architecture, or module design is
adapted from — or materially inspired by — another project's code, the debt is cited even
when no code is transcribed. The module docstring's `## References` section names the
source project, author, module or archive entry, the commit or version consulted, and its
license, with a short tag usable at declaration level; the precedent is
`TuringMachine/Composition.lean`'s `[Balbach22]` for the Isabelle AFP `Cook_Levin`
composition-combinator architecture. Design documents and blueprint entries built on the
adapted design carry the same citation. Examining external code purely for comparison,
with nothing taken, creates no citation duty, but on a campaign it belongs in the
campaign's records (plan decision log or backlog) so the provenance question is answerable
later. (Maintainer guideline, binding, 2026-10-06.)

## 3. Proof sketches

Every nontrivial formal proof is accompanied by a human-readable English proof sketch, kept
next to the Lean it describes.

**What counts as nontrivial.** Rule of thumb: any proof longer than ~20 lines of tactics, or
that would rate difficulty ≥ 3 on the blueprint scale. One-line `simp`/`omega`/`exact`
proofs need no sketch.

**Where sketches live.** In the Lean file itself:

- For most theorems: a `**Proof sketch.**` paragraph at the end of the theorem's docstring,
  written in mathematical English (not Lean identifiers), naming the key intermediate steps.
- For long proofs: additionally, short comments at the major `have`/section boundaries tying
  the tactics back to the sketch's steps.

The named intermediate steps of a sketch should be visible in the formalization as `have`s
or standalone lemmas — if the sketch says "first reduce to the one-tape case", there should
be a lemma that is that reduction.

**Where sketches do not live.** Not in the blueprint. Blueprint statement entries state
claims only; `scripts/dataset_hygiene.py --strict` hard-fails on proof content there. The
blueprint records *what* is true and its dependency structure; the Lean docstrings record
*why* it is true.

**Sketches and the sorry ladder.** When landing a sorry-skeleton, write the sketch at
skeleton time — the sketch *is* the plan, and each `sorry` should correspond to a named step
of it. A skeleton whose sketch cannot be written is not ready to land.

**Synchronization.** When a proof strategy changes, the sketch changes in the same commit.
A sketch that describes a proof the code no longer performs is worse than no sketch.

## Review checklist

Before merging new Lean content, check:

1. Files follow the Area/Topic layout with a facade, and `TCSlib.lean` exports are updated.
2. Imports are precise; no bare `import Mathlib`.
3. Every file has a `## References` section; every source-derived declaration has a
   `[Tag, location]` in its docstring; deviations from sources are noted.
4. Every nontrivial proof (or sorry-stub standing in for one) has a proof sketch.
5. Every public declaration (instances and vendored files excepted) has a docstring
   opening with a natural-language statement of what it asserts
   (`python3 scripts/style_lint.py` checks presence mechanically; statement quality is
   review judgment).
6. `zsh scripts/lean_check.sh <file>` reports zero errors for each touched file.
7. If blueprint content was touched: `python3 scripts/blueprint_validate.py --strict` and
   `python3 scripts/dataset_hygiene.py --strict` pass.
8. No new private host: every search, recursion, interpreter, runner or input device the
   change introduces is a registered public host, or cites one (§1, **Hosts come first**).

## ===== workflow.md (records, at 659542ecd9413b504d30da8c937b9805e6c1f71f) =====

# TCSlib Formalization Workflow

How large formalization campaigns are run in this repository. [`policy.md`](policy.md)
says what landed Lean code must look like; this document says what *process* produces
it. The reference implementation is the Arora-Barak campaign
(`AroraBarakChapter1Plan.md`, complete and audited end to end;
`AroraBarakChapter2Plan.md`, in progress) — file paths below cite its artifacts as
worked examples. Where an older document describes a mechanism this one supersedes
(e.g. the PR-based fill delivery in `AroraBarakChapter1Plan.md` §5, since replaced by
zip delivery), this document records current practice.

```
plan  →  statement phases  →  audit gates  →  fill campaign  →  closure
          (sorry-skeletons)    (per phase)     (epochs/batches)   (attestation, final
                                                                   audit, blueprint)
```

The load-bearing idea: **statements are audited before proofs are attempted.** Lean
already checks proofs; the dominant failure mode of formalization is a wrong or
subtly-weakened *statement*, and that is cheapest to catch while everything is still a
`sorry`. Every phase therefore lands as a compiling skeleton, passes an adversarial
external audit gate, and only then becomes fill work.

## 1. The campaign plan

Each campaign (typically one textbook chapter) begins with a plan file at the repo
root — `<Source>Chapter<N>Plan.md` — containing:

* **Scope**: which results are mandatory core, which are deferred, with source
  citations.
* **Foundation decisions**: the definitional conventions, each with its rationale
  (these are where audits bite; see §3).
* **Architecture and module layout**: directories, namespaces, facades, per policy §1.
* **Phasing**: the statement phases and the anticipated fill epochs.
* **Risks and honest effort assessment**.
* **Open design questions (human review required)**: decisions reserved for a human
  maintainer. Audit rounds *verify* these but never *dispose* of them; each records
  the maintainer's provisional choice and stays open until a human closes it. The
  consolidated register — full statements, cross-links, and status — is
  [`backlog.md`](backlog.md); the plans keep stable numbered stubs, which is what
  audit documents cite.
* **Decision log**: an append-only table. Every methodological decision, every audit
  round's verdict, and every repair round gets a row. The log is the campaign's
  memory; when a decision is reversed, the old row is marked **Superseded** in place,
  never deleted.

## 2. Statement phases (sorry-skeletons)

A phase lands the definitions plus the theorem *statements* of one coherent slice,
every proof a `sorry` under a policy-grade proof sketch (policy §3: the sketch is
written at skeleton time and is the plan; a skeleton whose sketch cannot be written is
not ready to land). Ground rules:

* Definitions and sorried statements only. Proofs appear in a skeleton only for
  definitional-unfolding lemmas whose home module mirrors proved infrastructure (the
  precedent: the `runWith` algebra of `TuringMachine/Nondeterministic.lean`, mirroring
  the vendored `runFrom` lemmas), and any such deviation is flagged in the audit pack
  with the proofs declared part of the audited surface.
* Sketches name their obligations: a sketch that will need a machine construction
  names each sub-machine as an explicit fill obligation, so the eventual brief can
  inherit the list. It also names every **host** the route needs (policy §1, **Hosts come
  first**), from the registry in `machine-library-design.md` §14. A sketch that needs an
  unregistered host is not ready: the host's public contract is a statement-phase item of
  its own, gated before the consumer's fill.
* Everything gate-verifies before commit: per-module checks plus a full fresh sweep
  (§6), style lint, and the headline axiom prints.

## 3. Audit gates (between phases)

Right after a skeleton lands — statements frozen — an **external adversarial audit**
runs before any fill or any next phase. The auditor is an LLM from a different vendor,
in a fresh context, reviewing the trusted surface (definitions, statements, sketches,
and any skeleton-time proofs) against the source text.

**Artifacts**, committed under `audits/` with campaign-scoped names
(`ch2-phase1-*`, `epoch4-*`), except the bundle:

* `…-pack.md` — the auditor's instructions: the audited commit, repository-side
  attestations (freeze by path enumeration, sweep results, admission inventory, axiom
  prints, lint — stated so the auditor can verify or challenge them, with source facts
  kept separate from maintainer execution claims), the under-audit inventory, a
  prioritized brief (the plan's seeded design questions go here), and the findings
  table format with the severity guide: **blocker** (a downstream phase would build on
  a wrong statement) / **major** (fixable but materially misleading) / **minor** /
  **note**. `campaign/standards/TEMPLATE.md` is the skeleton.
* `…-bundle.md` — a single uploadable file: the pack verbatim, then every attachment
  under a `## ===== <path> =====` header (prior findings, both plans, `policy.md`,
  the root, and the full module tree). **Not committed** (user, 2026-10-15): it is kept
  in the local dispatch folder, and the resolutions record its SHA-256 and section
  count. Bundles committed before then are indexed in `campaign/BUNDLES.md`, with how to
  retrieve them from history.
* A short kickoff message (drafted per round, pasted by the maintainer into a fresh
  auditor chat with the bundle attached).
* `…-findings.md` — the auditor's report, preserved **verbatim**, including anything
  the maintainer disputes. Pack errata found later are acknowledged in the resolutions
  file; shipped packs are never edited retroactively.

**The gate rule**: a gate closes only on a round reporting **zero blockers and zero
majors**. A round with majors triggers repairs and a full re-audit round (minors may
be swept in the closing commit and re-verified). Repairs adopt the auditor's own
constructions where supplied, are re-gated, and are recorded in the decision log; when
the loop closes, `…-resolutions.md` summarizes every round, every repair, and the note
dispositions. The complete worked example is the three-round
`campaign/gates/ch2-phase1{,-reaudit,-round3}/{pack,findings,resolutions}.md` loop.

Audits complement, never replace, in-Lean sanity theorems — the machine-checked and
permanent form of the same checks.

## 4. The fill campaign (epochs and batches)

With all phase gates closed, the audited-true sorries are filled in **epochs** —
sequential, ordered by risk retirement, with an audit round at each epoch boundary —
each consisting of **batches** run in parallel by cloud agents with disjoint file
ownership, from self-contained briefs in `briefs/`.

**Binding batch ground rules** (full text repeated in every brief):

1. **Exclusive file ownership.** Helpers live `private` in owned files; a lemma that
   belongs in a shared file is *requested* in the report and added serially at epoch
   merge, flagged for the next audit. **Hosts are the exception** (rule 4).
2. **Statement freeze.** Audited declarations are never renamed, re-signatured, or
   re-stated by fill work. A target that looks unprovable as stated is an
   *escalation*, reported with the obstruction — never "fixed" inline.
3. **Verification per batch**: the check script (§6) over the owned files, zero
   `error:` lines, sorries only at documented out-of-scope items.
4. **Hosts first** (user, 2026-10-12; policy §1). A batch never builds a search,
   recursion, interpreter, runner or input device as a private one-off. It cites the
   registered public host its brief names. If the route turns out to need a host the
   brief does not name, that is an escalation, reported with the contract the batch
   would need; the batch continues on its other targets.

**Hosts in briefs.** A fill brief is issued only when every host its route needs is
registered (`machine-library-design.md` §14) and the host's statement gate has closed. The
host's own fill may run in the same wave, in its own batch, with consumers citing it under
the proved-modulo rule. The readiness check for any target lists the hosts it needs. A
private host already in the tree is harvested (a promotion PR and its gate) before a second
consumer is briefed against it.

**Delivery is by zip, not PR.** Each batch returns an archive containing `REPORT.md`,
the full source files, a `git format-patch` series, a git bundle, the batch's sweep
log, the axiom-print log, and `SHA256SUMS`. The maintainer verifies before
integrating: checksums; the statement freeze (comment-stripped comparison of every
audited signature); enumeration of any removals; public-declaration drift; a full
fresh sweep; the headline axiom prints; and the **duplication ledger** — every
private copy of existing proved material in the delivery enumerated, with each
touched file's cumulative copied-material count and fraction. If a delivery pushes a
file past **one fifth copied material**, or adds copies to a file that already
received copies in an earlier epoch, the maintainer opens a `backlog.md` §1
human-review item before the epoch's audit pack ships — no discretion. Integration
is `git am -3` from the patch series, preserving the agent's authorship. Large fills that exhaust one agent's budget
continue via a continuation brief to a fresh agent (the `universal` B2 precedent).

**Counting public names** (user, 2026-10-22; gate 59). Public-declaration drift, the statement
freeze and a brief's "no new public declaration" rule count **public declarations**: the
declarations the source introduces without `private` (`theorem`, `lemma`, `def`, `abbrev`,
`instance`, `structure`, `inductive`, `class`), counted by the comment-aware source census
(`devtools/seyoon/declfreeze.py`). Packs say so ("N → N public declarations, at source"). A
**public constant** is a non-private name in the module's elaborated environment (the axiom
probe's walk of the module's publics). Packs and reviews report a module's new public constants
separately, by kind:
- a declaration's compiler auxiliaries (`_proof_N`, `_simp_N`, `match_N`, `eq_N`, `eq_def`,
  `congr_simp`);
- the instances that `deriving` generates for a **private** type, which Lean 4.25 names publicly
  (e.g. `instDecidableEqSl_Key`).

Neither kind is a public declaration. A derived instance of a private type needs no finding when
its type is private to its file and a name check over the tree and the open PRs finds no clash;
where a derived name would clash, write an explicit `private instance`. Any other new public
constant is reported as a finding.

**Epoch boundaries**: the maintainer re-runs the full sweep, produces a **drift
attestation** (§6), and prepares the epoch's audit pack with elaboration evidence
and the epoch's **duplication ledger**, which the auditor verifies independently
(audit template failure mode 5); the epoch's gate follows the same
zero-blockers/majors rule as phase gates, and a debt major closes only by explicit
human acknowledgment recorded in the resolutions file. Once a family is
acknowledged, later corrections to its accounting are minors (audit template
failure mode 5) and do not hold the gate; the ledger is still corrected.

## 5. Closure

When the last sorry falls: a zero-sorry sweep with build evidence; a campaign-wide
drift attestation against the audited baselines; a final audit pack covering the fill
rounds; and the blueprint increment — dependency graph from `.ilean` artifacts,
`scripts/blueprint_{enumerate,assemble,validate}.py`, blueprint-writer agents, with
the blueprint **late-bound** throughout (extraction only at boundaries; no blueprint
LaTeX hand-written ahead of the Lean; `blueprint/BLUEPRINT_PIPELINE.md` has the
pipeline detail).

## 6. Verification tooling

* **`scripts/lean_check_tree.sh <module>`** — the campaign's elaboration gate: a
  direct `lean` invocation per module (**`lake build` is banned on campaign
  branches** — see the Chapter-1 decision log), emitting fresh `.olean`s into a
  scratch tree. Pass requires exit 0, zero `error:` lines, *and* a fresh olean, so a
  stale artifact can never satisfy the check. The full sweep runs it over every
  module, in dependency order, from `scripts/ab_ch1_module_order.txt`:

  ```
  ( while read -r m; do bash scripts/lean_check_tree.sh "$m" || exit 1; done \
      < scripts/ab_ch1_module_order.txt )
  ```

  Admission counting is by `declaration uses 'sorry'` warnings in the sweep log; the
  expected count is attested in every pack.
* **`scripts/campaign_style_lint.py`** (named `scripts/style_lint.py` until the
  main merge, which adopted main's per-file policy linter under that name — the
  historical audit logs' invocations refer to this tool) — mechanical policy checks: statement-prose docstrings,
  sketch-before-sorry, file sizes, `## References`, facade coverage, and (check 8, since
  2026-10-16) public definitions without a lemma beside them (`policy.md` §1, *Definitions
  land with their lemmas*). Campaign baseline: zero FAIL (legacy pre-campaign files outside
  the audited surface are tolerated and listed). Check 8 is a WARN listing names; a landing
  adds no name to it.
* **Axiom prints** — `#print axioms` for every headline theorem on the *fresh* olean
  tree: closed results must show exactly `[propext, Classical.choice, Quot.sound]`;
  sorried statements show `sorryAx`, and any other axiom is a stop-the-line event.
* **Drift attestation** — the anti-tamper check between audited baselines: strip
  comments from every module, compare both the **multiset** of declarations and the
  **ordered declaration sequence** against the baseline, and enumerate public
  declarations (gained / lost / changed) so that "nothing audited moved" is a checked
  claim, not an impression.
* **Vendored files** are frozen at their recorded upstream pin and periodically
  byte-compared against upstream; local modifications live only in the header list.

## 7. Relationship to the other documents

* [`ROADMAP.md`](ROADMAP.md) — a one-page orientation: the phases ahead and pointers to
  the documents that hold the detail.
* [`policy.md`](policy.md) — the standards this workflow enforces (modularity,
  attribution, sketches, review checklist).
* [`lean-glossary.md`](lean-glossary.md) — the Lean/Mathlib jargon appearing in
  declaration names and docstrings (fuel, Sigma, `Prop` vs `Bool`, the naming
  grammar, …), for readers fluent in TCS but not in Lean.
* [`AGENTS.md`](AGENTS.md) / `.claude/` — the sorry-ladder proof technique and agent
  roster; useful *inside* a fill batch, but campaign verification runs through §6, not
  through `lake build` or editor-only checks.
* [`blueprint/BLUEPRINT_PIPELINE.md`](blueprint/BLUEPRINT_PIPELINE.md) — blueprint
  generation and validation.
* [`.github/copilot-instructions.md`](.github/copilot-instructions.md) — main-branch
  build and CI; campaign branches deviate as recorded in their decision logs.

## ===== briefs/pairings/gates/44-pairing-fills/findings-r1.md (records, at 659542ecd9413b504d30da8c937b9805e6c1f71f) =====

<!-- Filed by the maintainer on 2026-11-17 from the auditor's chat reply, pasted by Seyoon. The text below is verbatim.
The evidence ZIP it mentions (gate44-pairing-fills-evidence.zip) was not uploaded; only this Markdown was received. -->

# Gate 44 pairing fills — round 1 findings

**Verdict: HOLD. Open findings: 0 blockers, 1 major, 1 minor, 1 note.**

The delivered proofs establish the frozen T1 and T4 statements. The hold concerns the required acceptance of disclosed duplication.

| Audited item | Pin |
|---|---|
| Exchange | `30ef1257a56873489b599007782046b7dedeb7fc` |
| Campaign records | `8f888790b7e40f9e0529967e29a05a72c5ee8ba3` |
| #340 / merge base | `916afc25c21f5e52b4b01958186ad55d2f615fd1` / `9e7a96481785d6cac4dea3b2e990c49ac278b060` |
| #346 / merge base | `89a18a8225be1b76166af12a15179da291747783` / `7291f6b237fec75add1549c0992c174442180488` |
| Joint tree T44 | `33681cb8ed893a897ca2028d5ada70ca29237978` |

## Findings

Lean paths below are under `TCSlib/Cryptography/`.

| ID | Severity | PR · location | Claim and evidence | Proposed fix |
|---|---|---|---|---|
| G44-01 | **Major** | #340, `Pairing/Assumptions.lean:199`; #346, `IdentityBased/BonehBoyenMachine/Words.lean:261` and neighboring reader proofs | Disclosed exact re-derivations are classified as “no duplicated proved material; nothing for the duplication ledger.” T1’s inline verdict identity is precisely public `TrapdoorPredictor.decide_singleton_eq_true` (`Encryption/PublicKey/TrapdoorPredictor.lean:144`), specialized to the solver-success decision bit. The checkpoint’s `poly_rU`, `poly_rZ`, `poly_rW`, `poly_rS` also re-prove the polynomial-time facts for identical public `InteractiveHandler` projection functions (`Games/Efficiency.lean:538`, `:542`, `:546`, `:550`). Both families are disclosed, but no explicit human acceptance and scheduled repayment is recorded in the audited material or pinned duplication ledger. Policy §1 requires that acceptance, including for mechanically forced copies. | Reuse shared facts, promoting missing generic readers where necessary; or record Seyoon’s explicit acceptance, the shared home and repayment point. Correct both reports’ “nothing for the ledger” dispositions. |
| G44-02 | **Minor** | #346, `BonehBoyenMachine/Draws.lean:58`, `:130`; References entries in `Words.lean:60` and `Handler.lean:62` | `[PS10, Theorem 52.3]` is an inaccurate locator for bounded rejection sampling. That theorem concerns the discrete-log collection of one-way functions; its proof merely remarks that the domain is easy to sample. It does not specify this sampler, fixed coin budget, fallback or statistical bound. The actual formal justification is `Candidates.statClose_sampleBelowL`. This is a genuine source with an inaccurate citation, rather than a fabricated-tag major. | Attribute the bounded sampler to the existing library construction and bound. Retain PS10 §2.8/Theorem 52.3 only as context, and correct the three References entries consistently. |
| G44-03 | **Note** | `pack-r1.md:339`, Assumptions paired-control figures | The prose doubles the totals. Each variant has **2 sealed and 2 unsealed probes**, with **25** expected negative errors: 12 in A and 13 in B. Across strict and coe together: 4 sealed, 4 unsealed and 50 negative errors. The raw logs and plans verify these actual counts, with every reader passing. | Correct “per variant” and “50 … in each.” No replay or control repair is needed. |

The PS10 source supports G44-02’s distinction between its discrete-log theorem and the bounded sampler. [cs.cornell.edu](https://www.cs.cornell.edu/courses/cs4830/2010fa/lecnotes.pdf?utm_source=chatgpt.com)

G44-01 is an acceptance/ledger requirement. The overlaps were disclosed; it is **not** an undisclosed-copy accusation.

## Proof and scope checks

| Question | Result |
|---|---|
| **1 — T1 correctness** | **Pass.** `exists_bdhDistinguisher` constructs a total polynomial-time raw function through `NUPPT.ofPolyTime`, retaining the solver’s coins and advice. On the real tuple law, `coinsCongr` and `expect_sample_equiv` preserve success probability and the unused target sample disappears. On the random law, exchanging independent target/coin samples and encoding injectivity give the inverse-order bound, including outputs outside the encoding range. `accept_bdhGame_le` is pointwise in the security parameter; the bad-order charge is exactly the stated hypothesis. The final negligibility argument adds no assumption. |
| **1 — T4 correctness** | **Pass.** The handler uses total polynomial-time string operations. Negation reduces before subtracting from the modulus; differences and inverses agree with `ZMod`, including inverse zero. Membership precedes message decoding. The per-call identity covers all three oracles and every simulator state. At most one tape entry is consumed per oracle call, so the budget suffices. The sampler is exactly G40-03’s; encoding injectivity supplies its strict modulus bound on every generated group. Machines and error function are chosen before the universally quantified bits and security parameter. |
| **1 — edge cases and sufficiency** | **Pass.** Parameter zero, zero budget, empty coins/advice, absent initialization/challenge, refused target-key queries, repetitions, invalid messages and identity collisions are covered. T4 requires no identity-injectivity/order-growth hypothesis: both simulations use the same zero-inverse convention. Orders zero and one and invalid mathematical group objects are excluded by `BilinearGroup`’s fields; malformed machine strings still receive total polynomial-time behavior. `bb1_sidSecure` is unchanged and reaches `sorryAx` exactly through T2 and T3. T1 is not used by that consumer. |
| **2 — frozen declarations** | **Pass.** Independently reconstructed T44 from the pinned trees; both PR diffs match the pack. T1/T4 headers and statement prose are unchanged. Restoring permitted regions restores the base files. All six T1 and ten T4 mutation controls reject their mutations. The checkpoint inserts only its four imports and Contents section. Public declarations: 101 → 275, exactly 174 additions, with no other frozen declaration changed or removed. |
| **3 — seven readers** | **Pass.** Independent reconstruction is byte-exact: `Defs` +43/−0, `BonehBoyen` +37/−0 at the approved positions. All nine controls reject their mutations. These are precisely the three `oracleImpl_*_onSpec` readers and four approved BB1 encoding/message-space readers, with approved proofs and no added attribute. The casts’ `rfl` witnesses read `Defs`’ own `sidSpec`; consumers use published theorems. |
| **4 — LE-bb1m** | **Pass.** Direct parent/head comparison confirms only deletion of unused `hpp` and reordering of the formula docstring. No statement changes. |
| **5 — duplication** | G44-01 and the grading tables below. No additional undisclosed duplicate was identified. The checkpoint overlaps were reviewed beyond the full-name clash check. |
| **6 — Rule 10** | **Pass.** Recounted **24/24** joint-owner and **16/16** supplement seals: source/probe hashes, conservative request sets reconstructed from collector catalogs, exact source recovery after removing harness insertions, install/EOF coverage, rc 0 and no errors. Strict/coe A/B exclusions match the rulings. Assumptions controls pass at the corrected counts; supplement controls give 24 expected negatives per variant, with all readers/unsealed controls passing. The three skipped owners have **12** row-, source- and probe-identical records against phase 2; its **32/32** earlier seals also recount cleanly. Those owners do not import changed Assumptions, so unchanged inputs justify reuse. The explicit scan has 1,016 items and zero foreign reads; source inspection agrees. |
| **7 — sources** | **Pass apart from G44-02.** BB04 §4.2/Theorem 4.1 and algorithm B are correct sources. The theorem is on printed p. 6 and its proof on pp. 7–8, so the locators are compatible. T1’s independent folklore attribution is accurate under Q10. PS10 Algorithm 43.2 and Definition 181.1 are apt for Euclid and statistical closeness. Inherited missing SOK00/BF01 entries remain outside these fills. |
| **8 — documentation** | **Pass apart from G44-02.** New public docstrings state their formulas; sketches describe the delivered proofs. The sole 15-line sketch omission is pre-existing frozen `bb1SimChal_fresh`. “Handler theorem T1” explicitly names `Games.exists_handlerMachine`, distinguishing it from pairing T1; consistently spelling out “Games” would improve readability. |
| **9 — replay and axioms** | **Pass on supplied evidence.** Independently reconstructed the 16-module downstream set and 1,427-module root/audit closure. All 16 build logs and source bindings recount cleanly: rc 0, no errors, exactly the two T2/T3 admission warnings. Census: **198 → 196**, exactly T1 and T4 removed. Both targets have the standard three axioms and no sorried dependency; the owner census has 604 constants and no nonstandard axioms. State, output-map and snapshot-preservation records are consistent. |
| **10 — disclosures** | G44-03 is an additional pack discrepancy. Other recorded staging/provenance slips do not alter the audited code or conclusions. The shared signing key establishes account-session provenance, not individual authorship. |

The BB04 page locators and the PS10 Euclid/statistical-closeness locators were checked against the primary texts. [crypto.stanford.edu](https://crypto.stanford.edu/~xb/eurocrypt04b/bbibe.pdf?utm_source=chatgpt.com)

The principal bounds checked are

\[
\operatorname{accept}(G.\mathrm{bdhGame}\ A\ \kappa)
\le G.\mathrm{dbdhAdv}\ D\ \kappa+2^{-\kappa}+\delta(\kappa),
\]

\[
q(\kappa)2^{-n}\le(q(\kappa)+1)2^{-\kappa}=\sigma(\kappa),
\qquad n=\kappa+w_G(\kappa)+1.
\]

## Grades: BM-F01–BM-F09

These dispositions do not add to the open-finding counts.

| Finding | Grade / disposition |
|---|---|
| BM-F01 | Agree: note, **closed** by removal of the unused proof. |
| BM-F02 | Agree: minor, **closed** by corrected argument order and explicit security parameter. |
| BM-F03 | Agree: evidence note, **closed**. Independently recounted Oracles controls: 14 negative and 14 reader rows per variant, all as expected. |
| BM-F04 | Agree: note, superseded by landing-head seals and unchanged-input comparisons. |
| BM-F05 | Agree: evidence nits; source/log/hash checks resolve the substantive questions. G44-03 is separate. |
| BM-F06 | Agree: inherited documentation note, outside permitted edits. |
| BM-F07 | Agree: size note; the files exceed the target but remain below the cap. |
| BM-F08 | Agree: disclosed promotion request. The private range-type lemmas derive from published readers without re-proving an existing public IBE theorem. |
| BM-F09 | Agree: suitable machine-specific public glue, with its formula and sketch. |

## Grades: #340’s seven overlap disclosures

| Item | Grade / disposition |
|---|---|
| 1 — raw machine versus `NUPPT.wrap` | Agree. Composition of verified construction layers; the alternative’s bookkeeping does not make this an additional copied theorem. |
| 2 — equality test | Agree. `polyTimeComputable_pairEq` is reused. |
| 3 — projections | Agree. Fixed compositions of published projections; the iterated-first-projection theorem does not supply the required second-projection contract. |
| 4 — target probability | Agree. Tuple-specific application of published probability/injectivity facts; the list-membership bound is a near-alternative. |
| 5 — verdict identity | **Reject “no duplicated proved material / no ledger”: G44-01.** The exact public identity is re-derived inline. Disclosure does not establish acceptance of retained debt. |
| 6 — bad-order bound | Agree as disclosed pattern overlap. The ElGamal safe-prime/index proof is not copied as an interchangeable theorem. |
| 7 — advantage inequality | Agree. Direct absolute-value API use; no matching public Games lemma was identified. |

The checkpoint’s identical round-input projections and polynomial-time facts have the same acceptance gap. Its API obstruction is real, but the required acceptance/repayment record is absent. Other disclosed specializations, casts, encoding-contract applications and simulator comparisons have different contracts or apply existing facts.

## Verification and limits

All **14/14** outer and **549/549** verification-archive checksums pass, with an exact file set. All **186** source-manifest entries pass; **181** Lean source copies bind to pinned git blobs. All **43** bundle sections match their separate copies. The two additionally consulted review archives verify **962/962** and **255/255** inner files and their pinned outer hashes.

The ZIP contains the independent checks, results, mutation-control reruns and pinned duplication ledger. **I did not run a fresh Lean compilation**; compilation/axiom conclusions use the hash-bound supplied replay and probes, independently recounted and checked against the inspected sources.

Gate 40, the T2/T3 fill and #351/#352 are not re-audited. Merge order and snapshot adoption remain maintainer conditions.

**Notation:** `A`: adversary/solver; `D`: reduction distinguisher; `G`: bilinear generator; `κ`: security parameter; `q(κ)`: query budget; `w_G(κ)`: source-group encoding width; `n`: sampler width defined above; `δ(κ)`: bad-order bound; `σ(κ)`: simulation-error bound. T1/T4 and BM-F01–BM-F09 retain the campaign’s labels.

## ===== briefs/pairings/gates/44-pairing-fills/findings-r2.md (records, at 659542ecd9413b504d30da8c937b9805e6c1f71f) =====

<!-- Filed by the maintainer on 2026-11-17 from the auditor's reply, uploaded by Seyoon. Verbatim below. -->

**Gate 44 pairing fills — round 2 findings**

**Verdict: CLEAR. Open findings: 0 blockers, 0 majors, 0 minors, 0 notes.**

All three round-1 findings are closed. DL-55 and DL-56 remain accepted debt scheduled for cleanup Stage 2; closing G44-01 does not mean that repayment has already occurred.

| Audited item | Pin |
|---|---|
| Exchange | `2e0152540aae5bb1ce7f8061572aedc5a4fc5437` |
| Campaign records | `4f4a7592a54cf82fa04f96b83645d7936672614c` |
| PR #340, T1 | `916afc25c21f5e52b4b01958186ad55d2f615fd1` — unchanged |
| PR #346, T4 | `98cb0e521a94e94c304c78348fb5d3033435a3ed` |
| Joint tree T44′ | `bee027f0903d531b3a43511cea16bfa123210291` |
| Round-1 joint tree T44 | `33681cb8ed893a897ca2028d5ada70ca29237978` |

| Finding | Previous severity | Disposition and evidence |
|---|---|---|
| **G44-01** | Major | **Closed by explicit acceptance and scheduled repayment.** At the records pin, the plan's ruling, ledger rows DL-55/DL-56 and Stage 2 scope agree. DL-55 identifies the published verdict identity, its promotion to a shared low-level home importable by both layers, and the subsequent re-points of `TrapdoorPredictor` and pairing T1. DL-56 identifies the four projection facts in `Games/Efficiency` as the shared home and schedules the four re-points, with a reader there if required. Both identify Seyoon's acceptance and cleanup Stage 2 as the repayment point. This satisfies policy §1. Both reports retain their original disposition with an accurate dated correction; the bb1-machine review carries the matching correction. These copies bind to staging records commit `bb0199d6dc6753996e674b6a5dcdcb49b092f5f9`, after the records pin, as disclosed. |
| **G44-02** | Minor | **Closed by LE-g44.** Its sole parent is round 1's #346 head. Only `BonehBoyenMachine/Draws.lean`, `Words.lean` and `Handler.lean` change, by +22/−7 lines. Each is byte-identical to its parent after removing comments, including nested block comments and docstrings while preserving strings. The sampler attribution is correct: `Candidates.sampleBelowL` supplies the construction, and `Candidates.statClose_sampleBelowL` supplies precisely the stated fixed-coin, fallback-zero statistical bound. The unchanged `statClose_draw` applies that theorem. PS10 §2.8/Theorem 52.3 is consistently marked as context for easy domain sampling; all three References entries are corrected. |
| **G44-03** | Note | **Closed by the corrected figures.** Raw logs and control records confirm, per strict/coe variant, **2 sealed and 2 unsealed probes**, with **25 negatives: 12 in A and 13 in B**. Across both variants: **4 sealed, 4 unsealed, 50 negatives**. Every negative fails exactly once, every reader passes, and both unsealed probes have zero errors in each variant. Both control checks report `ALL_OK True`. |

The T44′ evidence binds to the audited heads and shows no regression:

| Check | Result |
|---|---|
| **Integrity and bundle** | **Pass.** All **14/14** outer checksums and **132/132** inner verification checksums pass, with exact file sets. All **30** bundle sections match their separate pack, archive or pinned repository sources. All seven Lean copies in `sources-r2.zip` bind to pinned git blobs. The round-1 material used for comparisons matches its specified exchange pin. |
| **Merges and delta** | **Pass.** Independently reconstructed T44 and all **six** permutations of the records pin and two PR heads. Each merge is clean and yields T44′. Its nine changed paths relative to the records pin equal their respective PR-head blobs. The entire code diff from T44 to T44′ equals `le-g44.diff.txt` byte for byte. The records advance adds no code change. |
| **Replay and state** | **Pass on supplied replay evidence.** Independently recovered the **10-module** downstream subset; the build queue covers it exactly. All ten source/log/output hashes bind, all return rc 0, and no build log contains an error. The only warnings are the two inherited T2/T3 admissions. The copied state hash matches round 1's final state. The plan builds 10 and reuses 1417; the unchanged full root/audit order contains **1427 modules**, all reported OK by the final state check. The nine replay-tool hashes match round 1's supplied tool bytes. |
| **Objects and preservation** | **Pass.** All ten rebuilt oleans have link count 1, different inodes from the base output, and no `.ilean`. Seven are byte-identical to T44's; only the three documentation-edited modules differ. The 1458-entry output maps independently compare as **1455 equal, 3 changed**, with no additions or removals. The new map hashes to `fca1b6a308ac1585fb5897fae95e8294b54be55e160119e4eca1702692b41ef9`. Snapshot #4's before/after/final rehashes report **0 extra / 0 changed / 0 missing**. The old-output rechecks and subsequent deletion record are consistent with preservation of the new output. |
| **Admissions and axioms** | **Pass.** The recorded per-module admission counts are identical: **196 → 196**, with zero in the three edited owners. The axioms probe hashes to both rounds' run records; its log is byte-identical to round 1's. T1 and T4 use only `propext`, `Classical.choice` and `Quot.sound`. The nine-owner census reports **604 constants, 0 nonstandard axioms**. `bb1_sidSecure` still reaches `sorryAx` exactly through the two out-of-scope T2/T3 statements. |
| **Canonical coe-A seals** | **Pass.** Draws **1644**, Words **2242**, Handler **2275**, and BonehBoyenMachine **2311** requests. All four runs have rc 0 and zero errors. Independently checked source/probe/log hashes, exact source recovery after removing harness insertions, identical request rows/readers/exclusions and insertion payloads, and complete install/EOF coverage. Comparisons use round 1's `rel/` request-set record for Draws, as disclosed. |
| **Lint** | **Pass: no regression.** Non-INFO campaign output is byte-identical: **92 FAIL / 104 WARN over 524 files**. INFO differences are only the three line counts. The supplied three-file style check reports zero findings, and `sk15` has zero hits. |

**The remaining round-1 seals can be carried forward; a rerun is unnecessary for this delta.** Every other code source is blob-identical, the three edited owners have identical code after comment removal, and both the collector probe and its complete log are byte-identical to round 1's. The four new canonical seals additionally confirm unchanged requests and harness behavior against the new output. Together these justify carrying the strict/coercion A/B variants, paired controls, supplement seals and explicit-unfold results within this round's stated scope.

**Round 1's passes still hold and were not re-audited.** No change reopens the proof or edge-case conclusions, frozen statements and statement prose, seven readers, LE-bb1m, declaration inventory, name-clash result, or the prior grading of BM-F01–BM-F09 and #340's disclosures. Item 5 and the four projection re-derivations now have the acceptance records required by G44-01.

**No new undisclosed change or finding was identified.** The three corrections' post-pin provenance is accurate. Live PR checks confirm #346 is pushed to `98cb0e52`, #340 remains at `916afc25`, and both descriptions now disclose the resolutions. The other known slips remain compatible with the audited material.

I did **not** run a fresh Lean compilation. Compilation, axiom and filesystem-preservation conclusions rely on the supplied hash-bound replay/probe records, independently recounted and checked against pinned sources. Git reconstruction, checksum verification, source binding, comment removal, map comparisons and seal-record comparisons were performed locally.

Gate 40, the T2/T3 fill and #351/#352 remain outside scope. Merge order and snapshot adoption remain maintainer conditions. The user dispatches and merges.

## ===== briefs/lattice-gsw/gates/45-gsw-6a/findings-r1.md (records, at 659542ecd9413b504d30da8c937b9805e6c1f71f) =====

# Gate 45 · round 1 findings (Codex), filed verbatim

Received from Seyoon as an upload, 2026-11-17 (`gate45-gsw-6a-findings.md`). The `audit/target-review.tsv` it cites was
not supplied.

---

# Gate 45 — GSW phase 6a, round 1

**Overall verdict: HOLD. PR #358: CLEAR. PR #359: HOLD.**

All 98 admitted targets are mathematically sound as stated and strong enough for the named r3 consumers. The hold concerns an additional, undisclosed duplication that LE-ren did not remove.

| Audited item | Pinned revision |
|---|---|
| Exchange | `059331913c8a5380d3ae53e5e9dffa3c7ff6e2b4` |
| Campaign records | `8c5875fa268a622e4e166da5f7a992715097c2c7` |
| #358 / merge base | `a616adcac0760ab56b1b0a2a4869f4763843f9ab` / `e1d39836ed4a69a34914c35f4c73c71de853dcc6` |
| #359 / stacked base | `73aedcdaaaffef7e69ab012d9b9195f150bae68d` / `a616adcac0760ab56b1b0a2a4869f4763843f9ab` |

Open findings, counted once against the PR introducing the issue:

| PR | Blockers | Majors | Minors | Notes | Verdict |
|---|---:|---:|---:|---:|---|
| #358 | 0 | 0 | 0 | 1 | **CLEAR** |
| #359 | 0 | 1 | 1 | 0 | **HOLD** |
| Overall | 0 | 1 | 1 | 1 | **HOLD** |

## Findings

Lean paths below are relative to `TCSlib/Complexity/`.

| ID | Severity | PR · location | Claim and evidence | Proposed fix |
|---|---|---|---|---|
| **G45-01** | **Major** | #359 · `CircuitComplexity/FormulaArith/Combinators.lean:425`, `TreeCircuit.const_eval` | This admitted target exactly restates public, proved `BoolCircuit.eval_node_nil` at `CircuitComplexity/Hierarchy.lean:105`, after `const_eq`. Its sketch re-derives the identity by splitting the Boolean gate kind. Neither the overlap inventory nor DL-54 discloses or accepts this duplicate. Under policy §1 and the G44-01 precedent, a new name and a definition wrapper do not resolve exact theorem duplication. | Reuse the existing fact, moving it to an upstream shared module if necessary; make the new reader a citation and remove it from the admitted-target inventory. Alternatively, record Seyoon's explicit acceptance and a ledger row with the shared home and repayment point. Correct the overlap inventory. |
| **G45-02** | **Note** | #358 · `CircuitComplexity/FormulaArith/Combinators.lean:15` | “Promoted unchanged” accurately describes the computation, but can be read as claiming byte-identical moved proofs. There were five sound, Q2-approved repairs. #359 inherits this sentence. | Optionally clarify that the computation is unchanged and the proofs have the five approved repairs. |
| **G45-03** | **Minor** | #359 · `BranchingPrograms/Barrington.lean:40` and `:339` | The convention prose calls `(13254)` “0-based.” That is Bar89's **one-based** cycle notation; its zero-based translation is `(0 2 1 4 3)`, as the code correctly implements. | Label the notation correctly. The formal permutations and statements need no change. |

The exact equality behind G45-01 is:

```lean
TreeCircuit.const b = TreeCircuit.node b []                 -- const_eq
(TreeCircuit.node b []).eval x = b                         -- existing eval_node_nil
(TreeCircuit.const b : TreeCircuit n).eval x = b            -- new admitted const_eval
```

Importing `Hierarchy` directly into `Combinators` would create a cycle: `Hierarchy` imports `TreeNCAC`, which imports `Combinators`. This explains the need for an upstream move or explicit accepted debt; it does not establish acceptance.

## Proof, statement and source audit

| Surface | Result |
|---|---|
| **#358 move and proofs** | **Pass.** The diff is exactly four files, +279/−184. The moved block has the stated renaming/promotion, five repairs, three line re-wraps, promoted documentation and two new `rfl` readers. All seven public declarations are sound. Pairing preserves the gate's Boolean value, halves list length with ceiling, adds at most one depth level and does not increase `sumSize + length`. The fuel induction establishes the published fan-in, depth and size bounds, including the empty and singleton lists. |
| **Frozen `TreeNCAC` surface** | **Pass.** Public statements are unchanged. `toBinary` computes the same circuit after replacing private `combine` by the identical `balanced` construction. The two remaining seal failures and four explicit foreign unfolds are pre-existing G6A-F05, not introduced by O1. |
| **C1–C4: 11 targets** | **Pass.** Composition order, conjugation, last-instruction complement, lengths and bijectivity match the model. The positive-length hypothesis is necessary for the complement-yield equation. Empty programs and zero width/input arity have the expected interpretations. |
| **C5–C8: 5 targets** | **Pass.** The push form works for general maps; permutation fibers are singletons, giving C6's pull form. Prefix induction proves the indexed relational contract C7. A pushed one-hot vector remains one-hot even for noninjective maps. These contracts suffice for G2. |
| **C9–C16: 11 targets** | **Pass mathematically; G45-03 concerns cycle-label prose.** The commutator and explicit orbit-matching conjugator have the required orientation. The four-block AND construction cancels on rejection; the OR construction correctly complements both children and the result. Constants, unary gates, arbitrary output permutations in C14, and nonemptiness are handled. C13/C16 correctly require fan-in at most two and a five-cycle. |
| **C17–C21: 11 targets** | **Pass.** The instruction wires, composition formula, midpoint recursion and accepting-function enumeration implement Bar89's three proof sections. The composition bound is `(clog 2 w + 2) * clog 2 length + 1`; the acceptance constant `w * clog 2 w + clog 2 w + 3` suffices because the accepting set has at most `w^w` functions. Widths zero/one, lengths zero/one and empty accepting sets are covered. |
| **C22–C25: 5 targets** | **Pass.** `IsFaninTwo` supplies the well-formedness needed for tree unrolling. The family statements are nonuniform NC¹/BWBP/PBP₅ statements. Polynomial lengths/depths give the advertised inclusions; the accepting set handles input length zero. |
| **N1–N6: 6 targets** | **Pass.** Every gadget case satisfies all seven `GadgetSpec` fields, including empty/unary gates. Cost is at most fan-in plus two; depth factor two and size `n + 4 * #gates` follow from the existing rewrite contracts. NAND form does not imply `IsWellFormed`; those predicates can overlap on unary-only circuits. |
| **N7–N13: 7 targets** | **Pass.** The column invariant supplies in-range copies at every required level. Base copies, parity twins and double-NAND links preserve values under `IsNANDForm`; their depth and acyclicity arguments need no NAND hypothesis. The empty-gate twin uses the literal pair and needs positive input arity. Output depth is preserved exactly, including depth zero; dead columns cause no problem. N11's bound covers every column. N12 is exactly the required `args_lt` field, equivalent to the planned `GatesAcyclic` proposition, as ruled by Q4. |
| **F1–F3: 24 targets** | **Pass mathematically; G45-01 concerns reuse.** De Morgan negation preserves depth and fan-in. Substitution and finite-supremum bounds include the empty variable type. Gadget truth tables, depth increments and fan-in bounds are correct. |
| **F5–F6: 7 targets** | **Pass.** The weighted full-adder identity preserves the sum; padding and unequal/empty word lengths are correct. One layer sends `k` words to `2 * (k / 3) + k % 3`; the two-round shrinkage supports `csaLevels k ≤ 2 * clog 2 k`, including counts zero, one and two. |
| **F7–F8: 7 targets** | **Pass.** Generate/propagate gives the ripple carry, and the threshold theorem has the necessary word-length bounds. For `p = max lengths + 1`, the CSA carry word's top bit is `maj(false,false,T) = false`, so comparison works for every constant, including zero, `2^p` and larger constants. The padding-depth and `+7` bounds are sound. |
| **F9–F10: 4 targets** | **Pass.** For positive modulus the sum bound `S < max M 1 * q ≤ 2^w` justifies trimming both nonnegative words; the quotient gives the interval witness. Empty/reversed intervals, `M = 0` and `q = 1` work. If `q = 0`, the hypotheses force `M = 0` and `lo = hi = 0`, and both sides are false; that case must precede the division argument in the fill. The closed depth bound has no term linear in `log q`. |

These counts sum to **98**. `audit/target-review.tsv` records every declaration individually, with its domain/edge checks, reasoning and consumer. This is a semantic audit of admitted statements, not 98 completed Lean proofs.

**C16 reading.** BV14 accepts return to its start state. Here C16 gives `(barrington c σ).yield x 0 = σ 0` on acceptance and `0` on rejection. Since a five-cycle moves `0`, G3 must read coordinate `σ 0`; coordinate `0` would encode the complement. The deviation is mathematically harmless and is disclosed, although spelling out this acceptance distinction would make the note clearer.

**Definitions and consumers.** No definition contains a `sorry` body. The only non-target constants reaching `sorryAx` are `toNANDForm`, `toNANDForm_eq`, `layerNAND`, `layerNAND_gates` and `layerNAND_output`: two definitions and three theorems. N2 enters `rewrite` only through correctness proofs; N12–N13 enter only through structure proof fields. The gate lists and output indices do not compute from admitted witnesses. This is acceptable for the explicitly planned statement phase. The 89 self-only and nine additional target traces are exactly as disclosed. The proved readers/helpers and decidability instances are sound; the separate Q3 readers remain fill prerequisites, outside this audit.

**Reuse and registration.** LE-ren completely removes the `rename` family. `widenCircuit` is a specialization of `reidx`; `restrictCircuit` is a special case of general substitution, not a theorem that proves general substitution. No additional duplicate of those families remains. DL-54 correctly records the deferred relocation of `reidx`. The computable C10 contract is stronger than Mathlib's conjugacy-existence theorem. Other compared circuit models and private dual-rail machinery are not interchangeable public theorems. G45-01 is the additional exact public overlap. Both models, all four conversions, facades, and H18–H20 are registered correctly; the listed contract locations resolve. `Combinators` is 629 lines; the stated fill-time split condition is reasonable.

**Sources.** All 112 anchors resolve in the pinned ingests. The 18 exact and six rendering-different quotations check against their passages, including C6's pull equation. The source results, disclosed glue/deviations and reference lines are appropriate, subject to G45-03. Bar89's downloaded original matches the ingest's PDF SHA-256, and the relevant scanned theorem/lemma pages agree. BV11/BV14 comparison used the pinned ingests; independent PDF fetches were unavailable. The retained AB09 tag is pre-existing; no Gen09 issue arises.

## Replay and Rule 10 evidence

**Integrity verified:** 13/13 outer checksums; 483/483 verification-archive files; 42/42 source copies bound to git; all 86 bundle sections bound to their stated sources. The two additional raw archives verify 984/984 and 260/260 files and their pinned outer hashes. The delivery manifests verify 2137/2137 and 2105/2105 with exact file sets. All six worker commits reproduce hash-for-hash with `git am`; the 1,345 raw build logs recount cleanly. Declaration drift is **267 added / 0 changed / 0 removed** against the tip, including O1's seven declarations.

| Snapshot-#5 evidence | #358 / R1 | #359 / R2 |
|---|---:|---:|
| Successful rebuilt modules | 9/9 | 20/20 |
| Checked module states | 1429/1429 | 1440/1440 |
| Admission delta | +0 | +98, exact targets |
| Axiom census | 141 constants, standard only | 544 constants; `sorryAx` in 98 targets + five dependents |
| Canonical owner records reproduced | 4/4 | 16/16 |

Build log/source hashes, state keys and recorded object hashes agree with the pinned heads. The two snapshot-#4 landing **full trees** reconstruct exactly as `ba964762…` and `34e41f15…`. Equal-key modules also have identical recorded olean hashes: 1,413 in R1 and 1,424 in R2. The axiom logs are byte-identical between snapshots.

Exact statement-owner request counts, in **strict A / strict B / coe-A / coe-B** order:

| Owner | A | B | coe-A | coe-B | Errors per variant |
|---|---:|---:|---:|---:|---:|
| BP/Defs | 0 | 0 | 0 | 0 | 0 |
| BP/Eval | 25 | 25 | 25 | 25 | 0 |
| BP/Barrington | 119 | 119 | 119 | 119 | 0 |
| BP/BarringtonConverse | 243 | 243 | 243 | 243 | 0 |
| BP/NC1 | 333 | 333 | 333 | 333 | 0 |
| BranchingPrograms facade | 335 | 335 | 335 | 335 | 0 |
| FA/Combinators | 174 | 174 | 174 | 174 | 0 |
| FA/CarrySave | 253 | 253 | 253 | 253 | 0 |
| FA/Compare | 269 | 269 | 269 | 269 | 0 |
| FA/ModSum | 273 | 273 | 273 | 273 | 0 |
| FormulaArith facade | 276 | 276 | 276 | 276 | 0 |
| NANDForm | 180 | 180 | 180 | 180 | 0 |
| NANDLayering | 187 | 187 | 187 | 187 | 0 |
| TreeNCAC | 218 | 218 | 218 | 218 | 2, pre-existing |
| CircuitComplexity facade | 3726 | 3726 | 3726 | 3726 | 0 |
| ComputationalModels | 1106 | 1107 | 1106 | 1107 | 0 |
| **Total** | **7717** | **7718** | **7717** | **7718** | **2** |

O1's four owners have **174/194/194/3659** requests respectively in each variant (`Combinators`/`FormulaArith`/`TreeNCAC`/`CircuitComplexity`), totaling **4221**; only `TreeNCAC` has its two inherited failures. The base file has 94 requests and four failures, including the two nil cases O1 repairs.

The delivered root counts are exactly **13762/13763/13761/13762**, all clean. Phase 2 root coe-A has **13991** requests; snapshot #5 has **14074**, in 15 verified chunks with zero errors. Its 83 additions are confined to #340/#346. A/B differs by `PolyExpr.eval`; strict/coe differs by the projection `CoeFun` instance. The latter is absent from the `ComputationalModels` closure, explaining that owner's two equal pairs. These are variant counts, not interchangeable totals.

**Controls:** per harness (strict or coe), O1 has eight probes, four sealed, with **10 negative + 10 reader** checks under seals and 20 unsealed checks. The statement run has 40 probes, 20 sealed, with **92 negative + 92 reader** checks under seals and 184 unsealed checks. Every negative fails exactly once; readers and unsealed checks pass. The delivered controls independently recount **30/30**. The explicit-unfold scan has zero foreign reads in the 13 new files and precisely the four inherited `TreeNCAC` reads.

**Carry-forward argument: confirmed for the claimed checks.** I reconstructed the old trees, recomputed the closure keys, reconstructed conservative request sets from collector catalogs, recovered source bytes from the instrumented probes, and checked their hashes, install/EOF coverage and raw errors. All 20 canonical owner records match. All 26 reused tools match archived copies. The collectors import the same owner union; strict/coe-B generation and controls use fixed variant settings and those records, not the root or discovery of unrelated snapshot modules. With the fixed Mathlib/toolchain, no changed input to the carried checks was identified. The root's closure changed and its canonical seal was rerun. This confirms reuse of recorded results; it is not a claim that those variants were freshly executed on #5.

## Grades of G6A-F01–G6A-F15

These dispositions are not additional open findings.

| Review finding | Audit grade / disposition |
|---|---|
| F01 | Agree: the specific `rename` duplicate is closed by LE-ren. Reject a broader “no remaining duplication” conclusion: **G45-01**. |
| F02 | Agree: semantics-free repairs, explicitly accepted by Q2; controls cover both extra nil cases. |
| F03 | Agree: separate reader prerequisite, ruled by Q3 and out of scope here. |
| F04 | Agree: equivalent field-form N12, accepted by Q4; no mathematical defect. |
| F05 | Agree: pre-existing failures and unfolds; independently confirmed. |
| F06 | Agree: size watch, not a present blocker or major; retain the fill split trigger. |
| F07 | Agree: documentation note, **G45-02**. The computation is unchanged; qualifying the claim about the proofs would improve precision. Bibliographic spelling/abbreviation and “frozen” wording do not change source identity. |
| F08 | Agree: the 16 disclosed adaptations and settled constants preserve the intended contracts. |
| F09 | Agree: redundant `lo ≤ hi` is harmless and follows r3; no contradiction. |
| F10 | Agree: tooling/environment note; chunking has complete request coverage. |
| F11 | Agree: convention note. BV14 accepts return to its start state; C16's five-cycle recognizer accepts at `σ 0`. Reading state `0` here would give the complement. The stated deviation is sound; explicitly spelling out the acceptance change would help readers. G45-03 is a separate cycle-label defect. |
| F12 | Agree: historical freshness note, superseded by the verified #5 replay. |
| F13 | Agree: checkpoint source/head gaps are closed by final delivery and reproduction. |
| F14 | Agree: trace correction is accurate; nine targets additionally reach N2 or N12–N13. |
| F15 | Agree: process note. The terminal driver syntax error is disclosed; every required child result, source binding and seal/control record is complete. It does not invalidate the recorded checks. |

The pack's other listed slips are accounted for: old review heads, snapshot numbering, “five definitions,” record-versus-distinct-owner counts, range-diff wording and missing tool-match annotations. G45-01 is an additional undisclosed overlap. No other blocker or major was identified.

**Verification limit:** I did not run a fresh Lean compilation. Compilation, axiom and seal conclusions use the supplied, hash-bound raw runs, independently recounted and compared with the inspected source. Q3 readers, in-house fills, Gate 46, bootstrapping/circular security, Gen09, merge order and snapshot adoption remain outside the requested audit. The user dispatches and merges.

**Notation:** BP = `BranchingPrograms`; FA = `CircuitComplexity/FormulaArith`; `b` = Boolean gate kind; `c` = formula; `x` = input assignment; `n` = input arity; `σ` = five-cycle; `w` = branching width or, in the F9 discussion, retained bit count; `D` = output depth; `δ` = old vertex depth; `k` = word count; `M` = summand count; `q` = modulus; `S` = subset sum; `p` = comparison width; `U,W` = carry-save words; `lo,hi` = interval endpoints; `T` = a bit of the added constant. Campaign labels retain the pack's meanings.

## ===== briefs/pairings/gates/48-bb1-sim-fill/findings-r1.md (records, at 659542ecd9413b504d30da8c937b9805e6c1f71f) =====

# Gate 48 · round 1 findings (Codex), filed verbatim

Received from Seyoon in chat, 2026-11-17. The referenced `gate48-bb1-sim-evidence.zip` was linked from the auditor's
chat and was not supplied to the maintainer; this file is the auditor's Markdown summary as pasted.

---

**HOLD — 0 blockers, 1 major, 0 minors, 0 notes.**

Audited PR **#357**, Lean head `7a98ba0140ce6334bef1f2a8d39c6dfceb6ccaff`, records `e6cdf4d4eed898acd71d48bd60082140eb076cfe`, exchange `827065642ff5965c6f7c51c592f18b9f32dc2811`.

| # | Severity | File · declaration | Finding | Proposed fix |
|---|---|---|---|---|
| **G48-01** | **major** | `BonehBoyenSecurity.lean:128–134` · `bb1_sim_real`, local `h01` | The bad-coin proof re-derives the public Mathlib lemma `abs_sub_le_of_nonneg_of_le`, specialized to real numbers and upper bound `1`. This duplication is unaccepted, and the pack's assertion that no public counterpart exists is incorrect. | Remove `h01` and apply the Mathlib lemma directly. Correct the reuse claim and refresh verification at the repaired head. |

`abs_sub_le_of_nonneg_of_le` takes exactly the four bounds supplied to `h01`, in the same order, and bounds the absolute difference by their common upper bound.

This lemma exists in the **pinned** Mathlib revision `029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e`: `Mathlib/Algebra/Order/Group/Abs.lean:119–124` generates it through `@[to_additive]`. The audited checkout already uses the identifier in `TCSlib/Cryptography/LWE/BitNoise.lean:110`.

The bad-coin branch can instead use:

```lean
    exact abs_sub_le_of_nonneg_of_le
      (ProbComp.prob_nonneg _ _) (ProbComp.prob_le_one _ _)
      (ProbComp.prob_nonneg _ _) (ProbComp.prob_le_one _ _)
```

This is a proposed proof-only repair, not a tested patch. DL-57 covers the `sidSpec_rng_*` twins; it does not cover this overlap. The contrary reuse claims occur in `pack-r1.md:254–255` and `fill-final-r1/review.md:218–219`. The major grading follows the gate's explicit duplication rule and Gate 44's inline-identity precedent.

The remaining audit checks passed:

| Area | Result |
|---|---|
| Integrity | **11/11** pack checksums and **189/189** verification-archive entries pass. The original phase-2 ZIP and its complete manifest also verify; I recovered its seven omitted entries. |
| Four targets | No correctness defect found. The relational induction generalizes both states; sampling reindexes along the supplied equivalence. T2 uses exactly the frozen bad event and proves identity injectivity on good coins. T3 uses the correct target-group translation. |
| Helpers and edge cases | No false, vacuous, or assumption-like helper found. All nine Step-M cases are covered, including pre-initialization calls, target-key queries, invalid/repeated challenges, and recorded challenges without an identity. Zero parameters/budgets and runs without initialization or challenge are covered. Order `1` and trivial groups are excluded by the existing bundle. |
| Frozen declarations | Independently reproduced **12/12** frozen checks, all **8** mutation controls, and **69 ADDED / 0 CHANGED / 0 REMOVED**. `bb1_sidSecure`, `prob_simulate_rel`, and the frozen sketches remain unchanged. |
| Ten readers | Both blocks are verbatim insertions at their approved anchors, retain the specified pins, restore the base exactly when removed, and reject all **12** insertion mutations. |
| LE-bsf1 | Matches the proposed diff. Apart from the added `rfl` reader `bb1RealState_eq`, all changes are comments. |
| Rule 10 | Independently recounted **36 worker head seals** and **16 base seals**, with source/probe/log bindings. Reconstructed **36/36 phase-2 seal sources** and **64/64 control sources**, matching recorded hashes and plans. Each harness has **485** sealed negatives, each failing once, and **1479** clean other entries. |
| Exceptions and unfolds | The abbrev reader's positive-only treatment and `RealReads` projection treatment satisfy the recorded rulings. The recovered scan contains **527** entries and **zero foreign definitions**; I inspected its non-theorem classes. |
| Other duplication | DL-57 records both twins, acceptance, and Stage-2 repayment. Searches across all **529** cryptography files and comparison with #355's pinned `Games/Tapes.lean` found no further undisclosed duplication. The eager/relational instances apply public framework results. |
| Sources and documentation | BB04 quotation checks match the supplied December-2004 transcription. Locators, glue notes, variant descriptions, sketches, file sizes, and widths are acceptable. |
| Replay | All **19/19** build sources and logs bind to the audited head. Recovered state contains **1432** modules; reused records are unchanged. Recorded builds have rc 0 and no error, warning, or `sorry` diagnostic. Admissions fall **196 → 192**, exactly the four targets. |
| Axioms | **76** named constants and **325** owner constants have no nonstandard axioms. All six traces are empty, including `bb1_sidSecure`'s **20,373**-constant closure. The intentional sorry control is caught by both checks. |

The prior review findings are graded separately from the new Gate-48 count:

| Review finding | Grade and disposition |
|---|---|
| BSF-F01 | Agree: minor, process only; remains disclosed. Fix future rebase/signing instructions. No history rewrite requested. |
| BSF-F02 | Agree: minor, closed by `bb1RealState_eq`. |
| BSF-F03 | Agree: minor, closed by LE-bsf1's documentation changes. |
| BSF-F04 | Regrade the pre-acceptance gap as major under the duplication rule; **closed at this pin** by Q1 and DL-57. |
| BSF-F05 | Agree: information, accepted; projections and consumer seals provide the required treatment. |
| BSF-F06 | Agree: information; the missing checkpoint acknowledgment is disclosed and resolutions are traceable. |
| BSF-F07 | Agree: information / accepted placement debt; promotion is recorded for Stage 2. |
| BSF-F08 | Agree: maintainer merge condition, outside this audit. |

I did **not** execute Lean afresh. I independently checked the static surface, regenerated probe hashes, recounted raw worker logs, and verified the recorded native-build and axiom logs. Phase-2 raw seal/probe logs remain on the maintainer host; the supplied result tables, exact regenerated sources, and worker recounts support their reported outcomes.

#351/#352 and the closed Gates 40/44 were not re-audited. No dispatch or merge was performed.

