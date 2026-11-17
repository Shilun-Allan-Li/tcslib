# bb1-sim-statements · maintainer delivery review (r1)

**Verdict (interim, phase 1 of 2): ACCEPT WITH ONE OPTIONAL LANDING EDIT, pending one ruling and the phase-2 Lean checks.**
- Both series reproduce hash for hash, and every change is a pure insertion or the new module, inside the brief's scope tables.
  - **Series 1** (Games): `expect_simulate_rel` and `expect_sample_rel` are `sorry`'d with design r1 §2.2's headers verbatim. `prob_simulate_rel` is proved from the target, and `ProbComp.abs_expect_sub_le_expect` is proved and public.
  - **Series 2** (group helpers): the four Q10 helpers are proved.
- decls2 gives exactly the 8 expected ADDED, with 0 CHANGED and 0 REMOVED. Admissions are +2 (the two targets) for series 1 and +0 for series 2.
- Phase 1 found 0 blockers, 0 majors, 2 minors (BS-F01, BS-F08) and 8 infos.
- **BS-F01 needs Seyoon's ruling.** `natCast_inj_of_lt` is an iff wrapper of Mathlib's `CharP.natCast_injOn_Iio`, and the brief's Mathlib-first rule says not to insert it.
  - Recommended: the landing edit **LE-grp1**, which drops the helper and its bullet. Group.lean stays a pure insertion.
  - If Seyoon keeps it, the group PR lands as delivered, with a ledger note.
- The verdict becomes final only after phase 2 (`PHASE2-PLAN.txt`, below).

## Delivery and landing
- **Delivery:** Claude, a lead with one sub-agent (`probe`).
  - Final: exchange `a3cb45f6a83c7308db5f2c5fcf95d25fc7f3fef9` ("stmt bb1-sim: final").
  - Checkpoint 1: `8899115b8292b0ff001dd325bea9a8054074d279`. It holds the probe and series 2.
  - Both commits touch only `inbox/fills/bb1-sim-statements/`. Nothing on the exchange changes that path after the final.
  - The final keeps checkpoint 1's `probe/` (tree `7f2578fa…`), `patches/group-helpers/` and `src/group-helpers/` unchanged. Seyoon has already ruled on the probe (Q7 follow-up: ten readers, which land in the fill PR, not here).
- **Issue base:** `bdcadd858cbe043e8c41e465a96e81feb1eecda1`. Series heads:
  - `stmt/games-relational`: `912a343e538f9b5d9306561a35100f5490a6a11b` (`Probability.lean` only), then `d742bf025d471c3ba0ef889bd4e8986ff9062aeb` (`Relational.lean` and the facade);
  - `stmt/pairing-group-helpers`: `fc9cf2f510622a6a1027c14a614c1d453da5d520`.
- **Files** against the base:

  | File | Lines (base → head) | Change |
  |---|---|---|
  | `Games/Relational.lean` | new, 134 | the module of design §2.2, citations per Q11 |
  | `Games/Probability.lean` | 409 → 423 | bullet after line 48; lemma after line 403 |
  | `Games.lean` (facade) | 64 → 67 | import after line 9; `## Contents` entry after line 42 |
  | `Pairing/Group.lean` | 304 → 338 | four bullets after line 62; helper block after line 232 (`pow_val_bijective`) |

  Nothing else changes. `Defs.lean`, `BonehBoyen.lean`, `Forgery.lean`, `Hopping.lean`, `Simulate.lean`, `TCSlib.lean` and `blueprint/` are untouched.
- **Records tip** after the container restart: `7486e401c5a274c2f67590eb3ea264fdf209186c`. It is records-only since the start of this review (`e6734ef4`). Its Lean equals snapshot #2's `T` (`a6d01b1b`, 0 files differ).
- **Merge checks** (`git merge-tree --write-tree`; all clean, 0 conflicts; the series files are blob-equal in every result):
  - tip × series 1 → `fe093214d79ca1ca312540d7d137e8e32e4bf186`;
  - tip × series 2 → `dd8d3efcbd6415dabc29a58ef5ed133306964c3d`;
  - #346 head `89a18a8225be1b76166af12a15179da291747783` × series 1 → `851e83b1…`;
  - #346 head × series 2 → `d475bcf0…`;
  - tip × #346 × series 1 × series 2 → `21c1aa45bdbd34fd0db085688f25f17471463315`.

  #346 and the tip leave all four series files unchanged. The dry-run cherry-picks onto the tip are clean, and their trees equal the merge-tree trees.
- **Evidence:** `bb1-sim-statements-r1-phase1-evidence.zip`, SHA-256 `6e4cbadd51e8478fb9093172e42dc6fd4da7b1a1e8ed1408047d9c60bb86c960`, 68 entries under `bb1-sim-statements-r1/` (53 files with its own `SHA256SUMS`); `evidence-SHA256SUMS` sits beside it.

## Checks (phase 1)
- **Integrity.**
  - **Manifests,** streamed from git, with exact path sets and no `./`:
    - final: top-level 1639/1639 and `evidence/` 1622/1622;
    - checkpoint 1: 1149/1149 and 1138/1138.
  - **Issue package:** 8/8. The design, policy and ingest hashes equal the brief's pins.
- **Reproduction.** I ran `git am` at the base in new sparse worktrees on the local branches `review/bb1sim-games` and `review/bb1sim-group`, never pushed. I used `COMMITS.tsv`'s committer data and no signing.
  - All 3 hashes reproduce.
  - `COMMITS.tsv` has the signing column, `none` in all rows, and the commits really are unsigned.
  - `src/` equals the changed path set of each series byte for byte (3 + 1 files).
  - After the restart, both worktrees were checked: clean, with no `am` in progress and the heads as reproduced.
- **Scope** (my `insertion_check.py`, independent of the worker's):
  - Every difflib opcode against the base is `equal` or `insert`. Each block is at the brief's anchor: `Probability` 48 and 403, `Games` 9 and 42, `Group` 62 and 232.
  - Removing the blocks restores the base byte for byte (`a7d79d12…`, `dd67d695…`, `ae72aa9c…`, the brief's pins).
  - Head hashes: `ddbe55e9…`, `1ee49c04…` and `235b0646…`.
  - Commit 1 alone also passes for `Probability`.
  - Five controls per file all behave as required: a changed character, a deleted line, an extra line, a moved block, and the unchanged file.
- **Statements.**
  - The three `Relational` headers and its two imports are byte-identical to design §2.2. Its prose differs only by the brief's supersessions:
    - the citation placeholders are replaced;
    - the F4 deviation note, plus one permitted sentence;
    - the References lines;
    - a sketch and an [Sho04] tag on `prob_simulate_rel`.
  - The averaging lemma is byte-identical to the brief's §1a block. It is the ETT copy with `α` for `β`.
  - The facade entry and the `Probability` bullet are the brief's text.
  - **decls2** (the maintainer copy, run in the reproduced worktrees) gives exactly the expected declarations, with empty `.err` files. Its output equals the delivered TSVs.
    - Series 1 ADDED: `expect_simulate_rel`, `prob_simulate_rel`, `expect_sample_rel` and `abs_expect_sub_le_expect`.
    - Series 2 ADDED: `pow_val_add`, `pow_val_neg`, `pow_val_bijective_of_ne_one` and `natCast_inj_of_lt` (the identity-injectivity form).
    - 0 CHANGED and 0 REMOVED in both.
  - The delivered `StmtDump` types match the source headers.
- **Admissions.**
  - Source level: series 1 adds exactly 2 `sorry` (`Relational:93`, `:130`) and series 2 adds 0.
  - The delivered admission checks pass against `base-sorries.txt`: 28 → 30 for series 1, 28 for series 2.
  - In the raw sweep logs, `Relational` has exactly 2 `sorry` warnings (lines 85 and 124), and `prob_simulate_rel` has none.
- **Docstrings, sketches and sources.**
  - Every new declaration has a formula docstring. Both targets and `prob_simulate_rel` carry a `**Proof sketch.**`. Every new declaration with its proof is under 15 lines (2–10).
  - Every bracketed citation is one of the seven approved strings (`citations_check.py`).
    - `expect_simulate_rel` has all seven.
    - `prob_simulate_rel` has `[Sho04, §1.1, bridging steps]`.
    - `expect_sample_rel`, the averaging bound and the helpers carry no tag.
  - The F4 note is verbatim after `**Deviation:**`. There is no "adversary rule" wording and no `[BGZ09, rule`.
  - The module References are the review §4 lines verbatim.
  - I read each cited claim against the ingest anchors (`p006-b001` "free to call oracles", `p007-b002`, `p007-b005`, `p008-b003` `⊨_φ`, `p009-b002`/`p009-b003`/`p010-b001`, Sho04 `p003-b002` and `p013-b001`). All are faithful.
- **Style.**
  - Widths are at most 99, and sizes are at most 423 lines.
  - The new code has no `@[simp]`, `attribute`, `open`, tab, trailing space or micro sign. The base's own `@[simp]` and `attribute` lines only shift.
  - `style_lint` gives 0 findings on the 4 files.
  - `campaign_style_lint --check8b` gives 92 FAIL / 103 WARN at the base and at both heads, over 450 → 451 / 450 files. The FAIL/WARN line sets are identical; only INFO size lines change. My runs equal the delivered outputs.
- **Clashes and name resolution.**
  - The 8 names on all 279 ref tips: the only other declaration is the private `ETTGame.abs_expect_sub_le_expect` (`Forgery.lean:515`), and no Mathlib declaration shares a name.
  - Resolution and protection: see BS-F03.
- **Duplication and reuse.**
  - All 15 `path:line` citations I checked in the REPORT's added rows hold at the base.
  - The averaging bound is the disclosed, ruled duplicate of the ETT copy (Q6); the Stage 2 re-point is a pure deletion.
  - In Mathlib (sources at the pinned `029db123`):
    - `natCast_inj_of_lt` restates `CharP.natCast_injOn_Iio` (BS-F01);
    - `pow_val_bijective_of_ne_one` has an undisclosed near relative, `IsCyclic.unique_zpow_zmod`, which is not usable as is (BS-F02);
    - `pow_val_add` and `pow_val_neg` have no Mathlib statement.
  - No library lemma restates any helper: Schnorr, MatchingMath and Primality only inline the laws.
- **Rule 10, by source reading.** The new proofs use only published lemmas (`expect_sub`, `expect_mono`, `expect_const_mul`, `prob_eq_expect`, the `B.pow_order`/`card_G` fields, and the Mathlib `ZMod`/`orderOf` API). There is no `unfold`, `delta`, `change` or `show` of a definition.
- **Delivered evidence, recounted from the raw logs** (`recount.py`, `sweepbind.py`, `seal_recount.py`, `ctl_recount.py`; regex `^\S+\.lean:\d+:\d+: error[:(]`):
  - **Run directories:** 73, with 1091 records and every log hash matching. Each record's error and `sorry` counts equal my recount. The only nonzero-rc runs are the expected ones:
    - the Mathlib `exact?` probe;
    - the strict `dist_apply` seals;
    - the sealed control probes;
    - scan attempt 1;
    - the probe's refuted alternatives.
  - **Sweeps** (all with every source bound to its head, and the module set equal to the expected one):
    - series 1: 151/151 rc 0, 0 errors in both forms; the expected 150 modules + `Relational`;
    - series 2: 11/11 rc 0, 0 errors; equal to `DOWN-GROUP`;
    - bootstrap S: 612/612 against `order.txt`, 28 `sorry` warnings;
    - bootstrap P: 189/189, bound to `c90273fa`, equal to T4's `order-final.txt` (`f17ade1e…`);
    - commit-1 check: 1/1.

    The warning lines of every swept module equal its bootstrap log.
  - **Seals:** 16 at the heads and 8 at the base. Each probe is the owner's source plus the harness only, and has install and EOF records with `requested = verified`. Counts (strict A / strict B / coe A / coe B):

    | Owner | Counts | Errors |
    |---|---|---|
    | `Relational` | 53/53/52/52 | 0 |
    | `Probability` | 36/36/35/35 | 0 in coe; strict 1 each, `dist_apply` (BS-F06) |
    | `Group` | 567/568/567/568 | 0 |
    | `Assumptions` (control carrier) | 644/645/643/644 | 0 |

    The base seals are identical: `dist_apply` is at base line 402 and head line 403. The request name sets of `Probability` and `Group` equal the base's in all four variants. Strict minus coe is exactly `FinDist.instCoeFunForallReal`.
  - **Controls:** in both variants, every sealed negative fails exactly once (series 1: 6/6, series 2: 34/34), 0 positives fail, unsealed probes have 0 errors, there are 0 stray errors, and the result is ALL_OK. The pretest has 0 errors.
  - **Axioms:**
    - `abs_expect_sub_le_expect` and the four helpers use `[propext, Classical.choice, Quot.sound]`;
    - the three `Relational` lemmas use those plus `sorryAx`;
    - the census: `Relational` and `Probability` 60 constants, non-standard only in those three; `Group` 83 constants, 0 non-standard;
    - the trace: each target reaches only itself, so each is the only `sorryAx` user in its closure; `prob_simulate_rel` reaches exactly `expect_simulate_rel`.
  - **Unfold scan:** 0 foreign in both series (101 and 59 items).
  - **Gaps:** none blocking. The sweeps ran at the issue base, so the 27 modules #341 added downstream of `Probability` and the two `audits/*/Checks` are not covered (BS-F04, BS-F05); phase 2 covers them.

## Findings

| # | Severity | Finding | Disposition |
|---|---|---|---|
| BS-F01 | minor, undisclosed relative | `BilinearGroup.natCast_inj_of_lt` (`Group.lean:262–267`) is an `iff` wrapper of Mathlib's `CharP.natCast_injOn_Iio`. With `ZMod.charP`, `CharP.natCast_injOn_Iio (ZMod B.order) B.order hm hn : (m : ZMod B.order) = n → m = n` is the substantive direction, and the converse is `congrArg`. The fill needs only the injective direction (`idToZ ID ≠ idToZ ID*`), so Mathlib states the helper "in a form the fill can use directly", and the brief says not to insert it. The worker posed the `iff` to `exact?` (which cannot find it) and grepped only `Data/ZMod/`; the REPORT says "Mathlib states none of them in a directly usable form". Q10 lists "identity injectivity on good coins" among the approved helpers, subject to "reuse Mathlib … where it applies". | **Ruling needed.** Recommended: **LE-grp1** (`landing/LE-grp1-proposed.diff`) deletes the helper and its bullet (−7 lines). `Group.lean` stays a pure insertion (`59c605e1…`, 331 lines, insertion check PASS), and the fill uses `CharP.natCast_injOn_Iio`. If Seyoon prefers the `iff` convenience, keep it, name the Mathlib lemma in its docstring at the fill, and add a ledger row. |
| BS-F02 | info, undisclosed near relative | `pow_val_bijective_of_ne_one`: Mathlib's `IsCyclic.unique_zpow_zmod` states `∃! n : ZMod (Fintype.card α), x = a ^ n.val` for a generator `a`. It is indexed by `ZMod (Fintype.card B.G)`, not `ZMod B.order`, and needs a generator hypothesis, so it is not a restatement. The proof repeats `pow_val_bijective`'s seven lines with `G` for `G_T`, which the REPORT discloses. | Ledger note: a generic prime-order lemma could carry both later. Re-proving the frozen `pow_val_bijective` needs a frozen-file ruling. No action here. |
| BS-F03 | info | Name resolution and protection of `ProbComp.abs_expect_sub_le_expect`. It is not `protected`, which is consistent with `Probability.lean`, where no lemma is protected. Inside `namespace …ETTGame`, Lean resolves a bare name through the current namespace before open declarations, so the call at `Forgery.lean:545` resolves to the private copy; the two statements are identical anyway. The worker's sweep built `Forgery.lean` with rc 0, bound to the head. No other declaration of the name exists on any ref. After the Stage 2 deletion of the private copy, the call resolves to the public lemma through `open … ProbComp`, with the same binder names (`c f g h hb`). | Phase 2 (P2-2) adds a resolution probe. |
| BS-F04 | info, pack | The issued `closures.txt` and `order.txt` omit the two modules `audits/pass-shelat/Checks` and `audits/garg-ch1-3/Checks`, which are downstream of `Probability`. `base-sorries.txt` lists 13 modules where the README and brief say 14; the worker disclosed this. | Phase 2 rebuilds both `Checks`. Fix the pack template. |
| BS-F05 | info | The sweeps ran at the issue base, as the brief asked. At the tip, `Probability`'s downstream has 27 more modules (`Yao/HybridProof/*`, #341). | Phase-2 replay R1: 181 modules, root and both `Checks` included. |
| BS-F06 | info, pre-existing | The strict seals of `Probability` fail once, at `ProbComp.dist_apply` (`FinDist` `CoeFun` request), identically at the base. The canonical coe seals pass. | DW-10 / Stage 2. No action here. |
| BS-F07 | info, pre-existing | The frozen `Games.lean:62` and `Hopping.lean:53` carry an older [Sho04] References line (sentence-case title, "IACR ePrint"), not the review §4 string that `Relational.lean` now uses. | Docstring-only, for the Stage 2/3 citation pass. Out of scope here. |
| BS-F08 | minor, process | The final exchange commit `a3cb45f6` carries an SSH signature by key `SHA256:32dP45eSMmVSt/G/CGvcxl/P+MO3Nwj9xeTh/GSA2wc`, the key that signs the maintainer's staging and records commits (`a6a21775`, `66419662`, `7486e401`). Checkpoint 1 is unsigned. `workflow.md` §4.1 says workers commit with signing off. The series commits themselves are unsigned and reproduce, so the content is unaffected; the signature does not attest maintainer authorship. | Record it, and check the worker environment's signing configuration before the next dispatch. |
| BS-F09 | info | Cleanup Stage 1 inserts into `Games.lean` after lines 11 and 47 (its issued brief). A simulated three-way merge with series 1 (after 9 and 42) is clean (`git merge-file` rc 0). | Merge the Games PR first, as the stage preconditions say. |
| BS-F10 | info, evidence nits | Evidence nits:<br>• Scan attempt 1 stopped with a `KeyError`; this is disclosed.<br>• Between checkpoint 1 and the final, 14 tool copies gained header lines only, and `rule10_b.sh` gained its recorded `R10DIR`/`TOUCHED` change.<br>• The group-helpers `insertion-check.out` changed only in its base path label (same hashes).<br>• `current.pid` files were removed.<br>• The series commits carry the standard attribution trailers, as #346's landed commits do. | None. |

## Landing plan
Two PRs, each cherry-picked onto the records tip. Authors are kept, the committer is Claude, and each commit is SSH-signed with the Co-Authored-By and Claude-Session trailers.
- **PR 1, the Games statement PR** (Q9: its own small PR on the records tip). Branch `land/bb1-sim-games` from `7486e401`, cherry-picking `912a343e` and `d742bf02`.
  - Dry run: both picks are clean, with tree `fe093214…` (= merge-tree tip × `d742bf02`). The expected range-diff is 2/2 identical.
  - No landing edit. Its diff against the tip is the 3 files.
  - Draft on `cryptography/pass-shelat-ch2-4`. Q8 puts its audit in the bb1-sim gate after Gate 44.
  - The cleanup stages need it merged before Stage 1, and it frees `Probability.lean` for CS1-Q9 and the Stage 2 re-point. So merge it on Seyoon's approval once phase 2 passes, ahead of the gate.
- **PR 2, the group-helper PR.** Branch `land/bb1-sim-group` from `7486e401`, cherry-picking `fc9cf2f5` (clean, tree `dd8d3efc…`), then **LE-grp1** as one signed commit if Seyoon rules for it (BS-F01).
  - Its diff against the tip is `Group.lean` only.
  - Its downstream overlaps #346 (`BonehBoyen*`), so it goes with the bb1-sim gate and the fill. It may merge before #346; after #346 merges, re-replay it.
- **Order** (`workflow.md` §6.1 step 4): the Games PR has the largest rebuild (181 modules), so merge it first. Then re-replay #346 and the group PR on the new tip; each rebuilds only its own closure (12, or 17 after #346).
- **Merge conditions:** the phase-2 checklist passes, and BS-F01 is ruled.

## Phase-2 checklist (merged-tree replays per `snapshots.md`; `PHASE2-PLAN.txt` has the exact steps)
- **P2-0 Tip and snapshot.** Re-fetch the tip. If any Lean or lake file changed since `7486e401`, redo `landing/`. Verify snapshot #2 (`95493449…`, `T` `a6d01b1b`) at 0/0/0 before and after.
- **P2-1 Landing branches.** Build both as above, with range-diff 2/2 and 1/1 and the trees `fe093214`/`dd8d3efc`. Apply LE-grp1 only on the ruling. Check the export against `src/`.
- **P2-2 Replay R1 (Games PR).** Use `cp -al` of the snapshot, the overlay, `stateplan`/`downorder`/`fullorder`, then `runner.py`.
  - Rebuild at least the 181 modules of `landing/down-games-pr-merged.txt`: `Probability`, `Relational`, the downstream, root, and both `Checks`.
  - Require rc 0 and 0 `error:`/`error(`, a state check that is OK, and link count 1.
  - `Relational` has exactly 2 `sorry` warnings, and other warnings are unchanged. Admissions go from the tip by +2, exactly the targets.
  - Name-resolution probes (BS-F03).
- **P2-3 Axioms.**
  - The averaging bound: standard three.
  - The three `Relational` lemmas: those plus `sorryAx`.
  - Census: non-standard only in those three.
  - Trace: each target reaches only itself, and `prob_simulate_rel` reaches only `expect_simulate_rel`.
- **P2-4 Rule 10 on R1.**
  - Seals of `Probability` 36/36/35/35 and `Relational` 53/53/52/52. Coe gives 0 errors; strict gives only `dist_apply` in `Probability`.
  - Controls are ALL_OK in both variants, and the unfold scan finds 0 foreign.
- **P2-5 Replay R2 (group PR).**
  - Rebuild 12 modules, or 17 if #346 has merged.
  - Admissions +0. The helpers use the standard three, and the census has 0 non-standard.
  - Seals: `Group` 567/568/567/568 and the carrier `Assumptions` 644/645/643/644, with 0 errors.
  - Controls 34/34 per harness, ALL_OK; the scan finds 0 foreign.
  - With LE-grp1, the request sets are unchanged.
- **P2-6 Lint.** Tip against each head: no new FAIL/WARN line, `style_lint` 0, and `sk15` none.
- **P2-7 (recommended)** Cross-build tree `21c1aa45` (tip × #346 × both series). Expect admissions −1 (T4) +2 against the tip; `bb1_sidSecure` reaches exactly T2/T3.
- **P2-8 Order, adopt and record.**
  - Merge the Games PR first. On each merge, the prospective-tree diff must be empty, and then the replay output is adopted (recipe step 6), with a new `snapshots.md` row. Otherwise, discard it and replay again.
  - Then zip the phase-2 evidence, finalize this review, add the decision-log row, and open the draft PRs.

## Evidence (`bb1-sim-statements-r1-phase1-evidence.zip`, under `bb1-sim-statements-r1/`)
- `PROVENANCE.txt`, `PHASE2-PLAN.txt`, `SHA256SUMS`.
- `integrity/`, `scope/`, `statements/`, `admissions/`, `citations/`, `style/`, `lint/`, `clash/` and `overlap/` (including `mathlib-relatives.txt`).
- `rule10/`: request sets against the base; source reading.
- `delivered-evidence/`: recounts of every run, the sweeps, seals and controls.
- `landing/`: the merge-tree runs (at `7486e401`, and the pre-restart run at `e6734ef4`), closures, the facade merge with Stage 1, and `LE-grp1-proposed.diff` with its insertion check.
- `tools/`: `manifest_check.py`, `insertion_check.py`, `style_scan.py`, `citations_check.py`, `decl_scan.py`, `closures.py`, `recount.py`, `sweepbind.py`, `seal_recount.py`, `ctl_recount.py`, and an unmodified copy of `decls2.py`.

**Not yet clear to merge — BS-F01 needs Seyoon's ruling (LE-grp1 recommended), and phase 2 (the Lean replays) is pending; no PR is opened yet**

## Ruling (2026-11-17)
- **BS-F01: drop the helper (Seyoon).** The group-helper PR lands `fc9cf2f5` plus **LE-grp1**, which removes `natCast_inj_of_lt` and its docstring bullet (−7 lines). `Group.lean` remains a pure insertion. Phase 2 builds and seals the LE-grp1 head.
