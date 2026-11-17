# bb1-machine · maintainer delivery review (r1)

**Verdict (final, after phase 2): ACCEPT WITH LANDING EDITS.**
- **The landing edit is in place.** LE-bb1m is #346's 7th commit (`89a18a82`, `Oracles.lean` only, +2/−8). It is identical to the proposed diff, it builds, and the request sets do not change. That closes BM-F01 and BM-F02.
- **T4 `exists_bb1_distinguisher` is proved and standard.** The seven approved readers are pure verbatim insertions at the brief's positions, with the pinned hashes. Only the four permitted files change, which makes 8 files against the records tip.
- **Findings:** 0 blockers, 0 majors, 1 minor (BM-F02, fixed by LE-bb1m) and 8 info findings. BM-F03 is closed by the `Oracles`-owned controls, and BM-F04 is superseded because phase 2 sealed the landing head.
- **Phase 2** (`phase2/README.md`, `phase2/phase2-evidence.zip`). The final replay is on olean snapshot #4 (`463f2244`, the #352 merge), with prospective tree `2ec72515…` = tip `ca129d64` × #346.
  - The build is 12/12 rc 0 with 0 `error:`/`error(`, and the full-closure state check is OK.
  - Admissions go down by 1, exactly T4, with 22 → 21 over the issued closure.
  - The axioms are as required.
  - All 32 seals have 0 errors, with request sets identical to the worker's. The paired controls are ALL_OK, and so are the `Oracles` controls. The scan finds 0 foreign items, and lint has nothing new.
  - The cross-build with #340 is clean: admissions go down by 2, T1 is standard, `bb1_sidSecure` reaches exactly T2 and T3, and the `Assumptions` coe A/B seals have 0 errors.
- **The replay output is kept** at `$SP/olean-replay-346c`, with map SHA-256 `5e63b3cc…5404` once the overlay is removed. It can be adopted if #346 merges unchanged.

## Delivery and landing
- **Delivery:** Claude, a lead with one sub-agent (`tools-agent`: evidence tooling only, no Lean).
  - The final is exchange `f14ac810da888829d21a1bd94fef4dcd4258b863` ("fill bb1-machine: final").
  - Checkpoint 1 is `309071c6efc7a98cf0e832c7ff0c8973127d3701`.
  - Both commits touch only `inbox/fills/bb1-machine/`, and neither is signed.
  - The final keeps checkpoint 1's three patches, `COMMITS.tsv` and `src/` byte-identical. It removes 30 unused tool copies, each listed in `tools/PRUNED.txt` with a SHA-256 that matches the checkpoint blob (30/30).
- **Issue base:** `7c0a55e0239c14786612d0cd4462e64238543ca1`. It holds three SSH-signed in-house checkpoint commits on #331's head `9e7a96481785d6cac4dea3b2e990c49ac278b060`.
- **Worker head:** `c90273fad3511ada7c9c1a53e1abdd8478237cee`, with three unsigned commits:
  - `633dcf99`: the readers alone, in `Defs.lean` and `BonehBoyen.lean`;
  - `b9a242ea`: the new helper `BonehBoyenMachine/Oracles.lean`;
  - `c90273fa`: T4's body and `**Proof sketch.**`, the `Oracles` import line and one `## Contents` bullet.
- **Files** against the base: 4 changed, +507/−17.

  | File | Lines (base → head) |
  |---|---|
  | `Defs.lean` | 433 → 476 |
  | `BonehBoyen.lean` | 677 → 714 |
  | `BonehBoyenMachine.lean` | 100 → 137 |
  | `BonehBoyenMachine/Oracles.lean` | new, 373 |

  `Draws`, `Words`, `Handler` and `Reduction` are unchanged. There is no scope request, and there are no new imports other than the permitted `Oracles` line.
- **Landing.** #331 has merged (`22e3f809`), so `9e7a9648` is an ancestor of the records tip `bdcadd858cbe043e8c41e465a96e81feb1eecda1`.
  - `git merge-tree` of the tip and `c90273fa` is clean, with tree `68452acf8fdf313c7e4405d66245af1eb5542e24`.
  - That tree differs from the tip only in the 8 files of the T4 PR (the 4 above plus the base's 4 helpers), and each file is blob-equal to the head's.
  - The tip changed 64 modules since `9e7a9648` (GSW, SequentialZK, ComposeSecurity, `SIS/Columns`, `ZeroKnowledge/Defs`). None of them is in the import closure of any of the 8 owners or of `BonehBoyenSecurity`: all 9 closures are equal at the head and on the merged tree.
  - It also merges cleanly with #340 (T1; tree `2d8e51b3`, no name overlap) and with #341.
- **Evidence:** `bb1-machine-r1-phase1-evidence.zip`, SHA-256 `8157bdfca262ed37cf9721b2d1ea35e3ca382c6e28a8b8eac6b2f5787b8b1502`. It has 43 files under `bb1-machine-r1/`; `evidence-SHA256SUMS` sits beside it.

## Checks (phase 1)
- **Integrity.**
  - **Manifests.** Every manifest was checked by streaming blobs from git, with exact path sets and no `./`:
    - the top-level `SHA256SUMS` verifies 1040/1040 and equals the 1040 delivered files other than itself;
    - `evidence/SHA256SUMS` verifies 1030/1030;
    - checkpoint 1 verifies 704/704 and 694/694;
    - the sub-agent's `files.sha256` verifies 97/97.
  - **`COMMITS.tsv`.** It has 3 rows, and the identities and dates are Claude `<noreply@anthropic.com>`. The signing column is `none` in all three rows, and the commits really are unsigned (no `gpgsig` header).
  - **Issue package.** `issued-r1/` verifies 7/7. The outbox at `78d89c5c` verifies 7/7 at the top level and 61/61 in `checkpoint/`, and its 7 files equal the records copies. `SOURCE-SHA256SUMS` verifies 188/188 at the base.
- **Reproduction.** I ran `git am` of the three patches onto `7c0a55e0` in a new sparse worktree, on local branch `review/bb1-machine-am`, which was not pushed.
  - It used committer Claude, `--committer-date-is-author-date` and no signing.
  - It reproduces all three hashes, so the branch head is `c90273fa`.
  - `src/` (4 files) is blob-equal to the head's 4 changed paths, and those are exactly the changed set.
  - Per commit: `633dcf99` touches only `Defs`/`BonehBoyen`, `b9a242ea` only `Oracles`, and `c90273fa` only `BonehBoyenMachine.lean`.
  - I removed the worktree afterwards and kept the branch.
- **Scope: reader insertion** (my `readers_check.py`, independent of the worker's).
  - The approved text has SHA-256 `8644e722…`. Its lines 27–68, 74–97 and 99–109 are each preceded by one blank line.
  - Inserted after base lines `Defs:387`, `BonehBoyen:387` and `BonehBoyen:551` (anchors checked), they give exactly the head files.
  - The head hashes are `4e220ead…` (`Defs`, 476 lines) and `da875140…` (`BonehBoyen`, 714 lines), as the brief pins.
  - Removing the blocks restores the base byte for byte (`9af4b773…`, `22caae4f…`). The diff against the base is +43/+37, with 0 lines removed and 0 changed.
  - Nine mutation controls all FAIL as required: a changed character (×2), a deleted reader (×2), an extra line (×2), a moved `ofFn_bb1SimCt`, and a docstring edit (×2).
- **Scope: `BonehBoyenMachine.lean`** (my `frozen_t4.py`).
  - Against `7c0a55e0`, everything outside four regions is byte-identical, and the result is PASS. The regions are:
    - the `Oracles` import, placed in sorted position;
    - one 2-line `## Contents` bullet, after the existing bullets;
    - T4's `**Proof sketch.**` paragraph, 16 → 23 lines;
    - T4's body, 28 lines with step comments, replacing `sorry`.
  - T4's header and the statement prose before `**Proof sketch.**` are byte-identical at `9e7a9648`, at `7c0a55e0` and at the head.
  - The body has no admission and no column-0 line.
  - Ten controls all FAIL as required. They cover the header, the prose, a sketch spilling into the prose, the title, a second bullet, an edited existing bullet, an extra import, a `sorry` in the body, an edit after T4, and a deleted `variable`.
  - No other frozen file changes: `BonehBoyenSecurity`, `Pairing/*`, `Games/*` and the facades are untouched.
- **Statements.** `decls2.py` (the maintainer copy, run on the reproduced head) gives:
  - against `7c0a55e0`: 8 ADDED (the 7 readers and `BB1Machine.abs_expect_bb1Sim_sub_distinguisherL_le`), 0 CHANGED, 0 REMOVED;
  - against `9e7a9648`: 174 ADDED, 0 CHANGED, 0 REMOVED.

  My declaration scan also finds the 6 private glue lemmas as the only other additions, with no other body changes outside T4. T1 (`Pairing/Assumptions`) and T2/T3 (`BonehBoyenSecurity`) are untouched: those files are byte-identical.
- **Admissions** (source level, over the 188 issued modules plus `Oracles`):
  - base: 57 in 18 modules;
  - head: 56 in 17 modules. The only change is T4.
  - tip: 22. On the merged tree I expect 21: the 18 Complexity admissions, T1, T2 and T3.
  - The delivered sweep agrees: 56 `sorry` warnings in 17 modules, and `BonehBoyenMachine` has 0.
- **Docstrings, sketches and style.**
  - Every new public declaration has a docstring. The 7 readers carry the approved formula text verbatim. `abs_expect_bb1Sim_sub_distinguisherL_le` has a formula docstring, with its arguments slightly out of Lean order (BM-F02), and a `**Proof sketch.**`.
  - Proofs of 15 or more lines all have sketches: T4 (28 lines), `expect_bb1SimImpl` (private, about 190 lines, with sketch and per-case step comments) and the public lemma (16 lines).
  - T4's new sketch matches the delivered proof:
    - `D_b` from `exists_toCompOn_of_toComp` and `exists_handlerMachine`;
    - `σ(κ) = (q(κ)+1)·2^{−κ}`;
    - four `abs_expect_sub_le` steps down to one tuple;
    - the per-call identity through the seven readers;
    - `q·(1/2)^n ≤ σ(κ)`;
    - G40-03's `n = κ + wG(κ) + 1` and `sampleBelowL p (Nat.size p) n n`.

    It says "differ by at most", which is consistent with LE-doc-abs.
  - Line widths are at most 100 in all 8 files. Sizes: `Oracles` 373; `BonehBoyen` 714, which is over the 600 target but was already 677 at the base; `Handler` 899 and `Words` 632, both unchanged. All are under the 1000 cap.
  - There is no `sorry`, `admit`, `native_decide`, `@[simp]`, `attribute`, `µ`, tab or trailing space.
  - `Oracles` is the probe's code: my comment-free token comparison against `MachineProbeMin.lean.txt` lines 16–294 and 296–323 finds exactly one difference, the dropped `private` of the renamed public lemma. The four rewrapped lines are layout only.
- **Sources.** The new declarations carry no source tag. `Oracles`' References block equals `Reduction`'s ([BB04] §4.2, [PS10] Definition 26.8). There is no new excerpt or location.
- **Clashes.** None of the 14 new names is declared in `TCSlib/` or `audits/` at the base or at the tip. Three positive controls hit, as they should.
- **Duplication and reuse.** I searched the tip and Mathlib/core for relatives of each helper.
  - All 33 REPORT `path:line` citations I checked hold at the head or the tip (`citations-check.txt`); the two `Defs.lean:413/428` references point at the `show` line of the inline equation.
  - I found **no undisclosed duplicate of a public lemma**:
    - `ofFn_padFin_ofFn` is a one-line specialization of the public `ofFn_padFin_of_length`, as disclosed;
    - `cast_eq_padFin` follows from `padFin_ofFn` and `cast_eq`, as disclosed (no public `cast … = padFin …` exists);
    - `ofFn_decAnswer_some` is `decAnswer_some` plus Mathlib `List.ofFn_cons`, as disclosed;
    - `sidSpec_rng_one'`/`_two'` have no published IBE counterpart; the promotion request is recorded and not asked for this PR.
  - The new public `ofFn_padFin` (`ComposeSecurity/Machines.lean:244`, on the tip) maps to `padTo` and is not a restatement.
  - **Correction (2026-11-17, Gate 44 G44-01).** This review checked the worker's delta only. It took the checkpoint helpers' overlap dispositions from the in-house REPORT, including its line "No duplicated proved material; nothing for the duplication ledger" (`inhouse-r1/REPORT.md:260`), without regrading them. That line is wrong for the checkpoint's `poly_rU`, `poly_rZ`, `poly_rW`, `poly_rS` (`Words.lean:261–271`), which re-prove `Games.polyTimeComputable_rU`/`_rZ`/`_rW`/`_rS` (`Games/Efficiency.lean:538–550`). They are disclosed, but no acceptance was recorded. Seyoon accepted them on 2026-11-17: ledger row **DL-56**, repaid in cleanup Stage 2. The REPORT carries a dated correction under the line, and the verdict above is unchanged. See `gates/44-pairing-fills/resolutions-r1.md`.
- **Rule 10, by source reading** (my `unfold_scan.py` over `Oracles.lean` and T4's body):
  - It finds 184 theorem selectors and 0 foreign TCSlib or core/Mathlib definitions.
  - The other rows are local hypotheses, the `@[simps]` readers `bb1Scheme_{pp,sk,ct}Len`, `abs_sub_comm` (via `to_additive`), or tokenizer artefacts.
  - There is no `unfold`, `delta`, `change` or `show`. The cast type equations come from `sidSpec_eq`/`bitSpec_rng`/`outLens_*`/`inLens_*`, never from unfolding `inLens`/`outLens`.
- **Delivered evidence, recounted from the raw logs** (`recount.py`, `ctl_recount.py`; regex `^\S+\.lean:\d+:\d+: error[:(]`):
  - **Sweep at `c90273fa`:** 189/189 rc 0, 0 `error:`, 0 `error(`, 0 `error` substrings. All log hashes match, every source is bound to the head blob (189/189), the facades are included, and `Oracles`, `BonehBoyenMachine`, `Defs` and `BonehBoyen` have empty logs. The bootstrap at `633dcf99` gives 188/188 with 57 `sorry` warnings.
  - **Seals:** 32/32 (8 owners × strict/coe × A/B), each with 0 errors in both forms, install and EOF records, and `requested = verified`. Each probe equals the head source plus the harness and `import Lean`. Request counts:

    | Owner | strict A | strict B | coe A | coe B |
    |---|---|---|---|---|
    | `Defs` | 805 | 806 | 804 | 805 |
    | `BonehBoyen` | 840 | 841 | 839 | 840 |
    | `Draws` | 1645 | 1646 | 1644 | 1645 |
    | `Words` | 2241 | 2242 | 2240 | 2241 |
    | `Handler` | 2274 | 2275 | 2273 | 2274 |
    | `Reduction` | 2308 | 2309 | 2307 | 2308 |
    | `Oracles` | 2309 | 2310 | 2308 | 2309 |
    | `BonehBoyenMachine` | 2310 | 2311 | 2309 | 2310 |

    The base seals of `Defs` and `BonehBoyen` (8/8) have 0 errors and the same counts, equal to the #331 record.
  - **Attribution checked:**
    - `Oracles` = `Reduction` + `BB1Machine.runAccept`;
    - `BonehBoyenMachine` = `Oracles` + the private matcher `expect_bb1SimImpl.match_1_1`;
    - every reader-row target is in both sets.
  - **Controls:** 24 probes per variant. In each of coe and strict, the 314 sealed negatives each fail exactly once (attributed per control from the raw logs and equal to `ctlcheck`), the 314 sealed positives pass, the unsealed probes have 0 errors, there are 0 stray errors, and `all_ok` is True. The seven reader rows are exercised in `Draws`, `Words`, `Handler` and `Reduction`, and the `oracleImpl` rows also in `BonehBoyen`. The pretest is 6/6 with 0 errors.
  - **Axioms:**
    - the census covers 8 owners, 571 constants, 0 non-standard;
    - T4 and the public lemma use `[propext, Classical.choice, Quot.sound]`; the `onSpec` readers use `[propext, Quot.sound]`; the BonehBoyen readers use the standard three;
    - the trace: T4 reaches 0 sorried constants (closure 19638), and `bb1_sidSecure` reaches exactly `bb1_sim_real` and `bb1_sim_random`.
  - **Scan:** 952 items, 0 foreign. The kinds probe and the collector have rc 0.
  - **Gaps:** none blocking. See BM-F03 to BM-F05.
- **Lint** (my rerun, `campaign_style_lint.py TCSlib/Cryptography --check8b`): base and head both give 92 FAIL / 103 WARN, over 400 → 401 files. The non-INFO line sets are identical apart from the summary line's file count. `style_lint.py` on the 4 changed files gives 0 findings.
- **Merge check:** clean with the tip, and the merged tree equals the dry-run rebase tree (below).

## Findings

| # | Severity | Finding | Disposition |
|---|---|---|---|
| BM-F01 | info | `expect_bb1SimImpl`, case `0` (`Oracles.lean:129–134`): the `have hpp` is never used. Nothing in that branch reads the local context (`rw`/`simp only` with explicit lists, `refine`). It was carried verbatim from the probe. The sweep log is empty, so no linter flagged it. | **LE-bb1m** deletes the 6 lines. Phase 2 confirms that it builds and that the seals are unchanged. |
| BM-F02 | minor | The docstring of `abs_expect_bb1Sim_sub_distinguisherL_le` names `φ'`/`hφ'` before `q`, `b` and `κ`, and never names `κ`. Lean's order is `H O A A' q b κ φ' hφ' B φ hφ r g X Y Z T`. The brief requires "its arguments in the Lean order". | **LE-bb1m** reorders the docstring only (3 lines; the formula is unchanged; width ≤ 100). |
| BM-F03 | info (evidence) | By the covering-subset rule, the reader control rows run in `Draws`/`Words`/`Handler`/`Reduction`/`BonehBoyen` and not in `Oracles`, their only consumer. `Oracles`' request set is `Reduction`'s plus `runAccept`, so the same targets are sealed there, and its seals pass with 0 errors. | Phase 2 adds one `Oracles`-owned control probe (coe A and strict A, sealed and unsealed) with the seven rows. |
| BM-F04 | info (evidence) | The base seals of `BonehBoyen` at `7c0a55e0` were elaborated against the head's olean tree, whose `Defs` olean holds the three extra reader theorems. Theorems add no seal request, and the counts equal the #331 record, so the result stands. | None. Phase 2 seals the landing head. |
| BM-F05 | info (nits) | Evidence nits:<br>• `cache-get.log` does not record the command line; narrowing is shown by the 2339-file count and by `mathlib-roots.txt`, whose roots equal `roots.txt`.<br>• The final sweep lives in `build/sweep-cp1/`, although it ran at the final head; the REPORT explains this.<br>• The worker's `nonINFO-*` files omit the summary line. | None. |
| BM-F06 | info, pre-existing | `bb1SimChal_fresh` (frozen `BonehBoyen.lean:631`, `:594` at the base) has a 15-line proof without a `**Proof sketch.**` (`sk15`). It comes from #331 and is outside this fill's scope; the worker disclosed it. | Cleanup ledger. A frozen-file edit needs Seyoon's ruling. |
| BM-F07 | info | Sizes: `BonehBoyen.lean` grows 677 → 714. That is over the 600 target (INFO lint line) and under the cap, and the approved readers account for all +37. `Handler` (899) and `Words` (632) are the checkpoint's and unchanged. | None. |
| BM-F08 | info, disclosed | Promotion request: `IBEScheme.sidSpec_rng_one/_two` (and the `dom` analogues) belong in `Defs.lean`; they are private in `Oracles` now. The bb1-sim design note also expects more readers in `Defs`/`BonehBoyen`. | Record it for the bb1-sim reader probe, which follows the T4 PR. It is not part of this PR. |
| BM-F09 | info | The new public lemma is glue specific to this machine. It is listed under `Oracles`' `## Main results`, and its name clashes with nothing. | None. |

## Landing plan
- **Branch:** `land/pairings-bb1-machine`, from the records tip `bdcadd85` (or the current tip, after the P2-0 check). It holds:
  1. the six commits `9e7a9648..c90273fa`, cherry-picked in order: the in-house checkpoints `c158b66e`, `8dc69cda`, `7c0a55e0`, then the worker's `633dcf99`, `b9a242ea`, `c90273fa`. Authors are kept, the committer is Claude, and each commit is SSH-signed with the Co-Authored-By and Claude-Session trailers, as for the gsw-core landing;
  2. **LE-bb1m**, one signed commit that applies `landing/LE-bb1m-proposed.diff`: `Oracles.lean` only, +2/−8.
- **Dry run** (merge-tree, no refs): every pick is clean, and the tree after the six picks is `68452acf`, the same as the merge of the tip and `c90273fa`. The expected range-diff is 6/6 identical.
- **Alternative,** if Seyoon prefers to keep the worker's hashes: base the PR on the pushed `fill/pairings-bb1-machine`, fast-forwarded to `c90273fa`, plus LE-bb1m, and merge it into the tip. The tree is the same; the worker's three commits stay unsigned.
- **PR:** a draft on `cryptography/pass-shelat-ch2-4`. Its diff against the tip is the 8 files. It goes to Gate 44 (Codex) together with #340, and Gate 44 checks that the readers are insertions only.
- **Merge conditions:** the phase-2 checklist passes. The cross-build with #340 is recommended (P2-11).

## Phase-2 checklist (Lean; `PHASE2-PLAN.txt` in the ZIP has the exact steps)
- **P2-0 Tip and tree.** Re-check the tip; if the tip's code changed, redo the merge-tree and closure checks. Take snapshot-pre and plan the rebuild with stateplan.
- **P2-1 Landing branch.** Build it as above. The range-diff must be 6/6 identical, the tree after the picks must be `68452acf`, and LE-bb1m must touch `Oracles.lean` only.
- **P2-2 Export check.** The changed paths must equal the delivery, with `Oracles` differing only by LE-bb1m.
- **P2-3 Build,** one module at a time with `scripts/lean_check_tree.sh`, in order:
  - `Defs`, `BonehBoyen`;
  - the 5 helpers;
  - `BonehBoyenMachine`, `BonehBoyenSecurity`;
  - the facades `IdentityBased` and `AdvancedEncryption`;
  - root `TCSlib`;
  - anything else stateplan adds.

  Expect rc 0, 0 `error:`/`error(`, no `error` substring, and a whole-tree state check that is OK, with the `audits/*/Checks` keys unchanged (they are not downstream).
- **P2-4 Warnings.** 0 in the 8 owners. `BonehBoyenSecurity` has exactly 2 `sorry` warnings.
- **P2-5 Admissions.** The whole tree goes from the tip to the landing head by −1, exactly T4. Over the issued closure: 22 → 21.
- **P2-6 Axioms.**
  - T4, the public lemma and the 4 BonehBoyen readers: the standard three.
  - The 3 `onSpec` readers: `[propext, Quot.sound]`.
  - The census of the 8 owners: 0 non-standard.
  - The trace: T4 reaches 0 sorried constants, and `bb1_sidSecure` reaches exactly T2/T3.
- **P2-7 Seals.** Strict/coe × A/B on the 8 owners with `-DmaxErrors=0`, both error forms, and install/EOF records. The request counts must equal the delivered table, because the closures are unchanged by the tip. Expect 0 errors, and attribute any difference.
- **P2-8 Controls.** The reader rows, plus one `Oracles`-owned probe (BM-F03). In both variants, every sealed negative fails exactly once, every positive passes, the unsealed probes have 0 errors, and the result is ALL_OK.
- **P2-9 Unfold scan.** 0 foreign.
- **P2-10 Lint.** Tip against landing head: no new FAIL/WARN line. `style_lint` gives 0, and `sk15` finds only BM-F06.
- **P2-11 (recommended)** Cross-build the tip with T4 and #340 (merge-tree tree `2d8e51b3`). Expect admissions −2 against the tip.
- **P2-12 Restore and record.** Restore the tree (snapshot equal). Add the phase-2 ZIP, finalize this review, add the decision-log row, then open the draft PR and stage Gate 44.

## Evidence (`bb1-machine-r1-phase1-evidence.zip`, under `bb1-machine-r1/`)
- `PROVENANCE.txt`, `PHASE2-PLAN.txt`, `SHA256SUMS`.
- `integrity/`, `scope/`, `statements/`, `admissions/`, `style/`, `lint/`, `clash/`, `overlap/`, `probe-compare/`.
- `rule10/`: the unfold scan with dispositions, and the seal request-set comparison.
- `delivered-evidence/`: the raw-log recounts.
- `landing/`: the merge-tree, the dry-run rebase, the closures, the rebuild set, #340/#341, and `LE-bb1m-proposed.diff`.
- `tools/`: `manifest_check.py`, `readers_check.py`, `frozen_t4.py`, `decls_scan.py`, `recount.py`, `ctl_recount.py`, `unfold_scan.py`, and an unmodified copy of `decls2.py`.

## Phase 2 result (2026-11-17)
- **Every check from P2-0 to P2-12 passes.** I adapted the checklist to the olean snapshot procedure: replays instead of in-place builds, no restore, and the output is kept. Details, trees and figures are in `phase2/README.md`.
- **The verdict rests on the replay on snapshot #4.** The earlier replays on #2, the full Rule 10 run and the #340 cross-build, and on #3 are supporting evidence.
- **Findings are unchanged.** BM-F01 and BM-F02 are fixed by LE-bb1m in #346. BM-F03 is closed, with ALL_OK in both variants. BM-F04 is superseded. BM-F06 and BM-F08 stay with the cleanup ledger and the bb1-sim reader probe.
- **Phase 2 found nothing new.** It has three disclosures: a container restart, which led to a full re-run of the interrupted phases; two snapshot advances during the job; and one harmless tool-path slip.

**Clear to merge** (ready for Gate 44 together with #340)
