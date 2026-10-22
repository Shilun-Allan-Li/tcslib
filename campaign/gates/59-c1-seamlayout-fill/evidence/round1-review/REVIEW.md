# Review: gates 59, 60 and 61 (the fill gates of #145, #146 and #148). The findings checked, the resolutions drafted

Read-only review by the maintainer's review sub-agent, 2026-10-22. Nothing in the repository, in
`exchange/` or on GitHub was changed. The only writes are under this folder: `out/` (one file per
check) and `scripts/` (the small read-only scripts the checks used). No Lean was run; none was
needed. No build command, no cache command and no screen was run. Python ran with `python3 -I`.
The three findings files are treated as data. They equal the inbox copies byte for byte.

**Bottom line.** All three PASS verdicts hold. Every finding was checked against the repository,
the bundles and `git`:
- **Gate 59:** 17 findings, all true. F1 is true but was already disclosed in the pack's question
  6; the point that stands is that pack question 1 and REPORT §7 use the source count without
  saying so.
- **Gate 60:** 16 findings, all true. F1 is a real pack error: the head is not "on" `43d22595`.
- **Gate 61:** 18 findings. 17 are true. **F10 is partly true**: the three outputs were missing from
  the bundle, but they *are* in the pinned records tree, and they show what the review said.

No finding needs a Lean change. The resolutions are records:
- 2 pack errata (gate 59 line 36, optional; gate 60 lines 13–14);
- 2 report errata (`seamlayout-1`, 7 items; `g4-cont3`, 3 items);
- 1 evidence note (gate 61 F10);
- carries into the F6 and U2-E briefs, G4 continuation 4 and addendum v2.5;
- backlog lines.

The reviewer additions are records only:
- A process fault: gates 60 and 61's bundles kept only the first 60 entries of each review's
  `out/` folder.
- Two small inaccuracies in the reviews:
  - g4-cont3's "only the two target warnings" for `targets-1_1b.out`;
  - its "re-wrap composes: PASS", which a partial application only partly shows.

## Common checks (all three gates)

| Check | Result | Evidence |
|---|---|---|
| Findings files | `in/*.md` equal the `exchange/inbox/` copies. Rows and severities: 59: 17 (3 minor, 14 note); 60: 16 (16 note); 61: 18 (2 minor, 16 note). Each verdict line matches its rows | `out/all-findings-sha256.txt` |
| Bundles | SHA-256 values as the auditors quote. `SHA256SUMS` OK for the bundle and the README. The section headers are distinct (81, 106, 107) and in `BUNDLE-FILES.txt` order | `out/all-bundles.txt` |
| Owned-file sections | each equals the PR head's blob: `05d4e353…`, `c6b99e69…`, `1abbb871…` | `out/all-owned-section-blobs.txt` |
| PR heads (GitHub) | #145 `126127b8959e4b64b37ac8ed15c0b1b05d747c9e` (3 commits); #146 `8114e482fcad1f1d07abdcc244ef74755b752b56` (3 commits); #148 `13e1758929aa0eb3f298a8dd399e3dbc4bd809c0` (1 commit). All open, all based on `complexity/arora-barak-ch3-4` | `out/all-pr-metadata.txt`, `out/60-F1-merge-base.txt` |
| Sizes | SeamLayout 120 → 1,757 lines, width ≤ 99. InputDevice 525 → 1,294 lines, width ≤ 100 (the 100 is inherited; added lines ≤ 98). ZoneRebalance 1,370 → 1,572 lines, width ≤ 99 (added lines ≤ 97) | `out/all-blobs-lines.txt` |
| Source freeze (`tools/declfreeze.py`, base → head) | 59: 1 → 1 public, 0 → 35 private. 60: 15 → 15 public, 9 → 41 private (the 32 additions all `rd_`). 61: 18 → 18 public, 65 → 73 private (8 added, 4 changed). None removed | `out/all-declfreeze.txt` |
| Replay pins | `replay-lsl.sh` 10/10 at `7cd01f84`; `replay-lf5c1.sh` 11/11 at `8114e482`; `replay-lg4c3.sh` 11/11 at `13e17589`. Sorry totals 8, 8 and 10; static mismatches 0 | `out/all-replay-pins.txt`, the gate folders' `evidence/replay-*` |
| Closures at the heads | SeamLayout {itself, the facade}; InputDevice {itself, `UniversalK`, `SelfUniversal`, the facade}; ZoneRebalance {itself, the facade}. They meet only at the facade. #144 (merged, `0416ffea`) closes over {`ExhaustiveReplay`, `ClassNP`, `Diagonalization/NTimeHierarchy`, `Diagonalization`}, disjoint from all three. #145's and #146's facade hunks are at lines 175–177 and 226–229, far apart | `out/all-pr-closures.txt` |
| Bundle coverage of the reviews | see the gate 61 F10 row and **Reviewer additions** | `out/bundle-vs-review-dirs.txt`, `out/bundle-cited-vs-included.txt` |

---

## Gate 59: PR #145 (`lean/c1-seamlayout-fill` at `126127b8`): PASS, 0 blockers, 0 majors, 3 minors, 14 notes. Findings SHA-256 `5e288fb044945ae47ec16e774055334bac4121abfd0b7a75f7add42526c3cb6d`

| # | Severity | Finding (one line) | Verified | Proposed resolution |
|---|---|---|---|---|
| 1 | minor | The freeze's "1 → 1 public" counts source declarations only. `deriving DecidableEq, Fintype` on the three private inductives adds six public instance names, plus auxiliaries. | **True, but the pack already disclosed the instances** (its question 6, and the review's F2). The source has three `deriving DecidableEq, Fintype` clauses (lines 55, 88, 754). The review's MODULE PUBLICS lists 55 constants: 20 are the target and its 19 `_proof_1_N`; 24 are the six instance heads (`Turing.instDecidableEqSl_{Key,PairPhase,SplitPhase}`, `Turing.instFintypeSl_{…}`) and 18 auxiliaries; 11 are the probe's own commands. So the module adds 44 public constants and 1 public declaration. **Precedent:** 35 private types with `deriving` in 20 landed files at `0416ffea` (e.g. `xr_St`, `wl_Phase`, Inclusions' five `B2b*`). Chapter 2 listed such instances as `generatedExceptions` ("non-private in name by a known Lean quirk"). Chapter 1 used explicit private instances (the "2D trap"). Gate 14's findings drew the same line ("counts only explicitly named declarations"). Gate 60's review row 10 already separates "declarations" from "public constants". There is no name clash at the tip or at the three heads (`out/59-F1-generated-instances.txt`, `out/59-F1-precedent-private-deriving.txt`) | **True; records. No Lean change**, per precedent (the maintainer's backlog note, "F2 … as landed code has, no ruling needed"). Adopt the counting convention **W1** below, which defines "public declaration" and "public constant". **Pack erratum E59-P1** (line 36), optional. REPORT erratum **E59-R1** item 7 (§7's "No new public declaration" and §12's "1 public" count source declarations) |
| 2 | minor | 14 private proofs over 20 lines have no "Proof sketch"; the user's deferral is respected. | **True.** An independent census of the landed head gives the same 14: `sl_unarySplit_copy`, `sl_pairSkipTM_run`, `sl_phase6`, `sl_unarySplitTM_run`, `sl_phase4`, `sl_phase8`, `sl_phase7`, `sl_phase5`, `sl_pairSkip_two_steps`, `sl_phase2`, `sl_phase1`, `sl_phase3`, `sl_split_step_exit` and `sl_split_step_true`. Each has a contract docstring; the target has its sketch (`out/59-F2-sketches-landed.txt`). The backlog records the user's ruling (committed `0416ffea`, lines 1350–1356): "F3 by a docstring-only follow-up PR after the landing" | **True; already ruled** (user, 2026-10-22). The follow-up PR comes after #145 merges. It is docstring-only, so by the user's #144 ruling it needs no gate; replay its closure (SeamLayout, the facade). **Backlog:** name the 14 in the seam-layout entry (line **B59-1** below) |
| 3 | minor | Several REPORT claims need an erratum: §5's seal claim, `bufferTape_of_neg`, the archive paths, `final-module-check.log`, the manifest's literal FAIL, and a sweep before commit 6. | **True, all six** (`out/59-F3-report-erratum-items.txt`). **(1)** `probe/SLPhase8Route.lean.txt` seals `phaseHostTM` (line 12). `simp only [phaseHostTM, hs]` at line 20 succeeds; `out/21b` has one error only, at line 27 (`simp only [hs]`, no progress). **(2)** `bufferTape_of_neg` occurs once in the landed file (line 1451, the frozen docstring; base line 57). It is among out/25's unreached issued names; `bufferTape_left` is reached. **(3)** 19 references (17 `evidence/logs/`, 2 `evidence/probe/`); the zip has `logs/` and `probes/`. **(4)** There is no `final-module-check.log`; only `module-check-cp1/cp2.log`. **(5)** The log ends `MANIFEST CHECK: FAIL`, with four `url MISMATCH rev MISMATCH` lines with empty values. **(6)** SeamLayout was swept at 03:32:31–39, between commit 5 (03:25:52) and commit 6 (03:39:39). After commit 6 only the facade was re-checked; the head was elaborated by the review (out/13) and the landing (exit 0). **Also** §7/§12 (finding 1) | **True; report erratum E59-R1** (7 items, below). Add it beside the unchanged report, as gate 53 did (`exhaustive-2-ERRATUM.md`), or append it to `seamlayout-1-REPORT.md` under the heading given |
| 8 | note | The self-redirect preserves the whole machine and its time; retain the construction and the scheduled last-phase lemma for `Build/Seam`. | **True** (out/21c exit 0; the review's (c)) | **No action; already in the backlog** (committed lines 1339–1343, the phase host's last phase: an API PR with its own gate) |
| 13 | note | The screen delta has no copied material; retain three promotion candidates for the shared-API window. | **True** (the review's rows 29–35, the auditor's fresh run) | **No action; already in the backlog** (committed line 1364: `sl_apply_eq` with `xr_act_apply`, and the reversed read; line 1339: the last phase) |
| 16 | note | The narrowed-cache and resource figures are consistent; record the literal manifest result. | **True.** 15,871,524 kB / 1,048,576 = 15.14 GiB. The disk was 24.56 and 22.15 GiB. 1,002 of 1,002 files were *downloaded*, so on this host the store was not pre-populated (`out/59-60-F16-addendum-v2.5.txt`) | **True; records.** The manifest goes into erratum E59-R1 item 5. **Carried** to addendum v2.5 (**V25-1**, below). The backlog already has the item as "for the addendum's next version" (committed lines 1366–1368). Re-label it "v2.5" (**B-2**) |
| 17 | note | The replay supports its tree; the later merges meet SeamLayout's closure only at the facade. Preserve the replay's commit and the facade qualification. | **True.** The pins are 10/10 at `7cd01f84`; 14 modules; sorry sum 8. #139 and #143 meet the closure only at the facade. #144 (merged since, `0416ffea`) is disjoint (`out/all-pr-closures.txt`) | **True; records** (the resolutions' header states `lsl` at `7cd01f84`, and the facade rule) |
| 4–7, 9–12, 14, 15 | notes | Integrity and scope; `C = 18` and the ledger; the leaves; the control; the endpoint, frame, silence and first exit; the word API; the edge cases; rule 10/11; axioms and probes; elaboration and lint. | **True.** Re-checked: the bundle hash, its 81 sections and the module blob `05d4e353e5e1460a8940f1fc6667d1e8e568ad97`. `bfe3e023` holds the worker blob `483be51b804c3927aed348d49de4d4d9aab51cbd`, and `7cd01f84` changes docstrings only (`out/59-F4-identity.txt`). The ledger sum: `T = 2n − r + 4h + 5q + 2\|v\| + 23`, `(7n+18) − T = h + 3\|v\| + r`, `18(n+1) − (7n+18) = 11n`; the witness at line 1526 precedes `intro` at 1528. The edge times 37, 34, 66, 49, 66, 88, 70, 81 match out/22. Lint 0 FAIL / 31 WARN over 39 files | **No action.** F12's "preserve both seal-with-controls and argument inspection" is already standing practice (rule-10 seals with controls and argument inspection, since gate 50) |

### Drafted texts for gate 59

**E59-P1 (pack erratum, optional).** `pack.md:36`, "(the review's `out/10-declfreeze.txt`: 1 → 1
public, 0 → 35 private, the only body change the target's)", reads **"(the review's
`out/10-declfreeze.txt`: 1 → 1 public declarations and 0 → 35 private, counted at source; the
only body change is the target's. The elaborated environment also gains public constants: the
target's 19 proof auxiliaries and the six derived instances of question 6, with their
auxiliaries)"**.

**E59-R1 (report erratum; for `campaign/fills/c1/reports/seamlayout-1-ERRATUM.md`, or appended to
`seamlayout-1-REPORT.md`)**

```markdown
## Erratum (at integration; gate 59, minors 1 and 3)

**Scope.** Seven statements of this report (`seamlayout-1-REPORT.md`, blob `ba3cb78b…`), as
corrected at integration. The report itself stays as delivered. Sources: the maintainer's review
(`campaign/fills/c1/reviews/seamlayout-1/REVIEW.md`, F1, F2 and F4) and gate 59, the fill gate
of PR #145 (`campaign/gates/59-c1-seamlayout-fill/`, minors 1 and 3). None changes the delivered
Lean or its verdict. `Turing.exists_seamLayoutTM` is proved on `[propext, Classical.choice,
Quot.sound]`, and the landed file elaborates with no diagnostic.

1. **§5, the seal.** "The seal test with `attribute [local irreducible] Turing.phaseHostTM` would
   fail on it" is wrong. `simp only [phaseHostTM, hs]` closes the table goal even with
   `phaseHostTM` sealed. Only `simp only [hs]` fails ("no progress"; review
   `probe/SLPhase8Route.lean.txt`, `out/21b-phase8-route.out`). A definition named explicitly is
   unfolded whatever its reducibility, so a seal cannot detect that unfolding. Rule 10 bans the
   unfolding itself. The review's inspection of every `rw`/`simp`/`dsimp`/`unfold` argument
   (`out/20-rwargs.txt`) found no other-file definition in the delivered proof. The phase-8
   self-redirect stands; its host's table equals the brief's host's table
   (`out/21c-same-machine.out`).
2. **CP2 and §6, `FinTM.bufferTape_of_neg`.** The proof does not cite it. `sl_reverse_read` uses
   `bufferTape_nat`, `List.getElem?_reverse`, `bufferTape_left` and
   `bufferTape_eq_none_of_not_mem`. `bufferTape_of_neg` occurs only in the frozen target
   docstring (review `out/25-citations-vs-probe.txt`; `out/15-ax-head.out.tcslib-consts.txt`).
3. **Paths.** In the archive, read `evidence/logs/…` as `logs/…` and `evidence/probe/…` as
   `probes/…`. There are 19 references, in §§1–3, 6, 10 and 11.
4. **§10, item 1.** The archive has no `final-module-check.log`, and the standalone check left no
   log either. Its module checks are `logs/module-check-cp1.log` and `logs/module-check-cp2.log`
   (checkpoints 1 and 2). The final state was checked as item 6 below says.
5. **§2, the manifest check.** `logs/manifest-check.log` ends `MANIFEST CHECK: FAIL`. The 11
   packages present show `url OK rev OK`. `doc-gen4`, `UnicodeBasic`, `BibtexQuery` and `MD4Lean`
   show `url MISMATCH rev MISMATCH` with empty values. These four are the documentation
   toolchain, which the narrowed fetch does not clone, so they are absent, not at another pin. The
   reading "absent, not mismatched" is right, but the check's literal result is FAIL, by
   construction under addendum v2.3's narrowed fetch.
6. **§§10–11, the final sweep.** The 94-module sweep checked `Build/SeamLayout` at
   03:32:31–03:32:39 UTC. That is after commit 5 (`56510600`, 03:25:52) and before commit 6
   (`09773a66`, 03:39:39, `sl_apply_eq`'s proof restated fieldwise). After commit 6, only the
   facade was re-checked. The delivered head was elaborated with no diagnostic by the review
   (`out/13-elab-head-lbw2.out`), and the landed file by the maintainer
   (`campaign/gates/59-c1-seamlayout-fill/evidence/land/elab-SeamLayout-lg4c2.out`, exit 0). The
   sweep's other results stand: 94/94, and 35 → 34 sorry warnings, by name.
7. **§7 and §12, "No new public declaration" and "1 public".** These count source declarations.
   In the elaborated environment the module also adds public constants:
   - the target's 19 `_proof_` auxiliaries;
   - six instances that `deriving DecidableEq, Fintype` generates for the three private
     inductives (`Turing.instDecidableEqSl_Key`, `…Sl_PairPhase`, `…Sl_SplitPhase`,
     `Turing.instFintypeSl_Key`, `…Sl_PairPhase`, `…Sl_SplitPhase`), with 18 auxiliaries.

   (Review `out/15-ax-head.out`, MODULE PUBLICS.) The instances' types are private, so no other
   file can use them, and no other file declares these names (`out/41-name-clash.txt`). Landed
   code does the same.
```

**W1 (the counting convention; proposed for `workflow.md` §4, at "public-declaration drift", and
for every pack, review and brief).**

> **Counting public names.**
> - A **public declaration** is one that the source introduces without `private` (`theorem`,
>   `lemma`, `def`, `abbrev`, `instance`, `structure`, `inductive`, `class`). The comment-aware
>   source census (`declfreeze.py`) counts them. The statement freeze, the briefs' "no new public
>   declaration" rule and a pack's "N → N public" count these, and say so ("public declarations,
>   source").
> - A **public constant** is a non-private name in the module's elaborated environment (the
>   axiom probe's module-publics walk). Packs and reviews report a module's new public constants
>   separately, by kind:
>   - compiler auxiliaries of a declaration (`_proof_N`, `_simp_N`, `match_N`, `eq_N`, `eq_def`,
>     `congr_simp`);
>   - instances that `deriving` generates for a **private** type. Lean 4.25 gives them public
>     names, e.g. `instDecidableEqSl_Key`.
>
>   Neither kind is a public declaration.
> - A derived instance of a private type needs no finding when two things hold: its type is
>   private to its file, so no other file can state a goal it solves; and a name check over the
>   tree and the open PRs finds no clash. Precedent: 35 private types with `deriving` in 20 landed
>   files (`0416ffea`); chapter 2's `generatedExceptions`. An explicit `private instance` remains
>   the form to use where a derived name would clash.
> - Any other new public constant is reported as a finding.

**B59-1 (backlog, the seam-layout entry).** "**Gate 59 closed** (PASS 0/0/3/14; resolutions
`campaign/gates/59-c1-seamlayout-fill/resolutions.md`). F2 and F4 are resolved in the records
(W1; erratum `seamlayout-1-ERRATUM.md`). The sketch follow-up PR, docstring-only, after #145 merges,
no gate (the #144 ruling), replays SeamLayout and the facade. It covers `sl_unarySplit_copy`,
`sl_pairSkipTM_run`, `sl_phase6`, `sl_unarySplitTM_run`, `sl_phase4`, `sl_phase8`, `sl_phase7`,
`sl_phase5`, `sl_pairSkip_two_steps`, `sl_phase2`, `sl_phase1`, `sl_phase3`, `sl_split_step_exit`
and `sl_split_step_true`."

---

## Gate 60: PR #146 (`lean/b6-f5-cont1` at `8114e482`): PASS, 0 blockers, 0 majors, 0 minors, 16 notes. Findings SHA-256 `70cf3a08a6c996ccdc2028a86074a94e4db67d36bb613d7dde0abf6cfc778e5a`

| # | Severity | Finding (one line) | Verified | Proposed resolution |
|---|---|---|---|---|
| 1 | note | Integrity, identity, ownership and the freeze pass; but the pack's `43d22595` is a later records snapshot, and the PR's merge-base is `34af2e0f`. | **True.** `git merge-base 8114e482… 0416ffea…` = `34af2e0f3bc984f336d08da42f55d448feb78a7b`; `b6c9e0c5`'s parent is `34af2e0f`. `43d22595f0e3aaa35eccda39dff031804ee351cc` is a child of `34af2e0f` (13:30, "Megafill B delivered … F5 landed as #146"), made after `8114e482` (13:28). It is not an ancestor of #146. The TCSlib tree is `2babcaec…` at `b7447492`, `34af2e0f` and `43d22595` alike, so every elaboration and replay claim stands. The worker blob `f8339572…` has SHA-256 `767e153e…f658987`. The commits touch what the finding says. The freeze is 15/15 and 9 → 41 (`out/60-F1-merge-base.txt`, `out/60-F1-identity.txt`). **Gate 61's pack** says the same `43d22595` and **is right**: #148's one commit has parent `43d22595`, which is also its merge-base | **True; pack erratum E60-P1.** Gate 61's pack needs none. **Process** (for the next packs): give the head's merge-base from `git merge-base <head> <campaign tip>`, and give the bundle's records revision separately |
| 13 | note | Two read exits are return points: from blank and `false` reads the machine keeps moving after `2ℓ + 5`. Put a "consume at the first exit" note in the F6/U2-E briefs. | **True, from the source** (`out/60-F13-read-exits.txt`). The final phase `.inr (.inr ())` gets `rd_test` from `rd_family`, and `rd_redirect` gives `none` there. `readExit none` = `.inr (false,false)` and `readExit (some false)` = `.inr (true,false)` are `rd_test`'s return-leg states: the input moves +1 and the ruler −1 while the ruler cell is `true`, else the ruler moves +1. `readExit (some true)` and `moveExit` (`.inr (·, true)`) are stationary. The statement constrains only `u < t`, `u ≤ t` and `t`. **More than the finding says:** the exit *state persists* (out/30c, A1: at `T + 1` the state is still `readExit none`, with heads (2, 4)). So a consumer that waits for the exit state after `t` sees it again with displaced heads | **True; carried** to the F6 and U2-E brief drafts (**C60-1**, below). No brief draft exists for either yet (`campaign/fills/*/drafts/`). The backlog already routes O1 there (committed line 1320): add C60-1's text to it (**B60-1**). **The API prose:** optional, the user's call. A sentence for `exists_rulerDeviceTM`'s docstring (**C60-2**) can go in the deferred public-facing pass or with the first consumer's PR, **not** on #146 (it would need a re-replay). Do not strengthen the frozen statement |
| 16 | note | The environment account is consistent. 967 of the 1,002 archives were already in the store, and their origin is not established; log the store in the next addendum. | **True.** The headroom is 8,589,934,592 − 100,847,616 − 193,372,160 = 8,295,714,816 B. "35 new downloads, 1,002 unpacked" (megafill-b REPORT, line 64). The review's "earlier session" is labelled an inference (REVIEW.md 360–367). The U2-S review's F4 says the same. **Already in the backlog** (committed lines 1331–1332): "for the addendum's next version: … 967 of the 1,002 cache files already on the host … record where they came from". It is not labelled v2.5, and no v2.5 draft exists (`out/59-60-F16-addendum-v2.5.txt`) | **True; records. Carried** to addendum v2.5 (**V25-2**, below). Re-label the backlog item "addendum v2.5" (**B-2**). Records wording: "967 archives pre-existing in the cache tool's store; origin not established". **Decision for the user:** whether v2.5 *allows* a pre-populated archive store (it is the cache tool's own, hash-named store; v2.4 forbids "another session's … object store" without saying whether this is one) or only requires it to be logged |
| 11 | note | The implementation paragraphs are accurate. "R1" shorthand and 11 docstring-less privates are left to the deferred pass. | **True** (the review's F2: three "R1" in new docstrings, at lines 765, 789 and 792; 11 privates without a docstring). A fourth "R1" (line 1198) is in the frozen base sketch (base line 493) | **No action; already in the backlog** ("optional private-docstring rewordings (its F2) are for the deferred public-facing pass") |
| 12 | note | No new cross-file copying. The in-file 79% pair (`exists_rulerTestTM`/`rd_test_return`) can wait for an authorized refactor. | **True** (out/31–32 are bundled. The 79% pair is the frozen target 1's inline endpoint projection) | **Backlog line B60-2** (the dedup window, the user's call because the proof is frozen): target 1's last bullet cites `rd_test_return`, which removes the pair |
| 14 | note | The elaboration, axiom, sweep and replay records are consistent; replay again if an overlapping landing changes the tree. | **True.** The pins are 11/11 at `8114e482`, 16 modules, sorry sum 8. #146's own closure is {InputDevice, `UniversalK`, `SelfUniversal`, the facade}. It meets #145's and #148's only at the facade, and #144 (merged) not at all | **No action.** The facade-only rule covers the open overlaps (**Merge state**, below) |
| 2–10, 15 | notes | The frozen definitions; the inherited test; the call controller; the call rows' time and space; the host controller; the host's frames and ledgers (the ruler clause is an upper bound; `inj` a state map); the edge cases; rule 10; rule 11; the sizes and lint. | **True.** Spot-checked in the source: `rd_answer`; `rd_family`/`rd_redirect`; `rd_hostCost` = `2ℓ + 3` exactly for a live left move with a cleared tag; the ruler clause `⊆ Finset.Icc (rp − 1) (rp + ℓ)`; `inj : S → Bool → Q` with no injectivity clause. 56 declarations = 15 public + 41 private. Lint 32 WARN: the new one is InputDevice's size, the other new one ZoneRebalance's growth from #143 (861 lines at `2ff214c5`, 1,370 after) | **No action.** F7's two readings ("an upper bound", "a state map") go into C60-1 for the consumers |

### Drafted texts for gate 60

**E60-P1 (pack erratum).** `pack.md:13–14`, "**The head:** `lean/b6-f5-cont1` at `8114e482`, on
the campaign branch at `43d22595` (TCSlib = `b7447492`'s, after #139 and #143):", reads **"The
head: `lean/b6-f5-cont1` at `8114e482`, on the campaign branch at `34af2e0f` (its merge-base; TCSlib
= `b7447492`'s, after #139 and #143). `43d22595`, the records commit that recorded this landing, is
a child of `34af2e0f` with the same TCSlib tree (`2babcaec`). It is not an ancestor of #146:"**.

**C60-1 (the carry into the F6 brief, `Complexity.space_universal`,
`SpaceComplexity/Hierarchy.lean:150`, and into the U2-E brief, `Turing.universalK`,
`UniversalK.lean:582`).**

> **The ruler device's exits are return points, not stationary anchors** (gate 60, note 13).
> - `Turing.exists_rulerDeviceTM` describes the device only up to its return time `t` (`2ℓ + 5`
>   in the proof): no exit before `t`, the stated endpoint at `t`, and the ruler-head bound for
>   `u ≤ t`. It says nothing after `t`.
> - After `t` the machine keeps running. From `readExit none` and `readExit (some false)` it runs
>   the boundary test's return leg: the next step moves the input head right and the ruler head
>   left, or the ruler head right. The exit state can persist with displaced heads. For example,
>   at `ℓ = 1`, `z = [true]`, a read at virtual position 0 with the ruler head at 5 has heads
>   (1, 5) at step 7 and is still in `readExit none` at step 8, with heads (2, 4).
> - `readExit (some true)` and `moveExit` happen to be stationary, but the statement does not
>   promise it.
> - **Consume each exit at its first occurrence.** Compose the device through a seam
>   (`seamCompTM`/`Contract.seq`) or a phase-host redirect that leaves at the exit state. Never
>   cite the device's configuration after `t`. Never treat an exit as a live anchor (a stationary
>   self-loop). Never detect an exit by its state at a later time.
> - If your route needs a stationary exit, escalate. The remedy is a one-line change of the final
>   phase in `rd_family`, as a separate authorized PR. Do not restate the frozen statement.
>
> Also: in `Turing.exists_rulerHostTM`, the ruler's space clause is an upper bound (the visited
> set is a subset of `[rp − 1, rp + ℓ]`), and `inj` is a state map, not an injection.

**C60-2 (optional docstring sentence for `exists_rulerDeviceTM`; the deferred public-facing pass or
the first consumer's PR).** "The exits are return points: nothing is stated after the return time,
and from the blank and `false` read exits the machine keeps moving, so a caller leaves the device
at its first exit, as a seam or a phase-host redirect does."

**B60-1 (backlog, the F5 cont1 line).** After "its O1 (two read exits keep moving after `2ℓ + 5`)
goes to the F6/U2-E briefs", add: "(text: gate 60's resolutions, C60-1; the exit state persists
with displaced heads)".

**B60-2 (backlog, the dedup window).** "`InputDevice`: the in-file 79% pair
`exists_rulerTestTM`/`rd_test_return` (gate 60, note 12). Target 1's last bullet can cite
`rd_test_return`. It touches a frozen proof, so it is the user's call. Also the review's promotion
candidates: the `Lockstep` frames corollary; the 'step plus bounded pause' block once U2-E's brief
fixes its shape; `rd_shift_move`."

---

## Gate 61: PR #148 (`lean/g4-cont3-partial` at `13e17589`): PASS, 0 blockers, 0 majors, 2 minors, 16 notes. Findings SHA-256 `30d8e6293e445347d71933455655d1da77016cc4ecc74ab3f3a70bf1abc5488e`

| # | Severity | Finding (one line) | Verified | Proposed resolution |
|---|---|---|---|---|
| 10 | minor | `seal-head.out`, `seal-tip.out` and `targets-1_1b.out` are absent from the 107 sections and the pinned tree, so the seal and characterization results are reviewer attestations. | **Partly true.** **Absent from the bundle: true.** **Absent from the pinned tree: false.** All three were committed with the review at `ca7d1feda54f1f5508a1a7c3564ed06235671a15` (13:46), before the records revision the bundle was built from (`050d547e…`, 13:52). The blobs are equal there and at the tip. **Cause:** the bundle list holds the first 61 C-sorted entries of the review's 81 `out/` entries, less `graph-wt-tip.json`, so a 60-entry cap. The cut fell between `screen-script-sha.txt` and `seal-head.out`. 21 `out/` files and 9 scripts were left out. REVIEW.md cites 15 of them (13 outputs, 2 scripts) (`out/61-F10-missing-outputs.txt`, `out/bundle-cited-vs-included.txt`). **Contents** (they show exactly what the review says):<br>• `seal-head.out` (`9402d51f2a955b9ba1e4119452c2054a23bd2b79`): four errors and nothing else. They are at 1357:63, 1360:29, 1366:54 and 1376:2, the four inside controls (probe lines 1355–1376: the catalog `time`, `zoneStart 0 = 2`, the adapter's `post`, the pass's `time`, each by `rfl`). The outside controls (1381–1403) have no diagnostic. The two target warnings are at 1449 and 1492, i.e. 1396 and 1439 plus the seal's 53 lines. Exit 1, as failing controls require.<br>• `seal-tip.out` (`4aa08a7ae5913647db720ab7dc7d14544e8b01fd`): the same diagnostics.<br>• `targets-1_1b.out` (`f79e4ab7ecc486247327fbf95aec20d361264301`): exit 0 and no error. Warnings: the targets at 1396 and 1439, and **one linter warning**, unused variable `x` at 1693:17, in the reviewer's own negative example (its `fail_if_success` body is discarded). All 11 appendix examples and the private lemma elaborate; the three `#check`s print.<br>Both probes embed the landed bytes. `G4C3Targets.lean.txt` lines 1–1571 = `13e17589` lines 1–1571. `G4C3SealHead.lean.txt` lines 130–1352 = head 127–1349 (the home), inside `section G4C3Seal`, with 57 names sealed | **Partly true; records.** The gate's evidence cites the three outputs by repository path and blob (**E61-V1**, below), with their commands and exits. No re-run is needed: the probe sources are byte-equal to the landed file. A re-run against `oleans-lg4c3` stays available if the user prefers fresh logs. **Review erratum** (in the resolutions only; REVIEW.md stays as written): for `targets-1_1b.out`, "0 errors, only the two target warnings" reads "0 errors; the two target warnings and one unused-variable linter warning in the reviewer's appendix (1693)". **Process:** see **Reviewer additions** (the bundle cap) |
| 11 | minor | The report puts `Turing.two_le_zoneStart` in the supplied inventory. It is in neither probe. The counts are 439/428, 445/434 and 446/435. | **True** (`out/61-F11-probe-counts.txt`). By `#check` count and distinct names: the brief's `G4C3ImportProbe.lean.txt` 439/428; the worker's `ImportProbe.lean` 445/434 (no `two_le_zoneStart`); the review's `G4C3WorkerProbePlus.lean.txt` 446/435 (the worker's plus that one check). `two_le_zoneStart` is a **public theorem**, `ZoneTape.lean:184`, at `6cfee544`, `43d22595` and `13e17589`. It is cited by the new `zr_rightPass_bounds` (line 1274) and `zr_rightPass_tape` (1325). The delivery's `external-citations.txt` (434 names) lacks it. **More than the finding says:** the frozen public `zoneRebalancePost_frames` already cited it at the base (`43d22595` line 1343; `6cfee544` line 834). So the brief's 439-check inventory missed a base citation too | **True; report erratum E61-R1** item 1. **Carried** to continuation 4 (in **C61-1**): 446 checks of 435 names, and an inventory taken from an elaborated-constant walk of the whole module. The review's (h) item 6 already says it; the backlog line does not (**B61-1**) |
| 6 | note | The envelopes and the bridge are correct. Use the preserved left interval, not global scratch blankness, for the second seek. | **True** (the review's table). The bridge `zr_rightPass_tape`: tape 0 on `q ≤ 0` equals the start's, so the second seek's agreement on `[−zoneStart ℓ, 0]` follows. Scratch is blank off `[q, q + m)` only. **Already carried:** the review's (h) item 2, gate 58's list ("not from `zoneRowPre`"), and the backlog ("from 1.1b's local agreement and scratch frame") (`out/61-F6-F8-F11-F13-carries.txt`) | **True; already carried.** Restated in C61-1 so the continuation-4 draft has one list |
| 8 | note | The re-wrap removes the exit-set mismatch, subject to the instance requirement. The probe's `let _C := …seq …` is a partial application, so the next precondition is still open. | **True.** `Contract.seq C₁ C₂ link hlink` (`Build/Contract/Seam.lean:134–139`). The probe passes `C₁`, `C₂` and a placeholder `link := fun _ => []`, and omits `hlink` (`G4C3Targets.lean.txt` 1684–1690). `deceq.out`/`deceq2.out`: default synthesis fails; `maxSize 256` works; raising heartbeats alone fails. **The instance remedy is carried** (the review's (h) item 1; the backlog). **The `link`/`hlink` obligation is carried nowhere** (only 1.2's "unchecked route guidance"). The review's table row "Re-wrap composes: PASS … elaborates" claims more than a partial application shows | **True; carried** (C61-1: give the instance explicitly; supply the real `link` and prove `hlink`). **Review erratum** (in the resolutions): "Re-wrap composes" reads "the types compose (a partial application: `link` a placeholder, `hlink` not supplied)" |
| 13 | note | No new copied implementation. Before the left pass, introduce per-stage field lemmas. | **True** (the 85% pair `zr_rightPass_bounds`/`zr_rightPass_time`: two long `simp only` lists; the review's (e)). **Already carried:** the review's (h) item 5; the backlog ("the left pass by per-stage lemmas (an 85% pair already)") | **True; already carried**; restated in C61-1 |
| 3 | note | The adapter and the re-wrap mean what they should; promoting the adapter is a suitable later API change. | **True** | **Backlog line B61-2** (the shared-API window): promote `zr_singletonContract` to `Build/Contract/Basic`, beside `Contract.ofSegment` (or as a `Contract.seq` corollary in `Build/Contract/Seam`), as a `def` with non-`simp` `simps` field lemmas, through an API PR and its gate |
| 7 | note | The boundary instances show no counterexample; keep them in future integration probes. | **True.** Level one (scratch at −7): cells 5–8, heads 7 and −7, time `5 + 10·2 + 23 = 48`. Level two: halves 10–13 and 14–17, heads 14 and 5, time `10 + 10·4 + 23 = 73` | **Carried** (C61-1: both as probe examples, and the left pass's `ℓ = 1` instance) |
| 15, 16 | notes | Both frozen statements are credible and unproved; the remaining phases and both admissions continue. | **True.** The extension's `ℓ = 0` case is a separate fixed sequence | **Carried** (C61-1: the open obligations, as in the review's (h) items 1–4) |
| 17 | note | The recovered checkpoint is self-consistent; keep the review's corrections with the historical records. | **True.** The headroom is 8,589,934,592 − 294,219,776 = 8,295,714,816 B. The review's F2/F3 points check in the delivery (read as data): `SealCp1.lean` has no `example` control; `rewrite-audit-cp1.txt` is 5 lines of fixed text; the shipped `audit-scope.py` writes "The 49-definition seal" where the file says 57; `package-cp1.log` is 0 bytes; `Work.lean` differs from the delivered file (blob `1abbb871…`) in two places, 8 diff lines (a wrap at 1245, the status paragraph at 1433–1436); the item-start disk is 25,530,646,528 B (REPORT) against 25,530,650,624 B (log), 4,096 B apart (`out/61-F11-F17-report-erratum-items.txt`) | **True; report erratum E61-R1** items 2 and 3 (the review's F2 and F3) |
| 2 | note | Only the authorized partial lands; do not re-land #143's commits. | **True.** One commit, `13e17589`, with parent `43d22595`. The freeze is 18/18, 65 → 73 (8 added, 4 changed). Outside the home, only the extension's status paragraph changes | **No action.** Continuation 4's base contains #143 and #148 (in C61-1) |
| 9 | note | Source inspection supports rules 10 and 11; retain both seal controls and argument inspection. | **True** (57 sealed names, counted on the probe's attribute line) | **Carried** (C61-1; already the review's (h) item 7) |
| 1, 4, 5, 12, 14, 18 | notes | Bundle identity; the four refactored contracts; the endpoint; elaboration, axioms and probes; lint and status text; the interruption and the replay. | **True.** The hash and the 107 sections; the owned section = blob `1abbb871…`; the pack's head line is right for #148 (merge-base `43d22595`); lint 0 FAIL / 31 WARN over 39 files; added lines ≤ 97 characters; the replay's pins 11/11, 16 modules, sorry sum 10 | **No action** |

### Drafted texts for gate 61

**E61-V1 (evidence note: `campaign/gates/61-s13d-g4-cont3-fill/evidence/round1-review/10-outputs.txt`,
or in the resolutions' row 10).**

```text
Gate 61, minor 10: the three review outputs the bundle lacked. They have been in the repository
since ca7d1feda54f1f5508a1a7c3564ed06235671a15 (2026-10-22 13:46, with the review), and are
unchanged at the bundle's records revision 050d547e148dfbca2fc5a3b5846f0973644cb2c1. The bundle
list kept the first 60 of the review's 81 out/ entries.

campaign/fills/s13d/reviews/g4-cont3/out/seal-head.out     blob 9402d51f2a955b9ba1e4119452c2054a23bd2b79
  probe ../probes/G4C3SealHead.lean.txt (made by scripts/mkseal3.py; 57 definitions sealed, list
  out/seal-list.txt blob 641ad91ccc4c6877d2e2f73075e4b5d5f5e059cf), elaborated with
  tools/leanelab.sh against oleans-lg4c2; last line "exit 1 (4 s)".
  Diagnostics: errors at 1357:63, 1360:29, 1366:54, 1376:2 (the four rfl controls inside
  section G4C3Seal: catalog time, zoneStart 0 = 2, the adapter's post, the pass's time); no
  diagnostic on the four outside controls (1381-1403); warnings at 1449 and 1492 (the two
  targets, 1396 and 1439 + 53).
campaign/fills/s13d/reviews/g4-cont3/out/seal-tip.out      blob 4aa08a7ae5913647db720ab7dc7d14544e8b01fd
  the same seal at the tip b7447492 with the worker's commit; last line "exit 1"; the same
  diagnostics.
campaign/fills/s13d/reviews/g4-cont3/out/targets-1_1b.out  blob f79e4ab7ecc486247327fbf95aec20d361264301
  probe ../probes/G4C3Targets.lean.txt (the landed module's lines 1-1571 + the appendix
  ../probes/g4c3-1_1b-appendix.lean.txt), the same tool; last line "exit 0 (5 s)".
  Diagnostics: no error; warnings at 1396 and 1439 (the targets) and 1693:17 (unused variable x
  in the appendix's fail_if_success example); all eleven examples elaborate.
Source identity: G4C3Targets.lean.txt 1-1571 = 13e17589's ZoneRebalance.lean 1-1571;
G4C3SealHead.lean.txt 130-1352 = 13e17589's 127-1349 (the private home).
```

**E61-R1 (report erratum; for `campaign/fills/s13d/reports/g4-cont3-ERRATUM.md`, or appended to
`g4-cont3-REPORT.md`)**

```markdown
## Erratum (at integration; gate 61, minor 11 and note 17)

**Scope.** Three passages of this report (`g4-cont3-REPORT.md`, blob `4c2055cd…`), as corrected
at integration. The report itself stays as delivered. Sources: the maintainer's review
(`campaign/fills/s13d/reviews/g4-cont3/REVIEW.md`, F1–F3) and gate 61, the fill gate of PR #148
(`campaign/gates/61-s13d-g4-cont3-fill/`). None changes the delivered Lean. Both targets stay
admitted, and the 12 new or changed privates are on `[propext, Classical.choice, Quot.sound]`.

1. **Verification, paragraph 2: the citation inventory.**
   - "New TCSlib citations are within the supplied inventory: … `two_le_zoneStart` …" is wrong
     for that name. `Turing.two_le_zoneStart` (a public theorem, `Build/ZoneTape.lean:184`) is
     cited by `zr_rightPass_bounds` and `zr_rightPass_tape`. It is in none of: the brief's probe,
     the expanded probe, `evidence/g4/external-citations.txt`. The frozen
     `zoneRebalancePost_frames` already cited it at the base.
   - Cause: `audit-scope.py` collects namespace-qualified names plus four literals, and the
     lemma is cited unqualified.
   - The counts: the supplied probe is 439 checks of **428 distinct names**; the expanded probe
     is 445 checks of **434 names**. With `two_le_zoneStart`: 446 checks of 435 names, 0 errors,
     0 warnings (the review's `G4C3WorkerProbePlus`, row 22).
2. **Verification, paragraph 3: the rule-10 evidence.**
   - The final seal `evidence/g4/SealCp1.lean` has no controls: no `rfl` example fails inside
     the seal and passes outside it.
   - `logs/g4/rewrite-audit-cp1.txt` is five lines of fixed text written by `audit-scope.py`. It
     lists no argument. The shipped script writes "The 49-definition seal", while the shipped file
     says 57, so the file came from another version of the script.
   - Both checks were replaced by the review's and pass: its 57-definition seal with four
     controls that fail inside and pass outside (`out/seal-head.out`, `out/seal-tip.out`), and its
     argument-by-argument inspection (`out/rwargs.txt`, `out/kinds.txt`).
3. **Packaging and records.**
   - `logs/g4/package-cp1.log` is empty (0 bytes).
   - `evidence/g4/Work.lean` is a stale development copy. Its extension status paragraph and one
     line wrap differ from the delivered file.
   - The item-start free disk is 25,530,650,624 B in `logs/g4/disk-before-item.log`, not
     25,530,646,528 B (4,096 B apart; both far above the floor).
```

**C61-1 (the carry into the G4 continuation-4 draft).** No draft file exists yet
(`campaign/fills/s13d/drafts/` holds only the cont1 draft). The carries are in three places: gate
58's resolutions, the g4-cont3 review's (h) items 1–9, and the backlog's continuation-4 line. When
the draft is written, it takes the review's (h) list, plus gate 58's list less its "1.1b remainder"
item (now discharged), plus these gate 61 points:

> **From gate 61 (#148, checkpoint 1.1b's landing):**
> - **The return home's seam (note 8).**
>   - Sequence `zr_rightPassRow` into the return home's first row by `Contract.seq`.
>   - Give the 12-leaf state type's `DecidableEq` explicitly: a private `instDecidableEqSum`
>     term, or `set_option synthInstance.maxSize 256 in` on that one declaration. Default search
>     fails, and raising heartbeats alone does not help.
>   - Supply the real `link`: the outer half's word, not the review probe's placeholder
>     `fun _ => []`.
>   - **Prove `hlink`**: the next row's precondition from `zr_rightPass_post`, with
>     `zonedTape_blank_outside` for the cell beyond the old layout. Gate 61's probe checked only
>     that the types fit (a partial application).
> - **The second seek (note 6).** State its precondition by two local facts:
>   - the preserved left interval: tape 0 equal to the start's at every `q ≤ 0`
>     (`zr_rightPass_tape.2`), hence agreement on `[−zoneStart ℓ, 0]`;
>   - the scratch frame: blank off `[q, q + m)` (`zr_rightPass_post`).
>
>   Do not use `zoneRowPre`'s global facts. They fail after the right pass, because the ruler is
>   on scratch and the right zone has changed.
> - **Per-stage field lemmas (note 13).** Prove `time`/`lo`/`hi` per sub-composite and combine
>   them. The left pass must not add a third whole-composite `simp only` expansion beside
>   `zr_rightPass_time`/`zr_rightPass_bounds` (already 85%).
> - **The probe (minor 11).**
>   - Start from 446 checks of 435 names: the worker's 445 checks of 434, plus
>     `Turing.two_le_zoneStart`. Add continuation 4's own.
>   - Count it as "N checks of M names", and build it as a standalone import of the landed
>     module, stating the expected warnings.
>   - Take the inventory from an elaborated-constant walk of the **whole** module, not of the new
>     declarations alone: `two_le_zoneStart` was already cited by the frozen
>     `zoneRebalancePost_frames`, and no inventory listed it.
> - **Boundary instances (note 7).** Keep both as probe examples: level one (scratch at −7:
>   cells 5–8, heads 7 and −7, time 48) and level two (scratch at 5: halves 10–13 and 14–17,
>   heads 14 and 5, time 73). Add the left pass's `ℓ = 1` instance (−8).
> - **Rule-10 evidence (notes 9 and 10).** Require a seal with failing controls (inside fails,
>   outside passes) and an argument-by-argument inspection table. Ship the raw outputs of the
>   seal, its controls and the characterization probes, with their commands and exit statuses.
> - **Open (notes 15 and 16).**
>   - For the extension: the return home, the left pass, the `ℓ = 0` branch (a separate fixed
>     finite sequence: the positive pass's data do not cover it), ruler cleanup and assembly.
>   - For the rebalance: the scan, the guarded column moves, the passes, the home move, the mirror
>     and cleanup.
>   - Both admissions stay until proved.
> - **Base (note 2).** The campaign branch with #143 and #148 merged. Do not re-apply #143's
>   commits. Region lines are re-derived from the landed file: 1,572 lines, 18 public / 73
>   private, targets at 1396 and 1439.

**B61-1 (backlog, the G4 cont3 line's "For continuation 4").** Add: "the `link` and `hlink` of
the return home's seam (gate 61 probe: types only); the probe at 446 checks of 435 names, its
inventory taken from the whole module's elaborated constants; the level-one and level-two instances
as probe examples. The consolidated list is in gate 61's resolutions (C61-1)."

**B61-2 (backlog, the shared-API window).** "`zr_singletonContract` (`Build/ZoneRebalance`):
promote it beside `Contract.ofSegment` in `Build/Contract/Basic`, or as a `Contract.seq` corollary
in `Build/Contract/Seam` returning `{some (Sum.inr e)}`. Make it a `def` with non-`simp` `simps`
field lemmas, through an API PR and its gate (gate 61, note 3; the review's (d))."

---

## Shared carries: addendum v2.5

**B-2 (backlog).** Re-label the two "for the addendum's next version" items (committed lines
1331–1332 and 1366–1368) as **addendum v2.5**, and point them to V25-1 and V25-2.

**V25-1 (Part 1, item 2, "Packages match the manifest"; replaces "check each one: …").**

> After the cache step, and before every later Lake command, check each package **present in**
> `.lake/packages`: `git -C .lake/packages/<name> remote get-url origin` and `rev-parse HEAD` must
> equal the manifest's URL and revision. If one differs, stop with E-RES.
>
> List the manifest's packages that the narrowed fetch did not clone as **ABSENT**, not as a
> mismatch. At this pin they are `doc-gen4`, `UnicodeBasic`, `BibtexQuery` and `MD4Lean`, the
> documentation toolchain. The check passes when every present package matches and no module of
> your order list imports an absent package. Quote the check's last line in `REPORT.md`.
>
> Never let Lake re-clone or update a package that is already present.

**V25-2 (Part 1, item 2, the cache; and Part 3, once for the queue).**

> Before the first `lake exe cache get`, log the cache tool's local archive store
> (`${XDG_CACHE_HOME:-$HOME/.cache}/mathlib` by default): whether it exists, how many files it
> holds and their total size. The fetch log's "Attempting to download N" and "Decompressing M"
> then show that `M − N` archives were already in the store.
>
> In `REPORT.md`, say how many there were and, if you know, where they came from (an earlier
> session on this host, the host image). Do not describe them as downloaded by this session.
> **[User's decision: either "Archives already in this store are the cache tool's own, named by
> hash and checked by it; using them is allowed, and this store is not 'another session's object
> store'", or "Start from an empty store: if it is not empty, move it aside and record that".]**

---

## Reviewer additions (records)

- **Gates 60 and 61's bundles capped each review's `out/` folder at 60 entries.**
  - Gate 60: its list is exactly the first 60 C-sorted entries of `rulerdevice-cont1/out/` (98
    entries). The 61st, `39-upstream-head.txt`, is the first left out.
  - Gate 61: its list is the first 61 entries less one JSON graph.
  - Both were built at 13:52–13:53 from `050d547e`. The builder (`devtools/seyoon/mkbundle-mixed.py`)
    takes the list as given, so the cap was in the list's composition. I did not find the
    command that composed it.
  - Effect on gate 60: 39 `out/` files left out, about 29 of them cited by its REVIEW.md, among
    them `41-elab-tip-lg4c2.out` (the elaboration at the tip), `43-merged-replay.txt`,
    `44-overlap.txt`, `48-ax-vs-worker.txt` (behind REVIEW row 17, "equal on all 35") and
    `49-publics-*.out` (row 10's public constants). Gate 60's auditor recorded the claims that rest
    on them as attestations (its notes 14 and 16), so no gate-60 finding changes.
  - Gate 59's list was chosen by hand: 33 of `seamlayout-1/out/`'s files, without e.g. the raw
    probe outputs `24-*.out` or `12-elab-base-lbw2.out` (`out/bundle-vs-review-dirs.txt`).
  - **Lesson for the bundle builder:** include every file the review cites. Use no per-folder
    cap. Before building, check the review's citations against the list (as
    `scripts/cited-vs-bundle.py` here does), as is already done for the pack's own citations.
- **Two review inaccuracies in g4-cont3** are recorded in the resolutions, not by editing the
  review: the unused-variable warning in `targets-1_1b.out` (row 10), and "Re-wrap composes:
  PASS" for a partial application (row 8).
- **Gate 61's note 11 understates the inventory gap.** The brief's own 439-check probe already
  missed `two_le_zoneStart`, which the frozen `zoneRebalancePost_frames` cited at the base.

## Merge state

#145, #146 and #148 are open, all three on the campaign branch (not stacked). Their closures meet
only at the `TuringMachine` facade. #145's and #146's facade edits are 50 lines apart. #144 merged
at `0416ffea` and is disjoint from all three. The replays are `lsl` (14/14 at `7cd01f84`), `lf5c1`
(16/16 at `8114e482`) and `lg4c3` (16/16 at `13e17589`). No resolution here changes a `.lean`
file. So once each resolutions file is committed:
- **#145: clear to merge** (gate 59 closed, replay passed, base the campaign branch).
- **#146: clear to merge** (gate 60 closed, replay passed). The facade-only rule covers its overlap
  with #145.
- **#148: clear to merge** (gate 61 closed, replay passed).
- #147 (U2-S) still merges after #145, then gets its own replay and gate, as the backlog says.

## Actions for the maintainer

1. **Commit the findings verbatim** as `campaign/gates/59-c1-seamlayout-fill/findings.md`,
   `60-b6-f5-cont1-fill/findings.md` and `61-s13d-g4-cont3-fill/findings.md` (SHA-256 above).
2. **Write the three `resolutions.md`** from the tables above, in gate 58's form: the header, the
   round-1 verdict ("PASS …; the gate is closed"), the table, the errata, the carries and the merge
   state.
3. **Pack errata** (in the resolutions; packs as dispatched):
   - E60-P1 (`pack.md:13–14`, the base `34af2e0f`);
   - optionally E59-P1 (`pack.md:36`, "public declarations, source").
4. **Report errata**, each as a sibling file (gate 53's precedent) or appended:
   - `campaign/fills/c1/reports/seamlayout-1-ERRATUM.md` (E59-R1, 7 items);
   - `campaign/fills/s13d/reports/g4-cont3-ERRATUM.md` (E61-R1, 3 items).
5. **Gate 61 evidence:** E61-V1 (the three outputs by path and blob, with their commands and
   exits), and the two review errata (rows 8 and 10) in the resolutions.
6. **The counting convention W1**, in `workflow.md` §4 (and the pack and brief templates): public
   declarations (source) against public constants (elaborated). It defines terms and changes no
   rule. Put it to the user if a standards edit needs a ruling.
7. **Backlog:**
   - B59-1 (gate 59 closed; the 14 names for the sketch PR);
   - B60-1 (C60-1's location, for the F6/U2-E briefs);
   - B60-2 (`rd_test_return` factoring and F5's promotion candidates);
   - B61-1 (continuation 4: `link`/`hlink`, 446/435, the instances);
   - B61-2 (promote `zr_singletonContract`);
   - B-2 (the addendum items re-labelled v2.5, with V25-1/V25-2);
   - the bundle-builder lesson (no cap; check citations against the list).
8. **Carries:**
   - C60-1 into the F6 and U2-E brief drafts when written;
   - C61-1 into the G4 continuation-4 draft when written;
   - V25-1 and V25-2 into addendum v2.5.
9. **Decisions for the user:**
   - (a) v2.5: allow a pre-populated cache archive store, or require an empty one (V25-2);
   - (b) optionally, C60-2's docstring sentence (deferred pass or first consumer PR);
   - (c) W1, if it needs a ruling.
10. **Merge:** after items 1–2, the three bold lines in **Merge state** apply.

## What the auditors got wrong (or missed)

- **Gate 61, minor 10:** "absent from … the pinned repository tree" is wrong. The three outputs
  are in the bundle's records revision `050d547e` (since `ca7d1fed`). The bundle's 60-entry cap
  left them out. Their content confirms the review's claims, with one extra linter warning the
  review did not mention.
- **Gate 59, minor 1:** right in substance, but it reads as if the instances were undisclosed. The
  pack's question 6 and the review's F2 named all six. Only the unqualified "1 → 1 public" and
  REPORT §7's "No new public declaration" needed qualifying.
- **Gate 60, note 13:** it misses that the exit *state* persists after `t` with displaced heads
  (out/30c, A1), which matters for a consumer that detects the exit by its state. C60-1 says it.
- **Gate 61, note 11:** it misses that the brief's inventory already lacked `two_le_zoneStart`
  for a base citation (`zoneRebalancePost_frames`).
- **Gate 60:** its auditor did not notice that about 29 cited review outputs were missing from its
  bundle (the same cap). It treated the affected claims as attestations, so no finding is wrong.
