# The seam layout's landing (PR #145, a fill gate): resolutions (round 1; gate CLOSED)

**Gate:** the fill gate of PR #145 (`lean/c1-seamlayout-fill` at `126127b8`): the worker's six
commits squashed (`bfe3e023`), the maintainer's status commit `7cd01f84` (docstrings only), and a
merge of the campaign branch after #139 and #143 (`126127b8`). `Turing.exists_seamLayoutTM` is
proved. Pack `pack.md`; bundle SHA-256
`3b3f345986fa306271492e0a95e6e9f890663e348107283075d06e3157d703c2` (81 sections; folder
`59-c1-seamlayout-fill-gate/`). Replay `replay-lsl.sh` passed (user, 2026-10-22): 14 of 14 at
`7cd01f84`, static-equal (8). #139 and #143, merged into the head afterwards, meet its closure
only at the facade (the standing rule: no re-replay), and #144 (merged since) not at all.

**Round 1** (`findings.md`, verbatim; received 2026-10-22, SHA-256
`5e288fb044945ae47ec16e774055334bac4121abfd0b7a75f7add42526c3cb6d`): **PASS, 0 blockers, 0 majors,
3 minors, 14 notes. The gate is closed.** No `.lean` change. The maintainer's review sub-agent
verified every finding, together with gates 60 and 61, against the repository, the bundles and
`git`: all 17 true (`evidence/round1-review/REVIEW.md`, its `out/` and `scripts/`; no Lean was
needed).

| # | Severity | Finding | Resolution |
|---|---|---|---|
| 1 | minor | The freeze's "1 → 1 public" counts source declarations; the three private inductives' `deriving DecidableEq, Fintype` add six public instance names and their auxiliaries to the elaborated environment. | **True; records. No Lean change.** The six (`Turing.instDecidableEqSl_Key`, `…Sl_PairPhase`, `…Sl_SplitPhase`, `Turing.instFintypeSl_Key`, `…Sl_PairPhase`, `…Sl_SplitPhase`) and 18 auxiliaries; with the target's 19 `_proof_` auxiliaries the module adds 44 public constants and 1 public declaration (`out/59-F1-generated-instances.txt`). The pack had named the six (its question 6, the review's F2); what lacked a qualifier is `pack.md:36` and the report's §7 and §12. Precedent: 35 private types with `deriving` in 20 landed files at `0416ffea`; chapter 2's `generatedExceptions`; gate 14's "explicitly named declarations" (`out/59-F1-precedent-private-deriving.txt`). No name clashes at the tip or at the open heads. **Pack erratum:** `pack.md:36`, "(the review's `out/10-declfreeze.txt`: 1 → 1 public, 0 → 35 private, the only body change the target's)", reads **"(the review's `out/10-declfreeze.txt`: 1 → 1 public declarations and 0 → 35 private, counted at source; the only body change is the target's. The elaborated environment also gains public constants: the target's 19 proof auxiliaries and the six derived instances of question 6, with their auxiliaries)"**. **Report erratum** item 7 (`campaign/fills/c1/reports/seamlayout-1-ERRATUM.md`). The counting convention below (W1) applies to packs and reviews from now on. |
| 2 | minor | 14 private proofs over 20 lines lack a "Proof sketch"; the user's deferral is respected. | **True; already ruled** (user, 2026-10-22: a docstring-only follow-up after the landing). The same 14 by an independent census of the landed head (`out/59-F2-sketches-landed.txt`). The follow-up is written: `lean/c1-seamlayout-sketches` (`ff8d5f10`, on `126127b8`; 1 → 15 sketches, code identical with comments stripped, 0 diagnostics against `oleans-lsl`), to open after #145 merges; no gate (the user's ruling on #144); its replay is SeamLayout and the facade. |
| 3 | minor | Several report claims need an erratum (the seal in §5, `bufferTape_of_neg`, the archive paths, `final-module-check.log`, the manifest's literal FAIL, the sweep before commit 6). | **True, all six; report erratum** `campaign/fills/c1/reports/seamlayout-1-ERRATUM.md` (seven items, with finding 1's), beside the unchanged report, as for gate 53 (`out/59-F3-report-erratum-items.txt`). |
| 16 | note | The narrowed-cache and resource figures are consistent; record the literal manifest result. | **True; records.** The manifest result is the erratum's item 5. On this host 1,002 of 1,002 cache files were downloaded. **Carried** to addendum v2.5: the manifest check counts only the packages present (`campaign/backlog.md`, the addendum v2.5 item). |
| 8, 13 | notes | Keep the self-redirect and the scheduled last-phase lemma for `Build/Seam`; three promotion candidates for the shared-API window. | **True; already in the backlog.** The last-phase lemma is written (`lean/phasehost-last`, `0b671a28`: `phaseHostTM_tr_of_red_none`, `phaseHostTM_run_le`; seal test clean), to open as an API PR with its own gate after #149 merges. |
| 17 | note | The replay supports its tree; later merges meet the closure only at the facade. | **True; records** (the header above). |
| 4–7, 9–12, 14, 15 | notes | Integrity and scope; `C = 18` and the ledger; the leaves; the dispatch; the endpoint, frame, silence and first exit; the word API; the edge cases; rules 10 and 11; axioms and probes; elaboration and lint. | **No action.** Re-checked: the bundle hash, its 81 sections, the module blob `05d4e353e5e1460a8940f1fc6667d1e8e568ad97`; `bfe3e023` holds the worker blob `483be51b804c3927aed348d49de4d4d9aab51cbd` and `7cd01f84` changes docstrings only (`out/59-F4-identity.txt`); the ledger `T = 2n − r + 4h + 5q + 2|v| + 23 ≤ 18(n + 1)`. Seals with controls together with the inspection of every argument (finding 12) are standing practice. |

**The counting convention (W1; for packs, reviews and briefs from this gate on).**
- A **public declaration** is one that the source introduces without `private`. The source
  census (`declfreeze.py`) counts these, and so do the statement freeze, a brief's "no new public
  declaration" rule and a pack's "N → N public", which say "public declarations, at source".
- A **public constant** is a non-private name in the module's elaborated environment (the axiom
  probe's walk of the module's publics). Packs and reviews report new public constants
  separately, by kind: a declaration's compiler auxiliaries (`_proof_N`, `match_N`, `eq_N`, …),
  and the instances that `deriving` generates for a private type (public names in Lean 4.25).
  Neither kind is a public declaration.
- A derived instance of a private type needs no finding when its type is private to its file
  and a name check over the tree and the open PRs finds no clash. An explicit `private instance`
  is the form to use where a derived name would clash. Any other new public constant is a
  finding.

(Whether W1 also goes into `workflow.md` §4 is put to the user.)

**Reviewer additions (records):**
- **The bundle lists of gates 60 and 61 were capped at 60 entries per review folder** (this
  gate's list was chosen by hand). Gate 61's minor 10 is the consequence; see its resolutions.
  **Lesson for the bundle builder:** include every file the review cites, with no per-folder
  cap, and check the review's citations against the list before staging, as for the pack's own
  citations (`scripts/cited-vs-bundle.py`).

**Merge state.** #145 is on the campaign branch (not stacked); its closure meets #146's and
#148's only at the facade (their facade hunks are 50 lines apart). **Clear to merge.** #147
(U2-S) merges after it, then replays on the merged tree and gets its fill gate (gate 63).
