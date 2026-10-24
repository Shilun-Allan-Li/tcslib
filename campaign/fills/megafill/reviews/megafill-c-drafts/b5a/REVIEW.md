# Review: megafill C's B5a brief draft (`b5a-fill-unisim`), and Q-B1, Q-B2, Q-B3

Reviewer: the maintainer's review sub-agent, 2026-10-24. Scope: the draft
`campaign/fills/b5a/drafts/b5a-fill-unisim.DRAFT.md`, its pre-ship
`campaign/fills/b5a/drafts/b5a-fill-unisim/preship-77f1eb4f/`, the drafting report's Item 3
(Q-B1 blocking, Q-B2, Q-B3) and its note on `Complexity.Codec.pe_drop`. Nothing in the repository
or `exchange/` was changed. Everything below is under
`$S/review/megafill-c-b5a/` (`S` = the session scratchpad): checks `out/`, probes `probe/`,
scripts `scripts/`, the fixed draft `fix/`, the diff `suggested-fix.diff`.

**Bases.** The records tip at the start was `6e8db28f23386c567466dd6a7357d8ec35d1cde8`. Its TCSlib tree
(`f2c39238…`), `CodeSimulator.lean` blob (`c64567f0…`), lakefile, manifest, toolchain and root
facade are the same as the drafting base `77f1eb4fb74deb7a1ac7bae7bc4e98d5d0f9a532` and
`906a9d7ba611dbb94a5b11c55a61faa9b0b6318f` (out/01). All Lean ran in my worktree at `6e8db28f`
against `oleans-lslsk`, one elaboration at a time, through `leanelab.sh`.
**Changed during the review:** #156 moved from `a4d9b024` to `0e5f210b` (2026-10-24T05:12Z), and
the campaign tip moved to `aad8a095` (records only: gate 69 round 1, the lphl2 replay, the user's
new ruling). Both matter here (F2).

## Verdict

**Not issuable until its prerequisites land.** These are:
1. #156 at its round-2 head. It now edits this brief's owned file: `canonEmitVerdict`, net −2 lines.
2. The follow-up phase-host API PR the user ruled on 2026-10-24. It edits `canonEmitVerdict` again,
   and the ruling says it lands before megafill C.
3. On the recommended Q-B1 ruling (A), the startup-kit API PR with its gate.

Then re-run the pre-ship at that base, regenerate every base-dependent number, and issue with the
edits in `suggested-fix.diff` (F1–F10). If the user rules Q-B1 = B instead, prerequisite 3 goes
away, but the other two still apply.

The route itself is sound. Every cited declaration exists, is public and is on the standard
axioms. All recorded probes reproduce.

## Checks

| # | Check | Result | Evidence |
|---|---|---|---|
| 1 | Base identity: the three revisions share one Lean tree; the hashes the text uses | pass; #156 and the tip moved during the review (F2) | out/01 |
| 2 | Completeness against §5 and the cont7 model, section by section | all sections present; gaps in F1, F2, F3, F5, F7 | out/02 |
| 3 | Frozen statement and docstring, byte for byte | verbatim (head = 8554–8582, tail = 8655–8664); the prose's ranges are off (F7) | out/03 |
| 4 | Import probe re-run | 109 checks of 109 names, 0 errors, 0 warnings, the eight axiom prints as recorded; extended to 137 names (0 errors, 18 prints, all standard) | out/04, probe/B5aUSImportProbe*.out |
| 5 | Every cited name: home module and publicity | 157 names, all public (none missing); only the target has `sorryAx` | out/05, probe/B5aReview{Homes,Axioms}.out |
| 6 | Route probe and seal controls re-run | 0 diagnostics; 16 controls close unsealed and fail sealed, each at its own goal; the seal misses three touched definitions (F8) | out/06 |
| 7 | Route lemmas at the prescribed home (region (b), inside `StepBlockClients`) | the six `us_` lemmas elaborate there, unsealed and sealed over 18; only the target's sorry | out/06, probe/HomeProbe*.out |
| 8 | Verdict probe: assembly, SHA-256, re-run | recipe reconstructed (it is not recorded); SHA-256 `b8a46abb…` matches; only the target's warning; standard axioms | out/07 |
| 9 | Route soundness and the uniform ledger | sound; phases, verdict start and ledger checked against the published statements; **the start from `S.tm.initCfg` is not in the route** (F3) | out/18, out/11 |
| 10 | Overlay elaboration | exactly the target's sorry (overlay 8661) | out/08 |
| 11 | Q-B2: no cycle, no clash, each import needed, downstream modules | pass; the five modules that gain names elaborate with the five imports with exactly their base sorries (the pre-ship did not check this) | out/08, probe/ImportClashProbe.out, probe/downstream/ |
| 12 | Q-B1: the eight privates, published equivalents, branch search | none published (`pe_drop` = `ic_input_suffix`, but behind a 56-module closure); `un_step` = `ic_seam_step` | out/09, out/10 |
| 13 | Q-B1 option A built as a probe | fails with the report's six imports (19 errors); with `Build/Primitives` and `Build/StepBlock` it elaborates; sealed over 22 with 22/22 controls; the bridge by `serializeK_eq` holds; `NDCodeSimulator` re-pointed elaborates with its base sorry only | out/09, probe/Kit*.out, probe/NDCodeSimulatorRepoint.out |
| 14 | The start from `initCfg` through published lemmas | sealed probe: 0 errors | out/11, probe/StartProbe.out |
| 15 | Q-B3 and the budget | both refinements legitimate; ledger uniform; budget tight (F6) | out/18 |
| 16 | Screen population and base (no screen run) | population lacks 2 cited files (F5); the status records no root or revision (F6); `screen-base.txt` internally consistent; 2,756 declarations recounted | out/12 |
| 17 | Order list, roots, base sorries | reproduced: 119 / 41 / 31 in 15 modules; `fillinputs-overlay.py` read first, safe, byte-identical outputs | out/13 |
| 18 | Placeholders, hashes, width | 23 marked placeholders plus the unmarked ones listed; every full hash resolves and means what the text says; only the title and a table row exceed 100 columns | out/14 |
| 19 | Lint | `TuringMachine` 0 FAIL / 68 WARN / 83 files (identical); `Diagonalization` 0 FAIL / 2 WARN / 5 files (not stated in the draft) | out/15 |
| 20 | Admission walk of targets 3–8 and BGS | their only admission is the target | out/16 |
| 21 | #156 and the follow-up: how the brief should read in each case | the drafting-base text is wrong now (F2) | out/17 |

## Findings

**F1 (major): the recommended outcome ⟨Q-B1: A⟩ is under-specified.**
- *Claim:* the A paragraphs appear only in the ancestor list, the "read first" note, the imports
  and route step 1 (header passes, capture, seam step). Route steps 2–3 (the window, the
  release-wrapped install, the layout), the Hosts' rows, the Known hazards and the population have
  no A variant. They prescribe the raw rows (`exists_inputWindowCopyTM`,
  `exists_installCallTM` behind `seamReleaseTM`, `exists_seamLayoutTM`) and call the core's private
  install phase "the pattern".
- *Why it matters:* under A, a fill following this text would re-derive the very lemmas the API PR
  publishes, which is exactly the copy A exists to prevent. The issue-time probe also lacks the
  kit's names.
- *Evidence:* draft lines 47–49, 184, 230, 290, 292–311, 261–266, 444–483.
- *Fix:* `suggested-fix.diff`. It names the kit's eight public lemmas in the ancestor list, gives A
  variants in steps 0′, 2 and 3 and in the Hosts' rows, adds the kit module to the population, and
  makes the issue-time probe "the review's 137 plus the kit's eight names".

**F2 (major): the owned file changes twice before issue.**
- *What changed:* #156's round-2 head `0e5f210b` re-points six phase-host prefixes (gate 69's
  major, "fix it in #156"), including `CodeSimulator.lean`'s `canonEmitVerdict` (hunk
  `@@ -4593,11 +4593,9 @@`, net −2). On 2026-10-24 the user also ruled a follow-up API PR (a
  start-state and a redirect-branch equation in `Build/Seam`) that re-points `canonEmitVerdict`'s
  start-state read (line 4602). That PR "lands before megafill C is issued (it changes
  `CodeSimulator`)" (gate 69's resolutions at `aad8a095`).
- *What goes stale:* every line number after 4600, the size, the blob check (`c64567f0…`), the
  overlay, the screen base, and the order list's oleans (#156 also edits `Build/StepBlock`).
- *What is wrong in the text:* "⟨IN-FLIGHT⟩ … #156, `Build/Seam`'s last-phase lemmas … not citable"
  and "Parallel batches: None in `CodeSimulator.lean`" no longer hold. The Hosts list also names
  `phaseHostTM`/`phaseHostTM_run` with no last-phase condition and without the new lemmas.
- *Fix:* fix the issue base after both PRs. Rebuild the pre-ship there, regenerating numbers rather
  than patching them. Use the case-1 text of out/17, which the diff carries: the ancestor list gains
  the last-phase lemmas, and the phase host gets its own bullet ("not needed; if used, only through
  `phaseHostTM_run`, `phaseHostTM_run_le`, `phaseHostTM_tr_of_red_none` and the follow-up's two
  equations"). If either PR is still open at issue (case 2, not recommended), say that it edits
  this file, and forbid hosting a last phase (the user's ruling of 2026-10-22).

**F3 (minor): the route never says how `S` starts.**
- *The gap:* the target is about `S.ComputesInTime z …`, so the run starts from
  `S.tm.initCfg z`. The core started from an explicit configuration and never needed this step. No
  lemma publishes the `q₀` of `seamCompTM`, `embedSilentRetTM`, `embedSilentTM`, `embedEmitTM` or
  `seamReleaseTM`. Without guidance a fill either reads them by `rfl`/`simp` (a rule-10 violation)
  or re-proves U2-S's private `ss_captureInitial` (a cross-file pair with `UniversalK`).
  `ExhaustiveReplay`'s `xr_E_initCfg` uses the same idiom.
- *The published route exists:* `{ W with q₀ := … }` read through
  `MultiTapeTM.initCfg_with_q₀`/`runFrom_with_q₀`, then the capture-initial identity and a
  relabelling of `Cfg.init`. probe/StartProbe.lean shows it, sealed, with 0 errors.
- *Fix:* the diff adds "The start" to step 0, a pitfall, the hazards, and (under A)
  `embedSilentCfg_initCfg` in the kit.

**F4 (minor): the report's option A would not compile as specified, and it misses one piece.**
- *Imports:* the proposed module's six imports (UniversalStartup, Build/Embed, Build/Seam,
  Build/Loop, Build/InputWindow, Build/SeamLayout) do not provide `FinTM.pairExtractTM`
  (`Build/Primitives`) or `StepBlock.summaryCells` (`Build/StepBlock`). The kit fails with them
  (probe/KitProbeSixImports.out: 19 errors). With the two added it elaborates, and neither addition
  creates a cycle.
- *The missing piece:* B5a needs `ss_captureInitial` (F3), which the kit does not include.
- *A better home for the seam step:* `seamCompTM_step` belongs in `Build/Seam`. The follow-up
  phase-host API PR edits that file anyway and pays Seam's 88-module replay, so it costs nothing
  extra there.
- *Fix:* use the corrected list in the Q-B1 recommendation below.

**F5 (minor): the screen population misses two files whose lemmas the route cites.**
- *Which files:* `Configuration` (`Cfg.ext`, `Cfg.init` and its fields, `Action.apply`) and
  `StateRenaming` (`Cfg.mapState` and its fields). The issued B6 model includes both. Adding them
  takes the screen from 2,756 to 2,776 declarations. Under A, also add the kit module.
- *Evidence:* out/05, out/12.
- *Fix:* in the diff (56 files, or 57 under A). Stage the new list at issue.

**F6 (minor): screen records, the screen race, and the budget.**
- *Records:* `screen-base.status` holds only start, exit and end. The model records the root path,
  the root HEAD and tracked changes. The 87-minute run's tree is therefore not attested, although
  the file is internally consistent (3,005 rows summing to 973,130; 2,756 declarations recounted).
- *Race:* the brief starts the before-screen "right after your first edit" while editing goes on.
  The script reads every file before pairing, so the run is safe only once its reads finish, and
  the brief does not say so.
- *Duration:* the after-screen will run longer than 87 minutes. The target's body is `sorry` at the
  base, so it is not screened; after the fill it becomes one of the largest screened declarations.
  The core's landing screen went from 76 s to 131 s for the same kind of change.
- *Fix:* run every screen on a frozen worktree of its commit (in the diff), and record the status
  in the model's format at issue. The budget question (Q-M2) is under decisions below.

**F7 (minor): line ranges in the prose.**
- *Frozen text:* the draft says "lines 8554–8580 … the fill appendices 8582–8654". The source has
  the sketch to 8582, a blank 8583, the appendices 8584–8653, a blank 8654, and `-/` alone on 8655.
- *Region (d):* it says "before its closing ` -/` (line 8655)", but the `-/` stands alone on 8655.
- *Fix:* in the diff. All of these move again at the issue base (F2).

**F8 (minor): pre-ship seal coverage and the home.**
- *Seal:* the route probe's seal leaves out `tableBitsK`, `pairEncode` and `unaryFin`, which
  `b5a_table_le`'s rewrite chain exposes. Sealing them changes nothing.
- *Home:* the drafting agent probed the lemmas standalone and the verdict after the target. It never
  probed them at the prescribed home inside `StepBlockClients`, with `open StepBlock` and the
  section variable in force.
- *Evidence:* the review did both: probe/HomeProbe{,Sealed} (18 sealed), clean.
- *Fix:* the diff records it. Ship the home probe at issue.

**F9 (minor): how the brief handles the hazards.**
- *Unworkable instruction:* "A proof reproducing one at 90% or more must be factored" cannot be
  carried out for cross-file hazards. The fill may not publish, nor edit other files, so the
  instruction should be "stop and escalate".
- *Unlisted duplicate:* `un_step` is `ic_seam_step`'s exact statement (out/10). The screen never
  pairs the two, because one is a term proof and the other a tactic proof.
- *A hazard option A leaves open:* the core's startup assembly. `exists_ndInterpreterCore`'s phases
  1–11 and loop entry are about 1,060 lines, and B5a's assembly will be structurally parallel to
  them. A ≥ 50% cross-file pair between the two bodies is a real possibility, and the brief must
  say beforehand what happens then (decision D-3).
- *Fix:* in the diff, with a ⟨D-3⟩ placeholder.

**F10 (minor): a sentence that contradicts outcome B.** Lines 347–349 say "Do not copy
`NDCodeSimulator`'s privates". Under B the brief tells the fill to re-prove them as `us_` privates,
with their pairs pre-disclosed. *Fix:* in the diff (made conditional on the outcome).

**F11 (note): H1's proofs predate rule 10.** `h1HostedVerdict_effect` (8499–8528) passes
`MultiTapeTM.initCfg`, `Cfg.init`, `FinTM.VirtualTag`, `Action.apply` and `vhostCfg` to `simp`, and
unfolds `MultiTapeTM.step`. It is the model nearest to B5a's verdict glue, so the fill is likely to
imitate it. The diff adds a pitfall. This rule-10 debt in the owned file is not recorded in the
backlog: for the user's dedup window.

**F12 (note): records.**
- The verdict probe's assembly recipe is not recorded; out/07 reconstructs it.
- The Diagonalization lint base (0 FAIL, 2 WARN over 5 files) is missing.
- Gate 46's folder is `campaign/gates/43-seam-layout-statements/`, round 2.
- Targets 3–8 and BGS become fully admission-free, not just free "from your file" (out/16).
- The report's "`Logspace/PathWalk`" is `SpaceComplexity/Logspace/PathWalk`.
- The restated `exists_layoutCall` has one line over 100 columns, to be wrapped in the API PR.
- The kit's public docstrings will need reference tags (policy §2).

## Q-B1: recommendation — A, the startup kit as an API PR before B5a

**Reasons:**
- *Policy requires it.* `workflow.md` §4, "Hosts in briefs", says: "A private host already in the
  tree is harvested (a promotion PR and its gate) before a second consumer is briefed against it."
  `policy.md` says "do not write a third private variant". B5a is the second consumer of every one
  of the eight.
- *The duplicates already exist.* B would be the third private seam package (after `ic_seam_step`
  and UN's identical `un_step`), the third or fourth header capture, and the fourth suffix drop.
- *A is verified mechanical and rule-10 clean.* The harvested proofs elaborate below
  `CodeSimulator` and pass a 22-definition seal with 22/22 controls. The re-pointed `NDCodeSimulator`
  elaborates with exactly its base sorry.
- *A is cheap to replay:* 5 modules.
- *The IR-1 precedent (#153) went the same way.*

**The API PR's contents.** Statements are verbatim from out/19 and probe/KitProbe.lean.

*Home:* a new module `TCSlib/Complexity/TuringMachine/Build/InterpreterStartup.lean`, importing
`UniversalStartup`, **`Build/Primitives`**, `Build/Embed`, `Build/Seam`, `Build/Loop`,
`Build/InputWindow`, `Build/SeamLayout` and **`Build/StepBlock`**.

*Public statements:*

| Public statement | Source private | Home |
|---|---|---|
| `Turing.prefixCanon_pairExtract_halt` | `ic_header_result` (NDCodeSimulator 101–131) | the new module |
| `Turing.embedSilentRetTM_firstReturn` | `ic_capture_return` (133–157) | the new module |
| `Turing.headerCapture_run` | `ic_header_capture` (199–240) | the new module |
| `Turing.exists_windowCall` | `ic_window_call` (348–405) | the new module |
| `Turing.installCall_releasePhase` | `ic_install_phase` (745–791) | the new module |
| `Turing.exists_layoutCall` | `ic_layout_call` (242–293), restated over `pairEncode n.bits (unaryFin M.q₀ ++ tableBitsK M.tr)` | the new module |
| `Turing.embedSilentCfg_initCfg` | U2-S's `ss_captureInitial` (UniversalK 324–362), verbatim | the new module |
| `Turing.seamCompTM_step` | `ic_seam_step` (719–743) = UN's `un_step` (NTimeHierarchy 255–274) | **`Build/Seam`, in the follow-up phase-host API PR** (recommended), or the new module |

*Details:*
- `ic_input_suffix` (336–346) moves into the new module **as a private** helper of
  `exists_windowCall`, so the copy count is unchanged. Its public equal `Complexity.Codec.pe_drop`
  is unusable from here: it would bring 56 more modules into the closure. The three copies
  (`pe_drop`, PathWalk's `drop_pairEncode`, this one) retire together in the dedup window, under a
  name beside `pairEncode_eq` in `Encoding` (a 257-module replay). I agree with the report's
  dedup note, with its path corrected.
- Optional: `Turing.Cfg.init_mapState`, the relabelling `(Cfg.init q x).mapState f = Cfg.init (f q) x`
  (5 lines, no copy known). Without it, B5a writes it as a leaf.
- Every proposed name is unused at the tip, at both PR heads and on the 25 newest local branches.

*Re-points:*
- `NDCodeSimulator` re-points in the same PR (the #153 precedent): −291 lines, plus one import and a
  `simp only [← serializeK_eq] at layouts`. It is C1's owned file, so C1's pre-ship must be re-run at
  the new base: its regions shift by one line and its blob and screen base change. The alternative
  is to defer this re-point and ledger the overlap.
- UN's `un_step` re-points with `seamCompTM_step`. It is in the closure already, so this costs no
  extra replay.
- U2-S's `ss_` family is the same mathematics under different contracts (out/10), and `UniversalK`
  is U2's file in megafill C, so it goes to the dedup window.

*Size and cost:* about +405/−291 lines. The replay is 5 modules: the new module, `NDCodeSimulator`,
`NTimeHierarchy` and both facades. It needs an API gate with the seal and its controls, the
bridge probe and the re-point.

**Not solved by A** (decision D-3): the assembly-level resemblance to the core's
`exists_ndInterpreterCore`. One alternative, "A+", harvests a generic startup contract: a startup
machine parametrized by an installer and a set of passive tapes, reaching the hosted loop's entry.
The core and B5a would both cite it. That is a larger design and refactor (about 1,000 lines
generalized out of the core). It belongs to the dedup window, unless the user wants no
assembly-level pair at all.

## Q-B2: recommendation — approve

- *No cycle:* none of the five imports' closures contains `CodeSimulator` or `NDCodeSimulator`.
- *No clash:* the five plus all nine downstream modules import together without error.
- *Each import is needed:* the header passes, the rewinds, the layout, the window, and locality
  (there is no deterministic locality lemma).
- *The five downstream modules that gain names still elaborate* under those imports, with exactly
  their base sorries.
- Under A the list becomes the kit module, `Build/Rewind` and `Nondeterministic`. The other three
  come in transitively, and listing them anyway is harmless.
- A public deterministic locality lemma beside `MultiTapeTM.toNDTM_runWith` is a fair promotion
  candidate; there is no second consumer yet.

## Q-B3: recommendation — accept both refinements

- *The window `x.take t`:* it is the only published way to place a suffix window. Locality makes
  acceptance on the window equal to acceptance on `x`, and `b5a_accepts_take` proves that.
- *The landed verdict:* it is the machine the sketch describes, already proved, and rule 7 requires
  citing it.
- The frozen docstring stays as it is. For a complete delivery, REPORT.md should propose the
  `**Implementation.**` paragraph, and the maintainer edits it in at integration together with the
  appendices' campaign labels (in the diff). This is the core landing's F7 pattern.
- Budget: 5 hours is tight even under A, and a partial at checkpoint 3 or 4 is the realistic
  outcome. Decide how the long after-screen is counted (D-5).

## Decisions for the user

- **D-1 Q-B1:** A (recommended) with the contents above, or B. Within A:
  - *where `seamCompTM_step` goes:* the follow-up phase-host API PR (recommended), or the new module;
  - *`NDCodeSimulator`'s re-point:* in the kit PR, with C1's pre-ship re-run (recommended), or
    deferred to the dedup window;
  - *UN's `un_step`:* re-pointed now (no extra replay), or in the dedup window.
- **D-2 Issue base:** fix it after #156, the follow-up phase-host API PR and (under A) the kit PR.
  The whole megafill C shares one base, so C1's and U2's pre-ships must also be re-run there, since
  #156 and the follow-up change `Build/StepBlock`, which is upstream of both.
- **D-3 The assembly pair with `exists_ndInterpreterCore`:** pre-disclose any pair below 90%, with
  its shared fragments listed, as a "startup assembly" family for the dedup window (recommended), or
  harvest a generic startup (A+) before B5a.
- **D-4 Q-B3:** accept the two refinements, and the REPORT.md `Implementation.` proposal.
- **D-5 Q-M2:** count B5a's budget up to the start of its after-screen, run screens on frozen
  worktrees, and let the next item start while the after-screen runs (recommended). Or raise B5a to
  6 hours.
- **D-6:** the suffix-drop family (`pe_drop`, `drop_pairEncode`, the kit's private) to the dedup
  window, with a home in `Encoding`.

## Files

- `REVIEW.md` (this file)
- `suggested-fix.diff` (unified, against the draft at `6e8db28f`; `git apply --check` passes; when
  applied, it equals `fix/b5a-fill-unisim.DRAFT.md`)
- `out/01`–`out/19` (one file per check)
- `probe/` (every probe and its output)
- `scripts/` (the review's tools: closure, the identifier census, the screen consistency check, the
  declarations-only count, the verdict assembly, `make_fix.py`)
