# External audit pack — the interpreter's startup kit (PR #162, an API gate)

Campaign: the Arora-Barak chapters 3-4 plan, B5a (the uniform simulator
`Turing.MachineFormat.exists_uniformSimulator`, the last admission of `CodeSimulator` and of
targets 3–8 and `Complexity.baker_gill_solovay`) and C1 (the interpreter core).
- **Why:** megafill C's draft brief for B5a (`campaign/fills/b5a/drafts/b5a-fill-unisim.DRAFT.md`)
  routes B5a's startup through the same pieces as the interpreter core
  `Turing.exists_ndInterpreterCore`, which proves them as eight privates of `NDCodeSimulator`.
  `CodeSimulator` is upstream of `NDCodeSimulator` and rule 11 forbids another file's privates, so
  a fill would re-prove them (the drafting report's Q-B1). The draft's review
  (`campaign/fills/megafill/reviews/megafill-c-drafts/b5a/REVIEW.md`, "Q-B1") recommended
  harvesting them first (`workflow.md` §4: a private host already in the tree is harvested before
  a second consumer is briefed against it) and probed the harvest. **The user ruled (2026-10-24):
  option A, the startup-kit API PR first**, with `NDCodeSimulator` re-pointed in it. The
  maintainer's choices within A: `seamCompTM_step` in the new module (so the PR depends on nothing
  in flight); UN's identical `un_step` re-pointed too (no extra replay); the suffix drop kept as a
  private helper of the window call (the ledger's SD-1).
- **The head:** `lean/startup-kit` at `06d314c3`, one commit (`evidence/startup-kit.patch`) on
  #160's final head `1cc8ab39`, which the campaign branch merged as `90688cbb` (the two have the
  same Lean files). This bundle's Lean files are from `06d314c3`, and its records from the records
  commit that the dispatch prompt names.

| File | Change |
|---|---|
| `TuringMachine/Build/InterpreterStartup` (new) | eight public lemmas: `Turing.seamCompTM_step` (from `ic_seam_step`), `Turing.prefixCanon_pairExtract_halt` (`ic_header_result`), `Turing.embedSilentRetTM_firstReturn` (`ic_capture_return`), `Turing.embedSilentCfg_initCfg` (U2-S's `ss_captureInitial`, `UniversalK`), `Turing.headerCapture_run` (`ic_header_capture`), `Turing.exists_windowCall` (`ic_window_call`), `Turing.installCall_releasePhase` (`ic_install_phase`), `Turing.exists_layoutCall` (`ic_layout_call`, restated over `pairEncode n.bits (unaryFin M.q₀ ++ tableBitsK M.tr)`, since `serializeK` lives in `CodeSimulator`); one private, the suffix drop; statements and proofs as the sources', docstrings with reference tags |
| `TuringMachine/NDCodeSimulator` | imports the kit; the eight privates removed (49 → 41 privates) and their uses re-pointed; the layout call's result read back through `serializeK_eq` (`simp only [← serializeK_eq] at layouts`) |
| `Diagonalization/NTimeHierarchy` | UN's private `un_step` removed; its two uses are `seamCompTM_step` (the same statement) |
| `TuringMachine` (facade) | imports the kit; one line in its module list |

## Brief for the auditor

1. **Faithfulness of the harvest.** Is each public statement exactly its source private's
   (`ic_layout_call`'s restatement through `serializeK_eq` aside), and is each docstring an exact
   reading? `exists_layoutCall`: is the restatement equivalent, and is the re-pointed use
   (`simp only [← serializeK_eq] at layouts`) exact?
2. **The re-points.** `NDCodeSimulator`'s core and the universal NDTM's setup now cite the kit:
   unchanged statements, no remaining use of a removed private, no change of meaning.
3. **Rule 10 in the kit.** The seal (`KitSealed.lean.txt`/`.out`, re-run at this head): the kit's
   whole text with `prefixCanonTM`, `FinTM.pairExtractTM`, `pairEncode`, `pairDecode`,
   `embedSilentRetTM`, `embedSilentCfg`, `embedSilentTM`, `seamCompTM`, `seamReleaseTM`,
   `Cfg.mapState`, `MultiTapeTM.runFrom`, `MultiTapeTM.initCfg`, `MultiTapeTM.step`, `Cfg.init`,
   `Action.apply`, `Cfg.ofWords`, `stateWord`, `FinTM.bufferTape`, `StepBlock.summaryCells`,
   `tableBitsK`, `unaryFin` and `counterValue` locally irreducible, and `MultiTapeTM.initCfg`,
   `Cfg.init` and `Action.apply` erased from `simp`; the only errors are the 22 controls at its top
   (lines 54–133; the kit from line 135); they close unsealed (`KitSealControl.*`). Inspect every
   `rw`/`simp`/`exact` argument.
4. **Placement and imports.** The new module imports `UniversalStartup`, `Build/Primitives`,
   `Build/Embed`, `Build/Seam`, `Build/Loop`, `Build/InputWindow`, `Build/SeamLayout` and
   `Build/StepBlock`, none of which sees `CodeSimulator` or `NDCodeSimulator`; is it the right home?
5. **Duplication.** The v3 screen (the kit, `NDCodeSimulator`, `NTimeHierarchy`, `UniversalK`,
   `UniversalStartup` and the seven `Build/` modules the kit imports;
   `screen-population*.txt`) at the campaign tip after #160 (`90688cbb`, without the kit) and at
   the kit's head: 743 → 743 declarations, 438 → 440 pairs (`screen-kit-*`). The two new pairs are
   `embedSilentCfg_initCfg` ⇄ `UniversalK`'s private `ss_captureInitial` (100% each way: the
   harvested statement and proof; `UniversalK` cannot see the kit until `CodeSimulator` imports
   it; the ledger's SK-1). No other pair is new or gone (`pairdiff-head.txt`). The remaining
   members: U2-S's `ss_` family in `UniversalK` (the same constructions under other contracts),
   for the dedup window or U2's fill, as `UniversalK` is U2's owned file; the suffix drop (SD-1).
6. **No collateral change.** The freeze (`evidence/freeze/`): `NDCodeSimulator` 3 → 3 public,
   49 → 41 private (the eight removed); `NTimeHierarchy` 5 → 5 public, 11 → 10 private
   (`un_step` removed; `un_setup` and `un_step'` changed by the rename only); no statement changed.

## Repository-side attestations (verify or challenge)

- **Elaboration** (against `oleans-lrcan3`, the replayed snapshot of #160's final head, the
  campaign's tree): the kit with no diagnostic (`elab-InterpreterStartup.out`); `NDCodeSimulator`
  and `NTimeHierarchy`, each checked as one file after the kit's text with the imports merged (no
  snapshot has the kit yet): no diagnostic, and only `ntime_hierarchy`'s sorry warning,
  respectively (`NDCSCat.out`, `NTHCat.out`). The recipe: `recheck.sh.txt` (maintainer-local
  paths), `mkax.py.txt`.
- **Axioms** (`NDCSCatAx.out`): the eight kit lemmas, `exists_replayCanonizer`,
  `exists_ndInterpreterCore` and the bridge on the standard three (`seamCompTM_step` on
  `[propext, Quot.sound]`).
- **Lint** (`lint-*.txt`): `TuringMachine` 0 FAIL, 68 WARN over 84 files (no new warning; the new
  file is counted); `Diagonalization` 0 FAIL, 2 WARN; no added line over 100 characters.
- **Replay:** `replay-lkit.sh`: the changed files' downstream closure (five modules: the kit,
  `NDCodeSimulator`, `NTimeHierarchy` and the two facades) on the tree after #161 (U2's API, whose
  merged-tree replay passed, 325 of 325, and covers these modules too), chained from its snapshot
  `oleans-lu2api`. **Pending** (after #161 merges; the gate is dispatched before it).

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Severity guide as in `campaign/standards/TEMPLATE.md`. Findings go verbatim into
`campaign/gates/74-startup-kit-api/findings.md`. The gate closes when it has zero blockers and
zero majors.

**Deliver your findings as a downloadable Markdown file named `startup-kit-api-findings.md`** (the
findings table and the verdict line, no other wrapping), and also paste its content in your
reply.
