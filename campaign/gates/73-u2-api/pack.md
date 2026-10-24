# External audit pack — U2's API (PR #161, an API gate)

Campaign: the Arora-Barak chapters 3-4 plan, U2 (the `k`-tape universal machines
`Turing.exists_selfUniversalK` and `Turing.universalK`, [AB09, Theorem 1.9, §1.4.1]).
- **Why:** megafill C's draft brief for U2 (`campaign/fills/u2s/drafts/u2s-fill-universal.DRAFT.md`)
  routes both targets through two public configuration encodings with no published lemma,
  `Turing.StepBlock.forwardLoopCfg` (`Build/StepBlockForward`) and `Turing.rulerHostCfg`
  (`Build/InputDevice`); rule 10 then leaves no route (the drafting report's Q-U1). The draft's
  review (`campaign/fills/megafill/reviews/megafill-c-drafts/u2/REVIEW.md`) verified that and found
  two more gaps: U2-U's space ledger needs a tape's space as the count of its visited cells (F1,
  a blocker), and U2-E's suffix drop has no lemma in U2's imports, so a fill would copy
  `NDCodeSimulator`'s private `ic_input_suffix` (F2). **The user ruled (2026-10-24): one API PR**
  with all of them, its own gate, the suffix-drop copies to the dedup window.
- **The head:** `lean/u2-api` at `a8c45ad7`, one commit on the campaign branch (Lean tree
  `21d53053`, after #156) (`evidence/u2-api.patch`). This bundle's Lean files are from `a8c45ad7`,
  and its records from the records commit that the dispatch prompt names.

| File | Change |
|---|---|
| `TuringMachine/Deterministic` (vendored) | **`Turing.MultiTapeTM.spaceUsedByTape_eq_card`**: `tm.spaceUsedByTape cfg t i = (tm.visitedByTapeHead cfg t i).card`, by `rfl` beside the definition (as #149's `spaceUsed_eq_sum`) |
| `TuringMachine/Build/StepBlockForward` | `attribute [simps (config := { isSimp := false }) state inputPos workTapes workTapePos output] forwardLoopCfg`: five field equations (`Turing.StepBlock.forwardLoopCfg_state` and the like; `_workTapes` pointwise in the tape and the cell); the header names them |
| `TuringMachine/Build/InputDevice` | the same attribute on `rulerHostCfg` (`Turing.rulerHostCfg_state` and the like; `_inputPos` is the `Fin` literal `⟨ℓ + c.inputPos.val, _⟩`); **`Turing.pairEncode_drop`**: `(pairEncode u x).drop (2 * u.length + 2) = x`, through `pairEncode_eq` and `length_pairEncode`; `Turing.pairEncode_pairEncode_drop` re-proved through it (statement unchanged; its local `hd` had unfolded `pairEncode`, another file's definition, by `simpa [pairEncode]` and `from rfl`); the header lists them |

## Brief for the auditor

1. **Faithfulness.** Are the ten generated equations exactly the two definitions' fields
   (`evidence/U2ApiConsumer.out` prints them)? Is `spaceUsedByTape_eq_card` the definition's
   reading, and `pairEncode_drop` true as stated (the empty `u`, the empty `x`)? Are the docstrings
   and the header sentences exact?
2. **Sufficiency.** The review's route lemmas for U2-U and U2-E (`r_encode_init_tapes`,
   `r_encode_init_fields`, `r_encode_halt`, `r_ruler_fields`, `r_seam_phase1`, `r_seam_phase2`:
   both phases' seam configurations) are re-run against the generated names, with the two module
   bodies at the head (`U2ApiConsumer.lean.txt`, imports hoisted); the space ledger's two steps
   against the new equation (`U2SpaceProbe.lean.txt`, a copy of `Deterministic` with the probe
   appended). Do they show U2 needs nothing more from these definitions? Is `_inputPos` as a `Fin`
   literal adequate for a consumer that reads `.val` (the review's alternative was a nested
   `inputPos_val` projection)?
3. **Rule 10 in the API.** The equations are generated or proved in their definitions' own files
   (`simps`, `rfl`). `pairEncode_drop` and the re-proof of `pairEncode_pairEncode_drop` read
   `pairEncode` (`Encoding`) only through `pairEncode_eq` and `length_pairEncode`: the consumer
   probe re-proves both with `pairEncode` irreducible (`section DropSealed`, its control failing
   sealed and closing unsealed). The consumer probe's seal (10 definitions:
   `StepBlock.forwardLoopCfg`, `rulerHostCfg`, `MultiTapeTM.initCfg`, `Cfg.init`,
   `FinTM.bufferTape`, `StepBlock.summaryCells`, `tableBitsK`, `unaryFin`, `embedEmitCfg`,
   `Cfg.mapState`, with the `simp` erasures) has its 10 controls failing at lines 2154–2173 and
   closing unsealed; the space probe's 2 controls fail sealed (lines 566, 571). Complete?
4. **Duplication.** The screen (the three files, `Encoding`, `UniversalStartup`, `NDCodeSimulator`,
   `Logspace/PathWalk`, `Codec/Parse`, `Finite`): 203 → 204 declarations, 24 → 26 pairs. The two
   new pairs are `pairEncode_drop` ⇄ `NDCodeSimulator`'s private `ic_input_suffix`, 100% each way:
   the same lemma and proof. With `Complexity.Codec.pe_drop` and `PathWalk`'s private
   `drop_pairEncode` (same statement, other proofs) they form the ledger's new family **SD-1**
   (`campaign/duplication-ledger.md`), acknowledged by the ruling, its disposition recorded there
   (the startup-kit PR re-points `ic_input_suffix` where acyclic; the rest in the dedup window).
   Is that disclosure complete? Does any other private restate a new equation?
5. **No collateral change.** The freeze (`evidence/freeze/`): public 41 → 42 (`Deterministic`),
   2 → 2 (`StepBlockForward`, the generated lemmas not counted as source declarations), 15 → 16
   (`InputDevice`); one body changed (`pairEncode_pairEncode_drop`); no statement changed.

## Repository-side attestations (verify or challenge)

- **Elaboration** (against `oleans-lphl2`): the three files with no diagnostic
  (`evidence/elab-*.out`).
- **Axioms:** the ten field equations on `[propext, Quot.sound]` (`U2ApiConsumerAx.out`);
  `pairEncode_drop` and `pairEncode_pairEncode_drop` on `[propext, Quot.sound]`;
  `spaceUsedByTape_eq_card` on `[propext, Classical.choice, Quot.sound]` (`U2SpaceProbe.out`).
- **Lint:** `TuringMachine` 0 FAIL, 67 WARN over 83 files (68 at the base: check 8 no longer lists
  `forwardLoopCfg` or `rulerHostCfg`; `RulerAt` stays listed); no added line over 100 characters.
- **Screen:** as in item 4 (`screen-u2api-*`, `pairdiff-head.txt`; the base read on a detached
  worktree at the campaign tip, Lean tree `21d53053`).
- **Replay:** `replay-lu2api.sh`, the three files' downstream closure (325 modules,
  `down-lu2api.txt`). It contains the files of the open #158, #159 and #160, so it runs after they
  merge, on the merged tree. **Pending:** this gate is dispatched before the replay; the PR is
  clear to merge only when both have passed.

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Severity guide as in `campaign/standards/TEMPLATE.md`. Findings go verbatim into
`campaign/gates/73-u2-api/findings.md`. The gate closes when it has zero blockers and zero majors.

**Deliver your findings as a downloadable Markdown file named `u2-api-findings.md`** (the findings
table and the verdict line, no other wrapping), and also paste its content in your reply.
