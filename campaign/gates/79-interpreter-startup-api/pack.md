# External audit pack — the interpreter startup (PR ⟨PR⟩, A+, an API gate)

Campaign: the Arora-Barak chapters 3-4 plan, B5a's uniform simulator and the interpreter core.
- **Why:** megafill C's review of B5a's brief (`campaign/fills/megafill/reviews/megafill-c-drafts/
  b5a/REVIEW.md`, F9 and decision D-3) found that B5a's target would need a twelve-phase startup
  structurally parallel to the interpreter core's (`Turing.exists_ndInterpreterCore`,
  `TuringMachine/NDCodeSimulator.lean`), even with the startup kit (#162, gate 74) published.
  **The user ruled (2026-10-25): D-3 = A+**, the startup harvested into one published contract
  that both cite, before B5a is briefed. The design note `campaign/items/b5a/
  A-plus-startup-design.md` sets the boundary, the statement and the vehicle. **The user ruled the
  note's recommendation on all five decisions:** a maintainer API PR; `p` passive tapes with an
  embedding; existential roles; the core re-pointed in the same PR; the PR opened after #164 and
  #165 merge.
- **The head:** `lean/interpreter-startup` at ⟨HEAD⟩: the commit `f30210d7`
  (`evidence/interpreter-startup.patch`) ⟨and the campaign merge after #164 and #165⟩. This
  bundle's Lean files are from ⟨HEAD⟩, and its records from the records commit that the dispatch
  prompt names.

| File | Change |
|---|---|
| `TuringMachine/Build/InterpreterStartup` | **`Turing.exists_interpreterStartup`** (+1,208 lines): for a machine family `M : ∀ α, MultiTapeTM k Bool (Fin (n α + 1))`, an installer `CI` with `exists_installCallTM`'s contract shape for `M α`'s serialization `pairEncode (n α).bits (unaryFin (M α).q₀ ++ tableBitsK (M α).tr)`, and `p : ℕ`, one machine `U` with four role tapes and `p` passive tapes, whose run from the timed paired input first reaches `done` within `costI α + A (|α| + |w| + 1) + B (|bits t| + min t |x| + 1)` with the counter, window, table and summary tapes laid out, every head at `0`, the passive tapes unchanged, and the input head at its first cell. Two imports added (`Build/Rewind`, `Build/InputRewind`); the module header names it |
| `TuringMachine/NDCodeSimulator` | `exists_ndInterpreterCore` re-proved: the startup at `p = 4` (the stream; the loop's two banks and its capture), seamed to the unchanged hosted loop. Statement unchanged; its **Implementation.** paragraph rewritten; 2,384 → 1,412 lines |

## Brief for the auditor

1. **Faithfulness.** Does `exists_interpreterStartup` hold as stated for every `α`, `x`, `t`
   (including `t = 0`, empty `α`, empty `x`, `t > |x|`) and every `p` (including `p = 0`)? Are the
   threshold fields exactly what the core's loop and B5a's verdict need? Is the time bound right?
   It is the sum of the eleven phases' bounds and the seams' steps (`hTsum`), relaxed to
   `A = 120 + C_L`, `B = 47 + C_W`. Is the docstring an exact reading?
2. **The generalization.** The proof is the core's phases 1–11 with the installer, the machine
   family and the passive tapes made parameters (`mkstartup.py.txt` lifts the lines and asserts
   each rewrite). The tape layout is renumbered (`K = 6 + k₁ + k₂ + CI.k + p`). The stream's blank
   lemma becomes "blank off the passive range", and the threshold reads the passive tapes by the
   clean ledger. Is anything of the core's argument lost or weakened?
3. **The statement's boundary.** It is stated with the serialization word rather than
   `serializeK`, because `serializeK` lives in `CodeSimulator`, which B5a's brief makes import
   this module (a cycle otherwise). Consumers convert by `serializeK_eq`. Is that the right
   boundary? Are the existential roles with their ten distinctness facts sufficient, and is
   anything missing that a consumer needs?
4. **The re-pointed core.** Is the core's statement unchanged? Does its proof use only the
   startup's conclusion, its own loop lemmas and published lemmas? Check the loop embedding over
   the seven role and passive tapes (an if-chain with 21 explicit distinctness facts), the
   start's identity and the time ledger through `ic_time_ledger`.
5. **Rule 10.** The startup reaches 23 other-file definitions (`evidence/seal/
   KitStartupDefScan.out`; the projections, instances and the reducible `Cfg.Halted` excluded).
   Sealed, with `MultiTapeTM.initCfg` and `Cfg.init` erased from `simp`, the startup has no body
   error, and each control fails at its own goal. The re-pointed `NDCodeSimulator` passes gate
   66's whole-module seal (46 definitions and 4 erasures), and that gate's 50 controls fail sealed
   and close unsealed at this base (`evidence/core/`). Does any step still close only by
   unfolding another file's definition?
6. **Duplication.** The v3 screen ran on gate 74's population, widened by the rows the startup now
   cites (`Build/Rewind`, `Build/InputRewind`) and by `ClassNP/ExhaustiveReplay`: 18 files
   (`evidence/screen-population.txt`). It ran at the campaign tip (`wt-mc`, `a524c36f`) and at the
   head (`f30210d7`): 955 → 956 declarations, 596 → 598 pairs, 2 new and none gone
   (`evidence/screen-aplus-*.txt`, `pairdiff-head-vs-base.txt`). **Both new pairs are the core's
   base pairs, moved with its text at the same scores** (`evidence/pairs-moved.txt`): the startup
   reproduces `InputRewind`'s `Cfg.mapState_mapState` (343/402, 85%) and `SeamLayout`'s `sl_rewrap`
   (252/322, 78%). At the base, `exists_ndInterpreterCore` held exactly these two. At the head, the
   core keeps weaker pairs with the same two lemmas (60%, 56%) from its loop junction. Both are the
   field-equation idiom. The first was accepted by the user as an idiom pair at gate 66
   (resolutions, note 12). The second is paired by `UniversalK`'s and `CodeSimulator`'s lemmas too
   (B5a's screen base). Semantic: the eleven phases now exist once (in the startup). Do any of the
   hazards in the population (U2-S's `ss_` startup in `UniversalK`, UN's `un_` setup in
   `NTimeHierarchy`, `ExhaustiveReplay`'s `xr_` idioms) re-derive the new lemma? The ledger's SK-1
   (`embedSilentCfg_initCfg` ⇄ `ss_captureInitial`) is unchanged.
7. **The consumer.** `B5aConsumerProbe.lean.txt` instantiates the startup at `p = 0` with B5a's
   installer (the polynomial canonizer through the install call, its route probe's
   `b5a_install`), and states the bound in `serializeK` terms. Is that what B5a's brief will need?

## Repository-side attestations (verify or challenge)

- **Elaboration** (against `oleans-lkit2`, the campaign's tree after #162; recipe
  `evidence/check.sh.txt`):
  - the kit module with no diagnostic, and `exists_interpreterStartup` on the standard three
    axioms (`Kit-ax.out`);
  - `NDCodeSimulator` after the kit's text, imports merged: no diagnostic, and the core on the
    standard three (`NDCSCat.out`);
  - `NTimeHierarchy` after both: only `ntime_hierarchy`'s existing sorry warning (`NTHCat.out`).
- **Seal** (`evidence/seal/`, `evidence/core/`): as in item 5.
- **Freeze** (`evidence/freeze/`, `declfreeze.py` v4):
  - `InterpreterStartup`: public 8 → 9, `Turing.exists_interpreterStartup` added, and no other
    change;
  - `NDCodeSimulator`: 3 → 3 public and 41 → 41 private, the one authorized body change being
    `Turing.exists_ndInterpreterCore`.
- **Lint** (`evidence/lint-*-TuringMachine.txt`): 0 FAIL at both; the head adds one WARN, the kit's
  size (1,592 lines > 1,000). No line over 100 characters.
- **Replay:** the kit's downstream closure (the module, `NDCodeSimulator`, `NTimeHierarchy` and the
  two facades), chained from the merged-tree snapshot after #164 and #165. **Pending.**

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Severity guide as in `campaign/standards/TEMPLATE.md`. Findings go verbatim into
`campaign/gates/79-interpreter-startup-api/findings.md`. The gate closes when it has zero blockers
and zero majors.

**Deliver your findings as a downloadable Markdown file named
`interpreter-startup-api-findings.md`** (the findings table and the verdict line, no other
wrapping), and also paste its content in your reply.
