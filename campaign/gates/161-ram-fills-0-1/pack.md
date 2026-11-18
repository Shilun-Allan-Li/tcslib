# Gate 161 · RAM tiers 0 and 1: the run calculus and the word size (PR #371)

**Not yet clear to merge.** PR #371 is a draft into `complexity/ram-simulation`, **stacked on
#370** (gate 160, CLEAR). Seyoon dispatches and merges, #370 first.

- **Lean head:** `24aa40503e183a6de58b67dc4d3f7aea08d670b5` (branch `ram/fills-0-1`): three
  commits on #370's head `25040f43`.
  1. **Tier 0** (`fill-ram-steps`, Codex): the 18 admissions of `Programs/WordRAM/Extended.lean`.
  2. **Tier 1** (`fill-ram-wordsize`, Codex): the 3 admissions of
     `RAMSimulation/WordSize.lean`.
  3. **A maintainer repair at intake.** The delivered private `cfg_map_comp` restated the public
     `Turing.Cfg.mapState_mapState` (`Build/InputRewind`, in the import closure) with the same
     proof. Its two uses now cite the public lemma, −13 lines.
- **Deliveries** (exchange `arora-barak-ch3-4/inbox/`): `fill-ram-steps.zip` SHA-256
  `cbc46b929f9a570f…` and `fill-ram-wordsize.zip` `d48bc9590e078412…`. Each patch applies to its
  base and reproduces the delivered file byte for byte. Commits 1 and 2 land them unchanged. The
  two reports are bundled (`evidence/REPORT-tier0.md`, `REPORT-tier1.md`).

## What changes

- **`Extended.lean`** (698 lines, +384/−84). All 18 run-calculus results are proved. There are
  nine private helpers:
  - `lift_run`: one induction, shared by every map between run relations;
  - `footprint_mono` and `exists_footprint`: footprint enlargement and the finite union;
  - the instruction-fetch lemmas `mapped_fetch`, `xstep_base_fetch` and `projected_fetch`;
  - `step_agreeOutside`, `xSteps_verdict_unique` and `xstep_coin_irrel`.

  It reads `step`, `effect` and `Steps` only through #370's readers. The module docstring now
  says that the results are proved.
- **`WordSize.lean`** (917 lines after the repair). All three results are proved, with eleven
  private declarations.
  - **The multiplier:** a finite-control arithmetic leaf with no work tapes (`mulMachine`, with
    its scan and flush runs) multiplies a binary word by the constant `c`.
  - **`scale_computes`:** captures an existing numerical machine's output (published embedding),
    rewinds it, and hosts the multiplier on it through two published seams.
  - **The logarithmic word size:** the published input-length counter writes `bits |x|`; a
    hosted conditional counter emits its length, which is exactly `logSpace |x|`, then the
    scaler multiplies.
  - **The space-constructible case:** consumes `ComputesInSpace.computesFunInTime_and_forall_spaceUsed_le`
    (`ConfigCount`) for a uniform deadline.
  - **Three added imports:** `SpaceComplexity/ConfigCount`, `Build/InterpreterStartup` and
    `Build/Rewind`. The brief allowed only `Build/*` imports. The `ConfigCount` import is
    recorded as approved by Seyoon in the fill's session
    (`evidence/import-approval-tier1.txt`); **Seyoon confirms it at merge**.
- **Statements:** every statement in both files is byte-identical (`SOURCE.json`: 2 owners, 41
  changed or added declarations, none added publicly, none removed, no header or definition
  change).
- **Admissions:** the RAM work's 32 drop to 11, namely Simulation 2 and Classes 9 (tiers 2 and
  3).

## Brief for the auditor

1. **Proofs and readers.** Check each of the 21 proofs and their sketches. Check rule 10: the
   reports list every other-file definition reached and the reader used; the evidence below
   seals them.
2. **Statement freeze.** Check that both files' statements are byte-identical to the base.
3. **Bounds (tier 1).** Check that the logarithmic construction's time is linear and its space
   is logarithmic at every length, `n = 0` and `c = 0` included. Check that the
   space-constructible case's `TW` depends on `n` only.
4. **Duplication.** Review the 9 copy-screen pairs and their dispositions
   (`PAIR-DISPOSITIONS.json`). Look for any re-proof of a published lemma that the screen
   misses. The intake found and repaired one.
5. **Imports:** the three added imports, and that nothing else changed.

## Evidence (`evidence/`)

- **`REPLAY.json`:** the merged-tree replay of the 2 owners' downstream closure on
  `oleans-cl160-cc91f4`, which is #370's build (gate 160's output).
  - 7 modules: 7 passed, 0 failed.
  - 11 inherited admissions: Simulation 2 and Classes 9.
  - Pool 3; peak memory 1.1 GB.
- **Seals:** the definition boundaries of 39 changed proofs were computed (40 heads); the 34
  proofs that reach another file's definition pass sealed (Extended 22, WordSize 12).
- **Controls:** 43 definitions and 86 identities, each native-PASS and sealed-FAIL.
- **Sweeps:** the proof-syntax sweep finds 39 roots and 0 read candidates; the Lean-backed sweep
  flags nothing; citation homes are in `CITATION-HOMES.json`.
- **Copy screen** (population: the 2 files): 0 → 9 directed pairs, all within the two files, all
  dispositioned (`pair-notes.json`):
  - parallel inductions over different relations, or the phases of one machine;
  - argument lists of calls to the fill's shared private helpers.

  Run 1 (on `e96813aa`, before the repair) had 11 pairs; the two `cfg_map_comp` pairs are gone.
- **Fill-side evidence:** each report gives the fill's own checks, among them axiom prints with
  only `propext`, `Classical.choice` and `Quot.sound`, sealed re-elaboration, controls and
  downstream elaboration.

Use the campaign finding table and give a CLEAR or HOLD verdict.
**Deliver your findings as a downloadable file named `gate161-ram-fills-0-1-findings.md`**
(the findings table and the verdict line, no other wrapping), and also paste its content in your
reply.
