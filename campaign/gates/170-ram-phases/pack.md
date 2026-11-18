# Gate 170 · RAM simulation, tier 2 job D: the phase interfaces (PR #386)

**Not yet clear to merge.** PR #386 is a draft into `complexity/ram-simulation`. It proves the
two phase interfaces of `RAMSimulation/Sim/Phases` (#372), the per-instruction phases of the
stage-2 machine (Codex fill `fill-ram-phases`, round 2). Codex audit approved by Seyoon on
2026-11-18. Seyoon dispatches and merges.

- **Lean head:** `09546b899d451b693e80588bd625e6b476eb930b` (branch `ram/fill-phases`), on the
  RAM branch after #379 (`3d2a6960`). One commit: the fill's patch, landed unchanged
  (`fill-ram-phases-r2.zip` SHA-256 `dc746470…`). The patch reproduces all 30 delivered files
  byte for byte.
- **Since the replay:** #385 (job A, the word rows) merged into the RAM branch. It changes only
  proof bodies of `Build/WordArith` and adds one reader in `StateRenaming`, with no statement
  changes, so this PR's replay is unaffected. #383 (job E) and #388 (job C) touch the same facade
  and `Build/Embed`. The second to merge takes the union of the facade's imports and keeps one
  copy of the identical reader `Turing.Cfg.select_eq`.
- **Rulings that bind:**
  - tier 2 design D1: public homes `RAMSimulation/Sim/*` under the internal namespace
    `WordRAM.Sim`;
  - D2: reuse `RecordTable`'s layout;
  - the standing reader rule: pure `rfl`/`Iff.rfl` readers beside a definition in its home file.

## What it adds

| Target | Status |
|---|---|
| `WordRAM.Sim.exists_phase`: a phase machine for every extended-RAM instruction | proved modulo the 12 row statements of jobs A, B, C |
| `WordRAM.Sim.exists_verdictPhase`: the verdict phases | proved, no admission |

**The 12 row statements** are `Turing.bvBits_injective`, `exists_wordAddTM`, `exists_wordSubTM`,
`exists_wordMulTM`, `exists_wordHalfTM`, `exists_wordSignExtendTM`, `exists_wordIntTM`,
`exists_wordSignTM`, `exists_wordNonzeroTM`, `exists_keyLookupTM`, `exists_keyAssignTM` and
`exists_inputBitTM`. The nine `Build/WordArith` statements are proved in #385 (merged).
`exists_keyLookupTM` and `exists_keyAssignTM` are proved in #389, and `exists_inputBitTM` in
#388.

**The modules:**
- 25 new modules `Sim/Phase*.lean`, each under 600 lines (inventory in `REPORT-phases.md`). They
  hold layout and table invariants, frames and rows, blocks and schedules, memory and input
  machines, tests and branches, the coin fork, and emission.
- `Phases.lean`: the two target bodies, importing the new modules.
- The facade lists the new modules.
- Three pure readers: `Turing.Cfg.select_eq` (`Build/Embed`), `Turing.seamCompTM_tr_inl`
  (`Build/Seam`) and `Turing.NDTM.phaseHostND_tr` (`Build/NDHost`).

## Brief for the auditor

1. **The construction.** Each instruction's phase must implement `xstep` on the encoding, as
   `exists_phase` states:
   - immediate addresses become keys;
   - keyed lookups fetch the operands;
   - a word or input row computes the result;
   - one keyed assignment updates the table;
   - indirect stores fetch their value before building the computed key;
   - `bltz` uses the sign test with two live exits;
   - `emit` uses the nonzero test and an optional-output leaf;
   - `coin` is one stationary choice in `NDTM.phaseHostND` with two deterministic continuations
     joined at `next`.

   Check that the encoding (`Encodes`, `TableOf`) is preserved, including width zero and absent
   cells. Check the footprint charge: the table has exactly
   `1 + entries·(keyWidth + valueWidth + 4)` cells.
2. **The bounds.** The common units `phaseTime` and `phaseSpace` must dominate every row's
   allowance (table scans, linear rows, quadratic multiplication, input length) and match the
   interface's `C·((T.card + 1)(W + 1) + W² + n + 1)` and radius.
3. **The verdict phase:** its one-step optional emission and halt, with the work heads
   unchanged.
4. **Admissions:** `exists_phase` reaches exactly the 12 row statements, and
   `exists_verdictPhase` none (the fill's walk; the metadata check, whose allowance is exactly
   those 12). Nothing in `Build/RecordTable` is reached.
5. **The public surface.** D1 allows public declarations in `WordRAM.Sim`; flag any that
   duplicate a library result.
   - **In particular, `PhaseBlock` (one exit) and `PhaseBranch` (two exits).** Their `seq`
     compositions and their `phase_machine_ofBlock`/`ofBranch` packagings share most of their
     text and differ in the exit set (copy screen, class `parallel`). Should they be merged
     into one structure over a finite exit family before this lands, or is the duplication
     acceptable?
6. **Readers and rule 10:** the three readers restate their definitions, and the seals pass.

## Evidence (`evidence/`)

- **`REPLAY.json`:** the merged-tree replay on `oleans-cl166-cl165`, 268 modules: 268 passed,
  0 failed.
- **Seals:** pass, 154 proofs and 66 heads. The metadata allowance is the 12 row statements.
- **Controls:** 70 definitions and 140 identities in two parts, native-PASS and sealed-FAIL.
- **Sweeps:** the proof-syntax sweep finds 0 read candidates in 154 roots. Citation homes are
  in `CITATION-HOMES.json`.
- **Copy screen:** 50 → 143 pairs, 93 new, all classified (`PAIR-DISPOSITIONS.json`). They are
  record-shape matches of configuration builders, instances of the shared row placement
  `phase_wordRow`, block and schedule compositions, and per-instruction certificates. The
  `PhaseBlock`/`PhaseBranch` family is raised in item 5.
- **The fill's report** (`REPORT-phases.md`): axiom prints, the admission walk, the module
  inventory, and the foreign definitions with their readers.

Use the campaign finding table and give a CLEAR or HOLD verdict.
**Deliver your findings as a downloadable file named `gate170-ram-phases-findings.md`**
(the findings table and the verdict line, no other wrapping), and also paste its content in your
reply.
