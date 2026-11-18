# Gate 168 · RAM simulation, tier 2 job E: the two stage-2 targets proved (PR #383)

**Not yet clear to merge.** PR #383 is a draft into `complexity/ram-simulation`. It proves the
two frozen stage-2 targets from the three tier 2 interface statements of #372 (Codex fill
`fill-ram-run`, round 2). Seyoon dispatches and merges.

- **Lean head:** `a6199066dcefcc0ab5cbf6d424693bba0cc4cae0` (branch `ram/fill-run`), with the
  RAM branch after #379 (`3d2a6960`) merged in. The commits:
  1. the fill's patch, landed unchanged (`fill-ram-run-r2.zip` SHA-256 `b4f8f533…`; the patch
     applies to the RAM branch and reproduces all 22 delivered files byte for byte). The fill
     worked from `7342f98b` (#375); the RAM branch has moved since (#379 is not merged; #381 is),
     and the patch applies cleanly;
  2. a one-token maintainer repair: an unused `simp` argument (`reduceCtorEq`) in
     `Sim/RunSource.lean`, flagged by the linter;
  3. a merge of the RAM branch (#379; `WordSize.lean` auto-merged: this PR's reader beside the
     definition, #379's results at the end);
  4. a maintainer repair from this gate's run 2: `runEntry_reconstruct` and
     `RunSetup.host_initCfg` rebuilt a renamed configuration field by field with `Cfg.ext`, the
     pattern of G154-02; they now cite the published `Cfg.mapState_eq_of_fields`.
- **Rulings that bind:** tier 2 design D1 (public homes `RAMSimulation/Sim/*` under the internal
  namespace `WordRAM.Sim`), D3 (one induction); the approved edit of `Simulation.lean`'s imports;
  the standing reader rule (pure `rfl`/`Iff.rfl` readers beside a definition in its home file).

## What it adds

| Module | Content | Status |
|---|---|---|
| `RAMSimulation/Simulation` (frozen statements) | `WordRAM.exists_simulation`, `WordRAM.exists_ndSimulation`: bodies, sketches, module docstring; stale line references replaced by names | proved modulo the three interfaces |
| `RAMSimulation/Sim/Run*` (17 new, 2,812 lines) | host and embedding (`RunHost`, `RunEncoding`, `RunSlices`, `RunPhase`); coin and schedule bookkeeping (`RunSource`, `RunChoices`, `RunDriver`); the induction (`RunInstruction`, `RunPrefix`, `RunInduction`, `RunStep`, `RunStartup`); bounds (`RunCosts`, `RunSpace`, `RunBounds`, `RunInput`, `RunBranch`) | proved modulo the three interfaces |
| `RAMSimulation` (facade) | imports and contents for the 17 modules | — |
| `Build/Embed`, `NondeterministicSpace`, `WordSize` | readers `Turing.embedEmitTM_q₀`, `Turing.NDTM.visitedWith_eq`, `Turing.NDTM.spaceUsedWith_eq`, `WordRAM.wordSizeComputable_iff` | `rfl` / `Iff.rfl` |

## Brief for the auditor

1. **The argument.** It should be gate 162's ("How the interfaces give the frozen bounds",
   G162-23), as the brief `fill-ram-run.md` sets out:
   - the machine is `Turing.NDTM.phaseHostND` over the start-up and the phases indexed by
     (position, parity); a nondeterministic phase is embedded as `runEmbedND`, whose transition
     under `b` is that of `embedEmitTM` applied to the phase's `fixChoice b`;
   - one fuel induction (`RunSetup.run_execution`) shared by the deterministic and the
     nondeterministic targets, through two drivers (`RunDriver.ofSchedule`, `.ofCoins`);
   - coin phases take the entry's choice explicitly (G162-21); other slices transfer through
     `runWith_eq_fixChoice_runFrom`;
   - the bounds: `time_total_le`, `space_total_le`, with the constant
     `C0 + 3·C1 + (8 + extraTapes)·(6·C1 + 1) + 3`.
2. **The targets** are the frozen statements, byte-identical (`SOURCE.json`). In
   `exists_ndSimulation`, check both directions of acceptance and that every branch of length `T`
   halts. In `exists_simulation`, check that `M = N.fixChoice false` and the all-`false` stream.
3. **Admissions:** both targets and the nine `Classes` corollaries reach exactly
   `WordRAM.Sim.exists_startup`, `exists_phase`, `exists_verdictPhase` (the fill's walk,
   `REPORT-run.md`; the metadata check, which allows only these three). Nothing in
   `Build/RecordTable` is reached.
4. **The public surface:** 247 public constants in `WordRAM.Sim` (listed in `REPORT-run.md`). D1
   allows public homes there; flag any that duplicate an existing library result or belong in a
   library home instead.
5. **Readers:** the four readers restate their definitions exactly, beside them.
6. **Rule 10 and duplication:** the seals and the copy screen, below. In particular,
   `RunSetup.host_ordinary` and `RunSetup.host_verdict` share a prelude of about 20 lines (the
   entry renaming, `phase_correct`, the word bookkeeping) before they diverge into dispatch and
   halt (`pair-notes.json`, class `shared-prelude`). Say whether it should be factored before
   the merge.

## Evidence (`evidence/`)

- **`REPLAY.json`:** the merged-tree replay on `oleans-cl166-cl165`, the branch's build after
  #379. 286 modules: 286 passed, 0 failed. They include every downstream user of `Build/Embed`,
  `NondeterministicSpace` and `WordSize`. There are 29 admissions in the replayed sources: the
  two targets' inherited interfaces and tier 2's open statements, none in this PR's files.
- **Seals:** run 3 passes, 108 proofs and 76 heads. The metadata check allows exactly the three
  Sim interfaces (`gate.json`'s `inherited_admissions`). Runs 1 and 2 are in the data carrier.
  Run 1 was on the pre-#379 head; run 2 found no seal failure, only the copy-screen
  reconstructions that run 3's head repairs.
- **Controls:** 79 definitions and 158 identities in two parts, native-PASS and sealed-FAIL.
- **Sweeps:** the proof-syntax sweep finds 0 read candidates in 108 roots. Citation homes are in
  `CITATION-HOMES.json`.
- **Copy screen:** 26 → 41 pairs, 15 new and 0 gone, all classified (`PAIR-DISPOSITIONS.json`).
  They are sibling lemmas, parallel equations and shared citation shapes within the new modules.
  One `shared-prelude` pair (`host_ordinary`/`host_verdict`) is raised in brief item 6.
- **The fill's report** (`REPORT-run.md`): axiom prints, the admission walk, the public
  declarations by module, and the foreign definitions with the readers each proof uses.

Use the campaign finding table and give a CLEAR or HOLD verdict.
**Deliver your findings as a downloadable file named `gate168-ram-run-findings.md`**
(the findings table and the verdict line, no other wrapping), and also paste its content in your
reply.
