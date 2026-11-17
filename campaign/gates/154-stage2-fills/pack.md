# Gate 154 · Closeout stage 2: fills A, B and C (PR #350)

**Not yet clear to merge** · PR #350 is a draft. Seyoon dispatches and merges.

- Lean head: `f2d1ead707d9ba12779dd0b377daba708bac8915` (branch `closeout/stage2`).
- Base: campaign Lean `5c153802` (the #349 merge). The branch is based on stage 1's head
  `a1a7c6ec`, which #349 merged; its Lean equals the merge's. Records: see the dispatch prompt.
- This is the first audit.

## Scope

Stage 2 of `campaign/closeout/STAGES.md`: three delegated fills, each in its own merge commit, then
the maintainer's integration commits. The briefs are `campaign/closeout/stage2/COMMON.md` and
`FILL-A.md`/`FILL-B.md`/`FILL-C.md`. The intake notes are in `campaign/closeout/STAGE2-BRIEFS.md`,
and Fill B's report is `campaign/closeout/stage2/stage2-fill-B-report.md`. Fills A and C sent no
report. All files are bundled, including the citation homes (G153-01).

**New public declarations (all approved by Seyoon):**

1. **`Turing.NDTM.exists_first_halt`** (`TuringMachine/Nondeterministic`, A2; Fill A). A halted
   branch halts first at a least prefix `u ≤ |w|` of its choice word. It is live along every
   shorter prefix, and its run along `w` is its run along `w.take u`. NDNormalForm's `nf_forward`
   and ExhaustiveReplay's `xr_replay_host` cite it in place of their inline `Nat.find` blocks.
2. **`Turing.Action.apply_workTapes_of_ne`** (`TuringMachine/CfgFacts`, B1; Fill B). An action
   leaves every work cell other than the one under that tape's head unchanged. It is harvested from
   Oracle's private `apply_workTapes_eq_of_ne`, which is deleted.
3. **`Turing.seamCompTM_spaceUsed_le_add_ofCfg`** (`Build/Seam`, B2; Fill B). The additive space
   bound for a seam from any configuration, with phase two's endpoint unconstrained. The canonical
   `seamCompTM_spaceUsed_le_add` is now derived from it. `seamCompTM_visitedByTapeHead_ofCfg` moved
   up, unchanged.
4. **`Turing.Cfg.inWindow_iff`** (`Build/CfgRecord`, approved 2026-11-17; maintainer). The window
   predicate as an equation (`Iff.rfl`).

**Changes without new API:**

- **IR-1, UniversalK half (Fill A).** The self-startup's input rewind runs on the public
  `Turing.inputRewindTM` (`inputRewindTM_run`, `2|α| + 4` steps instead of `2|α| + 5`). The
  private `ss_RewindState`, `ss_inputRewind`, `ss_inputRewind_done` and `ss_inputRewind_run` are
  deleted. The public `exists_selfStartupTMK` keeps its statement; its internal time `r` changes.
  Five composed renamings cite `Cfg.mapState_mapState`. ExhaustiveReplay's `xr_inRewindTM` is
  **carried** (Seyoon): the public run lemma needs input position ≥ 1, and the replay can rewind
  from 0.
- **WS-1 (Fill B; maintainer).** One-step window proofs cite the tape-half lemma or the window
  lemmas (`Cfg.InWindow.mono`, `apply_iff`, `apply_of_lt`):
  - ExpBFS/Radius `inWin_mono`/`inWin_stepWith`, Codec/Step `boundary_iff`, TQBF
    `codec_step_blank`, CfgRecord `InWindow.apply_iff` and Oracle `workTapes_step_eq_of_ne`.
  - Sweep `source_bounds`, SingleTape `dgWindow_step` and Build/Loop `emCall_track_*` read
    Configuration's equations; these files do not import CfgFacts.
  - The maintainer re-proved ExhaustiveReplay's `xr_window_stepWith` from the window lemmas
    (ExhaustiveReplay imports `Build/CfgRecord`). TQBF and Radius read windows through
    `inWindow_iff`. `boundary_iff` reads head flags through Codec/Word's `cellOf_head`.
- **F6-1(b) (Fill B; maintainer).** Constructible's private `b3a_seam_space` is a one-line
  citation of the new lemma. Its consumer `b3a_log_machine` stays at base: re-pointing it exposed
  older direct reads, including VirtualInput's `vhostCfg`, which has no published equations.
  Fill B's stops are recorded in its report: `b3a_cfg` via `Cfg.ofWords`, and the per-tape general
  twin.
- **RN-1 (Fill C).** CodeSimulator's renamed-configuration blocks cite `Cfg.mapState_eq_of_fields`
  (and `Cfg.mapState_const_eq_mapState_sigma` in `canonStageLeg_of`). These are
  `canonStageInnerSpec`, `canonStageOuterSpec`, `canonStageLeg_of`, `canonStageFrontSpec`,
  `canonReturnAdapter`, `exists_canonRecordRound` and `exists_canonGrammarStage`. `us_start` is
  unchanged.
- **MIG-7 (C2; Fill C).** UniversalStartup imports `Build/Embed`. `universalCaptureTM`'s capture
  phase is `embedSilentRetTM`, renamed into the wrapper's states (**its definition body changes**,
  the only entry in `definitions_changed`). The private `universalCapture_step`, `_run` and
  `_transfer` are deleted, and a private `universalCapture_embed` identifies the renamed
  embedding. `universalCaptureCfg` and `universalCapturedCfg` keep their bodies, and every public
  statement is unchanged. **UniversalStartup grows by 17 lines** (+104/−87); the backlog estimated
  about −130.

Statements: `SOURCE.json` has no `header_changed`. Net: **−177 Lean lines** (+341/−518) across 17
files. By file: UniversalK −138, CodeSimulator −46, Codec/Step −24, ExhaustiveReplay −13,
ExpBFS/Radius −13, Constructible −12, Oracle −10, NDNormalForm −8, Sweep −3, SingleTape −1, TQBF 0,
Build/Loop 0, CfgRecord +10, CfgFacts +14, UniversalStartup +17, Nondeterministic +25, Seam +25.

## Brief for the auditor

1. **Statements.** Confirm that every pre-existing public declaration keeps its statement
   byte-identical, `exists_selfStartupTMK` included, and that `seamCompTM_visitedByTapeHead_ofCfg`
   moved unchanged.
2. **New public declarations.** Check each one's statement, docstring, attribution and proof
   sketch against the four facts above.
3. **`universalCaptureTM`.** Check that the new body computes the same machine behavior that the
   unchanged public statements about it require, and that `universalCapture_embed` is the bridge
   the start lemma needs.
4. **Citations and deletions.** Check that each deleted private declaration stated the fact its
   replacement supplies, and that the rewind's new time is accounted for in
   `exists_selfStartupTMK`'s arithmetic.
5. **Rule 10.** The changed proofs: seals, controls and both sweeps (counts below).
6. **Copy screen** (population: the 17 changed files): `evidence/PAIR-DISPOSITIONS.json`.

## Evidence

- `evidence/REPLAY.json`: the merged-tree replay of the 17 owners' downstream closure on
  `oleans-c5c153` (the #349 merge's snapshot). 353 modules replayed: 353 passed, 0 failed, 28
  inherited admissions (pre-existing). There are 874 objects in and 874 out.
- **Seals:** all 33 changed or added proofs pass with every other-file definition they reach made
  irreducible (86 ordinary boundary heads).
- **Controls:** two disjoint parts, **86 sealed definitions and 172 paired identities** in all,
  each native-PASS and sealed-FAIL.
- **Proof-syntax sweep:** 33 roots, 1 read candidate. It is `unfold step` in
  `OracleTM.workTapes_step_eq_of_ne`, resolved to `MultiTapeTM.step`; it is Oracle's own
  `OracleTM.step` (same file). The sealed check passes.
- **Lean-backed sweep:** 529 identifiers. The one TCSlib definition flagged is
  `Turing.embedEmitTM` (Build/Embed). It occurs only as a machine argument, as in
  `seamReleaseTM_runFrom_pos (embedEmitTM ι₃ P) …`, in two of CodeSimulator's changed proofs
  (`canonStageFrontSpec`, `exists_canonGrammarStage`), on lines unchanged from base. It is not a
  rewrite rule. The other flags are outside TCSlib (`rfl`, `noConfusion`, `Nat.find`,
  `SignType.cast`, simprocs).
- **Citation homes** (`defsweep/CITATION-HOMES.json`), all bundled: Codec/Word, Build/Convention,
  Build/Embed, Build/InputRewind, Configuration, Deterministic, Simulation and StateRenaming. The
  scope pass's namespace errors (`LogProg`, `FinTM`) affect one scope block each in Codec/Step and
  UniversalStartup.
- **Lint:** 0 campaign FAIL and no new finding. Two style warnings are gone: `xr_window_stepWith`
  and `inWin_stepWith` now have proof sketches. Fill B reports one new unused-variable warning
  (`h₂` on the canonical `seamCompTM_spaceUsed_le_add`), as on its three siblings.
- **Copy screen:** 376 → 366 directed pairs, 12 new and 22 gone; 121,376 → 117,508 characters.
  - **Gone (22):** retired by WS-1, MIG-7, IR-1 (UniversalK), Fill A's renaming collapses, and
    RN-1.
  - **New: citation shapes (6).** Seam's four canonical corollaries share their one-line
    derivation from the general forms; CodeSimulator's two specs supply
    `mapState_eq_of_fields`'s field arguments as the sigma lemma's body does.
  - **New: shared preludes (3).** These are published-equation preludes in Build/Loop and Sweep.
  - **New: carried twin (1).** The new general total against the canonical per-tape bound.
  - **New: threshold crossing (1).** A pre-existing UniversalK similarity crossed 50% after Fill A
    shortened `ss_bufferSeek_run`.
  - **New: shape match (1).** `universalCapture_embed` mirrors `mapState_eq_of_fields`'s
    hypotheses. Citing it would need a CfgFacts import into UniversalStartup, which is not
    approved.
- `evidence/DATA-CARRIER.json` and its recovery map: decode each gzip+base64 blob, then check its
  SHA-256 and byte count.

Use the campaign finding table and give a CLEAR or HOLD verdict.
**Deliver your findings as a downloadable file named `gate154-stage2-fills-findings.md`**
(the findings table and the verdict line, no other wrapping), and also paste its content in your
reply.
