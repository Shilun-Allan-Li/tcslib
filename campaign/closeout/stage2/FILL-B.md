# Stage 2, Fill B: one-step windows and seam space (WS-1, F6-1(b))

Read `COMMON.md` first.

**Files you may change:**
- `TCSlib/Complexity/TuringMachine/CfgFacts.lean` (the new lemma only)
- `TCSlib/Complexity/TuringMachine/Oracle.lean`
- `TCSlib/Complexity/TuringMachine/Build/CfgRecord.lean`
- `TCSlib/Complexity/TuringMachine/Sweep.lean`
- `TCSlib/Complexity/TuringMachine/Robustness/SingleTape.lean`
- `TCSlib/Complexity/TuringMachine/Build/Loop.lean`
- `TCSlib/Complexity/ClassPSPACE/TQBF.lean`
- `TCSlib/Complexity/SpaceComplexity/ExpBFS/Radius.lean`
- `TCSlib/Complexity/SpaceComplexity/Codec/Step.lean`
- `TCSlib/Complexity/TuringMachine/Build/Seam.lean` (the new lemma only)
- `TCSlib/Complexity/SpaceComplexity/Constructible.lean`

ExpBFS and Codec are Hydroxyi's files: keep those edits to minimal citations.

## B1. WS-1: one step keeps a configuration in a window

Ledger: "WS-1, one step keeps a configuration in a window, scoped by kind". The new lemma below
was approved by Seyoon on 2026-11-16.

1. **Publish the tape half** in `TuringMachine/CfgFacts`: applying an action changes a work cell
   only under that tape's old head. In symbols, `z ≠ c.workTapePos i →
   (a.apply c).workTapes i z = c.workTapes i z`.
   - The harvest source is Oracle's private `apply_workTapes_eq_of_ne`, at line 304 of base.
   - Its proof unfolds `Action.apply`. Reprove it through Configuration's published
     `Action.apply_*` field equations.
   - Name it in the file's style, for example `Turing.Action.apply_workTapes_of_ne`.
   - Oracle's private copy is then deleted and its uses cite the public lemma. Oracle already
     imports CfgFacts.
2. **Re-prove or re-point the members** from `Turing.Cfg.InWindow.apply_iff`,
   `Cfg.InWindow.mono` (Build/CfgRecord) and the tape half. A member over another window shape
   keeps its statement and cites the canonical lemmas for its step. The members:
   - ExpBFS/Radius's `inWin_mono` and `inWin_stepWith`;
   - the window half of Codec/Step's `boundary_iff`;
   - TQBF's private `codec_step_blank`;
   - Sweep's `FinTM.source_bounds` (one-step case);
   - Oracle's `OracleTM.step_radius`;
   - SingleTape's private `dgWindow_step`;
   - Build/Loop's private `emCall_track_support` and `emCall_track_extent`.

   ExhaustiveReplay's member is Fill A's.
3. Measured: 11 members, 311 lines, 14 uses, about 19 rule-10 repairs. Several of these proofs
   unfold `Action.apply` today, so expect repairs there.

## B2. F6-1(b): a general seam space lemma (approved by Seyoon, 2026-11-16)

Backlog: `campaign/backlog.md` §F6-1, item (b). Read the correction recorded there at the B3a gate.

- Constructible's private `b3a_seam_space` is used at a genuine halt. The public additive lemmas
  `seamCompTM_spaceUsedByTape_le_add` and `seamCompTM_spaceUsed_le_add` need a live
  `Cfg.ofWords` endpoint, so citing them is not a valid retirement.
- **Publish** in `Build/Seam` a general-configuration additive space bound for `seamCompTM`,
  from the public trajectory theorem `seamCompTM_visitedByTapeHead_ofCfg`.
- If it is clean, derive the two canonical corollaries from it (their statements unchanged).
- Then replace `b3a_seam_space`.
- Also define Constructible's `b3a_cfg` through `Cfg.ofWords` if the shapes agree; otherwise
  leave it.
- Measured exposure: 1 member and 6 uses.
