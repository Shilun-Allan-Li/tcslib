# RAM fill (Codex), tier 2 job D, round 3: repair the phases' duplication (gate 170)

Read `COMMON.md` (bundled), its tier 2 addendum included; its rules bind. **Fill name:**
`fill-ram-phases-r3`. **Base:** the commit given in the dispatch prompt. It is PR #386's branch
`ram/fill-phases`: your round-2 delivery, landed unchanged, with the RAM branch merged in.

## What this is

Gate 170's audit (`gates/170-ram-phases/findings.md`, bundled) found your round-2 proofs sound
(G170-05, -06, -07). It held them on two majors, both about duplicated proof text. Seyoon ruled
(2026-11-18) that you repair both in this round rather than record them as debt.

1. **G170-01: re-derived segment algebra.**
   - `phase_reaches_trans` (`Sim/PhaseHost.lean`) repeats the argument of the published
     `Turing.Segment.trans` (`Build/Contract/Basic.lean`): `runFrom_add` and the two prefix
     splits.
   - `phase_reaches_zero` (`Sim/PhaseControl.lean`) repeats `Turing.Segment.zero`.
   - **Repair:** convert the `ReachesWithin` witnesses through `Turing.segment_iff`. Put both head
     predicates within the summed radius about the original heads, cite `Segment.trans` and
     `Segment.zero`, and recover `ReachesWithin` through `Turing.reachesWithin_iff`. Keep a thin
     public wrapper only if its callers need the `ReachesWithin` form; its proof must then be the
     citation, not the argument.
2. **G170-02: the one-exit and two-exit structures.**
   - `PhaseBlock` (`Sim/PhaseBlock.lean`, one exit) and `PhaseBranch` (`Sim/PhaseTests.lean`, two
     exits) duplicate their composition (`PhaseBlock.seq`, `PhaseBranch.seq`).
   - They also duplicate their fresh-entry packaging (`phase_machine_ofBlock`,
     `phase_machine_ofBranch`): the seam construction, run composition, constant absorption and
     the zero-time prefix.
   - **Repair:** one certificate over a finite exit family. For example, a structure with an exit
     type `E` (`[Fintype E] [DecidableEq E]`), an injective exit map, and a selected exit per input
     and data. Give one `seq` (a one-exit block followed by any certificate) and one packaging
     proof, with the one-exit (`E = Unit`) and two-exit (`E = Bool`) cases as specializations.
     Callers move to the unified form, or to thin specializations proved by citation.
   - If a full unification is impossible, share at least the composition and the fresh-entry
     packaging proofs, and say in `REPORT.md` exactly what remains duplicated and why.

## Rules for this round

- **Statements:** `WordRAM.Sim.exists_phase` and `WordRAM.Sim.exists_verdictPhase` stay
  byte-identical, and so does every statement outside your owned files.
- **Owned files:** `TCSlib/Complexity/RAMSimulation/Sim/Phase*.lean` and `Sim/Phases.lean` (proof
  bodies only for the two targets). You may add, merge or remove `Sim/Phase*` files. Keep the
  `RAMSimulation` facade's imports and contents in step, and keep every file under 600 lines.
  Public declarations stay in the internal namespace `WordRAM.Sim` (decision D1).
- **Admissions:** none allowed. Since round 2, the twelve row statements your proof cited are all
  proved on the RAM branch (PRs #385, #388, #389), so both targets must reach **no** admission.
  Give the full type-and-value walk for both targets in `REPORT.md`.
- **Readers:** your round-2 reader `Turing.Cfg.select_eq` is already on the branch (from #388),
  identical in statement. The base keeps one copy; do not add it again.
- **Copy screen:** run `scripts/copy-text-screen-v3.py` over your owned files together with
  `Build/Contract/Basic.lean`, `Build/Contract/Seam.lean`, `Build/Seam.lean` and
  `Build/NDHost.lean`. Report every pair at or above half, with the reason it remains.

## REPORT.md, in addition to COMMON's checklist

- **The refactor:**
  - the unified certificate and its specializations;
  - the declarations removed, merged or renamed, and where each caller moved;
  - the line counts per file, before and after.
- **G170-01:** the citations of `Segment.trans` and `Segment.zero`, and what remains of the
  wrappers.
- **The walk:** the admission walk for both targets (empty), and the axiom prints.
- **The copy screen** over the population above.

## Downstream check

`Sim/Phases`, the `RAMSimulation` facade, and `Simulation` and `Classes` (they import the phases
through the facade's closure).
