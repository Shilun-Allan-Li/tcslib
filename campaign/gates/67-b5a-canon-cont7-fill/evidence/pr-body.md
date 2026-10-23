B5a, the canonizer's continuation 7 (`TuringMachine/CodeSimulator.lean`): **the grammar stage
`exists_canonGrammarStage` is proved, and with it the polynomial canonizer
`Turing.MachineFormat.exists_polyCanonizer` is admission-free.** Only the uniform simulator
`MachineFormat.exists_uniformSimulator` remains admitted in the module. Delivered as item 3 of
megafill A (`fill-b5a-canon-cont7.zip`, SHA-256 `7fd5aa40…9e2c`), complete.

**Commits** (on the campaign branch at `86523ba5`):
- the delivery's 8 commits (`0b7c99d6..7e6829dc`, on the base `6cfee544`), cherry-picked from its
  verified bundle with their authorship and subjects (the user's ruling); they touch only the owned
  file, unchanged at the tip; the head is the delivered blob `3acc87c1`;
- `225bf442`, the maintainer's (the review's F2): `simp [Bool.toNat]` (twice) unfolded the core
  definition and created the module's only new public constant; now `simp only` with
  `Bool.toNat_true` and `Bool.toNat_false`;
- `8f539eef`, docstrings only: the status text for the proved stage (the module header; the
  headline's sketch appendices folded into one `Implementation.` paragraph; the stub; the
  checkpoint labels and one stale sentence in new private docstrings);
- `57a4b90f`, docstrings only: proof sketches for the 13 long private proofs (the record round,
  the inner and outer blocks, the block's consumption bound, the stage front and its seven legs,
  the ledger; the user's ruling);
- `8e74681a`, docstrings only: `Codes2Tape` and `EXPCOM` no longer say both shared contracts
  remain admitted (the user's ruling).

**Review** (sub-agent; `campaign/fills/b5a/reviews/canon-cont7/REVIEW.md`; "complete; land in full"):

| Check | Result |
|---|---|
| Integrity | 37/37 sums; the bundle's only prerequisite the base; 8 linear commits; patches = bundle = delivered file, commit by commit |
| Scope and freeze | two hunks (the home and the stub's `sorry`); 12 → 12 public declarations, 149 → 186 private; no statement change; imports unchanged |
| Elaboration | 0 errors at the base and at the tip; the only warning `exists_uniformSimulator`'s |
| Axioms | the 37 new privates, the stub, `exists_canonDecider` and the headline on the standard three; targets 3–8 and `baker_gill_solovay` reach `sorryAx` only through `exists_uniformSimulator` |
| Rule 10 | 36 definitions sealed, 74 `rfl` controls (fail sealed, close unsealed); the worker's seal and control reproduce |
| Probes | all of them, and a 253-check extended probe, 0 errors |
| v3 screen | 2,419 → 2,455 declarations, 2,633 → 2,692 pairs; 59 new, none cross-file; four in-file at 90% or more, recorded as acknowledged debt (CC7-1, the user's ruling) |
| Lint | the base's numbers, 0 FAIL |
| Sorry census | 37 by name, the base's 38 minus the stub |

**Rulings (user, 2026-10-22):** the two loops built directly from the round's orbit are accepted
(the prescribed `canonCounterRepeat` link could not give the per-round chain or silence; it is
retired in the dedup window); the parking machine is accepted.

The maintainer re-elaborated the landed module against `oleans-lu2sc1` (the only warning the
uniform simulator's sorry; `exists_polyCanonizer` and the decider on the standard three), checked
that each maintainer commit changes only what its message says (the three docstring commits
leave the code identical with comments stripped), and re-linted (`TuringMachine` 0 FAIL).

**Order.** After #149 (its closure contains this one's: 10 modules, `CodeSimulator` to the facade).
This closure meets #147's (`UniversalK`, `SelfUniversal`) and megafill A's other two landings
beyond the facade: whichever merges later replays.

**Replay:** after #149 merges. **Pending.**

**Gate:** a fill gate. **Pending.**

🤖 Generated with [Claude Code](https://claude.com/claude-code)

