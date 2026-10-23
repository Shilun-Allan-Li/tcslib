# External audit pack — B5a, the canonizer's continuation 7: the grammar stage (PR #152, a fill gate)

Campaign: the Arora-Barak chapters 3-4 plan, B5a (the polynomial-time canonizer for machine
codes, behind the code schemes of §13 and the relativization results). The fill brief
(`campaign/fills/b5a/briefs/b5a-fill-canon-cont7.md`) targets the frozen stub
`exists_canonGrammarStage` (`TCSlib/Complexity/TuringMachine/CodeSimulator.lean`). With it,
`Turing.MachineFormat.exists_polyCanonizer` becomes admission-free. It was delivered complete as
item 3 of megafill A on 2026-10-22 (`fill-b5a-canon-cont7.zip`, SHA-256
`7fd5aa40bcb49252a2d2f81e1fbf94e26bcc75b86a1bf9eba2d3ad54232c9e2c`). The worker's report is
`campaign/fills/b5a/reports/canon-cont7-REPORT.md`, with the session report
`campaign/fills/megafill/reports/megafill-a-REPORT.md`. The maintainer's review is
`campaign/fills/b5a/reviews/canon-cont7/REVIEW.md` ("complete; land in full").

**The head:** `lean/b5a-canon-cont7` at `8e74681a`, on the campaign branch at `86523ba5`. This
bundle's records are from a later records commit (stated in the bundle's README). The commits are
in `evidence/commits/`:
- the delivery's 8 commits, cherry-picked with their authorship and subjects (the user's ruling).
  They touch only the owned file, and the head of the eight is the delivered blob `3acc87c1`;
- `225bf442`, the maintainer's (F2): `simp [Bool.toNat]` (twice) unfolded the core definition and
  created the module's only new public constant; now `simp only [Bool.toNat_true,
  Bool.toNat_false]`;
- `8f539eef`, docstrings only (F4, F8): the status text for the proved stage; the headline's
  sketch appendices folded into one `Implementation.` paragraph; the stub; the checkpoint labels
  and one stale sentence in new private docstrings;
- `57a4b90f`, docstrings only (F4): proof sketches for the 13 long private proofs;
- `8e74681a`, docstrings only (F8): `Codes2Tape` and `EXPCOM` no longer say both shared contracts
  remain admitted.

⟨RULING: #152's private `canonGramMapComp` has the statement of #153's public
`Cfg.mapState_mapState`, written with `fun s => g (f s)`. The user's ruling on its disposition
goes here. If it is a re-point at landing, it is the prepared commit `e4c5d015` (local, on #152's
head with #153 merged in): `campaign/fills/b5a/evidence/b5a-canon-cont7-mapcomp-repoint/`⟩

## What changed (verify)

| Class | Declarations |
|---|---|
| **Stub proved** | `exists_canonGrammarStage`; with it, `Turing.MachineFormat.exists_polyCanonizer` on `[propext, Classical.choice, Quot.sound]` (`evidence/elab-CodeSimulator-head-axioms.out`) |
| **Privates added** | 37 (149 → 186), none removed (`evidence/freeze-base-to-head.txt`) |
| **Frozen** | every public statement; 12 → 12 public declarations. `exists_polyCanonizer`'s flagged change is docstring-only: its code is identical with comments stripped (`evidence/polyCanonizer-code-identity.txt`) |
| **Code after the delivery** | exactly the `Bool.toNat` fix (`evidence/code-diff-delivered-to-head.txt`) |
| **Other files** | `Codes2Tape`, `EXPCOM`: docstrings only (`evidence/other-files-docstring-only.txt`) |

## Brief for the auditor

1. **Faithfulness.** Does the proof establish the frozen stub's statement, for every machine
   format and every input, with its polynomial bound? Check the boundaries of the record round,
   the inner and outer blocks and the stage's seven legs: an empty table, a one-record table, and
   the empty word.
2. **The accepted route (the review's F1 and F5, the user's rulings).** The two loops are built
   directly from the round's orbit and the public done/escape contracts. The prescribed generic
   link `canonCounterRepeat` gives neither the per-round chain nor a silence clause; it is now
   dead code, to be retired in the dedup window. There is one further private machine, the
   never-executed parking phase `canonStageHaltTM`. Are both sound and within the brief?
3. **Rule 10.** The review's 36-definition seal and its 74 controls (sealed, every control fails
   and the body is clean; unsealed, all close). No TCSlib definition is passed to `rw`/`simp`,
   and there is no `unfold`. The one core unfolding (`Bool.toNat`, F2) is fixed. Does any step
   still close only because another file's definition reduces?
4. **Admission.** The headline is admission-free. Targets 3–8 and `baker_gill_solovay` reach
   `sorryAx` only through `exists_uniformSimulator`.
5. **Duplication (the review's F3, recorded as acknowledged debt CC7-1, the user's ruling).** The
   v3 screen: 2,419 → 2,455 declarations, 2,633 → 2,692 pairs; 59 new, all in-file. Four are
   ≥ 90%: the two cut legs at 97% each way, and `canonStageLeg4`/`Leg5` → `Leg1` at 94% and 91%.
   Is "acknowledged debt" adequate? Separately, `canonGramMapComp` (the ruling above).
6. **The text.** The status paragraph, the `Implementation.` paragraph, the 13 sketches, and the
   `Codes2Tape`/`EXPCOM` sentences: accurate and public-facing?
7. **Records.** The review's F6 (REPORT inaccuracies) and F7 (environment logs): any correctness
   gap?

## Repository-side attestations (verify or challenge)

- **Elaboration:** the review: 0 errors and the uniform simulator's sorry warning only, at the
  base (`oleans-lg4c2`) and at the tip (`oleans-lu2sc1`). The maintainer, at `8e74681a` against
  `oleans-lu2sc1`: the same, with the headline on the standard three.
- **Probes** (the review): 253 checks, cont3's 118, `B5aContPreShip`, note 50: 0 errors.
- **Lint** (`8e74681a`): `TuringMachine` 0 FAIL, 66 WARN over 82 files; `Diagonalization` 0 FAIL,
  1 WARN over 5 files (`evidence/lint-*.txt`).
- **The census** (the worker): 37 sorry warnings by name, the base's 38 minus the stub.
- **Replay:** the closure (10 modules, `evidence/down-codesimulator.txt`) overlaps #149's, so this
  PR merges after #149 and replays from the latest merged-tree snapshot. **Pending:** by the user's
  ruling (2026-10-23) this gate is dispatched before the replay, which is recorded when it passes.
  The PR is clear to merge only when both have passed. The branch merges cleanly with #149's head
  (`git merge-tree`).

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Severity guide as in `campaign/standards/TEMPLATE.md`. Findings go verbatim into
`campaign/gates/67-b5a-canon-cont7-fill/findings.md`. The gate closes when it has zero blockers and
zero majors.

**Deliver your findings as a downloadable Markdown file named `b5a-canon-cont7-fill-findings.md`**
(the findings table and the verdict line, no other wrapping), and also paste its content in your
reply.
