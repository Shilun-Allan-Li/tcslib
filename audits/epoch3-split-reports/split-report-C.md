# Split report — Robustness/Oblivious.lean (batch C, epoch-3→4 merge)

Mechanical linear split of `TCSlib/Complexity/TuringMachine/Robustness/Oblivious.lean`
(4086 lines) into four sequential modules plus the residual. All moves are verbatim;
the only source changes inside moved declarations are (a) the deletion of `private `
on the 77 declarations that a later module in the chain references (complete list
below) and (b) one forced one-line addition — a closing `rfl` in
`dataCfg_backward_step` — required by Lean's module-local matcher minting (see
Deviations). No declaration was renamed, no signature was touched, and no file
outside the five listed below was modified.

## Actual layer boundaries

The three layers named in the batch-C report (masked clock/schedule, decoration,
transverse coding) are **interleaved** in the original file: the generic
transformation layers (`maskedClock*` at 86–186, `decorateTM*` at 188–313,
`parallelTM*` at 315–487) all precede the concrete schedule machine, while the
schedule's own clock-stage (`clockStage*`, 1321–1490) and zipper-frontier
identities (`clockTape_zipper*`, 2134–2182) sit far downstream, and the candidate
assembly (`obliviousCandidate`, 781) comes *early*, not at the end. A linear
(contiguous, order-preserving) split therefore cannot reproduce the sketched
one-module-per-layer layout. The seams actually chosen are the five clean
declaration-group boundaries below; each module imports its predecessor, so
elaboration order is exactly the original's.

| Original lines | Content | Destination |
|---|---|---|
| 1–16 | copyright header, imports, `set_option`s | redistributed (see imports below); copyright block + `set_option`s replicated in every module |
| 18–64 | module docstring | split between `ObliviousSchedule.lean` and the residual (see docstring edits) |
| 66–680 | `Turing.FinTM.Oblivious`; masked clock (`maskedCfg`…`maskedClock_computes`); decoration layer (`decorateTM`…`decorateTM_oblivious`); transverse coding layer (`parallelCode`…`parallelTM_computes`); schedule alphabet/phases (`OblSymbol`, `OblPhase`); the length-only schedule machine (`obliviousSchedule`, `_output`, `_oblivious`) | `ObliviousSchedule.lean` |
| 682–1753 | payload alphabet and candidate assembly (`OblPayload`…`obliviousCandidate_oblivious`, idle lemmas); budget counter (`budgetValue`…`budgetBorrow_value`); one-lane transduction (`laneCfg`…`lane_run`); borrow sweeps (`budgetVisit`…`obliviousSchedule_borrow_run`); source payload correspondence (`inputPayload`…`sourceAnswer_at_budget`); captured clock stage (`clockTape`…`clockStageCfg_captures`); guide tape + macrostep cycle (`guideTape`…`macroCfg_finish`) | `ObliviousCandidate.lean` |
| 1755–2811 | setup-phase analysis: `setupCfg`/`setupWrite`, reset, copy, budget conversion + borrow rounds, unary rewind, guide layout in both directions, assembly into `setupCfg_initializes` (includes the `sweepTape_shift`/`clockTape_zipper` identities at 2134–2182) | `ObliviousSetup.lean` |
| 2813–2987 | cost ledger `obliviousLedger_bound`; halting bounds `obliviousSchedule_halts`, `obliviousCandidate_halts`; decorated-configuration bridge `decoratedCfg`, `_init`, `_step` | `ObliviousLedger.lean` |
| 2989–4086 | data machine `dataTM`/`dataCfg` and its full correctness development (sweeps, simulation, preparation invariant, `dataTM_computes`, `obliviousCandidate_decides`) and `theorem oblivious_of_mem_DTIME` | `Oblivious.lean` (residual) |

Bodies were verified byte-identical against the original ranges by an automated
line-by-line diff: the only differing lines are exactly the 77 `private ` deletions,
plus the single `rfl` line later added to `dataCfg_backward_step` in the residual
(see Deviations).

## Final line counts

| File | Lines |
|---|---|
| `TCSlib/Complexity/TuringMachine/Robustness/ObliviousSchedule.lean` | 688 |
| `TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean` | 1127 |
| `TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean` | 1102 |
| `TCSlib/Complexity/TuringMachine/Robustness/ObliviousLedger.lean` | 219 |
| `TCSlib/Complexity/TuringMachine/Robustness/Oblivious.lean` (residual) | 1147 |

All files are ≤ ~1200 lines. `ObliviousLedger.lean` is small but semantically
crisp (the quadratic ledger + halting bounds + the decorated-configuration
bridge); folding it into a neighbor would have pushed that neighbor past 1200.

## Public-API relocation: `Turing.FinTM.Oblivious`

**`def Turing.FinTM.Oblivious` moved from `Robustness/Oblivious.lean` to
`Robustness/ObliviousSchedule.lean`** (the first module of the chain), verbatim,
with its docstring, inside a replicated `namespace Turing.FinTM … end
Turing.FinTM` block. Its fully qualified name is unchanged; every downstream
import of `Robustness/Oblivious.lean` still sees it transitively through the
chain. It sits in the first module because the middle layers
(`maskedClock_oblivious`, `decorateTM_oblivious`, `parallelTM_oblivious`,
`obliviousSchedule_oblivious`) all state results about it.

## private → public flips (all 77, mandatory)

Each entry: name — earliest later module that references it (all referencing
modules listed). "Candidate/Setup/Ledger/Residual" = `ObliviousCandidate.lean` /
`ObliviousSetup.lean` / `ObliviousLedger.lean` / residual `Oblivious.lean`.
A declaration referenced only inside its own new module kept `private`
(161 of 238 private declarations remain private).

From `ObliviousSchedule.lean` (18):

1. `maskedClock` — Candidate
2. `maskedClock_computes` — Candidate
3. `decorateTM` — Candidate, Ledger, Residual
4. `decorateTM_run` — Ledger
5. `decorateTM_oblivious` — Candidate
6. `parallelTM` — Candidate
7. `parallelTM_run` — Ledger
8. `parallelTM_oblivious` — Candidate
9. `parallelTM_computes` — Residual
10. `OblSymbol` — Candidate, Setup, Residual
11. `oblEmbed` — Candidate, Ledger, Residual
12. `clockBit` — Candidate, Residual
13. `OblPhase` — Candidate, Setup, Residual
14. `oblAction` — Candidate, Setup, Residual
15. `nextThird` — Setup
16. `obliviousSchedule` — Candidate, Setup, Ledger, Residual
17. `obliviousSchedule_output` — Candidate, Ledger
18. `obliviousSchedule_oblivious` — Candidate

From `ObliviousCandidate.lean` (47):

19. `OblPayload` — Residual
20. `blankPayload` — Residual
21. `dataCell` — Residual
22. `OblData` — Residual
23. `obliviousSourceAction` — Residual
24. `obliviousSourceMove` — Residual
25. `obliviousDataInit` — Ledger, Residual
26. `obliviousVisit` — Ledger, Residual
27. `obliviousCandidate` — Ledger, Residual
28. `obliviousCandidate_oblivious` — Residual
29. `budgetValue` — Setup, Ledger, Residual
30. `budgetValue_bits` — Ledger, Residual
31. `budgetBorrow` — Setup
32. `budgetBorrow_length` — Setup
33. `budgetBorrow_underflow` — Setup
34. `budgetBorrow_value` — Setup
35. `laneCfg` — Setup
36. `obliviousSchedule_borrow_run` — Setup
37. `inputPayload` — Residual
38. `sourcePayload` — Residual
39. `sourceTotalAction` — Residual
40. `obliviousSourceAction_correct` — Residual
41. `sourceTotalAction_apply` — Residual
42. `obliviousSourceMove_correct` — Residual
43. `sourceWrittenPayload` — Residual
44. `sourcePayload_apply` — Residual
45. `inputPayload_outside` — Residual
46. `sourcePayload_support` — Residual
47. `lastOutput_append` — Residual
48. `sourceAnswer_at_budget` — Residual
49. `clockTape` — Setup, Ledger
50. `clockStageCfg` — Setup, Ledger, Residual
51. `finThree_cases` — Setup, Residual
52. `clockStageCfg_captures` — Ledger, Residual
53. `guideTape` — Setup, Residual
54. `guideTape_left` — Residual
55. `guideTape_right` — Residual
56. `guideTape_origin` — Setup, Residual
57. `macroCfg` — Setup, Residual
58. `macroCfg_unary` — Residual
59. `macroCfg_guide` — Residual
60. `macroCfg_check` — Residual
61. `macroCfg_seek` — Residual
62. `macroCfg_forward` — Residual
63. `macroCfg_backward` — Residual
64. `macroCfg_center` — Residual
65. `macroCfg_finish` — Setup

From `ObliviousSetup.lean` (8):

66. `setupCfg` — Residual
67. `setupWrite` — Ledger, Residual
68. `unaryTape` — Residual
69. `unaryTape_unit` — Residual
70. `unaryTape_end` — Residual
71. `clockStageCfg_setup` — Ledger, Residual
72. `setupCfg_finish` — Ledger
73. `setupCfg_initializes` — Ledger, Residual

From `ObliviousLedger.lean` (4):

74. `obliviousCandidate_halts` — Residual
75. `decoratedCfg` — Residual
76. `decoratedCfg_init` — Residual
77. `decoratedCfg_step` — Residual

The flip list was computed by exact-identifier search (identifier-boundary
regex) over the comment-stripped text of every later chunk, so no flip is
justified by a docstring/comment mention alone, and none was missed by
substring collision.

## Docstrings added

None. Every one of the 77 flipped declarations already carried a `/-- … -/`
docstring whose first sentence states the result (verified mechanically:
each flipped declaration line is immediately preceded by a docstring
terminator). No declaration docstring was reworded.

## Module-docstring edits (comment-only)

Original module docstring (lines 18–64) redistributed:

1. **Residual `Oblivious.lean`** keeps the original title + intro paragraph
   (orig 18–24), the theorem-relevant design bullet ("We state the quadratic
   version — Exercise 1.5's *first assertion* …", orig 46–49), the
   `## Main results` block (orig 55–58), and the `## References` block
   (orig 60–63), all verbatim, and **gains one sentence** after the intro:
   "The construction is developed in the layer modules `ObliviousSchedule.lean`
   (which now hosts `Turing.FinTM.Oblivious`), `ObliviousCandidate.lean`,
   `ObliviousSetup.lean`, and `ObliviousLedger.lean` in this directory, split
   out mechanically at the epoch-3→4 merge; this file proves the data machine's
   correctness invariant and the final theorem."
2. **Residual**: the `## Main definitions` block (orig 51–53, the
   `Turing.FinTM.Oblivious` bullet) was removed — the definition no longer
   lives in this file; the added sentence above points at its new home.
3. **`ObliviousSchedule.lean`** carries over the three definition-relevant
   design bullets (orig 28–45) verbatim under `## Design`, with two minimal
   accuracy fixes required by the relocation:
   - bullet 2: "as the decider produced below does" → "as the decider produced
     in `Robustness/Oblivious.lean` does" (the decider is no longer below);
   - bullet 3: "The `TimeConstructible` hypothesis below is required by the
     *construction*" → "The `TimeConstructible` hypothesis of the final theorem
     (in `Robustness/Oblivious.lean`) is required by the *construction*"
     (rewrapped to stay within line-length; no other wording changed).
4. The four new modules each carry the prescribed new header shape
   (copyright block, imports, the three `set_option`s, `/-! … -/` docstring
   with title, provenance prose "split out mechanically from
   `Robustness/Oblivious.lean` at the epoch-3→4 merge … epoch-3 fill, batch C",
   Main definitions/Main results bullets, and the [AB09] references block).

No other comment or docstring was altered anywhere.

## Final import lists

Lean imports are transitive along the chain; each module lists its predecessor
plus only what it newly needs.

| File | Imports |
|---|---|
| `ObliviousSchedule.lean` | `TCSlib.Complexity.TuringMachine.Simulation`, `Mathlib.Data.Fintype.Pi`, `Mathlib.Data.Fintype.EquivFin`, `Mathlib.Data.Nat.Bits`, `Mathlib.Tactic.DeriveFintype` |
| `ObliviousCandidate.lean` | `TCSlib.Complexity.TuringMachine.Robustness.ObliviousSchedule`, `TCSlib.Complexity.TuringMachine.Sweep`, `TCSlib.Complexity.ClassP.DTIME` |
| `ObliviousSetup.lean` | `TCSlib.Complexity.TuringMachine.Robustness.ObliviousCandidate` |
| `ObliviousLedger.lean` | `TCSlib.Complexity.TuringMachine.Robustness.ObliviousSetup` |
| `Oblivious.lean` (residual) | `TCSlib.Complexity.TuringMachine.Robustness.ObliviousLedger`, `TCSlib.Complexity.ClassP.TimeConstructible` |

Rationale: `Simulation` (which transitively provides `FinTM`, `Cfg`,
`MultiTapeTM`, `Action`) plus the three Fintype/DeriveFintype modules are what
the `Oblivious` definition, the generic layers, and the two `deriving
DecidableEq, Fintype` clauses need; `Sweep` (`FinTM.sweepTape/sweepFold/…`) and
DTIME (`Language`, `DecidesInTime`) are first used in `ObliviousCandidate.lean`;
`TimeConstructible` is only named in the final theorem. **One import is not
literally in the original list**: `Mathlib.Data.Nat.Bits` in
`ObliviousSchedule.lean`. `maskedClock_computes` (moved verbatim) states
`(T x.length).bits`, and `Nat.bits` is defined only in `Mathlib.Data.Nat.Bits`;
the original file obtained it transitively via
`TCSlib.Complexity.ClassP.TimeConstructible`, which now only the residual
imports. Importing `Mathlib.Data.Nat.Bits` directly is the precise choice under
the repo's "imports are precise" policy. The two Mathlib imports the original
carried for `deriving`/coding purposes stay in the first module; every other
original import appears exactly once in the chain.

## Verification

Each module checked in dependency order with
`TCSLIB_OLEANS=<scratchpad>/oleans-splitC bash scripts/lean_check_tree.sh <module>`
(the pre-seeded olean tree at the current commit; no `lake` invocation
anywhere). Pass criteria: lean exit 0, no `error:` lines, fresh `.olean`
produced. No `declaration uses 'sorry'` warnings appeared anywhere in the chain
(none expected).

All five checks pass. Summary and log tails (full logs preserved beside this
report as `check-candidate.log`, `check-ObliviousSetup.log`,
`check-ObliviousLedger.log`, `check-Oblivious.log`):

1. **ObliviousSchedule** — pass (script exit 0). The `lean` invocation produced
   *no output at all* (zero warnings, zero errors); a fresh
   `ObliviousSchedule.olean` (3,632,304 bytes) was produced. There is no log
   tail to quote because the log was empty.
2. **ObliviousCandidate** — pass, `SCRIPT_EXIT=0`, 0 `error:` lines, fresh
   olean. 15 pre-existing linter-warning blocks (`unnecessarySimpa`,
   `unusedSimpArgs`, `unreachableTactic`, `unusedTactic`,
   `unnecessarySeqFocus`) carried over verbatim from the monolith. Tail:
   ```
   TCSlib/.../ObliviousCandidate.lean:881:25: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice
   Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
   SCRIPT_EXIT=0
   ```
3. **ObliviousSetup** — pass, `SCRIPT_EXIT=0`, 0 `error:` lines, fresh olean,
   23 pre-existing `unusedSimpArgs`-style warning blocks. Tail:
   ```
   Hint: Omit it from the simp argument list.
     simp only [Fin.val_mk, Nat.cast_add, Nat.cast_one]   (strike-through hint)
   Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
   SCRIPT_EXIT=0
   ```
4. **ObliviousLedger** — pass, `SCRIPT_EXIT=0`; the log contains nothing but
   `SCRIPT_EXIT=0` (zero warnings, zero errors), fresh olean.
5. **Oblivious (residual)** — first run FAILED with exactly one error
   (`dataCfg_backward_step`, "unsolved goals" on a syntactically reflexive
   goal); after the one-line `rfl` fix described under Deviations, the re-run
   passes: `SCRIPT_EXIT=0`, 0 `error:` lines, fresh olean, 12 pre-existing
   linter-warning blocks. Tail:
   ```
     simp only [obliviousSchedule, obliviousVisit, hi, setupWrite, Option.toList_none, List.append_nil]
   Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
   SCRIPT_EXIT=0
   ```

`grep -c sorry` over all four logs: 0 — no `declaration uses 'sorry'` warning
anywhere in the chain, as expected. No module outside the chain was checked.
Final olean tree (all five fresh, timestamps 21:09–21:15):
`ObliviousSchedule.olean`, `ObliviousCandidate.olean`, `ObliviousSetup.olean`,
`ObliviousLedger.olean`, `Oblivious.olean`.

## Deviations

- The one-module-per-layer sketch in the task could not be realized by a linear
  split because the layers are interleaved in the original (see "Actual layer
  boundaries"); boundaries were chosen at the five clean contiguous seams
  instead, as the task allows.
- `Mathlib.Data.Nat.Bits` added to `ObliviousSchedule.lean` (see import
  rationale above); it replaces transitive provision through
  `TimeConstructible` and adds no new mathematics.
- Two single-phrase accuracy fixes inside carried-over docstring bullets
  (listed under module-docstring edits) — comment-only, forced by the
  relocation making "below" point at nothing.
- **One forced one-line proof edit** (the only edit to any proof body):
  `dataCfg_backward_step` in the residual gained a final `rfl` line after its
  closing `simp only [...]`. Cause: its *statement* contains a literal
  `match obliviousSourceMove M q read i with …` that, in the monolith, reused
  the very same auxiliary matcher constant that Lean minted for
  `obliviousVisit`'s body, so the closing `simp only [obliviousVisit, …]` left
  a syntactically reflexive goal. Lean's matcher reuse is module-local: with
  `obliviousVisit` now in `ObliviousCandidate.lean`, the residual mints a fresh
  `dataCfg_backward_step.match_1`, and after the simp the goal is
  `… obliviousVisit.match_1 … = … dataCfg_backward_step.match_1 …` — the two
  matchers are definitionally but not syntactically equal, which `simp only`
  cannot close (verified by re-eliciting the goal with `pp.match false`). No
  linear seam avoids this: `obliviousVisit` (orig line 730, needed by
  `obliviousCandidate` at 781 and by `ObliviousLedger.lean`) and
  `dataCfg_backward_step` (orig line 3053) cannot share a module without a
  2300-line file. The added `rfl` closes the matcher-identity goal by
  definitional unfolding; the statement, docstring, and every other proof line
  are untouched and byte-identical to the original.
- Unrelated working-tree state: `git status` shows
  `TCSlib/Complexity/TuringMachine/Encoding.lean` and
  `TCSlib/Complexity/TuringMachine/Universal.lean` modified by a concurrent
  session (they were clean in this session's opening snapshot). This split did
  not touch them and they are outside this chain.

No other deviations: no other file touched, no git state-changing command run,
no `lake` command run.
