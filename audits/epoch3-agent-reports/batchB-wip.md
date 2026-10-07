# Epoch 3, Batch B — INCOMPLETE

**The requested proof is not complete. Do not accept this archive as a passing batch.**
`Turing.universal` still contains one `sorry`, in the live-source table-lookup and
record-application block. Consequently the three requested public axiom prints all
still contain `sorryAx`. This archive preserves the checked partial construction,
its exact remaining obligation, and the verification evidence.

## Revision and ownership

- Repository: `https://github.com/Shilun-Allan-Li/tcslib`.
- Requested branch was cloned; the work branch is `fill/epoch3-B` at the exact base
  `71721842a2336d5562ef831a19b0e86e063dddaa`.
- Delivery commit: `f191b918220f673ffd2830ee66e8fee86689e0cb` (explicitly labeled WIP).
- Only tracked source change: `TCSlib/Complexity/TuringMachine/Universal.lean`.
- The original file header, imports, options, module docstring, public statements,
  and all original sketches are unchanged. `universal_quadratic` and
  `timed_universal`, including their docstrings and proof bodies, are byte-identical
  to the base. No other sorry was changed. No push or PR was made.
- No new axiom or admission was introduced in a helper. The original target's
  admission now occupies the one remaining concrete simulation obligation.
- `exists_effectiveMachineCode` is not cited by a proof. The construction uses
  only the supplied `c : EffectiveMachineCode` and its canonizer contract.

The patch is the output of `git format-patch 71721842 --stdout`. The bundle contains
this work branch's commit with the stated base as its prerequisite. The source
copy is the complete modified file, not an excerpt. `verification/freeze.log`
records the statement and ownership checks; `verification/package-check.log`
records patch/bundle consistency checks.

## Completed construction and its limits

### Prefix-only startup and canonical table

`universalPrefixTM` reads aligned doubled pairs, emits the undoubled code, and
halts after the second separator cell. `universalPrefix_start` proves its exact
configuration after `2 * α.length + 2` steps: output `α`, physical input position
`2 * α.length + 3`, and no work tapes. It has moved onto the suffix start but has
not inspected a suffix symbol. `universalPrefix_live` proves preceding steps live.
These statements cover both empty code and empty suffix.

`universalCanonTM` uses `bufferedCompTM` to run `c.canonizer` with its input served
from the extracted code on a work tape. `universalCanon_start` reaches the virtual
canonizer start in exactly `3 * α.length + 4` steps. `universalCanon_run` and
`universalCanon_complete` prove that the physical head remains parked and the
completed output is exactly `(c.decode α).serialize`.

`universalCaptureTM` captures these canonizer emissions on the eventual table tape,
keeps them off the real output, and transfers control to the interpreter. The
`universalCapture_*` lemmas include exact configuration and transfer proofs.
`universal_captured_table` is the explicit captured-table correspondence.

`universalInterpreter_initialize` proves the complete initialization of the
interpreter, including copying the unary initial state. `universal_initialized`
lifts it through the capture wrapper to the first checkpoint of the complete
candidate machine. This is the full prefix-start correspondence: correct table,
initial unary state, blank simulated work tape, installed boundary marker, empty
real output, and the untouched suffix head at its start.

### Virtual left boundary and unbounded state

The interpreter has four work tapes: table, unary state, mirrored source work,
and boundary marker. The boundary tape holds a permanent `true` at integer zero;
its head is the native virtual input position. `universalInput_read` proves that
masking the physical delimiter cell as blank produces exactly the source read.
`universalInput_move` proves both clamped physical movement and the matching
marker-head displacement. At virtual zero an outward left move is suppressed.
For empty `x`, virtual position one is the right blank adjacent to the marked
virtual left blank; the same proofs cover it.

The state tape holds `false` at zero and `q` copies of `true` beginning at one.
`UniversalControl` is a fixed finite type: its registers are booleans, `Fin 9`,
`Fin 8`, optional `Fin 9`, and eight-bit functions. It does not contain a
code-dependent state type or an unbounded natural counter. The candidate table
lookup erases one unary state cell per nine skipped records and later copies the
successor state from the selected record.

The controller is defined, but its complete lookup/application behavior remains
unproved. Proved administrative gadgets include table rewind, doubled count-field
skipping, initial-state skipping, unary copying, state-tape erasure/append
identities, and marker-directed state rewind. No executable diagnostic establishes
whole-interpreter correctness; the optional smoke runs described below failed in
the evaluator before returning results.

## Exact open obligation

In `universal`, the already-halted source case is proved using a one-step absorbing
halt. The remaining branch has `hs : src.state ≠ none` and must prove:

```lean
∃ d, 1 ≤ d ∧ d ≤ universalBlockBound c α ∧
  universalRelation c α x ((c.decode α).tm.step src)
    ((universalTM c).tm.runFrom dst d)
```

from `universalRelation c α x src dst`. The missing pieces are:

1. Prove skipping and reading one serialized transition record, including its
   eight fixed action bits and optional unary successor field.
2. Prove that each consumed state-tape symbol skips exactly nine records, then
   that the finite input/work offset selects the action of the source transition
   function in `CodeTM.serialize`'s enumeration order.
3. Prove that decoding/applying that action preserves the checkpoint relation,
   including optional writes, state replacement, native emissions, virtual input
   movement, halting, and the table-cursor bound.
4. Concatenate those runs and establish the positive, code-only step bound.

No obstruction to the frozen mathematical statement was found. This is an
unfinished proof/construction verification, not a claim that the theorem is false.

## Cost ledger

Write `M := c.decode α`, `L := M.serialize.length`, `N := M.numStates + 1`,
`k := 2 * (Nat.bits M.numStates).length + 2`, and `q₀ := M.tm.q₀.val`.
The proved startup bound is

```text
S(α) = 3|α| + c.canonizerTime |α| + L
       + 2|(Nat.bits M.numStates)| + 2q₀ + 12.
```

Its components are extraction/virtual-canonizer setup (`3|α|+4`), canonizer
execution (at most its supplied time), capture transfer (one transition), and
interpreter initialization (`L + 2|bits| + 2q₀ + 7`). `universalCapture_start`
allows an earlier actual canonizer halt. Every bound depends on `α`, not on `x`.

The following **intended live-step ledger is not a proved bound**. Let `h` be the
old table cursor, `q` the source state index, `q'` a live successor index, and `P`
the total serialized length of records skipped before the selected record.

| Phase | Intended transitions |
| --- | ---: |
| Read symbols and begin rewind | 1 |
| Rewind table to its start | h + 1 |
| Skip doubled count field | k |
| Skip initial-state unary field | q₀ + 1 |
| Consume old state and skip all preceding records | q + P + 1 |
| Rewind erased state tape to position one | q + 2 |
| Read the selected action's fixed fields | 8 |
| Detect a halting next-state field, then apply action | 2 |
| Alternatively: detect live successor, copy it, rewind it, apply | 2q' + 5 |

Thus the proposed total is `h + k + q₀ + 2q + P + 16` for a halting action,
or `h + k + q₀ + 2q + P + 2q' + 19` for a live successor. Using `h,k,P ≤ L`
and `q₀,q,q' < N` suggests `B(α) := 3L + 5N + 20`, the definition of
`universalBlockBound`. The record-selection proof and this ledger's realization
are precisely the missing obligation; the definition alone does not certify it.

## Forward and converse assembly

`universal_block_run` is fully proved with explicit start and step-simulation
hypotheses. Positive block lengths give, for every source time `n`, a related
physical checkpoint at a time `v` with `n ≤ v ≤ S + B*n`.
`universal_from_blocks` is also fully proved with explicit hypotheses. It uses
`C := S+B` for the forward bound `(S+B)*(t+1)`.

Its converse covers arbitrary divergent source runs, not just terminating runs:
if the target has halted at physical time `t`, the source-time-`t` checkpoint
occurs at physical time at least `t`. Absorbing halting preserves the completed
target output there, so the relation forces source halting and the identical
output. Equivalently, a divergent source cannot coexist with any completed target
output under those hypotheses. No fairness assumption is used.

The concrete relation's startup, two-way halting correspondence, and output
equality are proved by `universalRelation_start`, `universalRelation_halt`, and
`universalRelation_output`. **The concrete live-step hypothesis is not proved.**
Therefore the conditional converse argument does not yet establish divergence
preservation or correctness for the candidate interpreter itself.

## Verification

Pinned toolchain: Lean 4.25.0, as specified by `lean-toolchain`. No `lake build`
was run. `lake exe cache get` was invoked once; dependency checkout succeeded but
the leantar installer hit this environment's archive-ownership error. Recovery
used the already compiled mathlib cache executable, a writable cache directory,
and `TAR_OPTIONS=--no-same-owner` to download/decompress the 878 mathlib modules
needed by the chapter's imports. Both initial and recovery logs are included.
This is an environment deviation, not a proof or toolchain substitution.

The final source was checked using the brief's full command:

```bash
( while read -r m; do bash scripts/lean_check_tree.sh "$m" || exit 1; done \
    < scripts/ab_ch1_module_order.txt )
```

All 25 module checks finished; the strengthened checker produced fresh oleans and
the overall exit status is zero. `final-sweep.log` contains zero `error:` lines.
It contains existing and new style-linter warnings and **four** sorry warnings,
so this is successful elaboration but **not** the brief's completion gate.

| Remaining admission | Status |
| --- | --- |
| `Complexity.oblivious_of_mem_DTIME` | Untouched |
| `Turing.exists_effectiveMachineCode` | Untouched |
| `Turing.universal` | Live-source block remains open; batch failure |
| `Turing.timed_universal` | Untouched |

`axioms.log` records all three required public prints. Each has
`[propext, sorryAx, Classical.choice, Quot.sound]`:

- `Turing.universal`
- `Turing.universal_quadratic`
- `Complexity.UC_computable_of_HALT_computable`

`verification/private-axioms.log` records 54 explicit private-lemma
prints. None of those axiom sets contains `sorryAx`; all are subsets of the normal
`propext`, `Classical.choice`, and `Quot.sound` set. The log was made from a
scratch copy of the entire source followed by the supplied print snippet, so the
private names have a scratch-module prefix. These lemma checks do not validate
the unproved live-step obligation.

Optional executable diagnostics were attempted for empty/nonempty boundary
behavior, unary state indices including 16, optional writes, and a divergent
emitting source. Both the raw runner and an equivalent tape-projection-normalized
runner exited 134 with a deep-recursion stack trace, before returning case results.
**These diagnostics are inconclusive and are not passing tests.** Both failure
logs and the final diagnostic snippet are included. They do not replace the
module checker or the required proof.

## Requested shared lemmas

Kept private here to honor ownership; suggestions for a later shared refactor:

- `universal_live_before`: a live later configuration excludes earlier halts.
- The `universalCaptureTM`/configuration/step/run/transfer family: capture native
  emissions on a table work tape, then transfer to a framed interpreter block.
- `universal_block_run`: cofinal bounded-cost checkpoint simulation.
- The general marker-directed rewind and unary-copy gadget patterns, currently
  specialized to this private controller.

No shared module or existing public API was changed.

## Escalations and docstring appendices

1. **Unfinished target:** one live-step admission remains, as detailed above.
   The target and both regression theorems retain `sorryAx`.
2. **File size:** `Universal.lean` is 1668 lines, exceeding the roughly 1000-line
   escalation threshold. The 82 new explicit declarations remain private in this
   owned file as directed; no split or shared structure move was attempted.
3. **Environment:** cache extraction required the ownership workaround above;
   optional executable diagnostics aborted. Neither issue is presented as a
   mathematical obstruction or as a successful test.

The original module docstring and theorem sketches remain unchanged. Added
implementation notes explicitly mark the construction incomplete. New private
helper docstrings explain the representation, administrative phases, exact costs,
boundary handling, and conditional proof assembly.

## Reproduction and archive checks

In an existing clone containing the base, use either the patch or the bundle:

```bash
git switch -c review/epoch3-B 71721842
git am /absolute/path/to/epoch3-B.patch
```

or

```bash
git bundle verify /absolute/path/to/epoch3-B.bundle
git fetch /absolute/path/to/epoch3-B.bundle refs/heads/fill/epoch3-B
git switch --detach FETCH_HEAD
```

The bundle requires the base commit; it is not a full standalone repository.
Use the pinned toolchain and dependency cache, then run the full sweep above.
For axiom prints, use the same `LEAN_PATH` arrangement as
`scripts/lean_check_tree.sh`, and run `lean verification/PublicAxioms.lean` from
an extracted archive with that path pointing at the checked clone's oleans.
For private prints, concatenate the delivered source with
`verification/private-axioms-snippet.lean.txt` in a scratch Lean file and check it
with the same `LEAN_PATH`.

`SHA256SUMS` covers every archive file except itself, including both patch and
bundle. Run `sha256sum -c SHA256SUMS` from the extracted archive root. The source
in the archive was checked against both the delivery commit and the result of
applying the patch to a temporary index at the base. No dependencies, oleans,
toolchain binaries, or temporary proof drafts are bundled.

## New private declarations

All 82 explicit new declarations below are inside namespace `Turing`; their
source visibility is `private`. Lean also generates the usual constructors,
recursors, and derived `DecidableEq`/`Fintype` infrastructure for
`UniversalControl`. Compiler-generated auxiliary declarations are not independent
source additions. The optional diagnostic declarations are outside the repository
and are documented in the included snippet, not used by the target.

1. `universal_pair_length`
2. `universal_pair_get`
3. `universal_pair_separator`
4. `universalPrefixTM`
5. `universalPrefixCfg`
6. `universalPrefix_step`
7. `universalPrefix_bits`
8. `universalPrefix_start`
9. `universalPrefix_penultimate`
10. `universal_live_before`
11. `universalPrefix_live`
12. `universalCanonTM`
13. `universalCanon_start`
14. `universalCanon_run`
15. `universalCanon_complete`
16. `universal_pair_suffix`
17. `universalInputPos`
18. `universalInputCfg`
19. `universal_marker`
20. `universalInput_read`
21. `universalInput_tag`
22. `universalInput_move`
23. `universalCaptureTM`
24. `universalCaptureCfg`
25. `universalCapture_init`
26. `universalCapture_step`
27. `universalCapture_run`
28. `universalCapturedCfg`
29. `universalCapture_transfer`
30. `universalCapture_start`
31. `universal_captured_table`
32. `UniversalControl`
33. `universalFour`
34. `universalAdmin`
35. `universalReadIndex`
36. `universalRecordIndex`
37. `universalSign`
38. `universalWrite`
39. `universalInterpreter`
40. `universalStateTape`
41. `universalTM`
42. `universalEvalCfg`
43. `universalEval_reads`
44. `universalAdmin_apply`
45. `universalEval_step`
46. `universal_table_read`
47. `universal_table_rewind`
48. `universal_count_run`
49. `universalStateWindow`
50. `universalStateWindow_zero`
51. `universalStateWindow_read`
52. `universalStateWindow_end`
53. `universalStateWindow_erase`
54. `universalStateWindow_empty`
55. `universalStateTape_append`
56. `universalStateTape_end`
57. `universal_state_rewind`
58. `universal_initial_skip`
59. `universal_unary_copy`
60. `universalStateTape_marker`
61. `universal_install_marker`
62. `universalInterpreterInitial`
63. `universalInterpreterBase`
64. `universalInterpreter_first`
65. `universalRecordBits`
66. `universalRecords`
67. `universal_serialization_header`
68. `universalInterpreter_initialize`
69. `universalSimulationCfg`
70. `universalSimulation_fields`
71. `universalCaptured_right`
72. `universalCapture_interpreter_run`
73. `universalStartupBound`
74. `universal_initialized`
75. `universal_block_run`
76. `universal_from_blocks`
77. `universalBlockBound`
78. `universalRelation`
79. `universal_header_bound`
80. `universalRelation_start`
81. `universalRelation_halt`
82. `universalRelation_output`

## Brief checklist

- [ ] Target filled; `sorryAx` eliminated from target and both regressions.
- [x] Prefix-start and captured-table correspondence proved and named.
- [x] Boundary masking and clamped motion proved, including empty suffix.
- [ ] Complete concrete per-step simulation and its time bound proved.
- [x] Conditional forward/converse assembly proved, with positive block lengths.
- [ ] Concrete divergence preservation established without an admission.
- [x] All explicit new private declarations listed; shared-lemma requests,
  escalations, and added implementation notes recorded.
- [x] Full 25-module sweep, requested axiom log, exact remaining admissions, and
  failed optional-diagnostic evidence included.
- [x] Repository diff touches only `Universal.lean`; other bodies and statements
  remain frozen.
