# Split report B: Universal.lean → UniversalStartup / UniversalInterpreter / UniversalBlock / Universal

Mechanical linear split of `TCSlib/Complexity/TuringMachine/Universal.lean`
(2465 lines at the pre-split working-tree state) into four sequential modules,
performed at the epoch-3→4 merge. All declaration bodies were moved verbatim
(byte-identical, machine-verified line by line) with exactly one class of
permitted change: deletion of the leading `private ` on declarations that a
later module references. No declaration was renamed, reordered, or had its
signature, proof body, or docstring altered. `timed_universal` keeps its
`sorry` and its proof sketch character for character.

## 1. Exact cut points (original line ranges → destination)

| Original lines | Content | Destination |
|---|---|---|
| 1–5 | copyright header | replicated in all four files |
| 6 | `import TCSlib.Complexity.TuringMachine.Encoding` | UniversalStartup (residual and the other new modules import their predecessor instead) |
| 8–10 | `set_option` block | replicated in all four files |
| 12–68 | module docstring | residual Universal.lean (one paragraph added, see §5) |
| 70 | `namespace Turing` | replicated in all four files |
| 72–87 | section banner `### Private prefix-local startup infrastructure` (incl. epoch-3B/3B2 notes) | UniversalStartup, verbatim |
| 89 | `open FinTM` | UniversalStartup verbatim; replicated after `namespace Turing` in the other three files (context replication — the whole original file elaborated under this open) |
| 92–618 | `universal_pair_length` … `universal_captured_table` | UniversalStartup |
| 621–629 | section banner `### The table interpreter` | UniversalInterpreter, verbatim |
| 631–1501 | `UniversalControl` … `universal_from_blocks` | UniversalInterpreter |
| 1504–1508 | section banner `### Completion of the live table block (epoch 3B2)` | UniversalInterpreter, verbatim (see deviation, §8) |
| 1510–1590 | `universalActionBits`, `universalNextOnes`, `universal_record_shape`, `universal_skip_fixed`, `universalSkipDone` | UniversalInterpreter (see deviation, §8 — prescribed as Block, forced into Interpreter by cross-module `match`-auxiliary identity) |
| 1592–2335 | `universal_skip_unary` … `universalRelation_output` | UniversalBlock |
| 2337–2464 | `theorem universal`, `theorem universal_quadratic`, `theorem timed_universal` with docstrings, verbatim | residual Universal.lean |
| 2465 | `end Turing` | replicated in all four files |

So the actual ranges are: Startup = 72–618, Interpreter = 621–1590,
Block = 1592–2335, residual = 12–68 + 2337–2465. The Interpreter/Block cut
sits at the declaration boundary after `universalSkipDone` (line 1590), not at
the section banner (line 1504) as estimated in the task; §8 explains why.

## 2. Final line counts

| File | Lines |
|---|---|
| TCSlib/Complexity/TuringMachine/UniversalStartup.lean | 591 |
| TCSlib/Complexity/TuringMachine/UniversalInterpreter.lean | 1020 |
| TCSlib/Complexity/TuringMachine/UniversalBlock.lean | 794 |
| TCSlib/Complexity/TuringMachine/Universal.lean (residual) | 208 |
| Total | 2613 |

## 3. Complete private→public flip list (53 flips)

Every flip below is forced by a syntactic reference (code, not docstring) from
a strictly later module. "Required by" names the earliest later module that
references the declaration; several are also referenced by modules after that
one. Verified mechanically: within each new module, the only lines differing
from the original are exactly these declaration lines, each differing only by
the deleted `private ` prefix.

### In UniversalStartup.lean (10)

| Declaration | Required by |
|---|---|
| `universal_pair_length` | UniversalInterpreter (`universalInterpreter_initialize`), also UniversalBlock |
| `universalCanonTM` | UniversalInterpreter, also UniversalBlock, Universal |
| `universalCanon_complete` | UniversalInterpreter (`universal_initialized`) |
| `universalInputPos` | UniversalInterpreter (`universalSimulationCfg`) |
| `universalInput_read` | UniversalBlock (`universal_apply_record`, `universal_live_block`) |
| `universalInput_move` | UniversalBlock (`universal_apply_record`) |
| `universalCaptureTM` | UniversalInterpreter, also Universal |
| `universalCaptureCfg` | UniversalInterpreter (`universalCaptured_right`) |
| `universalCapturedCfg` | UniversalInterpreter (`universalCaptured_right`) |
| `universalCapture_start` | UniversalInterpreter (`universal_initialized`) |

### In UniversalInterpreter.lean (37)

| Declaration | Required by |
|---|---|
| `UniversalControl` | UniversalBlock (throughout) |
| `universalFour` | UniversalBlock |
| `universalAdmin` | UniversalBlock (`universal_live_block`, `change` step) |
| `universalRecordIndex` | UniversalBlock |
| `universalSign` | UniversalBlock (`universalActionBits_decode`) |
| `universalWrite` | UniversalBlock (`universalActionBits_decode`) |
| `universalInterpreter` | UniversalBlock, also Universal |
| `universalStateTape` | UniversalBlock |
| `universalTM` | UniversalBlock, also Universal |
| `universalEvalCfg` | UniversalBlock |
| `universalEval_step` | UniversalBlock |
| `universal_table_read` | UniversalBlock |
| `universal_table_rewind` | UniversalBlock (`universal_live_block`) |
| `universal_count_run` | UniversalBlock (`universal_live_block`) |
| `universalStateWindow` | UniversalBlock (`universal_skip_groups`) |
| `universalStateWindow_zero` | UniversalBlock (`universal_select`) |
| `universalStateWindow_read` | UniversalBlock (`universal_skip_groups`) |
| `universalStateWindow_end` | UniversalBlock (`universal_skip_groups`) |
| `universalStateWindow_erase` | UniversalBlock (`universal_skip_groups`) |
| `universalStateWindow_empty` | UniversalBlock (`universal_select`) |
| `universal_state_rewind` | UniversalBlock (`universal_prepare_next`, `universal_select`) |
| `universal_initial_skip` | UniversalBlock (`universal_live_block`) |
| `universal_unary_copy` | UniversalBlock (`universal_prepare_next`) |
| `universalStateTape_marker` | UniversalBlock |
| `universalRecordBits` | UniversalBlock (throughout) |
| `universalRecords` | UniversalBlock (`universal_serialization_actions`) |
| `universal_serialization_header` | UniversalBlock (`universal_header_bound`) |
| `universalSimulationCfg` | UniversalBlock, also Universal |
| `universalCapture_interpreter_run` | Universal (`universal`) |
| `universalStartupBound` | UniversalBlock (`universalRelation_start`), also Universal |
| `universal_initialized` | UniversalBlock (`universalRelation_start`) |
| `universal_from_blocks` | Universal (`universal`) |
| `universalActionBits` | UniversalBlock (`universalActionBits_decode`, `universal_apply_record`, `universal_live_block`) |
| `universalNextOnes` | UniversalBlock (`universal_prepare_next`, `universal_live_block`) |
| `universal_record_shape` | UniversalBlock (`universal_skip_record`, `universal_live_block`) |
| `universal_skip_fixed` | UniversalBlock (`universal_skip_record`) |
| `universalSkipDone` | UniversalBlock (`universal_skip_unary` … `universal_select`) |

### In UniversalBlock.lean (6)

| Declaration | Required by |
|---|---|
| `universal_live_block` | Universal (`universal`) |
| `universalBlockBound` | Universal (`universal`) |
| `universalRelation` | Universal (`universal`) |
| `universalRelation_start` | Universal (`universal`) |
| `universalRelation_halt` | Universal (`universal`) |
| `universalRelation_output` | Universal (`universal`) |

Declarations referenced only inside their own module keep `private`
(e.g. `universalPrefixTM` family, `universal_captured_table`,
`universalReadIndex`, `universalEval_reads`, `universalAdmin_apply`,
`universalStateTape_append`, `universalStateTape_end`,
`universal_install_marker`, `universalInterpreterInitial/Base/_first`,
`universalInterpreter_initialize`, `universalSimulation_fields`,
`universalCaptured_right`, `universal_block_run`, `universal_skip_unary`,
`universal_skip_record(s)`, `universal_skip_groups`, `universal_read_fixed`,
`universalNextCost`, `universalActions(_lookup)`, `universalHeader`,
`universal_serialization_actions`, `universal_lookup_parts`,
`universalActionBits_decode`, `universal_apply_record`, `universal_select`,
`universal_run_join`, `universal_header_bound`, and the rest).

## 4. Docstrings added

None. Every flipped declaration already carried a docstring whose first
sentence states the result in natural language; per the verbatim-move rule
none was reworded.

## 5. Module-docstring edits

1. **UniversalStartup.lean** — new module docstring (template shape): titles
   the startup layer (prefix parsing, canonization, virtual input-head
   embedding, table capture), records the mechanical split at the epoch-3→4
   merge with epoch-3 batch-B/B2 provenance, lists the main public surface,
   and carries the [AB09] reference.
2. **UniversalInterpreter.lean** — new module docstring (template shape): as
   above for the table-interpreter layer; additionally (a) notes that the
   public surface exists to support the epoch-4 `timed_universal` fill, with
   promotion recorded at the epoch-3→4 merge (shared-lemma requests of the
   batch-B/B2 reports), and (b) records that the head of the epoch-3B2
   completion (through `universalSkipDone`) lives here because those proofs
   need Lean's per-module `match` auxiliaries shared with
   `universalRecordBits`/`universalInterpreter` (see §8).
3. **UniversalBlock.lean** — new module docstring (template shape): as above
   for the live-block layer; notes the epoch-4 `timed_universal` support and
   promotion record, and points to UniversalInterpreter's docstring for the
   relocated 3B2 head.
4. **Residual Universal.lean** — one paragraph inserted after the opening
   statement paragraph (before "## Design and deviations"): the construction
   lives in UniversalStartup (prefix parsing, canonization, table capture),
   UniversalInterpreter (four-tape interpreter, block-simulation assembly),
   and UniversalBlock (live table block, checkpoint relation), split out
   mechanically at the epoch-3→4 merge; this file holds only the public
   statements. All existing design/deviation notes kept verbatim; no other
   docstring change.

Section banners moved verbatim: `### Private prefix-local startup
infrastructure` (with its epoch-3B/3B2 implementation notes) heads
UniversalStartup's content; `### The table interpreter` and `### Completion of
the live table block (epoch 3B2)` both live in UniversalInterpreter (the
latter immediately before `universalActionBits`, its original neighbor).
UniversalBlock's content starts directly at `universal_skip_unary`.

## 6. Final import lists

| File | Imports |
|---|---|
| UniversalStartup.lean | `TCSlib.Complexity.TuringMachine.Encoding` |
| UniversalInterpreter.lean | `TCSlib.Complexity.TuringMachine.UniversalStartup` |
| UniversalBlock.lean | `TCSlib.Complexity.TuringMachine.UniversalInterpreter` |
| Universal.lean | `TCSlib.Complexity.TuringMachine.UniversalBlock` |

Each file wraps its content in `namespace Turing` … `end Turing` with
`open FinTM` in scope (fully qualified names unchanged), and replicates the
original `set_option maxHeartbeats 0 / relaxedAutoImplicit false /
autoImplicit false` header.

## 7. Verification results

All four modules checked with `scripts/lean_check_tree.sh` against the
pre-seeded olean tree
`…/scratchpad/oleans-splitB`, in dependency order. Pass = exit 0, no `error:`
lines, fresh `.olean` produced. No module outside the four was checked; no
`lake` command and no git state-changing command was run.

- **UniversalStartup** — exit 0; 0 `error:` lines; 0 sorry warnings. Output:
  six pre-existing `linter.unusedSimpArgs` warnings (five `Fin.val_mk` at
  160:54, 164:54, 190:52, 197:54, 215:52 and one `VirtualTag` at 274:46 —
  lint noise carried over verbatim from the original proofs), tail:
  ```
  TCSlib/Complexity/TuringMachine/UniversalStartup.lean:274:46: warning: This simp argument is unused:
    VirtualTag
  ...
  Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
  EXIT=0
  ```
- **UniversalInterpreter** — exit 0; `grep -c "error:"` = 0; `grep -c sorry`
  = 0 (log: `scratchpad/check-interp2.log`; pre-existing lint warnings only).
- **UniversalBlock** — exit 0; `grep -c "error:"` = 0; `grep -c sorry` = 0
  (log: `scratchpad/check-block2.log`), tail:
  ```
    simp only ̵[̵F̵i̵n̵.̵v̵a̵l̵_̵m̵k̵]̵
  Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
  EXIT=0
  ```
- **Universal (residual)** — exit 0; 0 `error:` lines; exactly ONE sorry
  warning, as expected (log: `scratchpad/check-resid.log`), full output:
  ```
  TCSlib/Complexity/TuringMachine/Universal.lean:197:8: warning: declaration uses 'sorry'
  ```
  Line 197 is `theorem timed_universal (c : EffectiveMachineCode) :` — the
  expected, untouched sorry.

Additionally, byte-identity was machine-verified: for each new module, the
content between the namespace wrappers has the same number of lines as the
corresponding original range, and every differing line differs exactly by the
deleted `private ` prefix on a listed flip (10 + 37 + 6 = 53); the residual's
theorem block (original lines 2337–2464) is byte-identical.

## 8. Deviation from the prescribed split (one, forced; explained precisely)

**The UniversalInterpreter/UniversalBlock cut sits after `universalSkipDone`
(original line 1590), not at the `### Completion of the live table block
(epoch 3B2)` banner (line 1504).** Five declarations the task assigned to
UniversalBlock — `universalActionBits` (1511), `universalNextOnes` (1524),
`universal_record_shape` (1529), `universal_skip_fixed` (1562),
`universalSkipDone` (1589) — therefore live at the end of
UniversalInterpreter, in their original relative order, bodies verbatim, and
are flipped public (all five are referenced from UniversalBlock).

Reason: with the cut at 1504, checking UniversalBlock fails with exactly two
errors, both instances of Lean 4's per-module `match`-auxiliary identity.
A `match` expression re-elaborated in a different module mints a *distinct*
auxiliary matcher constant (structurally identical, pretty-printed
identically, but not syntactically equal and not reducible-transparency
defeq), and the affected proofs need *syntactic* matcher equality:

1. `universal_record_shape` (UniversalBlock.lean:97:6, `rewrite` failed):
   `unfold universalRecordBits` exposes the matcher constants minted in the
   interpreter module for `universalRecordBits`'s body, while the lemma's
   local `have hi/hw/hm/ho` statements re-elaborate the same `match … with`
   expressions in the Block module, minting fresh matchers; `rw [hi, hw, hm,
   ho]` then finds no occurrence of its pattern.
2. `universal_skip_unary` (UniversalBlock.lean:162:8, unsolved goal): the
   discharging `simp [universalInterpreter, …, universalSkipDone]` unfolds
   `universalInterpreter`'s `.skipUnary` branch to the interpreter module's
   matcher for `match dest with | none => .readAction 0 (fun _ => false) |
   some i => .group i`, and unfolds `universalSkipDone` to the Block module's
   freshly minted matcher for the same expression; the two `universalAdmin`
   applications then differ by matcher constant and simp cannot close the
   goal.

In the original single file both sides shared the module-local matcher cache,
so both proofs closed; the only way to preserve that without editing a proof
body (forbidden) is to keep these declarations in the same module as
`universalRecordBits` and `universalInterpreter`. The cut was moved to the
nearest declaration boundary after the last affected declaration
(`universalSkipDone`), keeping the linear order of every line; the
intermediate `universal_skip_fixed`, `universalActionBits`, `universalNextOnes`
move with the chunk because the split is linear (sequential modules must
partition the file at a single point). No inline `match` expression occurs
after line 1590 in the original file (checked mechanically), and with the
adjusted cut all four modules pass. Both affected module docstrings record
the relocation and its reason.

No other deviation: no other file was modified, no facade or module-order
edits, no `lake` invocation, no git state change.
