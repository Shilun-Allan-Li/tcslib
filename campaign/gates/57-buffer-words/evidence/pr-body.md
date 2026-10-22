## The cells of a buffer tape holding a composite word (a new public module, `TuringMachine/BufferWords`)

A new module `TuringMachine/BufferWords.lean` (imports `Simulation` only), proved:

| Declaration | What it states |
|---|---|
| `FinTM.bufferTape_append_shift` | for `z ≥ 0`, `bufferTape (u ++ w) (|u| + z) = bufferTape w z` (a suffix at an offset, its right blank and beyond included) |
| `FinTM.bufferTape_append_mid` | for `r < |w|`, `bufferTape (u ++ w ++ v) (|u| + r) = some w[r]` |
| `FinTM.bufferTape_drop` | for `z ≥ 0`, `bufferTape (w.drop r) z = bufferTape w (r + z)` |
| `FinTM.bufferTape_take` | for `z < n`, `bufferTape (w.take n) z = bufferTape w z` |
| `FinTM.bufferTape_eq_none_of_not_mem` | off `[0, |w|)`, `bufferTape w z = none` |
| `FinTM.bufferTape_unary` | for `r ≤ q`, `bufferTape (1^q 0) r = some (decide (r < q))` (the terminator included) |

The `TuringMachine` facade imports the module and lists it.

**Why** (the user's ruling of 2026-10-18): the seam layout's standalone fill (`Build/SeamLayout`)
reads its serialization `pairEncode a ((1^q 0) ++ v)` cell by cell: the unary state, the table,
the suffix `s.drop r`, the prefix `s.take (h + q)` and the blanks. Four of these identities exist
only as `Build/StepBlock`'s privates (`bufferTape_suffix`, `_reads`, `_outside`, `_unary`),
outside the layout's closure; the two on `drop` and `take` exist nowhere. The fill's brief
authorizes importing this module. `StepBlock`'s four privates state the same facts as four of
these lemmas (with different proofs); by the same ruling they are re-pointed in the user's dedup
window.

### Checks (maintainer, against `oleans-lc6m`, #131's replay at the merged state)

- **Elaboration:** the module, 0 errors, 0 warnings. Axioms: `_append_shift`, `_append_mid`,
  `_take` and `_unary` depend on `[propext, Quot.sound]`; `_drop` and `_eq_none_of_not_mem` on
  `[propext, Classical.choice, Quot.sound]`.
- **Rule 10:** every proof reads `FinTM.bufferTape` only through its published equations
  (`bufferTape_eq`, `bufferTape_nat`). With `FinTM.bufferTape` made `local irreducible`, the module
  elaborates; two controls (`bufferTape w (-1) = none` and the `bufferTape_eq` form, both by
  `rfl`) fail under the same seal.
- **The consumer's forms:** in the seam layout's import context, with `FinTM.bufferTape` and
  `pairEncode` sealed, six examples derive the layout's reads from the module and `pairEncode_eq`
  alone: the unary state's cells (terminator included), the table's cells from its first cell on,
  a suffix, a prefix, the blanks past the word, and a separator cell. 0 errors.
- **Lint:** `TuringMachine` 0 FAIL, 63 WARN over 81 files (the tip's 63 WARN over 80: no new
  warning); the module has 118 lines, 6 public / 0 private. No line over 100 characters.
- **Screen (v3):** the module with `Simulation`, `Build/StepBlock` and `Build/SeamLayout`: 140
  declarations, 32 pairs; the module is in none. StepBlock's four privates are recorded in the
  duplication ledger as a restated-fact family (BW-1), acknowledged by the user.

### Replay

At the merged state: the campaign branch after #132 (`e9e97970`) was merged into this branch, with
no conflict and this PR’s files byte-unchanged. `replay-lbw2.sh`: the changed modules' downstream closure on the merged tree (2 modules: `TuringMachine/BufferWords`, `TuringMachine`), chained from `oleans-l132b` (#132's replay at its merged state). **Passed (user, 2026-10-21):** 2 of 2, 0 failed, static-equal (0) (`campaign/gates/57-buffer-words/evidence/replay-lbw2.*`, `campaign/gates/57-buffer-words/evidence/down-lbw2.txt`).

### Gate

A statement-and-proof gate (the API gate's form): pending.

🤖 Generated with [Claude Code](https://claude.com/claude-code)

