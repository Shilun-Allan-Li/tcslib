# External audit pack — the cells of a buffer tape holding a composite word (PR #140, an API gate)

Campaign: the Arora-Barak chapters 3-4 plan, C1 (the nondeterministic time hierarchy, [AB09,
Theorem 3.2]), the seam layout `Turing.exists_seamLayoutTM` (`Build/SeamLayout`), which
redistributes a machine's serialization onto the step block's table and summary tapes. The
user's "Everything" rule (2026-10-16, `policy.md` §1): every definition a brief's route reads
gets a published equation before the brief is dispatched.
- **Why:** the seam layout's statement gate (round 2, `campaign/items/c1/seam-layout/gate46-review.md`,
  "Word identities") found that its fill reads the serialization `s = pairEncode a ((1^q 0) ++ v)`
  cell by cell (`s.drop r`, `s.take (h + q)`, the cells of the unary state and of the table, the
  blanks), and that four of the identities exist only as `Build/StepBlock`'s privates, outside
  the layout's closure. **The user ruled on 2026-10-18** for a new small public module beside
  `Simulation`, by an API PR with its own replay and gate; the fill's brief authorizes its import.
  `StepBlock`'s four privates become an acknowledged restated-fact family (BW-1), re-pointed in
  the user's dedup window.
- **The head:** `lean/buffer-words` at `7c963897`: one commit `c00375a8` on the campaign branch at
  `3e14cf34`, then a merge of the campaign branch after #132 (`e9e97970`; no conflict, both files
  byte-unchanged). Its Lean diff from the campaign tip is exactly the two files below.

| File | Change |
|---|---|
| `TuringMachine/BufferWords` (new, 118 lines; imports `Simulation` only) | six public lemmas in `Turing.FinTM` (below), no private declaration |
| `TuringMachine` (the facade) | imports the module and lists it ("Proved.") |

| Lemma | Statement |
|---|---|
| `bufferTape_append_shift` | `0 ≤ z → bufferTape (u ++ w) (u.length + z) = bufferTape w z` |
| `bufferTape_append_mid` | `r < w.length → bufferTape (u ++ w ++ v) (u.length + r) = some w[r]` |
| `bufferTape_drop` | `0 ≤ z → bufferTape (w.drop r) z = bufferTape w (r + z)` |
| `bufferTape_take` | `z < n → bufferTape (w.take n) z = bufferTape w z` |
| `bufferTape_eq_none_of_not_mem` | `¬(0 ≤ z ∧ z < w.length) → bufferTape w z = none` |
| `bufferTape_unary` | `r ≤ q → bufferTape (List.replicate q true ++ [false]) r = some (decide (r < q))` |

`bufferTape_drop` and `bufferTape_take` go beyond the four private identities: the layout reads
`s.drop r` and `s.take (h + q)` directly.

- **Evidence:** `evidence/`:
  - `bufferwords.patch` (the head's diff from `3e14cf34`);
  - `elab-BufferWords-axioms.out` (the module with `#print axioms` for the six appended);
  - `BufferWordsSeal.lean.txt`/`.out` (the module with `FinTM.bufferTape` sealed; empty output:
    0 errors, 0 warnings) and `BufferWordsSealControl.lean.txt`/`.out` (two `rfl` controls,
    failing as intended);
  - `BufferWordsProbe.lean.txt`/`.out` (the consumer's forms: in the seam layout's import context
    with the module's declarations inlined, `FinTM.bufferTape` and `pairEncode` sealed, six
    examples derive the layout's reads; empty output: 0 errors, 0 warnings);
  - `lint-tm.txt`; `screen.txt` and `screen-population.txt` (the copy-text screen v3);
  - `simulation-excerpts.lean.txt` (`bufferTape` and its published equations, verbatim) and
    `stepblock-excerpts.lean.txt` (the four privates, verbatim);
  - the replay's script, list, log and static check; `pr-body.md`.
- **The bundle** also contains the module and the facade at the head, `Build/SeamLayout` (the
  consumer's statement), the seam-layout gate's review, and the duplication ledger.

## Brief for the auditor

1. **Faithfulness.** Is each statement true for every argument, at the boundaries in particular:
   `z = 0` and the right blank `z = |w|` (`_append_shift`, `_drop`); `r > |w|` (`_drop`, where the
   suffix is empty); `n > |w|` and negative `z` (`_take`); `q = 0` (`_unary`, where the word is
   `[false]`)? Is each docstring an exact reading of its statement?
2. **Sufficiency.** Do the six give the seam layout's reads, as the probe derives them (the unary
   state with its terminator at offset `|P|`, the table from `|P| + q + 1`, `s.drop r`,
   `s.take n`, the blanks past `s`, a separator cell), from the published `pairEncode_eq` alone?
   Is anything the layout's fill will need still missing (compare the fill's route in the gate
   46 review)?
3. **Rule 10 in the module's proofs.** They read `FinTM.bufferTape` only through `bufferTape_eq`
   and `bufferTape_nat`. Does the seal cover every other-file definition the proofs could reach,
   and do the controls show it is effective?
4. **Duplication (acknowledged).** Four of the lemmas restate `StepBlock`'s privates (excerpted)
   with different proofs; the screen pairs none. The family is ledgered as BW-1 and acknowledged
   by the user, with its retirement (StepBlock re-pointed) in the dedup window. Is the ledger
   entry accurate?
5. **Naming and home.** Do the names fit the `FinTM.bufferTape_*` API in `Simulation`
   (`bufferTape_nat`, `_left`, `_eq`, `_of_neg`, `_append`)? Is a separate module the right home
   (the alternative, `Simulation` itself, has a 313-module downstream)?
6. **Public-facing text:** the module's docstrings and the facade's new line carry no campaign
   labels, paths or dated rulings.

## Repository-side attestations (verify or challenge)

- **Elaboration** (maintainer, against `oleans-lc6m`, #131's replay at the merged state): the
  module, 0 errors, 0 warnings. **Axioms:** `_append_shift`, `_append_mid`, `_take`, `_unary`:
  `[propext, Quot.sound]`; `_drop`, `_eq_none_of_not_mem`: `[propext, Classical.choice,
  Quot.sound]` (`evidence/elab-BufferWords-axioms.out`). The facade elaborates only with the
  module's `.olean`, which the replay builds.
- **Lint:** `TuringMachine` 0 FAIL, 63 WARN over 81 files (the tip's 63 over 80: no new
  warning). No line over 100 characters.
- **Screen (v3):** the module, `Simulation`, `Build/StepBlock`, `Build/SeamLayout`: 140
  declarations, 32 pairs; the module is in none (`evidence/screen.txt`).
- **Replay:** `replay-lbw2.sh`: the changed modules' downstream closure on the merged tree (2 modules: `TuringMachine/BufferWords`, `TuringMachine`), chained from `oleans-l132b` (#132's replay at its merged state). **Passed (user, 2026-10-21):** 2 of 2, 0 failed, static-equal (0) (`evidence/replay-lbw2.*`, `evidence/down-lbw2.txt`).

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Severity guide as in `campaign/standards/TEMPLATE.md`. Findings go verbatim into
`campaign/gates/57-buffer-words/findings.md`. The gate closes when it has zero blockers and zero
majors.

**Deliver your findings as a downloadable Markdown file named `buffer-words-findings.md`** (the
findings table and the verdict line, no other wrapping), and also paste its content in your
reply.
