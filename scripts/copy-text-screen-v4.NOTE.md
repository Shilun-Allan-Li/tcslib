# copy-text-screen v4: proposal for the screen's maintainers

**For:** the maintainers of `scripts/copy-text-screen-v3.py` (gate-86 tooling).
**Status:** proposed on branch `claude/fervent-mendel-tpkqmh`, not merged. v3 is unchanged.

## The defect

v3 opens a declaration only at `def|theorem|lemma|abbrev|instance|structure|inductive`
(`DECL`, line 40). Two consequences:

1. An anonymous `example` is read as part of the preceding declaration's body. In the quantum E1
   epoch audit (`campaign/gates/02-quantum-e1/findings.md` on `quantum/e1-fill`, findings 1 and 7),
   an `example` in `TCSlib/Quantum/Basic/Measure.lean` duplicating `Ket.probQubit_basis` was
   reported as `probQubit_zero_add_one reproduces probQubit_basis: 69/69`. In the minimal case
   (a theorem followed by a duplicate `example`), v3 reports nothing at all.
2. An anonymous `instance` is named after its first token: `:`, `(w`, `[Add`, `{k`, ... (60
   such instances in TCSlib today, counted on comment-stripped text). A named instance with a priority, `instance (priority := 100)
   instNonempty`, is named `(priority`.

`quantum/e1-fill` currently works around (1) with a `grep` pre-check in
`campaign/gates/02-quantum-e1/evidence-r1/scripts/copy_screen.sh`.

## The change

A new file, `scripts/copy-text-screen-v4.py`, so that every gate pack citing v3 output still
reproduces byte-for-byte against v3. This follows the v2 → v3 precedent. The diff against v3 is
about 15 lines:

- `DECL` also opens at `example`. The keyword must be followed by whitespace or one of
  `: ( [ { ⦃`, and an optional `(priority := …)` is skipped before the name token is read.
- **Synthetic names.** Every `example` is named `<example #k>`. An `instance` whose next token
  starts with `: ( [ { ⦃` is named `<instance #k>`. `k` counts that keyword's anonymous commands
  in the file in source order. This count includes anonymous commands that are too short to
  screen, so a name does not move when the 60-character threshold changes.
- **Kinds.** An `example` is screened as a **proof**, so it pairs with theorems and lemmas. An
  instance stays a **term**, as before.
- Nothing else changed: labels (`<file>::<name>`), namespace disambiguation, the header line, row
  format, sorting, thresholds and tiling are all v3's.

**When output differs from v3:** only for files that contain an `example`, an anonymous
instance or an instance with a priority. In those files:
- The header's `declarations screened` count can move, because an example's text no longer
  inflates its neighbour past the 60-character threshold.
- A row changes only when such a command, or a body that used to absorb one, takes part in it.

## Decisions to confirm

1. **Examples are proofs.** The screen cannot elaborate types. All 15 `example`s in TCSlib today
   state propositions. A data-valued `example` would only be compared with theorems and lemmas.
2. **One counter per keyword, per file, counting unscreened commands.** The alternatives are to
   count screened commands only, or to use one counter for both keywords.
3. **`instance (priority := p) foo` is now labelled `foo`**, not `(priority`. One instance in
   TCSlib has this form (`FiniteProbabilitySpace.lean:341`). It appears in no current row.
4. **New file, not an in-place edit.** The alternative is to edit v3 and re-baseline the packs
   that cite it.

## Regression evidence

Each run compared v3 and v4 on the same files. `python3 -I`, root = a tree of the given revision.

| File set | v3 | v4 | Difference |
|---|---|---|---|
| Fixture `TheoremThenExample.lean` (theorem, then the same body as `example`) | 1 decl, 0 pairs | 2 decls, 2 pairs | the theorem ↔ `<example #1>` pair (92/92, 92/102) |
| Fixture `ExampleBeforeTwin.lean` (shaped like E1 `Measure.lean`) | `length_append_reverse reproduces length_reverse_cons` | `<example #1>` ↔ `length_reverse_cons` | misattributed row replaced by the true pair |
| Fixture `Instances.lean` | names `:`, `(w`, `(priority` | `<instance #1>`, `<instance #2>`, `instBoxNonempty` | names only, same pairs and figures |
| Quantum E1, 7 files, at `a97fceca` (the audited revision) | 130 decls, 28 pairs, 3,495 chars | 131 decls, 29 pairs, 3,564 chars | Only the `probQubit_zero_add_one reproduces probQubit_basis: 69/69` row changes: it becomes the two `<example #1>` ↔ `probQubit_basis` rows. The other 27 rows are byte-identical. |
| Quantum E1, 7 files, at `quantum/e1-fill` tip (example removed) | 132 decls, 22 pairs | same | byte-identical |
| 12.2c T1 item 7 set: `PolyTimeBlock{Loop,Tests,Majority}`, `PClosure`, `EmitIter{Body,Embed}` at `main` | 94 decls, 41 pairs | same | byte-identical |
| 12.2c T1 CodeFormat set: `CodeParser`, `CodeFormat`, `Codes2Tape`, `NDCodes`, `MathlibBridge`, `Encoding` at `main` | 169 decls, 75 pairs | same | byte-identical |
| Every `TCSlib/**/*.lean` at `main`, one file per run (926 runs) | — | — | 921 byte-identical. In 4 `CircuitComplexity` files (`CircuitSat`, `DAGCircuitSatLang`, `Encoding`, `HardFunctions`) only the header count moves (13→12, 15→18, 17→21, 9→10), with no row changes. In `Build/CfgRecord.lean` only labels change: the 66/66 pair between two anonymous `instance {k …}` is relabelled from `Turing.{k#1`/`Turing.{k#2` to `<instance #2>`/`<instance #3>`, with the same figures. |

The fixtures and their exact expected outputs are in `tests/fixtures/copy_text_screen/` and
`tests/test_copy_text_screen.py`. Run them with `python3 -m pytest tests/test_copy_text_screen.py`.

## After adoption

- `quantum/e1-fill`'s `copy_screen.sh` can call v4 and drop its `example` pre-check. The E1
  ledger row for finding 1 would then read `<example #1>` ↔ `probQubit_basis`. The example has
  since been removed, and at the tip v4 and v3 agree.

## Known remaining gaps (unchanged by v4)

These commands are still not boundaries, so their text is still absorbed into the preceding
body. Counts are commands at column 0 in TCSlib at `main`:

- `scoped`/`local instance`: 29
- `class`: 21
- `axiom`, `opaque`: 5
- `partial`/`unsafe def`: 13
- `attribute [...]`: 93
- `notation`/`macro`/`syntax`, etc.: 96
- `set_option … in` / `open … in` lines: 385

`scoped`/`local instance` is the same defect class as `example`. It is left out here to keep v4's
departure from v3 to what the audit found.
