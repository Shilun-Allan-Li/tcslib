# RAM fill (Codex), tier 2 job B: the keyed table (`Build/KeyTable`, 2 admissions)

Read `COMMON.md` (bundled), its tier 2 addendum included; its rules bind. **Fill name:**
`fill-ram-key-table`. **Base:** the commit given in the dispatch prompt, on
`complexity/ram-simulation`.

## What this is

`TCSlib/Complexity/TuringMachine/Build/KeyTable.lean` is the memory host of a word RAM run on a
Turing machine. A keyed table is a list of `(key, value)` entries in `Build/RecordTable`'s layout
(`Turing.TableAt`): the header `[true]`, then for each entry the fields `true :: key` and
`true :: value`. The definitions (`keyFields`, `keyTableLength`, `KeyTableAt`, `keyTableWrite`,
`keyLookup`, `keyAssign`) and their readers are proved. **This job proves the two rows:**
1. `exists_keyLookupTM`: copy the value stored under the key on tape `1` into the register on
   tape `2`, or write zeros if the key is absent.
2. `exists_keyAssignTM`: overwrite every value stored under the key with tape `2`'s word, or
   append the entry.

Both are five-tape machines (table, key, register, two blank scratch tapes), stated with
`Turing.ReachesWithin`, within `O(table + key + value)` steps and radius. Jobs C and D cite them.

## Route

- **The marker adapter (gate 162, G162-02).** A field's payload follows its marker `true`, so a
  catalog word row, which needs a blank at the word's offset `-1`, applies only through an
  adapter:
  - blank the marker cell (one step);
  - run the row on the now-delimited payload;
  - write the marker back (one step).

  An empty payload is then the empty word between two blanks. State the adapter once, as a
  private contract transformer, with its intermediate delimiter facts, and use it for the key
  comparison and the value copy.
- **Search:** for each entry, compare the key payload with tape `1` through the adapter (the
  framed `Turing.compareTM` contract, `Build/Contract/Catalog`, returning both heads). Skip the
  entry's two fields with `Turing.skipTM` on a mismatch. A comparison stops at the first
  differing cell, so each one costs at most a constant times that entry's key field (G162-17).
  The search is a loop over entries: use a phase loop (`Turing.phaseHostTM` with
  `Contract.inPhase`), or a round loop with `RoundContract`. Its end is the blank pair after the
  table (the seek family).
- **Lookup:**
  - on a match, copy the value payload to tape `2` through the adapter (`Turing.copyTM`'s
    contract), return to the origin, and exit;
  - at the end, write zeros over tape `2`'s word (a one-word sweep), return, and exit.
- **Assignment:**
  - on every match, copy tape `2` over the value payload through the adapter (same length), and
    continue to the end;
  - if nothing matched, append at the end: a separator, `true :: key` from tape `1`, a separator,
    `true :: value` from tape `2`. The writers are `Turing.writeConstTM` and `copyTM`. The cells
    beyond are blank by `KeyTableAt`.
  - Return to the origin (`Turing.tableRewindTM` or the seek family).

  The endpoint is `keyTableWrite d 0 o (keyAssign es k v)` (G162-18).
- **Layout lemmas:** read `TableAt`, `tableFields`, `tableOffset`, `joinFields` and `fieldsTape`
  through their published equations in `Build/Catalog` and `Build/RecordTable`. `TableWF` holds,
  because every field starts with its marker.
- **Not to cite:** `Turing.exists_tableFindTM`, `Turing.exists_tableAppendTM` and
  `RecordTable`'s other admitted rows; nor their private `rt_*` helpers, which cannot be cited
  anyway.

## Owned file

`TCSlib/Complexity/TuringMachine/Build/KeyTable.lean`. Statements byte-identical. Private helpers
before their first use. You may add imports of existing `Build/*` modules, each listed in
`REPORT.md` with its reason.

## Admitted dependencies allowed

The statements of `Build/WordArith` (job A), if you use a word row (for example
`Turing.exists_wordIntTM` with `c = 0` for the zeros). Nothing else.

## Downstream check

`Build/InputBit` does not import this file. Elaborate `RAMSimulation/Sim/*`,
`RAMSimulation/Simulation`, `RAMSimulation/Classes` and the facades.
