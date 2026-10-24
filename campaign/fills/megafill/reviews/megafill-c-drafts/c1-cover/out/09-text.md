# Check 9: text

## 100-column reflow

Lines over 100 characters (scripts: a per-line length scan of each file):

| File | Over 100 | Kind |
|---|---|---|
| `c1-fill-replaycanon.DRAFT.md` | line 1 (114) | the title, as in every model brief (`c1-fill-core-cont2.md` line 1 is 150) |
| `megafill-C.DRAFT.md` | line 1 (103); 62–65 | the title; the queue table's rows (tables are not reflowed; `megafill-A.md` and `-B.md` have the same) |
| C1 pre-ship `README.md` | 13–21 | the results table's rows |
| env `README.md` | 9–17 | the log table's rows |

Every prose line is at most 100 columns. PASS.

## Lean text the brief prescribes (public-facing rule)

- The recommended definitions' docstrings (lines 237, 246, 251): "One lockstep round: peel one
  record off each table, emit the key's three replay records."; "The table rewrite: find the
  `true` table, then `27 (n + 1)` lockstep rounds."; "Keep the header (doubled count, separator,
  unary initial state); rewrite the tables." No campaign label, path, date or narrative. PASS.
  `rc_widen` (235) has none, though the brief requires one for every new declaration (F5 adds
  one: "Insert the choice tape's field, no write and a right move, after a two-tape record's input
  move and work fields.").
- Region (c) (178–184) states the rule for the status paragraph and every new docstring
  (mathematical terms; no brief, gate, finding or escalation names; no dates; provenance in
  `REPORT.md`) and requires a literal `**Proof sketch.**` for proofs over 20 lines. PASS.
- The frozen docstring is the landed one (check 1); the report's suggestion of an
  `**Implementation.**` paragraph at integration is the maintainer's, outside the fill.

## Other text points

- Line 12 "(the cover's proposal)" and line 80's drafting note are drafting text (F6, F9).
- Line 150 and 312: "every declaration this brief cites" overstates the probe (F2).
- Lines 333–334 vs 186–187: rule 6 contradicts the frozen imports (F4).
RESULT: PASS, with the minors listed.
