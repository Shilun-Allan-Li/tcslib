# Gate 146 resolutions

Round 1 CLEAR: 0 blockers, 0 majors, 1 minor, 7 notes (`findings.md`, verbatim).

- **G146-01 (minor), fixed in records (erratum; the dispatched pack is preserved verbatim).**
  `pack.md`'s scope paragraph says "the measurement came out at −295 lines". That figure is the
  first head's (`e73b59f9`, +125/−420). The audited head `2dc0fc30` is **−297** (+130/−427), as
  the pack's §Changes, the refactor plan, the ledger and the PR say. Only the scope line is stale.
- **G146-N7 (note), merge conditions.** These are acknowledged and recorded in `STATUS.md`:
  1. #334 (gate 145) merges first.
  2. Seyoon confirms Hardness's new `ClassP/BinaryArith/Iterate` import.
  3. #335 is retargeted to `complexity/arora-barak-ch3-4`.
  4. The merged-tree replay is run on the retargeted PR.
- Notes N1–N6: no action.
