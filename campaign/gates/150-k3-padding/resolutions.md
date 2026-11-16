# Gate 150 resolutions

Round 1 CLEAR: 0 blockers, 0 majors, 0 minors, 5 notes (`findings.md`, verbatim).

- Notes N1–N5: no action. The remaining private adapter/host twins stay carried with kind 6, as
  recorded (N5).
- **Merge condition.** The gate's replay is already the merged-tree replay: it ran against the
  campaign tip `70adbe56` (campaign Lean `c01114e7`, the #342 merge), and the campaign's Lean has
  not changed since. Its output `oleans-cl150-cc011` becomes the snapshot when #343 merges
  unchanged. #344 (gate 151) touches a disjoint file. If #344 merges first, #343 needs a fresh
  merged-tree replay, because both closures contain the 3 modules downstream of ExhaustiveReplay.
  **Clear to merge: #343.**
