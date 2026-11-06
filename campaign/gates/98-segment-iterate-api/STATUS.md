# Gate 98 (G5's iteration API: `Turing.Segment.iterate_seq`)

- 2026-11-05: G5's plan §8, Q2 ruled **API first** (the user). Branch `lean/segment-iterate`:
  `Segment.iterate_seq` in `Build/Contract/Basic`, with `Round.iterate_seq` re-proved as its
  corollary. #202 opened at `f0b31bb9` (on the campaign at `3a8c6199`).
- 2026-11-05: #196 merged; the campaign merged into the branch (`7b5774fb`, no change to the PR's
  file). `replay-lsi2` written on the merged tree: the closure of `Contract/Basic`, 112 modules,
  chained from `oleans-ldwa3`, precheck passed.
- 2026-11-05: the seal (4 definitions, 8 controls), axioms, freeze, names (354 refs), the sweep and
  lint are in `evidence/`. The pack is drafted; its screen and replay fields are filled when those
  runs end.
- 2026-11-06: `replay-lsi2` passed (112 modules, 0 failed; static 0 mismatches, the existing 45
  `sorry`s). The seal and axiom probes re-run on `oleans-lsi2` give identical outputs. The screen
  (17 files) is identical at base and head (0 new, 0 gone). The pack is complete; the gate is
  staged.
