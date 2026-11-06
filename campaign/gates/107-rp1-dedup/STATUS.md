# Gate 107 (#216, the dedup window's RP-1, widened)

- 2026-11-06: the change `f200144b` (a sub-agent; 14 files, 24 bodies), #216 opened. The exhaustive
  rule-10 check (52 sealed probes) in `evidence/rule10/`. `replay-lrp1` running. The policy linter
  finds one new item, `cl_iff` at 21 lines without a sketch: to fix after the replay.
- 2026-11-06: `cl_iff`'s sketch (`3d0f6ceb`); the campaign merged at `485cfbab` (after #208, #212, #213). `replay-lrp3` from `oleans-lcamp2`: 53 modules, 0 failed. Freeze and lint regenerated at the merged head; pack written; staged.
- 2026-11-06: **dispatched** by the user (57 sections, bundle `e10d6e0d…`).
