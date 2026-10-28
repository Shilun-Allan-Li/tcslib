# `NP` is closed downward under `≤ₚ` (PR #177, an API gate): resolutions

**Gate, round 1:** the API gate of PR #177 (`lean/np-closure` at `ce00b6d3`). Pack `pack.md`; bundle
SHA-256 `4ccd459ec5da8f5ec44228cf7b230b473b151328763e5e1681e8a8919677632b` (37 sections), the Lean at
`ce00b6d3d7ca57501bf66eb949a05b90d90f0452`, the records at `c63f9dce`. **Staged (2026-10-27); not yet
dispatched.** Findings: pending.

**The replay:** `replay-lnpc.sh` (`evidence/merged-tree/`), 86 modules from `oleans-lnfapi4`, pinning
`Reductions` `b5bfef1c`; precheck passed. **Not yet run.** Its closure overlaps #175's; whichever of
the two merges second takes a merged-tree replay of the overlap.

**Merge state. #177: not yet clear to merge** (2026-10-27): it waits for gate 88 and `replay-lnpc`.
