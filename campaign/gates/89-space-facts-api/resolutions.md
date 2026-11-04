# Four space facts out of `Machines/ARMWidth` (PR #181, an API gate): resolutions

**Gate, round 1:** the API gate of PR #181 (`lean/logspace-move` at `50adf098`). Pack `pack.md`.
**Ruled (user, 2026-11-04):** `logSpace_le_succ` moves to `SpaceComplexity/Basic` before H's brief
issues (instead of a fifth `ARMWidth` import into `Hierarchy`, or a new LS-1 copy), and with it
`LOGSPACE_subset_PSPACE`, `SPACE_succ_pow_subset_PSPACE` (to `SpaceClasses`) and
`logSpace_le_of_le_mul_two_pow` (to `Basic`). Bundle SHA-256
`29d886fbc4dc744c213d2a6e1645de8487e15461990aff3b08293a989aa23d16` (93 sections), the Lean at
`50adf098dc94d2d4fed3eb6c46c0263c502fd975`, the records at `bf117a80`. **Staged (2026-11-04)**; not yet
dispatched. Findings: pending.

**The replay:** `replay-lsm1.sh` (`evidence/merged-tree/`), 137 modules from `oleans-leqc3`,
pinning the four blobs; precheck passed. **Passed** (user, 2026-11-04): 137 of 137 at `50adf098`,
0 failed, static-equal; snapshot `oleans-lsm1`.

**Merge state. #181: not yet clear to merge** (2026-11-04): the replay passed; it waits for gate 89.
