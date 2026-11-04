# Four space facts out of `Machines/ARMWidth` (PR #181, an API gate): resolutions

**Gate, round 1:** the API gate of PR #181 (`lean/logspace-move` at `50adf098`). Pack `pack.md`.
**Ruled (user, 2026-11-04):** `logSpace_le_succ` moves to `SpaceComplexity/Basic` before H's brief
issues (instead of a fifth `ARMWidth` import into `Hierarchy`, or a new LS-1 copy), and with it
`LOGSPACE_subset_PSPACE`, `SPACE_succ_pow_subset_PSPACE` (to `SpaceClasses`) and
`logSpace_le_of_le_mul_two_pow` (to `Basic`). Bundle SHA-256
`29d886fbc4dc744c213d2a6e1645de8487e15461990aff3b08293a989aa23d16` (93 sections), the Lean at
`50adf098dc94d2d4fed3eb6c46c0263c502fd975`, the records at `bf117a80`. **Staged (2026-11-04); dispatched
(user, 2026-11-04).** **Findings** (`findings.md`, verbatim, SHA-256
`cf95cf1912bb4f90c16d34ef1c89756d91de4554408df982deeac152ce941eb2`; received 2026-11-04): **OPEN, 0
blockers, 1 major, 1 minor, 6 notes.**

| # | Severity | Finding | Resolution |
|---|---|---|---|
| 1 | major | LS-1 is not fully retired: `narm_decides` (`Machines/NARMProof`) and `narm_logspace_ptm` (`Machines/NARMLogspace`) still re-derive `logSpace n ≤ n + 1` inline, outside the acknowledged scope. | **True; fixed in round 2** (`1d1247a3`, head `5de52d9a`). Both proofs now cite `logSpace_le_succ`; the two files are Hydroxyi's, and the re-point is a mechanical ARM dedup edit (standing exception, FYI). The two elaborate with 0 diagnostics against `oleans-lsm1` (`evidence/round2/elab/`). The freeze shows exactly those two body changes (`round2/freeze/`). The screen population adds `NARMLogspace` (15 files, `round2/screen/`). A search of the round-2 head (`round2/ls1-search/`) finds the fact stated only in `Basic`. The three remaining hits are different facts: `BPLInP`'s bit-length bound, and the polylog bounds of `ImplicitPoly` and `PreimageHost`. The ledger's LS-1 entry records the corrected scope; **LS-1 is retired when #181 merges.** |
| 2 | minor | `screen-base.status` names `wt-edis` at `2219912d`, not the pack's `711f5444`. | **True; documented and re-run.** `2219912d` is a local pre-ship commit of E-D's overlay on that tree, and all 14 population blobs are equal at the two commits (`round2/screen/round1-base-provenance.txt`). Round 2's base screen runs on a frozen export of `711f5444` itself. |
| 3 | note | Bundle and declared changes authenticated. | Agreed. |
| 4 | note | No weakening; boundary cases checked. | Agreed; the positivity hypothesis `1 ≤ s` and the padded bounds are kept. |
| 5 | note | Homes, imports, consumers and the all-ref search check out. | Agreed. |
| 6 | note | The rule-10 probes support the scoped claims; the linear probe seals only `logSpace`. | Agreed; the pack's wording keeps that scope. |
| 7 | note | Screen and lint reproduce, subject to 1–2. | Agreed; see 1 and 2. |
| 8 | note | The execution evidence is consistent, but supplied rather than re-executed. | Agreed. |

**The replay:** `replay-lsm1.sh` (`evidence/merged-tree/`), 137 modules from `oleans-leqc3`,
pinning the four blobs; precheck passed. **Passed** (user, 2026-11-04): 137 of 137 at `50adf098`,
0 failed, static-equal; snapshot `oleans-lsm1`.

**Merge state. #181: not yet clear to merge** (2026-11-04): the replay passed; it waits for gate 89.

**Round 2 staged (2026-11-04):** `pack-r2.md`, at #181's head `5de52d9a` (the fix `1d1247a3`). Bundle
SHA-256 `88447a4c6de8012e3ed0c5eecddff6fd23c391c727af5bd730257b93b81397e6` (114 sections), the
records at `a47a9a90`. **Dispatched (user, 2026-11-04).**
- **The screen:** 15 files, base a `git archive` export of `711f5444`. 87 → 87 declarations,
  23 → 23 pairs, none new or gone.
- **The replay:** `replay-lsm2` (137 modules from `oleans-leqc3`, six blobs pinned) **passed** (user,
  2026-11-04): 137 of 137 at `5de52d9a`, 0 failed, static-equal (40, all pre-existing); snapshot
  `oleans-lsm2` (`evidence/round2/merged-tree/`).

**Round 2** (`pack-r2.md`, head `5de52d9a`). **Findings** (`findings-r2.md`, verbatim, SHA-256
`0affabd012805818bcc0bbaab77153a0c9a538e474caf04e185b2f4f2636c557`; received 2026-11-04): **OPEN, 0
blockers, 1 major, 0 minors, 7 notes.**

| # | Severity | Finding | Resolution |
|---|---|---|---|
| 1 | major | LS-1 is still not retired. `ImplicitPoly`'s `hWle` and `PreimageHost`'s inner `.trans` step each re-prove the logarithm's form of `logSpace m ≤ m + 1`; round 2's search had classed them as different polylogarithmic facts. | **True; fixed in round 3** (`8d41671c`, head `b8add1ac`). Both steps cite `logSpace_le_succ` through `logSpace_eq`, and both files elaborate with 0 diagnostics against `oleans-lsm2` (`evidence/round3/elab/`). `ImplicitPoly` is Hydroxyi's, an ARM-program file, so its re-point is the standing mechanical dedup exception (FYI); `PreimageHost` is the campaign's. The freeze shows exactly the two authorized bodies changed (`round3/freeze/`). A new search classifies every `Nat.log_le_self` use and every `logSpace`-by-successor statement (`round3/ls1-search/classification.md`): the fact is proved once, in `Basic`, and cited at eight sites. The screen covers 17 files with the two added (`round3/screen/`): 124 → 124 declarations, 23 → 23 pairs, none new or gone. The ledger records the corrected scope. |
| 2–8 | note | Provenance, the round-2 replacements, the baseline rerun, screen and lint reproduction, homes, meaning and execution evidence. | Agreed. On note 4, `NARMLogspace`'s missing `Main definitions` heading predates #181; it is in the deferred docstring cleanup. On note 8, `replay-lsm2` passed (above) but is superseded by round 3's `replay-lsm3`. |

**Round 3 staged (2026-11-04):** `pack-r3.md`, at #181's head `b8add1ac`. Bundle SHA-256
`763bee495a3bb520a2d0447b411c310f3d656e406966593c0338984820d509ec` (140 sections), the records at
`04d2123a`. **Dispatched (user, 2026-11-04); `replay-lsm3` running.** `replay-lsm3` is written
(137 modules from `oleans-leqc3`, eight blobs pinned; precheck passed); not yet run.
