# The polynomial bounds' constructibility moves to `Constructible` (PR #175, an API gate): resolutions

**Gate, round 1:** the API gate of PR #175 (`lean/scp-constructible` at `6ae641a2`). Pack `pack.md`;
bundle SHA-256 `5d6800fd6ee38c9765b25e2b6b630c5a058bf677b04e1c6e1cc2fdd66236bde4` (52 sections),
the Lean at `6ae641a27333a177203b0b276afe392366dbf967`, the records at `9cb9c734`. **Staged
(2026-10-27); dispatched (user, 2026-10-27).** **Findings** (`findings.md`, verbatim, SHA-256
`6a183e38a3e71caffe866c0ff6a82f078045827f2fde18b241a37c3415d46fda`; received 2026-10-27): **FAIL,
0 blockers, 2 majors, 3 minors, 10 notes.** The move, the freeze, rule 10, the screen and the
integrity are confirmed (notes 6–14); both majors ask for the user's explicit acknowledgment of
duplication debt.

**The round-1 fix:** commit `00d5ff05` on #175 (`evidence/round1-fix/round1-fix.patch`), the campaign's
records merged in by `ca0eafb8` (no Lean change).

| # | Severity | Finding | Resolution |
|---|---|---|---|
| 1 | major | The new inline `logSpace n ≤ n + 1` re-derives `ARMWidth`'s public `logSpace_le_succ`; no explicit human acceptance of the new debt. | **True. Ruled (user, 2026-10-27): accepted as debt, retired in 12.2c** — `logSpace_le_succ` moves to `SpaceComplexity/Basic` and both inline steps re-point to it, batched with that window's replay (moving it now would replay `Basic`'s 114 downstream modules and edit a colleague's file). Recorded in the ledger (LS-1). |
| 2 | major | The PL-1/WT-1 census omits `WordTests`, whose `computesFunInTime_decideEq` is 1 of its 4 declarations (25%), and still points `hD'` at `Savitch:193`. | **True. Ruled (user, 2026-10-27): re-point `hD'` now, accept the rest.** Fixed in `00d5ff05`: `Constructible` imports `Build/WordTests` (one module more in its closure; the replay list is unchanged) and takes the empty-input decider from `computesFunInTime_decideEq []`; the inline conversion is gone. The ledger's census is corrected source-inclusively (`WordTests` 1 of 4, 25%) and the user's acceptance recorded; the `SAT`/`CookLevin` twins are re-pointed in 12.2c. |
| 3 | minor | "Every origin branch … exactly one file" overstates a 108-match tally over 111 refs. | **True; erratum.** The search per ref (`evidence/round1-fix/api-copy-search.txt`): at most one file on every ref — `Savitch` on 107, `Constructible` on this PR's branch, and neither on 3 older branches that predate both files. |
| 4 | minor | The replay driver returns success after a failed module. | **True; fixed** in the generator (`devtools/seyoon/mkreplay.py`): the script now exits 1 unless the log's last line is `# modules=<n> failed=0` and the static check reports no mismatch. Tested in isolation: a failed module and a static mismatch each give exit 1, a clean run exit 0. `replay-lscp2.sh` is generated with it. |
| 5 | minor | The two module docstrings keep campaign prose; `Savitch` lacks `## Main definitions`; the seal generator says "six" helpers. | **True; fixed** in `00d5ff05`: both module docstrings drop their phase, plan, gate and audit history, and four declaration docstrings drop audit and phase labels; `Savitch` gains `## Main definitions`; the policy linter now reports 0 findings on both files. The generator says "eight". Design-note references inside two inherited proof sketches (`P11`, `§12 R3`, `R8.5c`) stay for the deferred docstring cleanup. |
| 6 | note | Integrity and provenance pass. | Agreed. |
| 7 | note | The relocation and the three hunks reproduce exactly. | Agreed. |
| 8 | note | The home and its dependency cost check out. | Agreed; finding 2's import adds `Build/WordTests` (whose closure was already in) to `Constructible`'s closure. |
| 9 | note | No semantic weakening. | Agreed. |
| 10 | note | Boundary checks pass; optional sanity examples. | Agreed; no examples added (they would be new public text in a move PR). |
| 11 | note | The dominance step respects rule 10; the seal is consistent. | Agreed. Round 2's seal (the same 12 definitions, 3 erased) has 0 diagnostics at `00d5ff05`; the 15 controls' output is identical to round 1's. |
| 12 | note | The screens reproduce; they do not discharge the semantic debt. | Agreed; findings 1–2 dispose of it. |
| 13 | note | Elaboration attestations are consistent; the replay is a merge condition. | Agreed. `replay-lscp2` (53 modules, the fixed driver) is the merge evidence for the new head. |
| 14 | note | The lint claims are supported. | Agreed; at `00d5ff05` the campaign lint is the base's but for the two files' INFO lines, and the policy linter reports 0 findings. |
| 15 | note | The remaining `savitch` admission is not introduced here. | Agreed. |

**The replay:** `replay-lscp.sh` (`evidence/merged-tree/`), 53 modules, chained from
`oleans-lnfapi4`, pinning `Constructible` `791f3a48` and `Savitch` `6ea81136`; precheck passed.
**Running (user, 2026-10-27).**

**The replay, round 2:** `replay-lscp2.sh` (`evidence/round1-fix/`), the same 53 modules from
`oleans-lnfapi4`, pinning `Constructible` `9fb71337` and `Savitch` `b4157d58`, with the corrected
exit status; precheck passed. **Passed** (user, 2026-10-27): 53 of 53 at `ca0eafb8`, 0 failed,
static-equal (`evidence/round1-fix/replay-lscp2.log`, `replay-lscp2-static.txt`); snapshot `oleans-lscp2`.
(`replay-lscp` at round 1's head also passed, 53 of 53: `evidence/merged-tree/replay-lscp.log`.)

**Round 2** (`pack-r2.md`, at `ca0eafb8`): bundle SHA-256
`6a103efc595f514a33777ac0835101bd4c0dbb44dc9611d54a8d06b242e06d6a` (44 sections), the records at
`283e6549`. The screen at `ca0eafb8` (13 files) equals the base's: 848 declarations, 1,146 pairs.
**Staged; dispatched (user, 2026-10-28).** **Findings** (`findings-r2.md`, verbatim, SHA-256
`3f4f1b32834863902e500f1a3fc0d56291db6776664fd5e6c651b1372dbf85de`; received 2026-11-03): **PASS,
0 blockers, 0 majors, 1 minor, 11 notes.** The gate closes.

| # | Severity | Finding | Resolution |
|---|---|---|---|
| 1 | minor | "The 15 controls' output identical to round 1's" holds only after normalizing the diagnostic path: round 1's log prefixes each location with `probe/`. | **True; erratum** (`pack-r2.md`, the rule-10 attestation, and this file's finding 11): the round-2 controls' output equals round 1's after removing the `probe/` path prefix, goal texts, locations and exit status included. The dispatched pack is kept as dispatched. |
| 2 | note | Integrity and provenance pass. | Agreed. |
| 3 | note | The recorded rulings discharge both round-1 majors. | Agreed; the 12.2c dispositions (LS-1, PL-1) stand. |
| 4 | note | The re-pointed decider is exactly the former `hD'` contract; the import adds one module, no cycle. | Agreed. |
| 5 | note | The fix and the freeze reproduce. | Agreed. |
| 6 | note | The published-reading discipline holds; the seal is consistent. | Agreed. |
| 7 | note | The per-ref search supports "at most one file on every ref". | Agreed. |
| 8 | note | The driver propagates module and static failures. | Agreed; `replay-lscp2` passed (53 of 53, static-equal) at `ca0eafb8`. |
| 9 | note | The documentation repair is adequate; the deferred cleanup should also list `R8.4` and `Savitch`'s `§12 R1/R2`. | Agreed; both added to the deferred docstring cleanup's inventory (backlog). |
| 10 | note | Both screens reproduce. | Agreed. |
| 11 | note | No semantic weakening or new obstruction. | Agreed. |
| 12 | note | The gate does not certify merge readiness; keep the replay's evidence. | Agreed. Since round 2, `main` has been merged into the campaign (#179), so the merge needs a fresh merged-tree replay from `oleans-lm2c` (`replay-lscp3`).

**Merge state. #175: not yet clear to merge** (2026-11-03): gate 86 passed in round 2; it waits for
`replay-lscp3`, the merged-tree replay after #179 brought `main` into the campaign: head
`1cf3da65` (the campaign merged in), 69 modules from `oleans-lm2c` (16 of `main`'s, among them
`Randomized/Space*`, now downstream of `Constructible`), precheck passed; **not yet run**.
