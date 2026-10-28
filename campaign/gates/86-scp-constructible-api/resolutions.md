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

**Merge state. #175: not yet clear to merge** (2026-10-27): it waits for gate 86's round 2 and
`replay-lscp2` (`replay-lscp`, at round 1's head, no longer certifies the PR).
