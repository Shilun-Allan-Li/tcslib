# Abstract register machines: step equations and block embedding (PR #182, an API gate): resolutions

**Gate, round 1:** the API gate of PR #182 (`lean/arm-embed` at `8fd6f91a`). Pack `pack.md`.
**Ruled (user, 2026-11-04):** the general `savitch` reuses Hydroxyi's Savitch search unchanged through
a generic block embedding, instead of restating the search for any containing program. The lemmas
sit beside the definitions they read, in his `Machines` and `SavitchARM` files: additive, and FYI
only, the user's to send. The design is
`campaign/items/ch34/savitch-general/SAVITCH-deepening-design.md`. Bundle SHA-256
`e253274fec7dbdc422563b96b501f3208909763e07894ef06c89a85827567819` (90 sections), the Lean at
`8fd6f91a270f497a872146765cfab8422c3faf8e`, the records at `415fe4ee`. **Staged (2026-11-04); dispatched
(user, 2026-11-04).** **Findings** (`findings.md`, verbatim, SHA-256
`b6b896a09cf95cb2035b774ce725620a5c5aa6666938ace08de9420cca0b1729`; received 2026-11-04): **PASS, 0
blockers, 0 majors, 3 minors, 9 notes.** The gate closes.

| # | Severity | Finding | Resolution |
|---|---|---|---|
| 1 | minor | `astep_embed`'s call case passes the core definition `Function.comp` to `dsimp only`. Rule 10's scope (2026-10-23) lets core definitions reduce in `rfl`, `decide` or `show`, never through `simp`/`dsimp`/`rw`/`unfold`. | **True.** It is a one-line change to `simp only [Function.comp_apply]` (or a `show`). It changes `ARMProof`'s blob, so `replay-larm` would no longer certify #182. **Ruled (user, 2026-11-04): fix now.** **Fixed** by `94093275` on #182, with `simp only [Function.comp_apply]`. `ARMProof` elaborates with 0 diagnostics, its regenerated sealed copy too, and the policy linter reports 0 findings (`evidence/round1-fix/*minor1*`). The fixed head needs a new replay. **Ruled (user, 2026-11-04): #181 merges first**; #182 then takes one merged-tree replay from `oleans-lsm2`, covering the fix and the overlap. |
| 2 | minor | The evidence was out of step with the head: `ARMProofSealed` lacked `astep_embed`'s proof sketch, the head lint log named `0614b077` (`ARMProof` 503 lines, not 509), and the seal union has 14 definitions, not 15. | **True; refreshed.** `evidence/round1-fix/` has `ARMProofSealed` regenerated at the head (it differs from the shipped one only by the six-line sketch comment) and elaborated, 0 diagnostics. The lint was re-run at `8fd6f91a` (0 FAIL, 83 WARN; `ARMProof` 509 lines). The union is **14 definitions**: `RegExt` left it when it became a structure, and the controls are 14 delta and 2 equation controls (16). The shipped evidence is kept as dispatched. |
| 3 | minor | AS-1 omits three older specializations of `astep_call` (`AdjScan.astep_rd`, `AdjWalk.astep_call₁`, `astep_call₂`), and `LogspaceUniformWalk` is not in the screen. | **True; recorded.** AS-1 now has six members (the ledger). The screen re-run with `LogspaceUniformWalk` (`evidence/round1-fix/screen-*`) gives 170 → 179 declarations, 46 → 46 pairs and 18,834 characters both times, with identical pair lists, as the auditor found. |
| 4–7 | note | Provenance, freeze, census, lint, names and the equations' and definitions' meanings check out. | Agreed. |
| 8 | note | `AReach` does not assert the guard at its endpoint: a consumer establishes its continuation's guard at the exit. | Agreed; the deepening fill's brief says so. |
| 9 | note | The degenerate cases (empty source register set, aliased registers, malformed input) support the hypotheses. | Agreed. |
| 10 | note | Apart from minor 1, no new proof unfolds an imported TCSlib definition. | Agreed. |
| 11 | note | `EmbedFit`'s two exits coincide; a consumer with distinct exits is optional. | Agreed. The deepening fill's pre-ship probes it with distinct exits. |
| 12 | note | The replay was outstanding at the audit. | `replay-larm` passed (above). Whichever of #181 and #182 merges second takes a merged-tree replay of the overlap. |

**The replay:** `replay-larm.sh` (`evidence/merged-tree/`), 138 modules from `oleans-leqc3`, pinning
the five blobs; precheck passed. **Passed** (user, 2026-11-04): 138 of 138 at `8fd6f91a`, 0 failed; the static sorry
check equal (22, all pre-existing); snapshot `oleans-larm` (`evidence/merged-tree/replay-larm.log`,
`replay-larm-static.txt`).

**Merged-tree replay after #181 (2026-11-04):** the campaign merged into #182 (`a199760e`;
`ARMProof` auto-merged with #181's edit to `arm_decides`). `replay-larm2` **passed**: 138 of 138,
0 failed, static-equal (22 sorry warnings, all pre-existing), chained from `oleans-lsm5`; snapshot
`oleans-larm2` (`evidence/merged-tree-larm2/`). **#182 is clear to merge.**
