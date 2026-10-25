# `spaceConstructible_poly` landed directly (PR #166, a maintainer landing): resolutions (round 1; PASS; gate CLOSED)

**Gate:** the gate of PR #166 (`lean/scp-landing` at `0282b487`, one commit on A1's head
`ae4849af`; stacked on #164). Pack `pack.md`; bundle SHA-256
`101d89d0a5111e7d622acccc6a21f45caa94e2ac1b67a0868ba558a6e8dbf71c` (68 sections; folder
`77-scp-landing-gate/`), built from the Lean files at `0282b4871fbdfdac744dc32f5ca18ed6015222ae`
and the records at `d01e302531c5429cabb7bb9b8e0daf52b9734fcf`. Dispatched before the replay.

**Round 1** (`findings.md`, verbatim; received 2026-10-25, SHA-256
`8bb5ecbaf341444c652af473718c380e99aa3a50ed29e3daf01bf26115a7aed3`): **PASS, 0 blockers, 0 majors,
1 minor, 15 notes. The gate is closed.** The maintainer checked the minor directly: true.

| # | Severity | Finding | Resolution |
|---|---|---|---|
| 1 | minor | The megafill D review's dossier (`out/04`, line 72) says "`exact?` finds nothing" of the tail-power inequality, the value split and the two arithmetic lemmas; no supplied probe poses `scp_value`, `scp_time_arith` or `scp_space_arith`. | **True; the omitted probes supplied.** `evidence/round1/SCPHelperDupProbe.*`: the three statements, verbatim from `Savitch.lean`, each posed to `exact?` against the landing's import closure (`oleans-lkit2`, the tree after #162): all three "could not close the goal". **Erratum to `out/04` line 72** (the review record is kept as written): the tail-power inequality was probed by the drafter's `SCPDupProbe`; the value split and the two arithmetic lemmas were not probed until this gate's probe, which finds nothing for them either. With the audit's source review, no published lemma states any of the eight helpers. |
| 16 | note | Complete A1's integrated replay, then the landing's downstream replay from that snapshot, before integration. | **Agreed;** these are #166's merge conditions (below). |
| 11, 15 | notes | The screen's scope (bodies of at least 60 characters); the audit did not re-elaborate. | **Agreed;** the semantic review (finding 12 and the probe above) covers the short helpers. |
| 12 | note | No new duplication; keep TC-1's cleanup commitment. | **Agreed;** TC-1 stands (the user's 12.2c window). |
| 2–10, 13, 14 | notes | Integrity; faithfulness; the helpers; adversarial inputs; the two arithmetic ledgers; rule 10; the overlay; the docstring; code identity and freeze; lint. | No action. |

**Merge state. #166: not yet clear to merge.** The gate is closed. #166 is stacked on #164
(A1): it waits for #164 to merge (A1's merged-tree replay first). Then it is retargeted to the
campaign branch, and its 2-module replay (`Savitch`, the `SpaceComplexity` facade) runs from A1's
snapshot.
