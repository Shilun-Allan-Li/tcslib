# The phase host's field equations (PR #159, an API gate): resolutions (round 1; PASS; gate CLOSED)

**Gate:** the API gate of PR #159 (`lean/phasehost-fields` at `5e881c42`: `ef3440ee`, the two
equations in `Build/Seam`, and `5e881c42`, the 12 re-points, on the campaign branch at
`21d53053`). Pack `pack.md`; bundle SHA-256
`3a0f3880b35a17c2b0c4060b088d504bc9f89273dc705f0cf5f30c7afdfc3a51` (99 sections; folder
`71-phasehost-fields-api-gate/`), built from the Lean files at `5e881c42` and the records at
`eb0ae86e3da4f3de18ef90c323ea4b55da42889f`. Dispatched before the replay.

**Round 1** (`findings.md`, verbatim; received 2026-10-24, SHA-256
`503298349859faedf21c570b103a8f62efbe860e44563871e159323e6fb8ed4d`): **PASS, 0 blockers, 0 majors,
3 minors, 13 notes. The gate is closed.** The maintainer checked the three minors directly: all
true.

| # | Severity | Finding | Resolution |
|---|---|---|---|
| 1 | minor | `Inclusions`' census again omits its six anonymous private instances (4/70/74, not 4/64/68); fix the census tooling. | **True; erratum and tool fix.** As at gate 69 round 2, the 4/64 (68) counts are named declarations only; the full census is 4/70 (74), unchanged. `devtools/seyoon/declfreeze.py` and `privstmt.py` (v3) now count anonymous instances, keyed by their statements: on `Inclusions` at the base and the head they report 4/70 and 74. The shipped evidence stays as it was. |
| 2 | minor | `NDHost`'s header still says `phaseHostND_fixChoice` holds "by `rfl`", and its new field-by-field proof (about twenty lines) has no sketch. | **True; fixed.** Commit `26fd5afe` on #159, docstrings only: the header says the lemma holds through the phase host's field equations, and the lemma's docstring gains a **Proof sketch** (the start states, the table split on the redirect, the machine from its two fields). The code is identical with comments stripped; `NDHost` elaborates as before, plain and with `phaseHostTM` sealed (the stand-in method). A docstring-only change needs no gate; the replay pins the new blob. |
| 3 | minor | The dispatch named the records commit `eb0ae86e` and pointed to the bundle's README for the full hash, but the README is not a bundle section. | **True; records.** The README sits beside the bundle in the gate's folder and was not attached. The full records commit is `eb0ae86e3da4f3de18ef90c323ea4b55da42889f` (recorded above and in the folder's README). From now on dispatch prompts give both full hashes in the prompt. |
| 11 | note | The seal certifies the host-definition boundary, not general rule-10 compliance of the files (older configuration, action and step reductions remain). | **Agreed;** as disclosed in the pack. |
| 12, 16 | notes | The stand-in method leaves real-tree integration to the replay; record it before merging; if #158 merges first, merge the campaign in and replay `WindowClock`'s closure on the merged tree. | **Agreed.** #159's replay runs after #158 and #160 merge: the campaign branch is merged into #159 and the closure of every file changed since `oleans-lphl2` (#159's eight, #158's `WindowClock`, #160's `NDCodeSimulator` and `NTimeHierarchy`) replays from the latest merged-tree snapshot. |
| 14 | note | The unchanged text screen is not a proof of semantic duplication-freedom. | **Agreed.** |
| 4–10, 13, 15 | notes | Integrity and the freeze; the equations' faithfulness and completeness; boundary cases; the start-state, dispatch and table re-points; `NDHost`; axioms; lint. | No action. |

**Merge state. #159: clear to merge.** The gate is closed, the replay on the tree after #158 has
passed (below), and the base is the campaign branch.

**Replay plan, revised after #158 merged (2026-10-24):** the campaign branch merged into #159
cleanly (`e3767525`); `replay-lphf.sh` replays the eight files' downstream closure (88 modules,
`WindowClock` included) from `oleans-lf3c2`, the tree after #158. If #160 merges before #159, its
closure (`NDCodeSimulator`, `NTimeHierarchy`, two facades) replays on #159's merged tree from
`oleans-lphf`.

**Replay** (2026-10-24): `replay-lphf.sh` at `e3767525`, 88 modules from `oleans-lf3c2`. **Passed
(user): 88 of 88**, 0 failed, static-equal (52; `WindowClock`'s sorry gone with #158)
(`evidence/replay/`). On the new snapshot `oleans-lphf` (notes 12 and 16, the real tree):
`phaseHostTM_q₀` on no axioms, `phaseHostTM_tr_of_red_some` on `[propext]`,
`phaseHostND_fixChoice` on `[propext, Quot.sound]`, `exists_forwardLoopTM` and
`exists_polyCanonizer` on the standard three; `exists_uniformSimulator` keeps its `sorryAx`
(`PHFRealAx.*`).
