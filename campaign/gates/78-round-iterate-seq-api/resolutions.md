# Round iteration along a sequence (PR #167, an API gate): resolutions (round 1; PASS; gate CLOSED)

**Gate:** the API gate of PR #167 (`lean/round-iterate-seq` at `b768859d`, one commit on #165's
merged head `308838e5`; stacked on #165). Pack `pack.md`; bundle SHA-256
`1065b0044ec299ffb22c60f477dab1c37b7e80e14416ef651888302b5bbe13c8` (40 sections; folder
`78-round-iterate-seq-api-gate/`), built from the Lean files at
`b768859d58d59a0952cf340439cba91740c95084` and the records at
`90d4ee727dea9b7d7f8a119167dfaeb394a504bc`. Dispatched before the replay.

**Round 1** (`findings.md`, verbatim; received 2026-10-25, SHA-256
`fbedd9c38b79580bc1a9fc3dc0de1182697bb8de712bed2d3609ced68a71d9ce`): **PASS, 0 blockers, 0 majors,
3 minors, 10 notes. The gate is closed.** The maintainer checked the three minors directly: all
true.

| # | Severity | Finding | Resolution |
|---|---|---|---|
| 1 | minor | `Round.iterate_seq`'s docstring (and `Round.iterate`'s) omits the hypotheses `some a ∉ E` and `P` at the start. | **True; fixed** by commit `98d56a71` on #167, docstrings only (`evidence/round1-fix/docfix.patch`). Both docstrings now open with "if the anchor is not an escape (`some a ∉ E`), the head condition `P` holds at …". The code is identical with comments stripped (`codeonly-docfix.txt`), and `Contract/Basic` elaborates with no diagnostic (`ContractBasic-docfix-ax.out`). Docstring-only changes need no gate. |
| 2 | minor | `declfreeze.py` keys declarations by short name and collapses same-named declarations in different namespaces: 78 → 79 instead of 84 → 85. | **True; the tool fixed** (`devtools/seyoon/declfreeze.py` v4, on the campaign branch). It tracks `namespace`, `section` and `end` and keys each declaration by its qualified name, adding `#k` for a name still not unique. The authorized list accepts qualified or short names, so older recipes still work. **Regenerated:** `evidence/round1-fix/freeze-v4-*.txt` gives `Contract/Basic` 84 → 85 public, 1 → 1 private, `Turing.Round.iterate_seq` added, and the one authorized body change `Turing.Round.iterate`. `ZoneRebalance` gives 18 → 18 and 853 → 853, the one changed private being `Turing.zr_pinLoop`. Regression check: gate 77's Savitch freeze has the same counts under v4, with qualified names. **Earlier freezes:** v3 kept only the last declaration of each colliding short name, on both sides. So in a file with colliding names, an earlier freeze compared only the last namesake, and a change to another namesake would not have been reported. Re-running v4 over the past gates' freeze pairs is in the backlog (`campaign/backlog.md`, FRZ-1). |
| 3 | minor | The pack says `oleans-lkit2`'s `ZoneRebalance` is the PR base's; it is the pre-G4 (sorried) version. | **True; erratum** (the dispatched pack is kept). **Erratum to the pack's elaboration attestation:** `oleans-lkit2` is the campaign's tree after #162. Its `Contract/Basic` is the PR base's, but its `ZoneRebalance` is the pre-#165 module (blob `1abbb871`, rows sorried). The overlay check elaborates the head's `ZoneRebalance` source against its imports and does not import the old module, so the result stands. The 91-module replay, chained from #165's merged-tree snapshot, is the check against the real base. |
| 10 | note | The 279-ref name search has no supplied output. | **Agreed; supplied:** `evidence/round1-fix/name-search-iterate_seq.txt` lists the command, the 284 refs searched now, and the hits, which are only #167's own branch (local and remote). |
| 13 | note | Complete #165's merged-tree replay and then the 91-module replay before merge clearance. | **Agreed;** these are #167's merge conditions (below). |
| 8 | note | The seal's control maps describe the pre-overlay file; add 28 to their lines. | **Agreed;** noted here. |
| 4–7, 9, 11, 12 | notes | Integrity; faithfulness; boundary cases; the consumers; the screen; the elaboration and axioms; lint. | No action. RI-1 retires when #167 lands. |

**Merged (user, 2026-10-26)** as `4c8c2e7e9ac3c0bd063cb3df074558de073bf7bf`. The campaign's TCSlib
tree after the merge equals the replayed head `508e0eab`'s, so `oleans-lriseqm` is the campaign's
snapshot after #167. RI-1 is retired (`campaign/duplication-ledger.md`). Before the merge:
**#167: clear to merge** (2026-10-26). `replay-lriseqm` passed (user, 2026-10-26): 91
of 91 modules, static-equal (0 mismatches, 49 in total; `evidence/merged-tree/replay-lriseqm.log`,
`-static.txt`) at the head `508e0eab`, whose base is the campaign branch; the campaign's Lean has
not moved since #164's merge. Its snapshot is `oleans-lriseqm`. Before the replay: the gate was closed. #165 merged (2026-10-26), and
#167 is retargeted to the campaign branch (head `98d56a71`; its diff is its two files). #164 (A1)
goes first. Then the campaign is merged into #167, and its 91-module replay runs from A1's snapshot
`oleans-la1m`. A trial merge on A1's tree gave the same 91-module list.
**#164 merged (2026-10-26, `c4ba87bf`).** The campaign is merged into #167 (head
`508e0eab1f82ae6edbc9ddb6c6a90de60e4b2f65`; its two files keep the gated head's blobs).
`replay-lriseqm` (`evidence/merged-tree/`) replays their downstream closure, 91 modules, chained
from `oleans-la1m`; its precheck passed. Its closure contains #166's, #168's and #169's, so their
replays chain after it.
