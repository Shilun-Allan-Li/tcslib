# The interpreter startup (PR #169, A+, an API gate): resolutions (round 1 FAIL; round 2 PASS; gate CLOSED)

**Gate:** the API gate of PR #169 (`lean/interpreter-startup` at `4bee8b09`). Pack `pack.md`;
bundle SHA-256 `e5fd8b80b595cbfa8bc89115f18c58971352634efef460d804c34c082955aeba` (61 sections),
the records at `7a1370d7`. **Round 1: FAIL, 0 blockers, 1 major, 2 minors, 8 notes**
(`findings.md`, verbatim). The audit found nothing to change in `Turing.exists_interpreterStartup`
or in the re-pointed core (notes 5–10).

**The user's rulings (2026-10-26):**
- finding 1: re-scope, with a non-vacuous probe, and record B5a's route;
- findings 2 and 3: fix both.

| # | Severity | Finding | Resolution |
|---|---|---|---|
| 1 | major | The B5a handoff at `p = 0` is not established. The consumer probe discards the roles, cut and fields, so it is vacuous. B5a's hosted verdict needs its `F.k` work tapes blank, which `p = 0` does not give. | **Re-scoped; the probe replaced; the route recorded.** <br>• **The claim withdrawn.** B5a does not cite the startup at `p = 0`. <br>• **The tape map.** Its loop `h1HostedVerdictTM F.k` (`CodeSimulator`, private) runs on `1 + (F.k + 2 + 1)` tapes from `vhostCfg (counterLoopCfg … d (bufferTape t.bits) 0) …` with `Rep M.tr (M.initCfg _) d`. The startup's roles supply the buffer (`jwin`, `x.take t`), the counter (`jctr`), the table (`jtbl`) and the summary (`jsm`). The `F.k` mirrored work tapes must be blank with their heads at `0`: **B5a reserves them as the startup's `p = F.k` passive tapes**, started blank, as the core reserves its four at `p = 4`. <br>• **The new probe** (`evidence/round2/B5aConsumerProbe2.lean.txt`): `b5aP_startup` instantiates the startup at `p = F.k` from all-blank tapes with B5a's installer. It **keeps every clause**: the roles and their ten separation facts, the first arrival at `done`, and the threshold fields. It adds that the `F.k` reserved tapes come out blank with their heads at `0`, which is the hosted loop's bank precondition. Against `oleans-la1m`: 0 errors, on the standard three axioms. <br>• **The junction** (the embedded threshold as that `vhostCfg` with the `Rep`) reads `CodeSimulator`'s private loop lemmas. It is recorded for B5a's brief, whose pre-ship proves it in a `CodeSimulator` overlay before B5a issues (`campaign/items/b5a/A-plus-startup-design.md`, "As built"). <br>• **The startup's statement is unchanged**, as the audit recommends. |
| 2 | minor | The core's Implementation paragraph says "every head at `0`"; the startup states only the role and passive heads; the design note's sketch promises more. | **Fixed.** `df992ad7` on #169, docstring only (`evidence/round2/df992ad7-docstring.patch`; code identical with comments stripped): the threshold leaves the role and passive heads at `0`, and the other tapes are internal scratch with no stated contents, which the loop's embedding leaves aside. The design note now records the departures: the serialization word, the role-and-passive endpoint, the core at `p = 4`, and B5a at `p = F.k`. |
| 3 | minor | The bundle lacked the core seal's source or recipe and five screen-population files (`ExhaustiveReplay`, `UniversalStartup`, `Build/Primitives`, `Codec/Parse`, `Logspace/PathWalk`). | **Fixed in round 2's bundle.** It carries: <br>• the core seal's exact sources: round 1's (`NDCSSealCat-round1.lean.txt`), and the head's (`NDCSSealCat.lean.txt`, 0 errors, the standard three); <br>• their recipe, `mksealcat.py.txt` with `c2seal-block.lean.txt` (gate 66's 46 `local irreducible` attributes and its `-simp` line, inserted after the core's `namespace Turing` in the elaboration recipe's `NDCSCat` file). Applied to round 1's `NDCSCat`, it reproduces round 1's source byte for byte; <br>• all 18 screen-population files. |
| 4–11 | notes | Integrity; the startup's guarantees and boundary cases; the layout and the serialization boundary; the time ledger; the core's re-proof; the seal; the screen; the elaboration and lint records. | No action. Note 6's "consumers must reserve any additional clean tapes explicitly" is now the design note's rule. Note 11's replay is #169's merge condition. |

**Round 2** audits the probe, the recorded route, the docstring fix and the completed bundle
(`pack-r2.md`).

## Round 2: PASS, 0 blockers, 0 majors, 0 minors, 9 notes; gate CLOSED

Pack `pack-r2.md`; bundle SHA-256 `854dddc5cc4d6c97cdcfd0b9919ec07acb0c2dcf99d76e8e18cbc28a7005f0c9`
(86 sections), the Lean at `df992ad7`, the records at `e259de60` (`findings-r2.md`, verbatim).

| # | Severity | Finding | Resolution |
|---|---|---|---|
| 3 | note | The tape map is consistent and `p = F.k` supplies the missing bank; the junction stays a B5a pre-ship obligation, and its acceptance argument must also bridge the window `x.take t` to `x`. | **Agreed; recorded** in the design note's "As built" for B5a's brief (the window bridge, as the B5a review records). |
| 1, 2, 4–9 | notes | Integrity; the probe non-vacuous; the docstring fix; the seal recipe reproducible; the semantic comparison now complete, with no new family; no regression; the contract and ledger; the attestations. | No action. |

**Merged (user, 2026-10-27)** as `94296486577d65204eedf41f3d73c3c82e61284f`. The campaign's TCSlib
tree after the merge equals the replayed head `9d0af8cb`'s, so `oleans-laplusm` is the campaign's
snapshot after #169. Before the merge: **#169: clear to merge** (2026-10-27). `replay-laplusm` passed (user, 2026-10-27): 5 of
5 modules, static-equal (0 mismatches; `NTimeHierarchy`'s one sorry is `ntime_hierarchy`; the kit
and `NDCodeSimulator` sorry-free; `evidence/merged-tree/replay-laplusm.log`, `-static.txt`) at the
head `9d0af8cb`, whose base is the campaign branch; the campaign's Lean has not moved since #168's
merge. Its snapshot is `oleans-laplusm`. The combined screen below finds no new pair. Before the
replay: the gate is closed. Its 5-module replay (the kit,
`NDCodeSimulator`, `NTimeHierarchy` and the two facades) chains after #166's and #168's, from the
snapshot the last of them leaves, after the campaign is merged in.
**#168 merged (2026-10-26).** The campaign is merged into #169 (head
`9d0af8cb3f72d6ee4fc7c76309d32215c694233d`; its two files keep the gated blobs `84c00e33` and
`baf1b454`). `replay-laplusm` (`evidence/merged-tree/`), 5 modules chained from `oleans-lu2m`, is
written; its precheck passed. Since #168 changed `UniversalK`, a population file, the screen is
re-run on the merged head and on the campaign tip after #168 (`13120e00`), and diffed by name
against both and round 1's screens.
**The combined screen** (`evidence/merged-tree/`, the 18-file population; about 12 minutes
each, peak 6.1 GB): the merged head `9d0af8cb` has 984 declarations and 605 pairs; the tip after
#168 has 983 and 603. **No pair at the merged head is new** against the union of the tip's and
round 1's two screens (`pairdiff-merged-head-vs-all.txt`). Against the tip alone, the only new
pairs are round 1's two inherited idiom pairs (`pairdiff-merged-head-vs-tip.txt`). No pair
joins the startup to U2's new privates. **Disclosed:** U2 itself adds 7 pairs against round 1's
base (`pairdiff-tip-vs-gate79-base.txt`). Five are gate 80's in-file pairs. Two are
cross-file pairs that gate 80's population (without `Build/SeamLayout`) did not show:
`uk_header_run` (74%) and `uk_suffixStartup_run` (59%) reproduce `SeamLayout`'s private
`sl_rewrap`, the five-field `Cfg.ext` rewrap. That is the idiom of round 1's `252/322` pair,
which round 1 (note 10) and round 2 (note 6) accepted. Both are below 90%, and no ledger family
is opened. A public rewrap lemma would serve all three; it is a candidate for the dedup window.
