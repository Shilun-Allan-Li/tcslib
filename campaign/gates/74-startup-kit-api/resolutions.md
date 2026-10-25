# Gate 74 (#162, the startup kit), round 1: resolutions

The findings (`findings.md`, verbatim): **FAIL, 0 blockers, 1 major, 1 minor, 11 notes.** The
maintainer checked the major and the minor directly: both true. **The user ruled (2026-10-25):
re-point in round 2** (not an acknowledgment of the 2/9 census). Round 2's fix is one commit on
#162, `f8860243` (`evidence/round1-fix/gate74-fix.patch`).

| # | Severity | Finding | Resolution |
|---|---|---|---|
| 1 | major | The cumulative census omits the new module: the kit's 2 of 9 declarations are copy-family members (SK-1's `embedSilentCfg_initCfg`, SD-1's private `is_input_suffix`), past the one-fifth rule, and the ledger does not record it. | **True; fixed by eliminating the member.** `is_input_suffix` has exactly the statement and proof of `Turing.pairEncode_drop`, public in `Build/InputDevice` since #161 merged (SD-1's recorded disposition was this re-point once #161 landed). Round 2: the kit imports `Build/InputDevice` (acyclic: it imports neither the kit nor anything that sees it), deletes the private, and the window call cites `pairEncode_drop`. The kit is now 8 public declarations, 0 private; its census is 1 of 8 (12.5%), SK-1's public member. The ledger (`campaign/duplication-ledger.md`): SD-1's `NDCodeSimulator` member retired, its census without `NDCodeSimulator` and the kit; SK-1's census on both sides (the kit 1/8, 40 lines; `UniversalK` 1/51, 39 lines) and the round-1 crossing recorded. |
| 2 | minor | The timing prose should distinguish the seam's dispatch step and a halting bound from a total and an exact first halt. | **True; fixed** (docstrings only). `seamCompTM_step`: "the endpoint and its control state, reached after the two runs and one additional dispatch transition (at time `T₁ + 1 + T₂`)"; the module's main results line likewise. `prefixCanon_pairExtract_halt`: "has halted at the suffix with its selected component by the common bound". |
| 3–11, 13 | notes | Provenance; the harvest and freeze; the header and capture contracts; the composition contracts; the window and layout; boundary checks; rule 10; placement; the screens; lint. | No action. |
| 12 | note | Keep the post-#161 replay obligation and record its exact-head result. | **Agreed.** Round 1's head merged the campaign after #161 (`e984516b`), and `replay-lkit` passed there (5 of 5; `evidence/replay/`). Round 2's head `d4759581` (the fix and a records-only merge) is replayed again (`replay-lkit2`, the same five modules): **passed**, 5 of 5, 0 failed, the static sorry count 1 (`ntime_hierarchy`) with no mismatch (`evidence/round1-fix/replay-lkit2.log`, `-static.txt`; the snapshot `oleans-lkit2`). |

**Round 2's checks** (`evidence/round1-fix/`), against `oleans-lu2api` (the tree after #161): the
kit with no diagnostic; `NDCodeSimulator` and `NTimeHierarchy` checked after the kit's text with
the imports merged: no diagnostic, and only `ntime_hierarchy`'s sorry warning (so `InputDevice`'s
names clash with nothing downstream); the seal re-run: its only errors are the 22 controls at its
top, which close unsealed; the axioms unchanged (`seamCompTM_step` on `[propext, Quot.sound]`, the
rest on the standard three). The freeze against round 1's head: 8 → 8 public, 1 → 0 private
(`is_input_suffix` removed); no statement changed; bodies or docstrings changed:
`exists_windowCall` (the re-point), `seamCompTM_step` and `prefixCanon_pairExtract_halt`
(docstrings). Lint: `TuringMachine` 0 FAIL, no added line over 100 characters. The screen,
widened by the suffix-drop family's files: 816 → 815 declarations, 446 → 446 pairs; SK-1's pair
new, SD-1's `ic_input_suffix` ⇄ `pairEncode_drop` gone, nothing else new or gone.

**Merge state. #162: not yet clear to merge.** `replay-lkit2` has passed; it needs gate 74's round 2.
