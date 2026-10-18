# Gate 44 review: PR #125, the §13d G4 continuation-1 partial landed (PASS 0/0/3/13)

Reviewer: read-only review sub-agent, 2026-10-17. `$S` is the scratchpad; `$Z = $S/review/gate44`.
Every claim cites a saved output under `$Z/out/`.

**The PASS stands: 0 blockers, 0 majors.** All 16 findings are true at the auditor's severities.
- **Minors 1 and 2** are records.
- **Minor 3** is a `.lean` docstring. Under the §13d rule (PR and gate for every zone-layer Lean
  change), I recommend it rides on continuation 2's landing.
- **One reviewer addition (records):** gate 44's replay script has the same wrong-base message
  that gates 42 and 45 flagged.

**#125 (`lean/g4-cont1-partial` at `4ab012d9`): not yet clear to merge.** Its gate is closed
(once the records are committed) and its replay passed (2 of 2, static-equal 2). But its base
is #124, whose gate 43 **failed**. #125 can merge only after #124 is revised, re-gated and
merged, or after #125 is restacked off #124 with a fresh replay (see (d)).

## Inputs

| Input | Value | Evidence |
|---|---|---|
| Findings | `audits/s13d-g4-cont1-fill-findings.md` at `a5128d97` (verbatim; SHA-256 `df433caf…9c34`), read as data. Row 4 quotes the bundle's SHA-256 | `out/bundle-check.txt` |
| Bundle | `44-s13d-g4-cont1-fill-gate/s13d-g4-cont1-fill-bundle.md`, SHA-256 `61e53a37…52f5`, 2,454,906 bytes, 56 sections; folder `SHA256SUMS` OK | `out/bundle-check.txt` |
| Bundle rebuild | from git (Lean `4ab012d9`, other `11a14de2`): **byte-identical** | `out/bundle-rebuild.txt` |
| Head | `4ab012d9` = `0355da56` (#124) + `778f9ada` (the worker's commit) + `4ab012d9` (the maintainer's). PR open, base `lean/seam-layout` | `out/pr125.json` |
| Sources | `src/ZR-base.lean` (`0355da56`, 571 lines, blob `9deb85fb`), `src/ZR-worker.lean` (`778f9ada`, 860, `bae3aac8`), `src/ZR-head.lean` (`4ab012d9`, 861, `e88edbda`) | `out/sizes.txt` |
| Scratch worktree | `$Z/wt`, detached at `4ab012d9`, `.lake/packages` linked | — |
| Elaboration | `tools/leanelab.sh $Z/wt $S/oleans-lg4c1 <file>`, 1 run | `out/elab-ZR-patched.out` |

## (a) The findings at the head

| # | Auditor | Verified | Grade | Basis |
|---|---|---|---|---|
| 1 | minor | **true** | minor (records) | `seal-Base.out`'s five errors (generated lines 145, 149, 233, 238, 240) fall in `zr_read_slot`, `zr_capacity_pos` and `zr_mirror_tape` ×3. None falls in `zr_ruler_length` (generated line 213) (`out/seal-base-error-map.txt`). Its base proof is `simp only [zoneCapacity, Nat.mul_comm]`, an explicit unfolding that `local irreducible` does not block (`out/statements.txt`). Both the pack (`:34`) and `REVIEW.md:98` claim "exactly the four" |
| 2 | minor | **true** | minor (records) | 571 → 860 (`778f9ada`) → 861 (`4ab012d9`) (`out/sizes.txt`). The pack's size row (`:26`) says 860. `REVIEW.md:193, 272` describe the worker's delivery, so their 860 is right |
| 3 | minor | **true** | minor | `ZoneRebalance.lean:723`: "The left route is stopped under ground rule 4". The rest of the appendix (lines 721–727) is accurate. The review had itself recommended this reword "once the route amendment is ruled" (`REVIEW.md:262`) |
| 4 | note | true | note | Bundle rebuilt byte for byte. The head is two commits on `0355da56`, and only `ZoneRebalance.lean` changes |
| 5 | note | true (reproduced) | note | My comment-aware freeze (`out/freeze-commentaware.txt`, `out/repointed-signatures.txt`): 13 added, none removed, order kept. The only code changes are the four re-pointed helpers, whose statements are byte-identical. Both targets' `theorem … sorry` text is byte-identical, with 2 literal `sorry`s at base and head |
| 6 | note | true | note | Retained definitions; not re-derived here |
| 7 | note | true | note | F1's two lines are the maintainer's commit (`land/maintainer-commit.patch`) |
| 8 | note | true (checked) | note | `zr_right_offset` (offset `i + 1` = `zoneStart i`) and `zr_left_offset` (`… + zoneStart (ℓ − j) = zoneStart ℓ`) have the stated shapes (`out/statements.txt`) |
| 9 | note | true (checked) | note | Both seek preconditions take the full `hd : zoneRowPre ⟨ℓ, z⟩ d`, so the second seek of an extension needs a weaker one, as the review (item 4) says |
| 10 | note | true (checked) | note | `zr_cascade_passes`: `zoneCascadeRight j z` = ascending left-out ∘ ascending right-in ∘ `zoneMove true` ∘ descending left-out ∘ descending right-in, with no guard dropped |
| 11 | note | true (checked) | note | `zoneStart i = 2^(i+1) + i` and `zoneCapacity i = 2·2^i` (`ZoneTape.lean:164`, `Zone.lean:103`). So `zoneStart (ℓ+1) = zoneStart ℓ + zoneCapacity ℓ + 1`, the left offset is `zoneStart ℓ − 2`, and `zr_left_two_walks`' right side is one more than the outermost cell `−(zoneStart ℓ + zoneCapacity ℓ − 1)`. At `ℓ = 1`: zones 2, 5, 10, so the stop is −3, two walks end at −7, the target is −8 and the bound −10 |
| 12 | note | true | note | Accepted only as a partial: both targets still `sorry` |
| 13 | note | true | note | Not re-run; the inventories are in `review-out/` |
| 14 | note | true | note | Not re-run |
| 15 | note | true (lint reproduced) | note | Lint at the head, re-run in `$Z/wt`: identical to `land/lint-head.txt` (0 FAIL, 63 WARN, 80 files) |
| 16 | note | true | note | The records' `replay-lg4c1.sh` and `.log` equal the `$S/fills/replay/` copies (SHA-256); footer `# modules=2 failed=0` |

**Reviewer addition:**
- **X1 (minor, records; the same class as gates 42 and 45's minor 2).** `land/replay-lg4c1.sh:18`
  compares against `0355da56`, but its failure message says "the Lean diff from 0a5878ed must be
  exactly ZoneRebalance" (`out/replay-diagnostics.txt`). It is the message copied from
  `replay-lndapi2.sh`, where it is right. No check is affected. The script is kept as run;
  correct it when the script is next derived (see (d): a restack needs a new one).

## (b) The minors' exact fixes

### Records (`records-gate44.patch`, SHA-256 `947b6e44…4192`; applies cleanly at `a5128d97`)

Made by `scripts/records.py`, with every replacement asserted unique.

| # | File | Change |
|---|---|---|
| R-1 (minor 1) | `audits/evidence/s13d-g4-cont1-fill/REVIEW.md:98–99` | The control bullet becomes: "It fails at three of the four helpers phase 0 named: `zr_read_slot`, `zr_capacity_pos` and `zr_mirror_tape`, base lines 142, 146, 230, 235 and 237 (`seal-Base.out`). These are `repoint.md`'s lines. The fourth, `zr_ruler_length`, unfolds `zoneCapacity` explicitly (`simp only [zoneCapacity, Nat.mul_comm]`), which a seal does not block; the inspection of rewrite arguments finds it. (Corrected: gate 44, finding 1.)" (2 → 5 lines) |
| R-2 (minors 1, 2; X1) | new `audits/s13d-g4-cont1-fill-resolutions.md` | round 1, gate closed. **Pack errata** (the pack is preserved as dispatched): `:34` reads "fails at three of the four helpers the brief named (`zr_read_slot`, `zr_capacity_pos`, `zr_mirror_tape`); the fourth, `zr_ruler_length`, unfolded `zoneCapacity` explicitly, which a seal does not block"; `:26` reads "571 → 861" (the worker's 860, plus one line from the maintainer). Also: rule 10's check is two checks; minor 3's home; X1; the carry-forward; and "**#125 is not yet clear to merge**" with the reason |

### Minor 3, `.lean` (`lean-zr-appendix.patch`, SHA-256 `784d191d…5968`)

`TCSlib/Complexity/TuringMachine/Build/ZoneRebalance.lean:723–725`. The blob goes from
`e88edbda` to `0f9e56ce`; the line count stays 861 and the widest line 99:
```
On the left, the prescribed two half-capacity walks require a one-cell alignment correction:
`zr_left_two_walks` proves that they stop one cell right of the new zone's outermost cell
(cont1-E1; `audits/evidence/s13d-g4-cont1-fill/REVIEW.md`, F2). The ruler builder,
```
- **The wording:** the auditor's sentence, with "On the left" kept, because the obstruction is
  the left side's.
- **What is kept:** the lemma, the label and the review path.
- **What is dropped:** "continuation 1's escalation" and "stopped under ground rule 4" (the
  workflow narration).

| Check | Result |
|---|---|
| Elaboration against `oleans-lg4c1` | exit 0, the two target warnings at 686 and 728, as in `land/elab-ZoneRebalance.out` (`out/elab-ZR-patched.out`) |
| Freeze, head → patched | no code change (`out/freeze-patch.txt`) |
| Lint | equals `land/lint-head.txt` (`out/lint-patched-TuringMachine.txt`) |

**Where it should land: continuation 2's landing.**
- **The rule.** The §13d rule requires a PR the user merges and its own gate for every
  zone-layer Lean change. So a commit on #125 now would be a Lean change after gate 44, with no
  gate of its own.
- **The cost of a commit on #125.** It would also force #126 to be restacked:
  `replay-lx2.sh:17–18` requires the diff from `4ab012d9` to be exactly `NTimeDiagonalizer`. And
  both #125 and #126 would need re-replays.
- **Why continuation 2.** Its landing has its own PR and gate, and it rewrites this appendix with
  the route amendment anyway. That matches the review's own deferral ("once the route amendment
  is ruled").
- **The brief's instruction:** state the obstruction mathematically. If the sentence survives the
  amendment, use the text above.

## (c) Carry-forward (G4 continuation 2's brief)

- **The left route** (note 11, the review's F2):
  - **The displacement.** From the seek's stop `2 − zoneStart ℓ`, the total displacement is
    `2·2^ℓ + 1`. Either take an unadjusted first walk of `2^ℓ + 1` and then an adjusted walk of
    `2^ℓ`, or two adjusted walks and one more left step.
  - **The envelope.** The endpoint is `−zoneStart (ℓ + 1) + 2 ≥ −zoneStart (ℓ + 1)`.
  - **Sanity case `ℓ = 1`:** the stop is at −8, not −7 (writing four cells from −7 overwrites the
    separator at −4).
  - **To prove:** ruler repositioning, control cost, cleanup and head restoration.
  - **The lemma:** restate or remove `zr_left_two_walks`.
- **The second seek** (note 9): state its precondition from the zoned head at home and from
  agreement on the cells it reads, `[0, zoneStart ℓ]` on the right and `[−zoneStart ℓ, 0]` on the
  left, through the first pass's frame. It needs no global scratch blankness.
- **Rule 10** (minor 1). The worker's self-check and the review's check are both of these:
  - the seal (implicit reduction);
  - an inspection of every `rw`/`simp`/`simpa`/`unfold` argument for another file's definition
    (explicit unfolding).

  Neither alone is complete.
- **Minor 3's appendix line**, as above.
- **Bases to re-measure at issue:** the screen (808 declarations, 439 pairs, 127,994 characters;
  the `zr_pair_pass`/`zr_inPass_out` pair is accepted, no factoring), and the lint (0 FAIL; the
  one existing ZoneRebalance warning, check 8's three definitions). The `oleans` base depends on
  how #124 is resolved.

## (d) Bottom line

- **The PASS stands:** 0 blockers, 0 majors. All three minors are true. Notes 4–16 are true. I
  checked 5, 8, 9, 10 and 11 in substance, and reproduced 4, 5 and 15. X1 is a fourth,
  records-only minor.
- **#125 is not yet clear to merge.** Gate 44's records are ready to commit. The blocker is stack
  order: #125's base is #124 (gate 43 FAILED, 0/2/1/7, reviewed separately).
  - **Path 1: wait for #124.** If #124 is revised by new commits, #125 must be rebased onto them
    and re-replayed with a re-derived script: today's pins `0355da56`, and requires the diff from
    it to be exactly ZoneRebalance. Fix X1's message there.
  - **Path 2: restack #125 (and #126) onto #123,** and merge them before #124. This is possible:
    ZoneRebalance's imports are ZoneTape and the three Contract modules, and only the
    `TuringMachine` facade mentions `SeamLayout` (`out/imports.txt`). The cost is new replays
    for #125 and #126 chained from `oleans-lc1w`, not `oleans-lseam`; #124's revision is then
    rebased onto the new tip, which it needs anyway.
  - **The choice is the user's.**
- **Then #125 is clear to merge** once its replay at the final base passes, with gate 44's
  records committed.
