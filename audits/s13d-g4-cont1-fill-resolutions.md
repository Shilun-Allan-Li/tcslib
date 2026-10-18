# §13d G4 continuation 1 fill gate (PR #125): resolutions (round 1; gate CLOSED)

**Gate:** the landing of the G4 continuation-1 partial in `TuringMachine/Build/ZoneRebalance.lean`
(PR #125, `lean/g4-cont1-partial` at `4ab012d9`, stacked on #124): 13 privates, four
re-pointings, and the maintainer's F1 fix and appendix label. Both targets stay admitted. Pack
`audits/s13d-g4-cont1-fill-pack.md`; bundle SHA-256
`61e53a37ed9a69863778f12b50b3a56e0c4378e22adec64be24f95a542d252f5` (56 sections; folder
`44-s13d-g4-cont1-fill-gate/`). Replay passed (user, 2026-10-17): 2 of 2, static-equal (2).

**Round 1** (`audits/s13d-g4-cont1-fill-findings.md`, verbatim): **PASS, 0 blockers, 0 majors,
3 minors, 13 notes.** The auditor could not run Lean and treated the elaboration, axiom, probe and
replay logs as supplied evidence. The maintainer's review sub-agent verified every finding at
`4ab012d9`: all true, at the auditor's severities. **The gate is closed; the landing is a
partial.**

| # | Severity | Finding | Resolution |
|---|---|---|---|
| 1 | minor | The seal control is overstated: `seal-Base.out` has five errors in three helpers (`zr_read_slot`, `zr_capacity_pos`, `zr_mirror_tape`) and none in `zr_ruler_length`, whose `simp only [zoneCapacity, …]` unfolds explicitly. | **True; records.** **Pack erratum** (the pack is preserved as dispatched): `s13d-g4-cont1-fill-pack.md:34`, "fails at exactly the four helpers the brief named", reads **"fails at three of the four helpers the brief named (`zr_read_slot`, `zr_capacity_pos`, `zr_mirror_tape`); the fourth, `zr_ruler_length`, unfolded `zoneCapacity` explicitly, which a seal does not block"**. `REVIEW.md`'s control bullet is corrected the same way. **Rule 10's check is two checks:** the seal (implicit reduction) and the inspection of rewrite and `simp` arguments for definitions (explicit unfolding). Both carry to continuation 2. |
| 2 | minor | The pack's size row says 571 → 860 lines; the landed file has 861. | **True; records.** **Pack erratum:** `s13d-g4-cont1-fill-pack.md:26` reads **571 → 861** (the worker's commit 860; the maintainer's commit adds one line). `REVIEW.md`'s 860 is the worker's delivery and stands. |
| 3 | minor | The extension appendix's "The left route is stopped under ground rule 4" narrates the workflow. | **True.** **The fix** (`.lean`, docstring only, line count kept; blob `e88edbda` → `0f9e56ce`): "On the left, the prescribed two half-capacity walks require a one-cell alignment correction:" / "`zr_left_two_walks` proves that they stop one cell right of the new zone's outermost cell" / "(cont1-E1; `audits/evidence/s13d-g4-cont1-fill/REVIEW.md`, F2). The ruler builder,". Elaborated against `oleans-lg4c1`: exit 0, the two target warnings at 686 and 728. **It rides on continuation 2's landing**, which has its own PR and gate (the §13d rule) and rewrites this appendix with the route amendment (the review deferred this reword to the amendment). A commit on #125 now would be an ungated §13d change and would force #126's restack and re-replay. |
| 4–16 | notes | Integrity and evidence scope; the freeze; the definitions; rule 10 on the landed head (F1 repaired); the layout statements; the seek preconditions; the side-pass reordering; the escalation's arithmetic; landing as a partial; axioms and admissions; the import probe; the screen pair; the logs and replay. | No action. Notes 9 and 11 carry to continuation 2. Note 12: accepted only as a partial. Note 15: `zr_pair_pass`/`zr_inPass_out` (72%, 62%) accepted, no factoring. |

**A reviewer addition (records):** `land/replay-lg4c1.sh:18`'s failure message names `0a5878ed`;
the check is against `0355da56`. It is the message copied from `replay-lndapi2.sh` (gates 42 and
45, minor 2). The script is kept as run, and the message is corrected when it is next derived.

**Carried to G4 continuation 2's brief:**
- **The left route** (note 11, F2): from the seek's stop `2 − zoneStart ℓ`, a total displacement
  of `2·2^ℓ + 1`: an unadjusted first walk of `2^ℓ + 1` and an adjusted walk of `2^ℓ`, or two
  adjusted walks and one more left step. The endpoint is `−zoneStart (ℓ + 1) + 2`, inside the
  envelope `−zoneStart (ℓ + 1)`. Sanity case `ℓ = 1`: stop at −8, not −7 (writing four cells
  from −7 overwrites the separator −4). Prove the composition: ruler repositioning, control cost,
  cleanup and head restoration.
- **The second seek** (note 9): its precondition from the zoned head at home and agreement on
  the cells it reads (`[0, zoneStart ℓ]` on the right, `[−zoneStart ℓ, 0]` on the left), through
  the first side pass's frame, without global scratch blankness.
- **Rule 10:** both checks (minor 1), the seal and the argument inspection.
- **Minor 3's appendix line**, if that sentence survives the amendment.

**#125 is not yet clear to merge.** Its gate is closed and its replay passed, but its base is #124,
whose gate 43 failed. #125 merges after #124 (revised and re-gated), or after a restack onto #123
(`ZoneRebalance`'s import closure does not contain `SeamLayout`) with a fresh replay.
