# External audit pack — §13d G4 continuation 3: checkpoint 1.1b's landing (PR #148, a fill gate)

Campaign: the Arora-Barak chapters 3-4 plan, §2.1 (Theorem 3.1 at `f log f`, through the
Hennie–Stearns simulation of [AB09, §1.7]). The §13d zone layer's rows G4 are two contracts in
`TuringMachine/Build/ZoneRebalance.lean`: the total rebalance `exists_zoneRebalanceTM` and the
extension by one level `exists_zoneExtendTM`. Continuation 2 composed the extension's positive
right pass into one contract (`zr_rightPassContract`; #143, gate 58) but did not characterize it.
**Continuation 3** (`campaign/fills/s13d/briefs/s13d-fill-g4-cont3.md`), item 3 of megafill B, asked
first for that characterization, checkpoint 1.1b. The session lost its workspace while on
checkpoint 1.2; the checkpoint archive was recovered intact and is delivered under the brief's
early-stop rule. **Both targets stay sorried.** The worker's report is
`campaign/fills/s13d/reports/g4-cont3-REPORT.md`; the maintainer's review,
`campaign/fills/s13d/reviews/g4-cont3/REVIEW.md` ("land checkpoint 1 as a partial").

**The head:** `lean/g4-cont3-partial` at `13e17589`, on the campaign branch at `43d22595` (TCSlib =
`b7447492`'s, after #139 and #143): the worker's commit `01bcc6e0`, cherry-picked from its verified
bundle. The bundle's first two commits are #143's two (applied by the brief's `git am`; equal
patch-ids), already merged, so only the worker's own commit lands. No maintainer commit: the two
status paragraphs are already public-facing and accurate.

## What changed (verify)

| Class | Declarations |
|---|---|
| **Privates added** (8) | `zr_rightPass_post` and `zr_rightPass_envelope` (the two statements the brief supplied in `inputs/s13d-fill-g4-cont3/G4C3Targets.lean.txt`), `zr_rightPass_tape`, `zr_rightPass_bounds`, `zr_halfCopy_post`, `zr_writeHalves_post`, `zr_rightPassRow` (the singleton-exit re-wrap) and `zr_singletonContract` (the composite adapter) |
| **Privates changed** (4) | `zr_adjustedBackContract`, `zr_adjustedWalkContract`, `zr_rightRulerContract`, `zr_rightSeekBackContract`: re-pointed through the adapter |
| **Targets** | still `sorry`; their statements and every public declaration unchanged; the extension's status paragraph updated |
| **Size** | 1,370 → 1,572 lines; 18 public, 65 → 73 private (`evidence/land/landing-checks.txt`) |

## Brief for the auditor

1. **Freeze.** No public statement changed; nothing new is public; the private changes are
   exactly those listed (`evidence/land/landing-checks.txt`, `evidence/land/landing.patch`).
2. **Checkpoint 1.1b.** Are `zr_rightPass_post` (the endpoint: the new right zone written, virtual
   blanks in its inner half and empty slots in its outer half; the nonpositive half-line
   preserved; the ruler on scratch; the scratch head restored; the zoned head at the stated cell)
   and `zr_rightPass_envelope` (the zoned head inside the level's box) true and proved as stated?
   The review checked the level-one instance in Lean (cells 5–8, heads 7 and −7, time 48). Is the
   bridge to the frozen extension specification (`zonedTape_extend`, `zr_extend_cell`) right?
3. **The adapter.** Does `zr_singletonContract` capture the four-line `Contract.seq`/
   `Contract.ofSegment` exit-set pattern exactly, and are all four earlier copies re-pointed (the
   former 81% pair is now 63%)? Does the singleton re-wrap sequence as claimed?
4. **Rule 10.** The review's seal: 57 other-file definitions over the private section, controls
   that fail inside and pass outside; every external rewrite argument a theorem. Does any step
   close only because another file's definition reduces? Rule 11.
5. **Landing a partial.** Is it right to land the characterization while both targets stay
   admitted, as for G4's earlier partials (#115, #125, #143)? Does the extension's status
   paragraph state exactly what is proved and what is open?
6. **Duplication.** Five new in-file pairs, all under 90%; the review notes an 85% pair
   (`zr_rightPass_bounds` against `zr_rightPass_time`, two long `simp only` lists). Acceptable,
   or factor it now?
7. **The interruption.** The session's environment was lost after this checkpoint; the full
   95-module sweep was not re-run after it (only the owned file and the facade, the whole
   downstream). Is the checkpoint complete and self-consistent as delivered?

## Repository-side attestations (verify or challenge)

- **Elaboration** (the review): 0 errors at the head and at the tip, only the two targets' sorry
  warnings (1396, 1439). The maintainer, the landed head against `oleans-lg4c2`: the same
  (`evidence/land/elab-ZoneRebalance-lg4c2.out`).
- **Axioms** (the review): the 12 new or changed privates on `[propext, Classical.choice,
  Quot.sound]`; `sorryAx` reaches each target only through its own body.
- **Probes** (the review): the brief's 439 checks, standalone and in-module; the worker's 445.
- **Lint** (the landed head): `TuringMachine/Build` 0 FAIL, 31 WARN over 39 files
  (`evidence/land/lint-build.txt`).
- **Integrity** (the review): the zip and its 70 internal sums; the session's recovery record.
- **Replay:** `replay-lg4c3.sh`: the downstream closure, on the merged tree `13e17589`, of every
  file changed since #132's merge (16 modules: `Build/ZoneRebalance` and the campaign's merges,
  the facade last), chained from `oleans-l132b`. **Passed (user, 2026-10-22):** 16 of 16, 0 failed,
  static-equal (10) (`evidence/replay-lg4c3.*`).

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Severity guide as in `campaign/standards/TEMPLATE.md`. Findings go verbatim into
`campaign/gates/61-s13d-g4-cont3-fill/findings.md`. The gate closes when it has zero blockers and
zero majors.

**Deliver your findings as a downloadable Markdown file named `s13d-g4-cont3-fill-findings.md`**
(the findings table and the verdict line, no other wrapping), and also paste its content in your
reply.
