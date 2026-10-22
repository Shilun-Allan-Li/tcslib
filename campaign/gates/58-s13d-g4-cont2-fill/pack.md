# External audit pack — §13d G4 continuation 2: the partial's landing (PR #143, a fill gate)

Campaign: the Arora-Barak chapters 3-4 plan, §2.1 (Theorem 3.1 at `f log f`, through the
Hennie–Stearns simulation of [AB09, §1.7]). The §13d zone layer's rows G4 are two contracts in
`TuringMachine/Build/ZoneRebalance.lean`:
- `exists_zoneRebalanceTM`, the total rebalance;
- `exists_zoneExtendTM`, the extension by one level.

Their first two fill rounds landed as partials (#125 for continuation 1, gate 44). **Continuation
2** (`campaign/fills/s13d/briefs/s13d-fill-g4-cont2.md`) was delivered on 2026-10-21 as another
partial: **both targets stay sorried.** It reached the brief's phase 1, checkpoint 1: one
composed contract for the extension's whole positive-level right pass. The worker's report is
`campaign/fills/s13d/reports/g4-cont2-REPORT.md`; the maintainer's review,
`campaign/fills/s13d/reviews/g4-cont2/REVIEW.md` ("partial 0/2, landable"), found the delivery
intact and in scope.

**The head:** `lean/g4-cont2-partial` at `c60ed898`, on the campaign branch at `eb08fb16` (after
#133, #134, #136, #138 and #140 merged):
- `4b76f0ff`, the worker's commit `6fe3bf88`, cherry-picked from its verified bundle (prerequisite
  `96d60278`; the owned file is unchanged from there to the tip);
- `c60ed898`, the maintainer's, docstrings and blank lines only (the code is identical with
  comments stripped): the extension's status paragraph in public-facing terms, now stating that
  the right pass's endpoint and envelope are not yet proved (the review's F1, F2); a proof sketch
  for `zr_adjustedBack_post`, a 21-line proof (F3); two double blank lines collapsed (F3).

## What changed (verify)

| Class | Declarations |
|---|---|
| **Privates added** (34) | the ruler prefix (`zr_rulerWord`, `zr_rulerStepContract`, `zr_rulerCopyContract`, `zr_rulerSkipContract` and their preconditions); the adjusted walk and the scratch rewind (`zr_adjustedWalkContract`, `zr_adjustedBackContract` and their endpoint lemmas); the half-zone writes (`zr_innerCopyContract`, `zr_halfCopyContract`, `zr_outerHalfContract`, `zr_writeHalvesContract`, `zr_constantCopy_cell`); the seeks (`zr_rightSeekContract`, `zr_rightSeekBackContract`, `zr_rightRulerContract`); and **`zr_rightPassContract`**, with `zr_rightPass_pre`, `zr_rightPass_time` and `zr_rightPass_time_le` |
| **Private restated** (1) | `zr_left_two_walks`: the left displacement for the amended route (an unadjusted walk, then an adjusted walk across the separating blank), as continuation 1's escalation and gate 44 proposed |
| **Targets** | still `sorry`; their statements and every public declaration unchanged; each status paragraph (region (c)) rewritten |
| **Size** | 861 → 1,370 lines; 18 public, 31 → 65 private |

## Brief for the auditor

1. **Freeze.** No public statement changed; nothing new is public; the private changes are
   exactly those listed (`evidence/land/declfreeze-base-vs-landed.txt`, the review's
   `out/declfreeze.txt`, `evidence/land/g4-cont2-landing.patch`).
2. **The right pass.** Does `zr_rightPassContract` compose exactly the brief's binding phase-1
   route for the right side (seek, skip, ruler copy, the two half-zone writes, the adjusted walk,
   the scratch rewind), only through the public contract API (`Contract.seq`,
   `Contract.ofSegment`, the catalog's row contracts), with no second host, seam or clock? Are its
   precondition (`zoneRowPre`), exact time `zoneStart ℓ + 10·2^ℓ + 23` and bound `32·(2^ℓ + 1)`
   right?
3. **Claim precision (the review's F1).** The contract is composed but not characterized: no
   lemma states its endpoint or bounds its envelope, which the brief's checkpoints 1.2, 1.3 and
   1.6 need. Is landing it now right, and does the maintainer's status paragraph state exactly
   what is proved and what is open? (The review wrote both missing statements for continuation 3;
   they elaborate: `out/cont3-targets.out`.)
4. **The left displacement.** Is `zr_left_two_walks`'s arithmetic right for the amended route,
   and does the envelope `−(zoneStart ℓ + cap ℓ − 1) ≥ −zoneStart (ℓ + 1)` still hold? The review
   checked the level-one example (`out/levelone.out`).
5. **Rule 10.** The review sealed 56 other-file definitions (the worker's 51 plus 5) over the
   whole home; the two `rfl` controls fail inside the seal and pass outside it
   (`out/seal-head.out`, `out/seal-list.txt`); every external rewrite argument is a published
   theorem (`out/rwargs.txt`). Does any step still close only because another file's definition
   reduces? Rule 11: no R3 row (`out/hygiene.txt`), no other file's private reached
   (`out/ax-head.out`); ground rule 7, no second host or re-walked trace (`out/rule7.txt`).
6. **Duplication.** The screen: 808 → 838 declarations, 439 → 478 pairs; the 39 new pairs are all
   inside the file, maximum 81% (`out/screen-compare.txt`). The top two share a four-line
   composite adapter (`Contract.seq` then `Contract.ofSegment` with the exit-set rewrite), which
   recurs with every composite. Should it be factored now, privately or as a published `seq`
   corollary, or in continuation 3?
7. **Public-facing text.** The added docstrings and the two status paragraphs carry no campaign
   labels, paths, dates or session narrative (`out/public-text.txt`, and the maintainer's
   rewording).

## Repository-side attestations (verify or challenge)

- **Elaboration** (the review): at the base against `oleans-lseam2`, at the dispatch tip against
  `oleans-l132b` and at `64e2dd9e` against `oleans-lbw2`: 0 errors, only the two targets' `sorry`
  warnings (`out/elab-*.out`). The maintainer, at the landed head against `oleans-l132b`: the
  same (`evidence/land/elab-ZoneRebalance-l132b.out`; the owned file's upstream at the tip is
  `oleans-l132b`'s).
- **Axioms** (the review): every private within `[propext, Classical.choice, Quot.sound]`;
  `sorryAx` reaches each target only through its own body (`out/ax-head.out`).
- **Import probe** (the review): 439/439, the brief's 338 plus 101 names, 0 errors
  (`out/importprobe-head.out`).
- **Lint** (the landed head): `TuringMachine/Build` 0 FAIL, 31 WARN over 39 files; the new WARN
  is the file's size (`evidence/land/lint-build.txt`). No line over 100 characters.
- **The sweep** (the worker): 81 modules in the brief's order, 0 errors; the 35 admissions equal
  to the base set by name (`out/sweep-check.txt`).
- **Environment:** the first delivery under addendum v2.3; the narrowed cache fetch (35 Mathlib
  roots, 967 files) succeeded with no retry (`out/environment-v23.txt`).
- **Replay:** `replay-lg4c2.sh`: the downstream closure, on the merged tree `c60ed898`, of every
  file changed since #132's merge (13 modules: `Build/ZoneRebalance` and the campaign's merges of
  #133, #134, #136, #138 and #140, the facade last), chained from `oleans-l132b` (#132's replay
  at its merged state). **Passed (user, 2026-10-22):** 13 of 13, 0 failed, static-equal (10)
  (`evidence/replay-lg4c2.*`, `evidence/down-lg4c2.txt`).

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Severity guide as in `campaign/standards/TEMPLATE.md`. Findings go verbatim into
`campaign/gates/58-s13d-g4-cont2-fill/findings.md`. The gate closes when it has zero blockers and
zero majors.

**Deliver your findings as a downloadable Markdown file named `s13d-g4-cont2-fill-findings.md`**
(the findings table and the verdict line, no other wrapping), and also paste its content in your
reply.
