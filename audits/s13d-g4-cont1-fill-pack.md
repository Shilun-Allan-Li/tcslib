# External audit pack — §13d G4 continuation 1: the partial's landing (PR #125)

Campaign: the Arora-Barak chapters 3-4 plan, §2.1 (Theorem 3.1 at `f log f`, through the
Hennie–Stearns simulation of [AB09, §1.7]). The §13d zone layer's rows G4 are two contracts in
`TuringMachine/Build/ZoneRebalance.lean`:
- `exists_zoneRebalanceTM`, the total rebalance;
- `exists_zoneExtendTM`, the extension by one level.

Their first fill round landed as a partial. **Continuation 1** (`briefs/s13d-fill-g4-cont1.md`)
was delivered on 2026-10-17 as another partial: **both targets stay sorried.** The maintainer's
review (`audits/evidence/s13d-g4-cont1-fill/REVIEW.md`) found the delivery intact and in scope.
Its proved pieces are on the brief's route, so it lands as a partial, as the first round did.

**Stacked on #124.** Head `lean/g4-cont1-partial` at `4ab012d9`:
- `778f9ada`, the worker's commit `66765b0c`, cherry-picked from its verified bundle;
- `4ab012d9`, the maintainer's commit: the review's F1 fix and the appendix label.

## What changed (verify)

| Class | Declarations |
|---|---|
| **Re-pointed helpers** (phase 0; statements byte-identical) | the four the brief named: `zr_read_slot` and three more. Each replacement lemma is public at the base. |
| **Privates added** (13) | the two layout bridges, the offset formulas, a generic field-layout comparison, both seek preconditions, the side-pass reordering `zr_cascade_passes`, `zr_left_two_walks` (the escalation's arithmetic), and their supporting lemmas |
| **Maintainer's commit** | `zr_zonedTape_right_fields`, two lines: the separator cell is read through `FinTM.bufferTape_nat`, not by definitional reduction (review F1); the extension appendix's label `E1` → `cont1-E1`, with the review's path |
| **Targets** | still `sorry`; their statements and the public declarations unchanged |
| **Size** | 571 → 860 lines; 18 public, 18 → 31 private |

## Brief for the auditor

1. **Freeze.** No public statement changed; nothing new is public; the private changes are exactly
   those listed (`audits/evidence/s13d-g4-cont1-fill/`: the review's `declfreeze.txt`, the
   worker's diff, and the landing patch).
2. **Rule 10 (no unfolding another file's definition).** The review re-elaborated with the other
   files' definitions sealed. On the base this fails at exactly the four helpers the brief named;
   on the landed head (with F1's fix) it passes. Check the proved helpers read every foreign
   definition through published lemmas.
3. **Correctness of the pieces.** Are the bridges, the offsets and the seek preconditions the
   statements the brief recommends, and is `zr_cascade_passes` the total cascade's side-pass
   reordering it claims?
4. **The worker's escalation (cont1-E1; the review's F2).** `zr_left_two_walks` proves that the
   brief's prescribed left route, two half-capacity walks, stops one cell right of the new zone's
   outermost cell. Is the arithmetic right? The review proposes an amendment within the permitted
   rows for continuation 2: either the first walk unadjusted (`2^ℓ + 1`), or one extra one-cell
   step. Is it sound, and does the envelope `−(zoneStart ℓ + cap ℓ − 1) ≥ −zoneStart (ℓ + 1)`
   still hold?
5. **Landing a partial.** Is it right to land proved private helpers while both targets stay
   admitted? The precedent is G4's first partial. Is the extension appendix's wording accurate,
   and free of session narrative?
6. **Duplication:** the two new within-file pairs (`zr_pair_pass`/`zr_inPass_out`, 72% and 62%;
   shared induction scaffolding). Acceptable, or factor them?

## Repository-side attestations (verify or challenge)

- **Elaboration** against `oleans-lndnf` (the landed head): 0 errors; the two targets' `sorry`
  warnings. The review also elaborated at the base snapshot `oleans-lbapi4`.
- **Axioms** (the review): standard for all 31 privates; `sorryAx` reaches each target only
  through its own body.
- **Import probe** (the review): 338/338, 0 errors.
- **Lint:** 0 FAIL, warnings unchanged; widest new line 99.
- **Screen:** 795 → 808 declarations, 437 → 439 pairs, 127,810 → 127,994 characters (the base is the
  brief's measured base). The two new pairs are within the file, `zr_pair_pass`/`zr_inPass_out`
  (72%, 62%), as the review found; no cross-file pair (`land/screen-*.txt`).
- **Replay:** `replay-lg4c1.sh`, 2 modules (`Build/ZoneRebalance` and the `TuringMachine` facade),
  chained from `oleans-lseam` (#124's replay). REPLAY-RESULT

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Severity guide as in `audits/TEMPLATE.md`. Findings go verbatim into
`audits/s13d-g4-cont1-fill-findings.md`. The gate closes when it has zero blockers and zero
majors.

**Deliver your findings as a downloadable Markdown file named `s13d-g4-cont1-fill-findings.md`**
(the findings table and the verdict line, no other wrapping), and also paste its content in your
reply.
