# External audit pack: B6's H landing, `Complexity.space_hierarchy` (PR #218, a fill gate)

## Why this PR

`Complexity.space_hierarchy` (`SpaceComplexity/Hierarchy`; [AB09, Theorem 4.8]) and its corollary
`Complexity.LOGSPACE_ssubset_PSPACE` ([AB09, §4.3.2]) were `sorry` in the campaign. The fill H
(brief `campaign/fills/b6/briefs/b6-fill-hierarchy.md`, agent Codex; REPORT
`campaign/fills/b6/reports/hierarchy-REPORT.md`) proves both, with the frozen statements, by the
window route. One fixed self-universal machine `U₀` is run in a radius-`a · g(n)` window, using
the configuration-count runner, and the verdict is flipped.

The third target, `SPACE_linear_ne_NP` ([AB09, Exercise 3.2]), ends in the brief's allowed named
escalation, **E-PAD**: the library has no host for the padded-language space decider. The private
`sph_linear_ne_NP_of_padding` proves the target from `space_hierarchy` and E-PAD's exact
statement. The user ruled on 2026-11-06:
- E-PAD is published as a general `mem_SPACE_padLang` in a new `SpaceComplexity/Padding` module.
  Its statement PR is #219, with its own gate.
- E-PAD comes before F6 in this file.
- `Hierarchy` may import the new module, and the maintainer closes the target afterwards in a
  small PR.

`space_universal` (F6) is outside H and unchanged.

**The PR:** #218 on `lean/b6h-landing`, head `65d72947` (full hash in the bundle header). It
consists of:
- the delivery `fill/b6-hierarchy` at `30222bbd` (base `e6bc1968`, kept as delivered;
  `campaign/fills/b6/`), merged at `14ee2e46`;
- the maintainer's landing edits `2d65a899` and `66fc5327`, made after a review of the delivery
  (`campaign/fills/b6/review/hierarchy-REVIEW.md`) and a library sweep
  (`campaign/fills/b6/sweep/`);
- merges of the campaign, the last at `65d72947` (after #216).

It changes one file, `Hierarchy.lean`: 317 → 2,507 lines, with 4 public declarations (statements
unchanged) and 43 private `sph_` declarations.

## What changed (verify)

| Declaration | What |
|---|---|
| `Complexity.space_hierarchy` (frozen statement) | proved; its sketch is corrected at landing (below) |
| `Complexity.LOGSPACE_ssubset_PSPACE` (frozen statement) | proved |
| `Complexity.SPACE_linear_ne_NP` (frozen statement) | still `sorry` (E-PAD); its sketch is corrected at landing |
| `Complexity.space_universal` (F6) | unchanged, `sorry` |
| 43 private `sph_` declarations | the diagonalizer pipeline (radius, record, runner, test, verdict), the window containment, the normal-form arithmetic, and `sph_linear_ne_NP_of_padding` |
| the imports | the brief's four (`SelfUniversal`, `Build/WindowRun`, `WindowClock`, `ClassNP/PClosure`) |

**The landing edits** (`2d65a899`, `66fc5327`) make no public statement changes:
- **The sweep's items** (`campaign/fills/b6/sweep/README.md`, copy C, clear and borderline as
  in #208's and #211's sweeps; no import): **17 of its 18 items, 30 sites**. The items are:
  - `Nat.le_mul_of_pos_right` (two sites), `Fin.val_ne_zero_iff`, `Fin.zero_ne_one` (three
    sites), `length_bits_le_self`, `Bool.eq_iff_iff`;
  - `Function.Embedding.ofIsEmpty`, `Finset.sum_le_card_nsmul`, `Fin.castLEEmb`;
  - four `Cfg.ext` skeletons replaced by `Cfg.mapState_mapState` and
    `Cfg.mapState_eq_of_fields`;
  - the borderline `Nat`/`Int`/`Option` lemmas M1–M4 and M6–M8.

  **M5 was applied, then reverted (`66fc5327`).** It rewrote five `1 ≤ g n` floors as
  `Nat.one_le_of_lt (… : logSpace n ≤ g n)`, which typechecks only by unfolding
  `Complexity.logSpace`. The seal at the landed head caught it (five errors, `sorryAx` in both
  headlines). The delivered text (`rw [logSpace_eq]; omega`) is restored at all five sites. The
  sweep's README had flagged M5 as depending on definitional unfolding.
- **The review's minor 3 and note 5:**
  - `space_hierarchy`'s sketch now describes the configuration-count runner
    (`exists_configWindowRunnerTM`) with its own clock. It cites `exists_codeTM_spaceUsed`, not
    a re-derived space clause through `relabelState`.
  - The module docstring no longer mentions "the clock width".
  - `SPACE_linear_ne_NP`'s sketch uses the `(|x|+1)²` pad and `m = (n+1)² + 2n + 2`, cites
    `preimage_mem_NP`, and drops two internal phrases.

## Known deviations and dispositions (for the audit)

- **E-PAD** (above): the brief's allowed escalation, ruled by the user.
- **Size:** 2,507 lines. The brief waives the size limit (its rule 8). It produces the style
  lint's one new WARN and the policy linter's one new finding. About 2,200 lines are the
  diagonalizer pipeline. A later split or harvest is optional (review note 9).
- **The review's minors 1, 2 and 4** concern the REPORT, not the code:
  - checkpoint 7's "admission-free" row was premature;
  - the checkpoint zips were not shipped, though the final zip, patch chain and bundle cover
    them;
  - the REPORT's proposed Implementation paragraph ends with process text. It was not
    inserted.
- **Promotion candidates** (review note 7): `Cfg.select` has no published field equations, so
  `sph_select_fields` is an API gap. `sph_seam_heads` and `sph_halt_contract` are general consumer
  lemmas. These are recorded for a later shared-file window.
- **The unused private** `sph_linear_ne_NP_of_padding` (review note 8) is kept. It becomes the
  target's body once E-PAD lands.

## Brief for the auditor

1. **Soundness and pins:**
   - Are the four statements frozen?
   - Is the proof of `space_hierarchy` correct, including the window containment, the clock
     sufficiency, `n` below the hypothesis' threshold, and the payload padding of the code?
   - Is `LOGSPACE_ssubset_PSPACE` correct?
2. **Rule 10:** do the proofs read other files' definitions only through published equations?
   The seal and its controls are below.
3. **Duplication:** does any proof still re-derive a published lemma (a typed or untyped `have`,
   a `simp` set, a rewrite chain, a conjunct), or another file's private? The review, the sweep
   and the delivery's screen classification list every candidate with a disposition. Challenge
   any of them.
4. **Public text:** are the module docstring and the three targets' docstrings accurate, free of
   campaign labels, and attributed? Does `sph_linear_ne_NP_of_padding`'s hypothesis match #219's
   statement at `S n = n² + 1`, `T n = n + 1`, `C = 1`, `d = 2`?

## Repository-side attestations (verify or challenge)

- **The delivery** (`campaign/fills/b6/`):
  - the REPORT and the delivery's `SHA256SUMS`;
  - the bundle checked against the source, and the patch chain from blob `287acce8` to
    `40d62c36`;
  - the review's freeze, seal (71 definitions, plus `[-simp]` on four), controls (**75 pass
    unsealed, 75 fail sealed**) and axioms, all on the delivered source.
- **Rule 10 at the head** (`evidence/seal/`): the delivered seal block, with the 71 definitions
  and the four `[-simp]` removals, inserted after `space_universal` in the head's `Hierarchy.lean`
  (`66fc5327`). It elaborates against the campaign snapshot with **0 errors**. The only messages
  are the two `sorry` warnings (`space_universal` and `SPACE_linear_ne_NP`).
  `#print axioms` at its end gives `space_hierarchy` and `LOGSPACE_ssubset_PSPACE` on
  `[propext, Classical.choice, Quot.sound]`. At `2d65a899`, before M5 was reverted, the same
  seal gave 5 errors; that output is kept (`seal-head-before-M5-revert.out`). The controls are
  the delivery's, unchanged, because the seal block is the delivered one. Their sources are
  `evidence/seal/HSealControl_*.lean.txt`, and their raw logs are in the delivery zip
  (`arora-barak-ch3-4/archive/deliveries/fill-b6-hierarchy.zip` on the exchange branch,
  `evidence/logs/`). The sealed head source is `evidence/seal/HSealHead.lean.txt`.
- **Freeze** (`evidence/freeze/`):
  - Against the campaign's Lean (`a28b8c42`): 4 → 4 public with statements unchanged, and
    0 → 43 private. The authorized changes are `space_hierarchy`'s and
    `LOGSPACE_ssubset_PSPACE`'s bodies, and `SPACE_linear_ne_NP`'s docstring.
  - Against the delivery: 43 → 43 private. 17 private bodies changed (the sweep), plus the two
    public docstrings.
- **Screen** (`evidence/screen/`): the brief's 43-file population on a `git archive` of the
  head: **1,894 declarations, 1,699 pairs, 539,014 characters**.
  - Against the delivery's after-screen (1,701 pairs): 0 new and 2 gone. The gone pairs are
    `sphWitnessSel` against `sphInitSel`, and `sph_record_suffix` against
    `Cfg.mapState_mapState`; the sweep removed both.
  - Against the brief's screen base (1,689 pairs): 10 new, each with a `Hierarchy` declaration
    on one side. The largest is 84%. They include four against `InputRewind`'s
    `Cfg.mapState_mapState` (84%, 82%, 61%, 58%), which the delivery's classification
    (`screen-final-classification.txt`) disposes of as concrete field readings, not the
    composition equation. The other six are between two `Hierarchy` declarations.
- **Lint** (`evidence/lint/`):
  - The campaign lint on `SpaceComplexity` gives 0 FAIL, 82 WARN over 112 files at the head,
    against 81 at the base. The new WARN is `Hierarchy`'s size.
  - The policy linter gives 2 findings: the size (new, waived) and a missing
    `## Main definitions` heading (pre-existing).
- **Replay** (`evidence/merged-tree/`):
  - `replay-lh2` at `65d72947` covers the downstream closure of `Hierarchy` (`Hierarchy` and the
    `SpaceComplexity` facade), chained from the campaign snapshot `oleans-lcamp3` (after #216).
  - **2 modules, 0 failed.** The static check finds 0 mismatches. The 2 `sorry` warnings are
    `space_universal` and `SPACE_linear_ne_NP`.
  - #217 (NZ-1) merged after this replay. It changes proof bodies in modules upstream of
    `Hierarchy` and adds one theorem. Before merge, the maintainer re-runs this 2-module replay
    on the campaign after #217.

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

The severity guide is in `campaign/standards/TEMPLATE.md`. Findings are copied verbatim into
`campaign/gates/109-h-landing-fill/findings.md`. The gate closes when it has zero blockers and
zero majors.

**Deliver your findings as a downloadable Markdown file named `h-landing-fill-findings.md`** (the
findings table and the verdict line, no other wrapping), and also paste its content in your reply.
