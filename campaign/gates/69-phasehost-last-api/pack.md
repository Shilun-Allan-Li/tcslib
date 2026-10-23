# External audit pack — the phase host's last phase (PR #156, an API gate)

Campaign: the Arora-Barak chapters 3-4 plan, the machine library (`machine-library-design.md`
§12.8, the phase host).
- **Why:** the seam layout's fill (C1, #145) had a host whose last phase ends at a live exit
  that the redirect table leaves alone. Its brief prescribed the agreement transfer
  (`MultiTapeTM.runFrom_mapState_of_agreeOn`) with the host's table off the redirects as the
  agreement hypothesis. No published lemma stated that table fact, and it closes only by
  unfolding `phaseHostTM`, which rule 10 forbids in another file. The worker gave the last phase
  a self-redirect instead, so that `phaseHostTM_run` covers it. The review accepted that route
  (`campaign/fills/c1/reviews/seamlayout-1/REVIEW.md`, F1). **The user ruled (2026-10-22): publish
  in `Build/Seam` a table equation for `phaseHostTM` on a non-redirected state, or a live-exit form
  of `phaseHostTM_run`, by a small API PR with its own gate.** This PR publishes both.
- **The head:** `lean/phasehost-last` at `a4d9b024`: the commit `0b671a28` (on the campaign branch
  at `9f8bba86`); the campaign branch after #154 merged in (`eed76e8e`, clean; `Seam` was
  unchanged there); `9f82de74`, the maintainer's rewrite of `phaseHostTM_run` (below); and the
  campaign branch after #155 merged in (`a4d9b024`, clean). Its Lean diff from the campaign branch
  is `Build/Seam` only (`evidence/phasehost-last.patch`, `evidence/phasehost-run-rewrite.patch`).
  This bundle's Lean files are from `a4d9b024`, and its records from the records commit that the
  dispatch prompt names.
- **Found while building the pack:** the v3 screen paired the existing `phaseHostTM_run` with the
  new `phaseHostTM_run_le` (77%): `phaseHostTM_run`'s inner `have hpre` was exactly the new lemma,
  statement and proof. `9f82de74` moves the two new lemmas above it and proves `hpre` by
  `phaseHostTM_run_le`. It also reads the dispatch step through `MultiTapeTM.step_of_some`, the
  host's table at the redirected exit, and the field equations of `Action.apply` and
  `Cfg.mapState`, where it had unfolded `MultiTapeTM.step` and `Cfg.mapState` (two rule-10 sites
  older than this PR). The statement of `phaseHostTM_run` is unchanged; its sketch says so.

| File | Change |
|---|---|
| `TuringMachine/Build/Seam` | `phaseHostTM_run`'s proof (above; its statement unchanged), and **`Turing.phaseHostTM_tr_of_red_none`**: for `red i s = none`, `(phaseHostTM M q0 red).tr ⟨i, s⟩ inp w = ((M i).tr s inp w).mapState (Sigma.mk i)`, by `simp only [phaseHostTM, hs]` (the definition is this file's); **`Turing.phaseHostTM_run_le`**: if no state reached strictly before `T` is redirected, then for every `u ≤ T` the host's run from `c.mapState (Sigma.mk i)` is the phase's run tagged by `i`, through the agreement transfer; two header sentences name them |

- **Evidence:** `evidence/`:
  - `phasehost-last.patch`, `pr-body.md`, `freeze-Seam.txt`, `lint-build.txt`;
  - against `oleans-lun2` (the campaign's Lean tree): `elab-Seam.out` (the head) and
    `elab-Seam-base.out` (the base), each with the module's five unused-variable warnings in older
    code; `SeamAx.lean.txt`/`.out` (both lemmas' axioms);
  - **the seal:** `SeamSeal2.lean.txt`/`.out`, primed copies of the three lemmas (the two new ones
    and the rewritten `phaseHostTM_run`) with `MultiTapeTM.runFrom`, `MultiTapeTM.step`,
    `Cfg.mapState`, `Action.mapState`, `Action.apply`, `Cfg.workTapeSymbols`, `moveInputPos` and
    `Cfg.inputSymbol` locally irreducible and `Action.apply` erased from the simp set, with eight
    `rfl` controls, sealed and unsealed (`SeamSeal.lean.txt`/`.out`: the first seal, of the two new
    lemmas only);
  - **the consumer probe:** `SeamConsumer.lean.txt`/`.out`, with `phaseHostTM` also sealed, as for
    another file: the brief's route (the agreement transfer, with the table equation as its
    hypothesis) and a last phase's live endpoint from `phaseHostTM_run_le`;
  - the v3 screen: `screen-population.txt`, `screen-*`, `pairdiff-*`;
  - the replay's list (`down-lphl.txt`, 88 modules); its script, log and static check follow it.
- **The bundle** also contains `Build/Seam` at the head (and the base's as `SeamBase.lean.txt`),
  `StateRenaming` (the agreement transfer `MultiTapeTM.runFrom_mapState_of_agreeOn`),
  `Build/SeamLayout` (the self-redirect workaround), the seam layout's review, and the screen's
  population.

## Brief for the auditor

1. **Faithfulness.** Is `phaseHostTM_tr_of_red_none` exactly the host's table at a
   non-redirected state? Is `phaseHostTM_run_le` true as stated? Check: the guard over `u < T`
   only; the conclusion for every `u ≤ T`, `u = T` included, with nothing assumed of the state at
   `T`; the case `T = 0`; a phase that halts (state `none`) before `T`; and a state at `T` that
   *is* redirected, where the lemma still gives the tagged configuration at `T` but says nothing
   after it. Are the docstrings exact readings?
2. **Sufficiency.** Does the pair give a host's last phase without the self-redirect? Check the
   seam layout's phase 8 and the review's F1 (out/21–21c), and the consumer probe. Would a
   consumer need another form, for example the dispatch step after a redirected `T` combined with
   this window?
3. **Rule 10 in the API proofs.** The table equation unfolds `phaseHostTM` in its own file. The
   run lemma reads the host only through the table equation and the agreement transfer. Does the
   seal cover every other-file definition the proofs could reach, and do its controls show it is
   effective? Inspect every `simp`, `rw` and `exact` argument. Under the user's ruling of
   2026-10-23 the rule binds TCSlib's own definitions; core and Mathlib definitions may reduce in
   `rfl` but are not passed to `simp`.
4. **Duplication.** No private restatement of either lemma exists on the campaign branch or the open
   PRs' branches (a search of every file using both `phaseHostTM` and the agreement transfer). The
   screen covers `Seam` and those files, eight in all: 548 → 549 declarations, 125 → 125 pairs at
   the final head, none new or gone. At the first head (before the rewrite) one new in-file pair,
   `phaseHostTM_run` → `phaseHostTM_run_le` (77%), which the rewrite removes
   (`evidence/pairdiff-first-head.txt`, `pairdiff-final-head.txt`). Is anything else a copy?
5. **The rewrite of `phaseHostTM_run`.** Is the re-proof exact? Its statement must be
   byte-identical, its window must now be `phaseHostTM_run_le`, and its dispatch must be read only
   through published equations, with no definition of another file unfolded.
6. **No collateral change:** two public lemmas, `phaseHostTM_run`'s proof and sketch, and two
   header sentences; no `@[simp]`; 22 → 24 public and 8 → 8 private declarations; no other
   declaration changed (`evidence/freeze-Seam.txt`).

## Repository-side attestations (verify or challenge)

- **Elaboration and axioms** (against `oleans-lun2`): the head has the base's five warnings, at
  lines shifted by the header's two lines, and no other diagnostic. `phaseHostTM_tr_of_red_none`
  is on `[propext]`, `phaseHostTM_run_le` on `[propext, Classical.choice, Quot.sound]`.
- **Seal:** the three primed lemmas elaborate; the eight controls fail sealed (lines 1003–1016 of
  `SeamSeal2`) and close unsealed. **Consumer probe:** elaborates with `phaseHostTM` sealed.
- **The rewrite:** `elab-Seam-r2.out`, the head with the rewrite, against `oleans-lun2`: the five
  older warnings only.
- **Freeze:** `evidence/freeze-Seam.txt`. **Lint:** 0 FAIL, 33 WARN over 40 files; the four lines
  over 100 characters are the base's.
- **Replay:** `replay-lphl.sh`, `Seam`'s downstream closure (88 modules, `down-lphl.txt`) at
  `a4d9b024`, chained from `oleans-lslsk` (#155's snapshot, the campaign's tree after #155).
  **Pending:** as for gates 64–68 (the user's ruling of 2026-10-23), this gate is dispatched before
  the replay, which is recorded when it passes; the PR is clear to merge only when both have passed.

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Severity guide as in `campaign/standards/TEMPLATE.md`. Findings go verbatim into
`campaign/gates/69-phasehost-last-api/findings.md`. The gate closes when it has zero blockers and
zero majors.

**Deliver your findings as a downloadable Markdown file named `phasehost-last-api-findings.md`**
(the findings table and the verdict line, no other wrapping), and also paste its content in your
reply.
