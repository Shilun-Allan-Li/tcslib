# External audit pack — C1, the seam layout: the fill's landing (PR #145, a fill gate)

Campaign: the Arora-Barak chapters 3-4 plan, C1 (the nondeterministic time hierarchy, [AB09,
Theorem 3.2]). **`Turing.exists_seamLayoutTM`**
(`TCSlib/Complexity/TuringMachine/Build/SeamLayout.lean`;
statement gate 43, round 2 PASS): for distinct tapes `src`, `tbl`, `sm`, one machine takes `src`
holding a captured serialization `s = pairEncode a ((1^q 0) ++ v)` with its head at `r ≤ |s|`, and
`tbl`, `sm` blank, to `tbl` holding `v` and `sm` the unary word from cell `2`, `src` cleared, every
head at `0`, everything else framed, silently, at one time `T ≤ C·(|s| + 1)` fixed before the
configuration, and not before. The step-block startups (U2-S's, R's, B5a's H1) cite it.

**A complete fill (1/1).** The brief is `campaign/fills/c1/briefs/c1-fill-seamlayout.md`; the
worker's report `campaign/fills/c1/reports/seamlayout-1-REPORT.md`; the maintainer's review
`campaign/fills/c1/reviews/seamlayout-1/REVIEW.md` ("complete; land, with the maintainer's landing
edits").

**The head:** `lean/c1-seamlayout-fill` at `126127b8`:
- `bfe3e023`: the worker's six commits (`d6dd89ab..09773a66`, on the base `1c06ea94`) squashed
  into one, with the worker's authorship; the file is byte-identical to the delivered one
  (`evidence/land/landing-checks.txt`). The squash drops the commits' campaign-labelled subjects
  and a private session trailer (the review's F5);
- `7cd01f84`: the maintainer's, docstrings only: the module's main results and the
  `TuringMachine` facade's line say "proved";
- `126127b8`: the campaign branch merged in after #139 and #143 (no conflict; this PR's files
  byte-unchanged).

**The user's rulings (2026-10-22):**
- **The route's one deviation is accepted** (the review's F1; question 2 below), with a published
  last-phase lemma for the phase host to follow in its own API PR.
- **Proof sketches follow up** (F3): the 14 long private proofs get their sketches in a
  docstring-only PR after this one merges.

## Brief for the auditor

1. **Faithfulness.** Does the proof establish the frozen statement (the review's
   `out/10-declfreeze.txt`: 1 → 1 public, 0 → 35 private, the only body change the target's), with
   `C = 18` and `T = 2n − r + 4h + 5q + 2|v| + 23` chosen before the configuration? Are the
   endpoint, the full frame (every other tape and head, the input position) and silence at every
   `u ≤ T` proved as stated?
2. **The route.** Eight phases on one `phaseHostTM`, seven dispatches, the two leaves (`pairSkip`,
   `unarySplit`) with framed contracts, the word identities through `TuringMachine/BufferWords`.
   **The deviation (F1):** phase 8 is run through `phaseHostTM_run` with a self-redirect on the
   clear row's `done`, not through `MultiTapeTM.runFrom_mapState_of_agreeOn` with the trivial
   guard as the brief said: the brief's route needs a table fact about `phaseHostTM` that no
   published lemma states. The review shows the two hosts' transition tables equal as functions
   (its `out/21c`). Is the machine therefore the one the brief and the docstring describe, and is
   the time unchanged?
3. **Rule 10.** The review's two seals (15 definitions; then 19, with `Action.apply` erased from
   the simp set), with controls at both ends of the private section. **Note** (the review's F1):
   `simp only [phaseHostTM, …]` closes a goal even with `phaseHostTM` sealed, so a seal alone does
   not detect that unfolding; the review inspected every `rw`/`simp`/`dsimp`/`unfold` argument.
   Does any step still close only because another file's definition reduces?
4. **The edge cases** the statement gate named (`r = n`, `q = 0`, `v = []`, `a = []`, an extra tape
   with a negative head, all-`false` table bits, and the auditor's four instances with times 37,
   34, 66 and 49): the review ran the delivered machine on them. Are they covered by the theorem
   itself?
5. **Duplication.** The screen: 867 → 897 declarations, 1,112 → 1,143 pairs; 31 new pairs, all
   in-file, maximum 89% (`sl_phase7`/`sl_phase2`). The review's promotion candidates: a published
   last-phase lemma for the phase host; `sl_apply_eq` against `ExhaustiveReplay`'s private
   `xr_act_apply` (landed after this fill's base); a reversed-word read for `BufferWords`. Is
   anything here copied material needing acknowledgment?
6. **Public text and scope.** The new docstrings carry no campaign labels. `deriving` on the three
   private inductives generates six instances with public names (the review's F2), as landed code
   already does. 14 private proofs over 20 lines have no "Proof sketch" (F3; a follow-up, by the
   user's ruling).

## Repository-side attestations (verify or challenge)

- **Elaboration** (maintainer, the landed head against `oleans-lg4c2`, the tip's merged-tree
  replay; the module's 17-module upstream is unchanged since the base): `Build/SeamLayout` 0
  errors, 0 warnings (`evidence/land/elab-SeamLayout-lg4c2.out`). The review: the same at the
  base (`oleans-lbw2`) and at the tip with the patch.
- **Axioms** (the review): the target on `[propext, Classical.choice, Quot.sound]`, no `sorryAx` in
  its closure; all 36 prints equal to the worker's.
- **Probes** (the review): the brief's 45 checks and the worker's 110, 0 errors each.
- **Lint** (the landed head): `TuringMachine/Build` 0 FAIL, 31 WARN over 39 files; the new WARN is
  the file's size (1,757 lines). No line over 100 characters.
- **The sweep** (the worker): 94 modules, 0 errors; 35 → 34 sorry warnings, every other unchanged
  by name.
- **Environment:** addendum v2.3's narrowed fetch, 40 roots, 1,002 files, no retry.
- **Replay:** `replay-lsl.sh`: the downstream closure, on the merged tree `7cd01f84`, of every
  file changed since #132's merge (14 modules: `Build/SeamLayout` and the campaign's merges of
  #133, #134, #136-#138 and #140, the facade last), chained from `oleans-l132b`. **Passed (user,
  2026-10-22):** 14 of 14, 0 failed, static-equal (8) (`evidence/replay-lsl.*`). #139 and #143,
  merged since (`126127b8`), meet this PR's closure only at the facade.

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Severity guide as in `campaign/standards/TEMPLATE.md`. Findings go verbatim into
`campaign/gates/59-c1-seamlayout-fill/findings.md`. The gate closes when it has zero blockers and
zero majors.

**Deliver your findings as a downloadable Markdown file named `c1-seamlayout-fill-findings.md`**
(the findings table and the verdict line, no other wrapping), and also paste its content in your
reply.
