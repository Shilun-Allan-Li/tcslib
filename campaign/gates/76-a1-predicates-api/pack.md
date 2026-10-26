# External audit pack — the chapter predicates' readings (PR #164, A1, an API gate)

Campaign: the Arora-Barak chapters 3-4 plan, the second fill track (megafill D).
- **Why:** megafill D's drafting delivery (`campaign/fills/megafill/drafts/
  megafill-D-DRAFTING-REPORT.md`) found no fill ready. The two nearest targets,
  `Complexity.spaceConstructible_poly` (`SpaceComplexity/Savitch`) and E-Q,
  `Turing.NTimeDiag.exists_queryTM` (`Diagonalization/NTimeDiagonalizer`), are blocked by one gap:
  under rule 10 a fill reads another file's definition only through published lemmas, and
  `Complexity.TimeConstructible`, `Complexity.SpaceConstructible`, `Turing.FinTM.ComputesInSpace`,
  `Complexity.logSpace` and `Complexity.transduce` have none that expose their bodies (lint check
  8 misses them, its recorded blind spot). The review of that delivery
  (`campaign/fills/megafill/reviews/megafill-d/REVIEW.md`) confirmed the gap, the statements and
  their completeness for both targets. **The user ruled (2026-10-25):** open A1 (Q-D1), include the
  copying-state lemma (Q-D2), and add the three readings the space hierarchy will need
  (`DecidesInSpace`, `SPACE`, `LOGSPACE`); `SpaceComplexity/Basic` and `ClassNP/Transducer` are
  Hydroxyi's files, and additions beside his definitions are the user's call (an FYI to him).
- **The head:** `lean/a1-predicates` at `ae4849af`, one commit (`evidence/a1-predicates.patch`)
  on the campaign tip `39c649e6` (Lean equal to #161's merged tree). This bundle's Lean files are
  from `ae4849af`, and its records from the records commit that the dispatch prompt names.

| File | New public lemmas (each beside its definition, no `@[simp]`) |
|---|---|
| `ClassP/TimeConstructible` | `Complexity.timeConstructible_iff` (`Iff.rfl`) |
| `SpaceComplexity/Constructible` | `Complexity.spaceConstructible_iff` (`Iff.rfl`) |
| `SpaceComplexity/Basic` | `Turing.FinTM.computesInSpace_iff`, `Turing.FinTM.decidesInSpace_iff`, `Complexity.mem_SPACE_iff` (`Iff.rfl`); `Complexity.logSpace_eq`, `Complexity.LOGSPACE_eq` (`rfl`) |
| `ClassNP/Transducer` | `Complexity.transduce_nil`, `Complexity.transduce_cons` (`rfl`); `Complexity.transduce_of_copy` (induction) |

Each file's "Main results" list gains its entries. Nothing else changes.

## Brief for the auditor

1. **Faithfulness.** Is each right-hand side exactly its definition's body (up to binder names),
   so that the lemma holds by `Iff.rfl` or `rfl` in its home file? Is each docstring an exact
   reading of its statement, in mathematical English?
2. **Completeness for the two targets.** Would a fill of `spaceConstructible_poly` or of E-Q,
   under rule 10, need any further reading of a chapter predicate that these do not give? The
   review's consumer probe (`probe/A1ConsumerProbe.*`) uses these names and proves
   `spaceConstructible_poly` (dominance through the published `Complexity.logSpace_le_succ`) and
   E-Q's witness step, under the drafting probes' seals.
3. **`transduce_of_copy`.** Does it generalize the two published instances,
   `Complexity.KarpLipton.transduce_drop_true` (`CircuitComplexity/KarpLiptonPrefix`, line 87) and
   `Complexity.Meyer.transduce_fT_copy` (`CircuitComplexity/MeyerVerifierGlue`, line 145)? Their
   re-pointing is deferred to the user's dedup window, not this PR.
4. **Placement and form.** Beside the definitions; no `@[simp]` (consumers rewrite with them
   explicitly); names consistent with the library's (`_iff` for predicates, `_eq` for functions,
   `mem_…_iff` for a set); no clash with any declaration downstream.
5. **No collateral change.** The freeze (`evidence/freeze/`): public 5 → 6, 3 → 4, 12 → 17,
   7 → 10; no statement and no body of an existing declaration changed.

## Repository-side attestations (verify or challenge)

- **Elaboration** (against `oleans-lu2api`, the tree after #161): each of the four files, with
  `#print axioms` for its new lemmas appended (`evidence/*-ax.out`; recipe `check.sh.txt`):
  0 errors; the only warnings are `TimeConstructible`'s two existing sorries (its MIG-1 stage S
  specifications).
- **Axioms:** the seven readings within `[propext, Classical.choice, Quot.sound]`
  (`logSpace_eq` on `[propext]`); `transduce_nil`, `transduce_cons` and `transduce_of_copy` on
  none.
- **Names:** unused at the tip, on #161, #162 and #135, and in Mathlib and the other packages
  (the review's check 1, `out/02-a1-statement-by-statement.txt`).
- **Lint** (`evidence/lint-*`): `ClassP` 0 FAIL / 3 WARN, `SpaceComplexity` 0 FAIL / 82 WARN,
  `ClassNP` 0 FAIL / 16 WARN, as at the base; check 8's list for `Basic` shrinks from five
  definitions to three (`SPACE` stays listed: the check's name match does not count
  `mem_SPACE_iff`). No added line over 100 characters.
- **Replay:** the four files' downstream closure (192 modules at the tip, 193 once #162 is in;
  the review's `out/08-replay-closure-and-order.txt`), on the tree after #162. **Pending** (the
  gate is dispatched before it).

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Severity guide as in `campaign/standards/TEMPLATE.md`. Findings go verbatim into
`campaign/gates/76-a1-predicates-api/findings.md`. The gate closes when it has zero blockers and
zero majors.

**Deliver your findings as a downloadable Markdown file named `a1-predicates-api-findings.md`**
(the findings table and the verdict line, no other wrapping), and also paste its content in your
reply.
