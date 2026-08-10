<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/ErrorCorrectingCodes/Basic.lean :: one_sub_nonneg_of_le_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# 1 − p is nonnegative at most one

**Claim.** For a real `p` with `p ≤ 1`, we have `0 ≤ 1 - p`. As with its strict
sibling, no lower bound on `p` is assumed.

**Proof.** Immediate from `linarith` — the goal is a direct linear rearrangement
of the hypothesis `hp`.

Granular helper: the nonstrict counterpart of `one_sub_pos_of_lt_one`, kept for
call sites where the probability parameter is only known to be at most one (so
the degenerate case `p = 1` is admitted) and a nonnegativity side condition —
for instance for `Real.sqrt` or an `rpow` base — is all that is required.

**Note for reviewers.** No Lean file in the repository currently applies this
lemma; the only reference outside `Basic.lean` is the `\lean{...}` entry in
`blueprint/src/chapter/ErrorCorrectingCodes/Basic.tex`. It is dead as of this
pass. The `p ≤ 1` regime is presently handled by `one_sub_pos_of_lt_one`
composed with a strictness step instead.
