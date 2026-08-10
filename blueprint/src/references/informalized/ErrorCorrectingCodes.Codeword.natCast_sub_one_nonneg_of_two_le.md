<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/ErrorCorrectingCodes/Basic.lean :: natCast_sub_one_nonneg_of_two_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# q − 1 is nonnegative when q is at least two

**Claim.** For `q : ℕ` with `2 ≤ q`, the real number `(q : ℝ) - 1` satisfies
`0 ≤ (q : ℝ) - 1`. The subtraction is real subtraction of the cast, not
truncated `ℕ` subtraction.

**Proof.** One line:
`linarith [show (1 : ℝ) < q from natCast_one_lt_of_two_le hq]`.

- The bracketed term supplies `1 < (q : ℝ)` from
  `natCast_one_lt_of_two_le`.
- `linarith` then reads off `0 ≤ q - 1` as a linear consequence.

Granular numeric helper. It is the nonstrict weakening of
`natCast_sub_one_pos_of_two_le`; the strict version is what the entropy
development actually consumes, since `Real.logb q (q-1)` needs `q - 1 ≠ 0`.

**Note for reviewers.** No Lean file in the repository currently applies this
lemma — the only reference to it outside `Basic.lean` is the `\lean{...}` entry
in `blueprint/src/chapter/ErrorCorrectingCodes/Basic.tex`. It is dead as of this
pass, retained as the nonnegative variant of its strict sibling.
