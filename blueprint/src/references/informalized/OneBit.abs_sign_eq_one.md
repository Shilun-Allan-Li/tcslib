<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/OneBit.lean :: abs_sign_eq_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The sign of a nonzero real has absolute value one

**Claim.** For `x : ℝ` with `x ≠ 0`, `|Real.sign x| = 1`. A `private`
one-liner about `Real.sign`.

**Proof.** Split on the sign with `lt_or_gt_of_ne hx`:

- `x < 0`: `simp [Real.sign_of_neg h]` — the sign is `-1`, whose absolute value is `1`.
- `x > 0`: `simp [Real.sign_of_pos h]` — the sign is `1`. ∎

**Note.** Dead declaration: nothing in the repository references it. Its neighbour
`sign_mul_self` (`Real.sign x * x = |x|`) plays the role one might expect this lemma
to play; the `holder_sharpness` proof handles `Real.sign` by unfolding and
`split_ifs` instead.
