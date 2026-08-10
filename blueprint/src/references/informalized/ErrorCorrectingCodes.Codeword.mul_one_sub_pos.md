<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/ErrorCorrectingCodes/Basic.lean :: mul_one_sub_pos -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The variance factor p(1 − p) is positive

**Claim.** For a real `p` with `0 < p` and `p < 1`, the product `p * (1 - p)` is
positive.

**Proof.** One line: `exact mul_pos hp (one_sub_pos_of_lt_one hp')`.

- `one_sub_pos_of_lt_one hp'` turns `p < 1` into `0 < 1 - p`.
- `mul_pos` combines that with `hp : 0 < p` to give positivity of the product.

Granular helper. The quantity `p (1 - p)` is the Bernoulli variance and appears
as a denominator in the entropy-derivative computation, so what is needed of it
is exactly nonvanishing-with-sign, which this lemma states directly.

**Used in.** `Entropy.lean`, the `hp1p` step (line 572), where `hp.1` and `hp.2`
are the two halves of a stored `0 < p ∧ p < 1`.
