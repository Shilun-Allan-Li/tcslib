<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/ErrorCorrectingCodes/Entropy.lean :: qary_entropy_logb_expand -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Rearranging the q-ary entropy exponent

**Claim.** For `q : ℕ` and `p : ℝ`,

```
p·logb q (q-1) - p·logb q p - (1-p)·logb q (1-p)
  = logb q (q-1)·p + logb q p·(-p) + logb q (1-p)·(-(1-p)).
```

A `private` purely formal rearrangement: the same sum with each factor commuted and
the subtractions absorbed into negated exponents.

**Proof.** Immediate from `linarith` — the two sides are equal as linear
combinations of the three (opaque) `Real.logb` terms.

**Used in.** `q_pow_qary_entropy_simp`, where the exponent must appear in the shape
`log-coefficient × exponent` before `Real.rpow_add` and `Real.rpow_mul` can split
`q ^ H_q(p)` into three `rpow` factors. It exists only because `rw` needs the
syntactic form, not because the identity has content.
