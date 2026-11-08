<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/NoiseStability/GaussianDisagreement.lean :: FABL.thresholdSign_ne_iff_mul_neg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Opposite Threshold Signs

**Claim.** For nonzero real numbers $a$ and $b$, their threshold signs differ if and only if $ab<0$.

**Proof.** Since neither number is zero, each is either positive or negative. If both are nonnegative, both are positive and their threshold signs are $1$; their product is positive. If $a$ is positive and $b$ is negative, their threshold signs are $1$ and $-1$, and their product is negative. If $a$ is negative and $b$ is nonnegative, the signs are $-1$ and $1$, again with negative product. If both are negative, both threshold signs are $-1$ and the product is positive. The threshold-sign values in these cases follow from the nonnegative and negative input rules (`thresholdSign_of_nonneg` and `thresholdSign_of_neg`).

**Key facts.** `FABL.thresholdSign_of_nonneg`, `FABL.thresholdSign_of_neg`.
