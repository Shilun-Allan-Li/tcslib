<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/LinearThresholdBias.lean :: FABL.thresholdPair_nonneg_of_bias_nonneg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nonnegative bias gives a nonnegative threshold pair

**Claim.** If $a_0\ge0$, then for every real $t$ the threshold signs of $a_0+t$ and $a_0-t$ have nonnegative sum.

**Proof.** A threshold sign has real value $1$ on a nonnegative input and $-1$ on a negative input (`signValue_thresholdSign`). If both $a_0+t$ and $a_0-t$ are nonnegative, the sum is $2$; if both are negative, the sum is $-2$, but this case is impossible because their sum is $2a_0\ge0$. In the remaining cases one is nonnegative and the other negative, so the sum is $0$. Equivalently, splitting first on the sign of $a_0+t$, when it is negative the inequality $a_0\ge0$ forces $a_0-t\ge0$; otherwise the two possibilities for $a_0-t$ directly give sums $2$ or $0$.

**Key facts.** `FABL.signValue_thresholdSign`.
