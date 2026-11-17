<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/KKLBribery.lean :: FABL.briberyIncrement_nonneg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nonnegative Bribery Increment

**Claim.** For every nonnegative integer $n$, the quantity $\frac{199\log n}{1000000n}$, interpreted over the reals, is nonnegative.

**Proof.** If $n=0$, the expression is zero, since $\log 0=0$ in Lean’s real logarithm convention. If $n\ne0$, then $n>0$, so $n\ge1$ and hence $\log n\ge0$. The coefficient $199$ and denominator $1000000n$ are positive, so the quotient is nonnegative.
