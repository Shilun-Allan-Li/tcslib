<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/KKLBribery.lean :: FABL.mean_bribeFunction_dual_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Mean under dual bribery

**Claim.** Bribing the dual function by setting the coordinates in $J$ to $1$ has mean equal to the negative of bribing $f$ by setting those coordinates to $-1$.

**Proof.** For each input $x$, the dual-after-bribery value is the negative of $f$ evaluated at the vector obtained by negating $x$ and setting every coordinate in $J$ to $-1$. Indeed, negating a coordinate that was bribed to $1$ gives $-1$, while outside $J$ it gives the negation of the original coordinate. Thus the first mean is the mean of the negative of the latter bribed function evaluated at the negated input. Negation is a bijection of the sign cube, so it preserves the uniform mean; taking the negative outside the mean then gives the asserted identity.
