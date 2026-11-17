<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/KKLCounterexample.lean :: FABL.truncateUnit_neg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Oddness of Unit Truncation

**Claim.** For every real number $z$, projection onto $[-1,1]$ is odd: truncating $-z$ gives the negative of truncating $z$.

**Proof.** We split into three ranges. If $z\le -1$, then $-z\ge 1$: the projections of $z$ and $-z$ are respectively the left and right endpoints, so they are negatives. If $z\le -1$ fails but $1\le z$, the projections are respectively $-1$ and $1$, again giving the claimed identity. In the remaining case, $-1<z<1$, so both $z$ and $-z$ lie in the interval. Projection fixes every point of the interval, and the identity follows from this together with negation.
