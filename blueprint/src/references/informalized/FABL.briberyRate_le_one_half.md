<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/KKLBribery.lean :: FABL.briberyRate_le_one_half -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Upper Bound for the Bribery Rate

**Claim.** For every integer $n\ge2$, the quantity $\frac{\log n}{100n}$ is at most $\frac12$, with logarithm and arithmetic interpreted over the reals.

**Proof.** Since $n\ge2$, we have $n>0$. The logarithm estimate $\log n\le n-1$ therefore applies. The denominator $100n$ is positive, so it is enough to show $\log n\le 50n$. The estimate gives $\log n\le n-1\le 50n$, proving the claimed bound after division by $100n$.
