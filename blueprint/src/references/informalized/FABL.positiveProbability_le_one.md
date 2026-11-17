<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/TotalInfluence/EdgeIsoperimetric.lean :: FABL.positiveProbability_le_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Upper Bound on Positive Probability

**Claim.** For any sign-valued function $f$ on the Boolean cube, the uniform probability that $f$ equals $1$ is at most $1$.

**Proof.** The indicator of the event $f(x)=1$ takes only the values $0$ and $1$, so it is at most $1$ at every point. Averaging this pointwise inequality over the finite cube gives the claimed bound.
