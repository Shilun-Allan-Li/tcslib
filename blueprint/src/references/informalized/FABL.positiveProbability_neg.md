<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/TotalInfluence/EdgeIsoperimetric.lean :: FABL.positiveProbability_neg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Positive Probability of the Negated Function

**Claim.** For any sign-valued function $f$, the uniform probability that $-f$ equals $1$ is the uniform probability that $f$ equals $-1$.

**Proof.** At each point $x$, the value $f(x)$ is either $1$ or $-1$. In the first case, $-f(x)$ is not $1$ and $f(x)$ is not $-1$; in the second case, $-f(x)=1$ and $f(x)=-1$. Thus the two event indicators agree pointwise, and their uniform expectations are equal.
