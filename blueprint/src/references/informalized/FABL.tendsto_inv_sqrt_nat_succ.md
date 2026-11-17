<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/GaussianSharpLevelOneCounterexample.lean :: FABL.tendsto_inv_sqrt_nat_succ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reciprocal square root limit

**Claim.** As $m$ tends to infinity through the natural numbers, $1/\sqrt{m+1}$ tends to $0$.

**Proof.** The natural numbers, viewed as real numbers, tend to positive infinity. The square-root function therefore sends them to positive infinity, and taking reciprocals sends those values to zero. This proves the limit for $1/\sqrt n$. Finally, $m+1$ tends to infinity with $m$, so composing that limit with the shift $m\mapsto m+1$ yields the desired result.
