<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/NearlyConstantLevelOne.lean :: FABL.abs_mean_toReal_le_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Mean Bound for a Boolean Sign Function

**Claim.** The absolute value of the uniform mean of any Boolean sign function is at most $1$.

**Proof.** Every value of the function is either $-1$ or $1$. Consequently, the constant function with value $-1$ is pointwise at most the given function, and the given function is pointwise at most the constant function with value $1$. Taking uniform expectations preserves both inequalities. The expectations of those constant functions are $-1$ and $1$, so the mean lies in $[-1,1]$, which is equivalent to the claimed absolute-value bound.
