<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/P.lean :: Complexity.dtime_one_subset_P -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Constant time lies in polynomial time

**Claim.** Every language in $\mathrm{DTIME}(n\mapsto 1)$ belongs to $\mathsf{P}$.

**Proof.** Apply the general polynomial-time inclusion criterion (\texttt{mem\_P\_of\_dtime\_le}) with polynomial degree $1$ and multiplicative constant $1$. For every input length $n$, the constant time bound is $1$, and $1\le n^1+1$. Thus the criterion places the language in $\mathsf{P}$.

**Key facts.** `Complexity.mem_P_of_dtime_le`.
