<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/EXP.lean :: Complexity.a3_split_empty -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# No split at length zero

**Claim.** If $C>0$, then the exponential-split search with parameters $C,c$ at length $0$ returns no value.

**Proof.** By the failure characterization (`a3_split_none_iff`), it suffices to show that no natural number $n$ satisfies $n+C\cdot 2^{(n+1)^c}=0$. Since $C>0$ and the power of $2$ is positive, the product $C\cdot 2^{(n+1)^c}$ is positive. Adding the nonnegative number $n$ therefore gives a positive result, so it cannot equal zero.

**Key facts.** `Complexity.a3_split_none_iff`.
