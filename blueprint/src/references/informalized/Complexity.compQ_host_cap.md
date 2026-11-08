<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/QueryReshape.lean :: Complexity.compQ_host_cap -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Output length bound for the query transformation

**Claim.** Under the assumed polynomial bound on $f$, the output length of the query transformation on $w$ is at most $(2C+3)(|\langle w,t\rangle|+1)^{e+1}$.

**Proof.** The bound `compQ_length_le` gives an upper bound of $(2C+3)(|w|+1)^{e+1}$ for the output. The encoding length formula `length_pairEncode` gives $|\langle w,t\rangle|=2|w|+2+|t|$, so in particular $|w|+1\le |\langle w,t\rangle|+1$. Raising these nonnegative quantities to the power $e+1$ preserves the inequality, and multiplying by $2C+3$ gives the claimed bound.

**Key facts.** `Complexity.compQ_length_le`, `Turing.length_pairEncode`.
