<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/NARM.lean :: Complexity.LogProg.nans_choose -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Answer After a Choice Instruction

**Claim.** If the instruction at $l$ chooses between $l_1$ and $l_0$, then a choice sequence of length $N+1$ yields answer $b$ from $(l,v,res)$ exactly when a sequence of length $N$ yields answer $b$ from at least one of $(l_1,v,res)$ or $(l_0,v,res)$.

**Proof.** For the forward direction, a sequence of length $N+1$ is nonempty, so write it as its first choice bit followed by a tail of length $N$. The recursion for a run on a nonempty sequence (narun_cons), together with the one-step rule for a choice instruction (nastep_choose), shows that the tail runs from $l_1$ if the first bit is true and from $l_0$ if it is false. It preserves the same recorded answer, so the tail witnesses the corresponding disjunct. Conversely, if a length-$N$ sequence yields answer $b$ from $l_1$, prefix it with the true choice bit; if it does so from $l_0$, prefix it with the false bit. The same run recursion and choice rule give a length-$N+1$ sequence with the required answer from $l$.

**Key facts.** `Complexity.LogProg.narun_cons`, `Complexity.LogProg.nastep_choose`.
