<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/EXP.lean :: Complexity.P_subset_EXP -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial time lies in exponential time

**Claim.** Every language in $\mathsf{P}$ belongs to $\mathrm{EXP}$.

**Proof.** Take a language in $\mathsf{P}$ and choose an exponent $c$ witnessing its polynomial-time bound. For every $n$, $n^c+1\le 2\cdot 2^{n^c}$, since $n^c<2^{n^c}$ and the right-hand side is at least twice that power of two. Thus its polynomial time bound is at most the exponential bound with exponent $c$, after multiplying the machine's time constant by $2$. Monotonicity of deterministic time classes under pointwise increases of the time bound (\texttt{Complexity.DTIME.mono}) transfers the language to that exponential-time class, and hence to $\mathrm{EXP}$.

**Key facts.** `Complexity.DTIME.mono`.
