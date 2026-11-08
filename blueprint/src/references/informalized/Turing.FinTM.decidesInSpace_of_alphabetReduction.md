<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ConfigCount.lean :: Turing.FinTM.decidesInSpace_of_alphabetReduction -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Space-efficient alphabet reduction

**Claim.** If $D$ computes the encoded binary decision output on encoded inputs and uses at most $S(|y|)$ space on every alphabet-$\Gamma$ input $y$, then some Boolean-alphabet machine decides $L$ using at most $c(S(n)+1)$ space on inputs of length $n$, for a natural number $c$.

**Proof.** For each binary word $x$, choose a time $g(x)$ at which $D$ computes the required encoded output on the encoded input. For each length $n$, take $T(n)$ to be the maximum of these chosen times over all binary words of length $n$; this maximum exists because there are finitely many such words. Every word $x$ is represented by a function from its length to the Boolean alphabet, and hence its chosen time is at most $T(|x|)$. The monotonicity of computation in the allowed time (`ComputesInTime.mono`) therefore gives a uniform time bound $T$ for the encoded computation. Apply the alphabet-reduction space theorem (`alphabet_reduction_spaceUsed`) to obtain a Boolean-alphabet machine with the corresponding decision computation and space bounded by $c(S(|x|)+1)$. Its computation has some finite time, so it witnesses the definition of deciding in that space bound.

**Key facts.** `Turing.FinTM.ComputesInTime.mono`, `Turing.FinTM.alphabet_reduction_spaceUsed`.
