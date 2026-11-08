<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/PathHard.lean :: Complexity.PathHard.ell_mono -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monotonicity of Bit Length

**Claim.** If $m\le m'$, then the length of the binary bit list of $m+1$ is at most the length of the binary bit list of $m'+1$.

**Proof.** Rewrite each bit-list length as the binary size of the corresponding number, using `ell_eq_size`. Since $m\le m'$, we have $m+1\le m'+1$. Binary size is monotone on natural numbers, so the desired inequality follows.

**Key facts.** `Complexity.PathHard.ell_eq_size`.
