<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/PrimalityMath.lean :: Randomized.isEulerLiar_of_prime_of_mem_Ico -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Euler Liars Among Bounded Prime Residues

**Claim.** If $p$ is a prime different from $2$ and $1\le A<p$, then $A$ is an Euler liar for $p$.

**Proof.** The prime Euler-liar criterion says that a number coprime to $p$ is an Euler liar for $p$ (`Randomized.isEulerLiar_of_prime`). It remains to check coprimality. For prime $p$, coprimality of $A$ and $p$ is equivalent to the cast of $A$ being nonzero modulo $p$ (`Randomized.coprime_iff_natCast_ne_zero`). The bounds $1\le A<p$ ensure that $p$ does not divide $A$, so this cast is nonzero. Applying the criterion proves the claim.

**Key facts.** `Randomized.coprime_iff_natCast_ne_zero`, `Randomized.isEulerLiar_of_prime`.
