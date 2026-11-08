<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/DeterministicCC/FuncIndexing/LowerBound.lean :: CommunicationComplexity.Functions.Indexing.exp_one_le_68_div_25 -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# A Rational Upper Bound for Euler’s Number

**Claim.** Euler’s number satisfies $\exp(1)\le 68/25$.

**Proof.** Bound the exponential series at $1$ by its first five terms together with a remainder bound. The sum of the terms of degrees $0$ through $4$ is $1+1+1/2+1/6+1/24=65/24$, and the remainder estimate supplied by the exponential-series bound is $1/100$. Their sum is $65/24+1/100\le68/25$, proving the claim.
