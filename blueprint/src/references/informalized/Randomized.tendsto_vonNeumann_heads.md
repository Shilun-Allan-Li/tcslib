<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Coins.lean :: Randomized.tendsto_vonNeumann_heads -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Von Neumann extraction tends to fair heads

**Claim.** When $0<\rho<1$, the probability that the procedure returns $1$ after inspecting $2K$ independent bits converges to $1/2$.

**Proof.** The exact probability after $K$ pairs is $(1-(\rho^2+(1-\rho)^2)^K)/2$, by the formula for the number of heads (`vonNeumann_heads`). The quantity $q=\rho^2+(1-\rho)^2$ is nonnegative and strictly less than $1$ under the given hypotheses. Therefore $q^K$ tends to zero, and the displayed probability tends to $(1-0)/2=1/2$.

**Key facts.** `Randomized.vonNeumann_heads`.
