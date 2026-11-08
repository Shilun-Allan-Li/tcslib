<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/PrimalityMath.lean :: Randomized.eulerLiarRounds_of_prime -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Prime inputs pass every Euler-liar round

**Claim.** For an odd prime $p$, every random string makes any number of Euler-liar rounds return true.

**Proof.** Induct on the number $k$ of rounds, allowing the random string to be arbitrary at each stage. With zero rounds the result is true by definition. For the successor case, the first round samples $A$ from the interval $[1,p)$, by the range theorem for Euler samples (`eulerSample_mem_Ico`), using $1<p$. The prime characterization theorem says that every such $A$ is an Euler liar for $p$ (`isEulerLiar_of_prime_of_mem_Ico`), so the first round accepts. The remaining rounds use the tail of the random string, and the induction hypothesis says they also return true. Hence all rounds return true.

**Key facts.** `Randomized.eulerSample_mem_Ico`, `Randomized.isEulerLiar_of_prime_of_mem_Ico`.
