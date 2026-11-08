<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/OracleNondeterministic.lean :: Turing.OracleNDTM.runWith_cons -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One-Step Expansion of a Computation

**Claim.** Running on $b::w$ from $c$ gives the same configuration as taking one step using $b$ and then running on $w$.

**Proof.** By the recursive definition of running on a choice sequence, a nonempty sequence $b::w$ is processed by first applying the step determined by $b$ to $c$, then running on the remaining sequence $w$. Thus the two configurations are equal by definition.
