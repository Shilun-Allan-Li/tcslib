<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/CounterProgSim.lean :: Complexity.CPSim.ev_rT -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Value at the Time Register

**Claim.** For the extended assignment, the value at register index $R+2$ is $tm$.

**Proof.** The index $R+2$ is neither less than $R$ nor equal to $R$ or $R+1$. Thus the final case of the extended assignment applies and returns $tm$.
