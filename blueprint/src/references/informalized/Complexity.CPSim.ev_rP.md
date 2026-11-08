<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/CounterProgSim.lean :: Complexity.CPSim.ev_rP -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Value at the Input Register

**Claim.** For the extended assignment, the value at register index $R$ is $p$.

**Proof.** The register at index $R$ is not among the original registers, whose indices are strictly less than $R$. It matches the next case in the definition of the extended assignment, which assigns it the value $p$.
