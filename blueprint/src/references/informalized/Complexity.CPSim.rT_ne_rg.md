<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/CounterProgSim.lean :: Complexity.CPSim.rT_ne_rg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Distinctness of the Temporary Register

**Claim.** In the register file with $R+3$ registers, the register at index $R+2$ is distinct from every original register among the first $R$ registers.

**Proof.** Suppose the two registers were equal. Equality of finite indices implies equality of their underlying natural-number indices. The temporary register has index $R+2$, whereas an original register has index less than $R$, by its membership in the first $R$ registers. These facts contradict one another, so the registers are distinct.
