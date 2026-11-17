<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/KarpLipton.lean :: Complexity.KarpLipton.pred_or -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Languages Are Closed Under Union

**Claim.** If the languages defined by predicates $p$ and $q$ belong to $\mathsf{P}$, then their union, defined by strings satisfying at least one predicate, also belongs to $\mathsf{P}$.

**Proof.** Apply closure of polynomial time under union (`union_mem_P`) to the two given languages. Their union consists exactly of strings satisfying $p$ or $q$, so the claimed language belongs to $\mathsf{P}$.

**Key facts.** `Complexity.union_mem_P`.
