<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/KarpLipton.lean :: Complexity.KarpLipton.pred_and -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Languages Are Closed Under Intersection

**Claim.** If the languages defined by predicates $p$ and $q$ belong to $\mathsf{P}$, then their intersection, defined by strings satisfying both predicates, also belongs to $\mathsf{P}$.

**Proof.** Apply closure of polynomial time under intersection (`inter_mem_P`) to the two given languages. The language of strings satisfying both predicates is exactly their intersection, so it belongs to $\mathsf{P}$.

**Key facts.** `Complexity.inter_mem_P`.
