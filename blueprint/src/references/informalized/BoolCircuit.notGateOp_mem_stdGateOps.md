<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/UnaryLanguages.lean :: BoolCircuit.notGateOp_mem_stdGateOps -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# NOT belongs to the standard gate set

**Claim.** The Boolean NOT gate operation on $\text{Fin }2$, given by $x\mapsto 1-x(0)$ on inputs indexed by $\text{Fin }1$, belongs to the standard set of gate operations.

**Proof.** The standard gate set contains, as one of the two operations in its first displayed pair, the unary operation with index type $\text{Fin }1$ and function $x\mapsto 1-x(0)$. This is exactly the definition of the NOT gate operation, so it belongs to that pair and hence to the standard gate set.
