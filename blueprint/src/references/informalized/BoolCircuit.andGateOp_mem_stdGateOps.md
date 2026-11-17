<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/SizeClasses.lean :: BoolCircuit.andGateOp_mem_stdGateOps -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# AND operations are standard gates

**Claim.** For every natural number $w$, the $w$-input AND operation belongs to the standard gate set.

**Proof.** The standard gate set is a union of the identity and NOT gates with a union, over all arities, of the corresponding AND gates. The operation with arity $w$ belongs to the latter union by choosing the index $w$; its defining expression then agrees with the $w$-input AND operation.
