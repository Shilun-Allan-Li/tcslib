<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/DAGTransform.lean :: BoolCircuit.rewriteGates_inv -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Invariant Under Gate Rewriting

**Claim.** If the gate-emission procedure meets the gadget specification for every eligible gate and acyclic existing list, then rewriting any acyclic list of eligible gates preserves the rewrite invariant: the vertex map has the required length and valid images, values are preserved, mapped depths satisfy the factor bound, and the rewritten list is acyclic, has the stated size bound, and consists of gates satisfying $P$.

**Proof.** Proceed by induction on the original list, appending its final gate at each step. For the empty list, the identity-map invariant is `rewriteInv_nil`. Suppose the invariant holds for an initial list and append a gate $g$. The initial list is acyclic because it is a prefix of the enlarged acyclic list, and every gate in it still satisfies $Q$. Apply the induction hypothesis to obtain the invariant for its rewritten state. The enlarged list is acyclic and $g$ satisfies $Q$, so `rewriteInv_step` extends that invariant through the rewrite of $g$. This proves the invariant for the enlarged list, and hence for the whole list.

**Key facts.** `BoolCircuit.rewriteInv_nil`, `BoolCircuit.rewriteInv_step`.
