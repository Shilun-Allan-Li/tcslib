<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LayeredPPoly.lean :: BoolCircuit.mem_LayeredPPoly_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Layered Polynomial-Size Membership

**Claim.** A language belongs to the class of layered polynomial-size languages exactly when it satisfies the predicate defining that class.

**Proof.** The set `LayeredPPoly` is defined to contain precisely those languages satisfying `InLayeredPPoly`. Thus the two sides express the same membership condition, and the equivalence holds by definition.
