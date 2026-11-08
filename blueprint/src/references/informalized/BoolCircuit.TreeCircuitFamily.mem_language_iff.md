<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/TreeNCAC.lean :: BoolCircuit.TreeCircuitFamily.mem_language_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Membership in a tree-circuit language

**Claim.** A finite Boolean word $w$ belongs to the language recognized by a tree-circuit family exactly when the circuit assigned to input length $|w|$ evaluates to true on the assignment given by the entries of $w$.

**Proof.** By definition, the language consists precisely of words accepted by the family, and acceptance is defined as the stated circuit evaluation being true. The equivalence is therefore immediate from the definitions.
