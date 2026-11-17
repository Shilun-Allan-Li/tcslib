<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/Basic.lean :: BoolCircuit.TreeCircuit.size_node -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Size of a Gate Circuit

**Claim.** A gate circuit with child list $cs$ has size $1$ plus the sum of the sizes of the circuits in $cs$.

**Proof.** By the definition of circuit size, a gate contributes one plus the right-fold sum of the sizes of its children. The definition of the sum of sizes is that same right fold, so the two expressions agree.
