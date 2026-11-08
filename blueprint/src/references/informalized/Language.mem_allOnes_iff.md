<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/SizeClasses.lean :: Language.mem_allOnes_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Membership in the All-Ones Language

**Claim.** A Boolean word belongs to the all-ones language exactly when it is the list of its length many true bits.

**Proof.** By the characterization of a list as a constant replicate, a list has every entry equal to `true` exactly when it equals the replicate of `true` with its own length. Applying this characterization to the defining condition for membership gives the equivalence.
