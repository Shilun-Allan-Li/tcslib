<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Inclusions.lean :: Complexity.SAT3_mem_PSPACE -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Three-SAT belongs to polynomial space

**Claim.** Serialized three-SAT is decidable by a finite Turing machine in polynomial space.

**Proof.** Three-SAT belongs to NP by `SAT3_mem_NP`. Every language in NP belongs to PSPACE (`NP_subset_PSPACE`), so applying that inclusion to three-SAT gives the claimed polynomial-space bound.

**Key facts.** `Complexity.SAT3_mem_NP`, `Complexity.NP_subset_PSPACE`.
