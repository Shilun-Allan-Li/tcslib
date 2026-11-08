<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/NARMProof.lean :: Complexity.LogProg.narm_decides_npspace_of_logspace -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Logspace Oracles Yield Polynomial Space

**Claim.** If every oracle language is in logarithmic space and the register program satisfies the stated polynomial register-size, halting, validity, and correctness assumptions, then its language belongs to nondeterministic polynomial space.

**Proof.** Each oracle language in logarithmic space is also in polynomial space, by `LOGSPACE_subset_PSPACE`. Apply the polynomial-space register simulation theorem `narm_decides_npspace` to these oracle languages, using the same register-size, halting, and acceptance hypotheses. It concludes that the language belongs to nondeterministic polynomial space.

**Key facts.** `Complexity.LOGSPACE_subset_PSPACE`, `Complexity.LogProg.narm_decides_npspace`.
