<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/BLR/LowDegree.lean :: LowDegreeTest.linear_mem_ReedMuller_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Linear functions have degree at most one

**Claim.** Every linear Boolean function belongs to the degree-one Reed–Muller code.

**Proof.** By the fact that every linear Boolean function has degree at most one (`LowDegreeTest.linear_is_degree_le_one`), the given function satisfies the defining degree condition. Membership in the Reed–Muller code is exactly that condition, so it belongs to `ReedMuller 1 n`.

**Key facts.** `LowDegreeTest.linear_is_degree_le_one`.
