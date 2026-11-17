<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/SAT.lean :: Complexity.sat_pt_head -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Length-One Prefix

**Claim.** The function sending each bit string to its prefix of length at most one is polynomial-time computable.

**Proof.** Use the polynomial-time finite-state word-mapping construction (`Complexity.satMap_poly`) with a two-state behavior: the starting state emits the first input bit and switches to the other state, while that other state emits nothing thereafter. The finishing output is empty. Thus the output on the empty input is empty, and on any nonempty input it consists precisely of its first bit, which is the prefix of length at most one.

**Key facts.** `Complexity.satMap_poly`.
