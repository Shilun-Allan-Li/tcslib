<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/CircuitSatNPHard.lean :: BoolCircuit.ofFn_getD_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reconstruction of a list from indexed values

**Claim.** If a Boolean list $u$ has length $m$, then listing its values at indices $0$ through $m-1$, with default value false, recovers exactly $u$.

**Proof.** Replace $m$ by the given length of $u$. The reconstructed list and $u$ have the same length. To establish equality, compare their entries at each valid index: the entry produced by the finite-index enumeration is precisely the value of $u$ at that index, and the index is within the list's length, so the default value is not used. Hence the lists agree entry by entry.
