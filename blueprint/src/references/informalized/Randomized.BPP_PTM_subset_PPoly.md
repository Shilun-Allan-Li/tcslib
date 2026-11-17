<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/PTMEquiv.lean :: Randomized.BPP_PTM_subset_PPoly -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial Circuit Simulation of BPP

**Claim.** Every language decidable by a bounded-error randomized Turing machine in polynomial time is decided by a family of Boolean circuits of fan-in at most two whose sizes are bounded by a polynomial in the input length.

**Proof.** Start with a language in the polynomial-time randomized class and translate its witness to the polynomial-time BPP model (`Randomized.inBPP_of_mem_BPP_PTM`). Adleman's theorem converts any language accepted by that model into a polynomial-size family of fan-in-two Boolean circuits (`Randomized.adleman_polyTime`), yielding the required circuit-size property. Finally, the characterization of membership in the circuit class identifies this property with membership in PPoly (`BoolCircuit.mem_PPoly_iff`).

**Key facts.** `Randomized.inBPP_of_mem_BPP_PTM`, `Randomized.adleman_polyTime`, `BoolCircuit.mem_PPoly_iff`.
