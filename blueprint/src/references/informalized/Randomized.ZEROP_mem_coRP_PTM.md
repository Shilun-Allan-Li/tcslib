<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/ZeroP.lean :: Randomized.ZEROP_mem_coRP_PTM -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Zero Polynomial Circuits Lie in coRP

**Claim.** The language of encodings of well-formed integer arithmetic circuits computing the zero polynomial belongs to coRP.

**Proof.** Use the established result that zero-polynomial testing belongs to the coRP polynomial-time model (`Randomized.inCoRP_ZEROP_polyTime`). The characterization of the coRP polynomial-time class identifies membership with that model (`Randomized.mem_coRP_PTM_iff`). Applying it to the established result proves the claim.

**Key facts.** `Randomized.inCoRP_ZEROP_polyTime`, `Randomized.mem_coRP_PTM_iff`.
