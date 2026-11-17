<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/ZeroP.lean :: Randomized.ZEROP_mem_BPP_PTM -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Zero Polynomial Testing in Bounded Error Polynomial Time

**Claim.** The language of encodings of well-formed integer arithmetic circuits computing the zero polynomial has a randomized polynomial-time decision procedure with the stated halting and correctness guarantees.

**Proof.** The proof uses the established result that zero-polynomial testing belongs to the bounded-error polynomial-time model (`Randomized.inBPP_ZEROP_polyTime`). The characterization of membership in the polynomial-time BPP class identifies that model with membership in the union of polynomial-time bounds used to define $\mathrm{BPP\_PTM}$ (`Randomized.mem_BPP_PTM_iff`). Applying this characterization to the established result gives the claim.

**Key facts.** `Randomized.inBPP_ZEROP_polyTime`, `Randomized.mem_BPP_PTM_iff`.
