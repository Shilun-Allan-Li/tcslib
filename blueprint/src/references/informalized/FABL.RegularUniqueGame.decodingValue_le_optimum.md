<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/UniqueGamesReduction.lean :: FABL.RegularUniqueGame.decodingValue_le_optimum -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Decoding value is bounded by the optimum

**Claim.** The decoding value formed from the notable-coordinate candidate sets is at most the optimum value of the finite unique-game constraint instance associated with $G$.

**Proof.** Use the bound for the candidate decoding value (`FABL.RegularUniqueGame.candidateDecodingValue_le_optimum`) with the candidate sets produced by the decoding procedure. By definition, the decoding value is this candidate decoding value for those sets, yielding the claimed upper bound.

**Key facts.** `FABL.RegularUniqueGame.candidateDecodingValue_le_optimum`.
