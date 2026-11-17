<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/BiasedCoinHalting.lean :: Randomized.not_computablePred_haltDigit -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Undecidability of the Halting Digit Predicate

**Claim.** The predicate that holds exactly of codes in the halting set is not computable.

**Proof.** The halting digit predicate is membership in the halting set. The undecidability theorem for that set states directly that its membership predicate is not computable (`Nat.Partrec.Code.not_computablePred_mem_haltingSet`). Hence the halting digit predicate is not computable.

**Key facts.** `Nat.Partrec.Code.not_computablePred_mem_haltingSet`.
