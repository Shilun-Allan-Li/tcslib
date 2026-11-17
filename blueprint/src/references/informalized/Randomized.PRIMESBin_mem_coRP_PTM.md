<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Primality.lean :: Randomized.PRIMESBin_mem_coRP_PTM -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# PRIMES in co-RP

**Claim.** The language of bit strings whose encoded natural number is prime belongs to co-RP with polynomial time bound.

**Proof.** The proof uses the established co-RP characterization of the language: `inCoRP_PRIMESBin` gives membership in the abstract class `InCoRP` for the polynomial-time model. The equivalence `mem_coRP_PTM_iff` identifies that class with membership in `coRP_PTM`, yielding the result. The number-theoretic testing argument is contained in the cited membership theorem and is not reproved here.

**Key facts.** `Randomized.inCoRP_PRIMESBin`, `Randomized.mem_coRP_PTM_iff`.
