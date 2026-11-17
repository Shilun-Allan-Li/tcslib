<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/BiasedCoinHalting.lean :: Randomized.haltLang_mem_biasedBPP -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Halting Language in Biased Randomized Polynomial Time

**Claim.** The halting language belongs to biased randomized polynomial time with bias equal to the halting number, and the verifier accepts the correct answer with probability at least $2/3$ on every input.

**Proof.** The proof applies the general criterion that a Boolean verifier places a language in biased randomized polynomial time when the verifier runs in polynomial time and its probability of returning the correct membership indicator is at least $2/3$ on every input (Randomized.mem_biasedBPP_of_eff). For the halting-language verifier, these two hypotheses are supplied respectively by its polynomial-time efficiency (Randomized.eff_haltCoinVerifier) and its per-input probability bound (Randomized.haltCoinVerifier_prob). Applying the criterion gives the claimed class membership.

**Key facts.** `Randomized.eff_haltCoinVerifier`, `Randomized.haltCoinVerifier_prob`, `Randomized.mem_biasedBPP_of_eff`.
