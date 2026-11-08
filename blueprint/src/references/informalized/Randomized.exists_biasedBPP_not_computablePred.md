<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/BiasedCoinHalting.lean :: Randomized.exists_biasedBPP_not_computablePred -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# A Biased BPP Language Beyond Computability

**Claim.** There are a bias ρ between zero and one and a noncomputable language of bit strings that belongs to biased BPP at bias ρ.

**Proof.** Choose ρ to be haltCoin and choose L to be haltLang. The established bound on haltCoin gives 0 ≤ ρ and ρ ≤ 1/3, hence also ρ ≤ 1 (`Randomized.haltCoin_mem`). The halting language is not computable (`Randomized.not_computablePred_haltLang`), while it belongs to biased BPP at this bias (`Randomized.haltLang_mem_biasedBPP`). These choices give all the required properties.

**Key facts.** `Randomized.haltCoin_mem`, `Randomized.not_computablePred_haltLang`, `Randomized.haltLang_mem_biasedBPP`.
