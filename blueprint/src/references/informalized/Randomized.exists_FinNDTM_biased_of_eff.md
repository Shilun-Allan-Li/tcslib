<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/BiasedCoin.lean :: Randomized.exists_FinNDTM_biased_of_eff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Simulation with Biased Random Bits

**Claim.** An efficient verifier M can be implemented by a finite nondeterministic machine that halts on every sufficiently long choice word and whose output distribution under a ρ-biased choice process is exactly the distribution of M on a uniformly ρ-biased random string of the prescribed polynomial length.

**Proof.** First use the mask-selection construction (`Randomized.exists_FinNDTM_maskSelect_of_eff`). It supplies fixed polynomial bounds K,e and a machine N. For each input x, it supplies an offset s and a Boolean mask: the mask has exactly polyLen(a,k,|x|) true entries, and the offset plus mask length fits within the total choice-word length K(|x|^e+1). On every choice word of that length, N halts and outputs the bit M(x,u), where u is obtained by applying the mask to the designated segment of the choice word.

For a fixed ρ and output bit b, compare the event that N outputs b with the event that the selected word u satisfies M(x,u)=b. On every choice word of the full length these events agree, since N's output is the singleton containing M(x,u); hence their biased probabilities agree (`Randomized.biasedProb_congr`). The first s bits and any unused suffix do not affect the selected segment, so removing them preserves its biased distribution (`Randomized.biasedProb_drop_take`). Applying the mask to a biased word of mask length produces the same distribution as a biased word whose length is the number of true mask entries (`Randomized.biasedProb_maskSelect`). That count is polyLen(a,k,|x|), as required. The machine's halting property is already supplied by the mask-selection construction.

**Key facts.** `Randomized.exists_FinNDTM_maskSelect_of_eff`, `Randomized.biasedProb_congr`, `Randomized.biasedProb_drop_take`, `Randomized.biasedProb_maskSelect`.
