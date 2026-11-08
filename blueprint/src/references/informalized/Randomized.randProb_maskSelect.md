<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/PTMEquiv.lean :: Randomized.randProb_maskSelect -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Probability Under Mask Selection

**Claim.** For a finite Boolean mask and any predicate on Boolean words, applying the mask to a uniformly random word of the mask's length gives the same probability of satisfying the predicate as a uniformly random word whose length is the number of true mask entries.

**Proof.** Induct on the mask. For the empty mask, the input has length zero and selection produces the empty word, so both probabilities agree. For a mask beginning with false, the first input bit is discarded; selection on the remaining mask therefore has the same distribution as selection from a uniform word of the shorter length. The probability that a predicate holds after selection is the average of its probabilities under the two possible first bits (`Randomized.randProb_succ`); because that bit is discarded, the two terms are equal, and the induction hypothesis identifies their common value with the probability for the shorter mask. For a mask beginning with true, the first input bit is retained. Split the probability according to whether this bit is true or false. In the two cases the resulting selected word is respectively the first bit followed by the selection from the tail. The induction hypothesis, applied to the predicates obtained by fixing that initial bit, identifies these two conditional probabilities with the corresponding probabilities for uniform words of the tail mask's selected length. Averaging them gives exactly the probability for a uniform word one bit longer, again by the one-bit averaging rule. The number of true entries increases by one precisely in this true-mask case, as required.

**Key facts.** `Randomized.randProb_congr`, `Randomized.randProb_succ`.
