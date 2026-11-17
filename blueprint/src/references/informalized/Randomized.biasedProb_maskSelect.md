<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/BiasedCoin.lean :: Randomized.biasedProb_maskSelect -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Biased Probability Under Mask Selection

**Claim.** For any real bias parameter, Boolean mask, and predicate $A$, the biased probability that applying the mask to a random string of length equal to the mask length produces a string satisfying $A$ equals the biased probability of $A$ on strings whose length is the number of true entries in the mask.

**Proof.** Induct on the mask, allowing $A$ to vary. For the empty mask, selection always produces the empty string, and the number of selected entries is zero, so both sides are the same. For a nonempty mask, consider its first entry. If it is false, that bit is discarded by selection and contributes no selected entry. The two first-bit branches of the probability therefore reduce to the same predicate on the shorter mask; by induction they have the same probability, and their weights sum to $\rho+(1-\rho)=1$. If the first entry is true, selection retains the first random bit and then applies the remaining mask. In the true branch the remaining predicate is obtained by prefixing true to the output of the shorter mask; in the false branch it is obtained by prefixing false. The induction hypothesis identifies each branch probability with the corresponding biased probability on the number of selected entries in the shorter mask. The recursion for biased probability (`Randomized.biasedProb_succ`) then combines those branches into the probability for one additional selected entry, as required.

**Key facts.** `Randomized.biasedProb_succ`.
