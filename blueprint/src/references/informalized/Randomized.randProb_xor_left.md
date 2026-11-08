<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/SipserGacs.lean :: Randomized.randProb_xor_left -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Invariance Under a Fixed XOR Mask

**Claim.** For a uniformly random Boolean vector of length $m$, applying entrywise XOR with a fixed vector $c$ does not change the probability of any property of the resulting bit string.

**Proof.** For any length-$m$ vector $r$, the lists formed by taking entrywise XOR of $r$ with $c$, or of $c$ with $r$, agree: XOR on Boolean entries is commutative, coordinate by coordinate. The probability-congruence principle (`randProb_congr`) therefore lets us rewrite the probability with the mask on the left. The fixed-mask invariance result (`randProb_xor_right`) says this rewritten probability equals the probability of the original property, as required.

**Key facts.** `Randomized.zipWith_ofFn`, `Randomized.randProb_congr`, `Randomized.randProb_xor_right`.
