<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/RandomBits.lean :: Randomized.exists_ofFn_of_randProb_pos -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Positive Probability Gives a Witness

**Claim.** If a decidable property of length-$m$ Boolean lists has positive randomized probability, then it holds for the list associated with some function from $\mathrm{Fin}(m)$ to the Booleans.

**Proof.** Suppose, for contradiction, that the property fails on every list associated with a function from $\mathrm{Fin}(m)$ to the Booleans. On all inputs counted in the definition of randomized probability, the property is then equivalent to false. The invariance of randomized probability under such pointwise equivalence (`Randomized.randProb_congr`) identifies its probability with that of the constantly false property, which is zero (`Randomized.randProb_false`). This contradicts the assumed strict positivity.

**Key facts.** `Randomized.randProb_congr`, `Randomized.randProb_false`.
