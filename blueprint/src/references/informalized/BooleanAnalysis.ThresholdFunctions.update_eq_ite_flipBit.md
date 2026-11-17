<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/ThresholdFunctions/LinearThresholdInfluence.lean :: BooleanAnalysis.ThresholdFunctions.update_eq_ite_flipBit -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Coordinate update by bit flip

**Claim.** Replacing coordinate $i$ of $x$ by $b$ gives $x$ if $x_i=b$, and otherwise gives the vector obtained by flipping bit $i$.

**Proof.** If $x_i=b$, updating coordinate $i$ to $b$ leaves every coordinate unchanged, so the result is $x$. If $x_i\ne b$, then, since both entries are Boolean, $b=\neg x_i$. The update therefore replaces the $i$th coordinate by its flipped value and leaves all other coordinates unchanged, which is precisely the bit-flipped vector.
