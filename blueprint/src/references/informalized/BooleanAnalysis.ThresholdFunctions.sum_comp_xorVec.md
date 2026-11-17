<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/ThresholdFunctions/BitFlipSets.lean :: BooleanAnalysis.ThresholdFunctions.sum_comp_xorVec -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Invariance of cube sums under XOR translations

**Claim.** For any function on the Boolean cube, summing its values after coordinatewise XOR with a fixed vector gives the same sum as summing its original values.

**Proof.** XORing a vector $c$ twice cancels it coordinatewise, so $z\mapsto z\oplus c$ is an involution (`xorVec_xorVec`). It is therefore a permutation of the finite Boolean cube. Reindexing the sum by this permutation yields the claimed equality.

**Key facts.** `BooleanAnalysis.ThresholdFunctions.xorVec_xorVec`.
