<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/ThresholdFunctions/BitFlipSets.lean :: BooleanAnalysis.ThresholdFunctions.sum_comp_flipSet -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Invariance of cube sums under flips

**Claim.** For any function on the Boolean cube, summing its values after flipping a fixed set of coordinates gives the same sum as summing its original values.

**Proof.** For a fixed set of coordinates $S$, flipping those coordinates twice returns every cube point to itself (`flipSet_flipSet`). Thus the map $x\mapsto x^S$ is an involution, hence a permutation of the finite Boolean cube. Reindexing a finite sum by a permutation preserves its value, giving $\sum_x F(x^S)=\sum_x F(x)$.

**Key facts.** `BooleanAnalysis.ThresholdFunctions.flipSet_flipSet`.
