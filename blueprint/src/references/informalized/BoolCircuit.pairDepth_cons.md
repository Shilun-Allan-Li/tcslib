<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/Parity.lean :: BoolCircuit.pairDepth_cons -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Pair Depth of a Leading Pair

**Claim.** The pair depth of a list beginning with $p$ is the maximum of the depths of the two circuits in $p$ and the pair depth of the remaining list.

**Proof.** The pair depth is defined by a right fold: each pair contributes the maximum of its two circuit depths, combined with the accumulated depth of the rest of the list. Unfolding this definition for a list with head $p$ and tail $ps$ gives exactly $\max(\max(\mathrm{depth}(p_1),\mathrm{depth}(p_2)),\mathrm{pairDepth}(ps))$.
