<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/HardWire.lean :: BoolCircuit.DAGCircuit.leftPerm_injective -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Injectivity of the Interval Permutation

**Claim.** The map that sends indices below $m$ to $n+v$, indices from $m$ up to but not including $m+n$ to $v-m$, and fixes indices at least $m+n$ is injective.

**Proof.** Suppose two indices have the same image. Split according to whether each lies below $m$, in the interval from $m$ to $m+n$, or at least $m+n$. In each of the resulting cases, the defining formulas for the map and the corresponding interval bounds force the two indices to be equal: within each region the formula is injective, while images from distinct regions lie in disjoint intervals. Thus the indices coincide.

**Caveat.** The source proof relies on arithmetic case analysis to discharge all combinations of the three regions; the detailed inequalities are not stated explicitly there.
