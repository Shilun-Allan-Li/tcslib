<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/AlgebraicPCPP.lean :: FABL.innerProductPrefixBit_full -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Full inner product prefix

**Claim.** For a Boolean vector $w$ of length $2m$, the sum of the products of corresponding bits in its two halves, computed in $\mathbb{F}_2$, equals the inner product bit of those halves.

**Proof.** Unfold the prefix sum and the inner product bit, and express the latter as a sum over all coordinates of the first half. Both sums now range over $i<m$. For each such $i$, the summand in the prefix is the product of the Boolean-to-$\mathbb{F}_2$ images of the two bits at positions $i$ and $i+m$. The two halves of the joined-coordinate identification select precisely those positions, so the summands agree coordinate by coordinate. The pointwise identification of a Boolean cube coordinate (`pcppBoolCubeEquiv_apply`) justifies reading each selected coordinate as the corresponding bit in $\mathbb{F}_2$.

**Key facts.** `FABL.pcppBoolCubeEquiv_apply`.
