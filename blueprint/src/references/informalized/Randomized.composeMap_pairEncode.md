<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Reductions.lean :: Randomized.composeMap_pairEncode -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Composition on Encoded Pairs

**Claim.** Applying the composition map to the encoding of $(x,t)$ yields the encoding whose first component is $f$ applied to the encoding of $x$ with the first $a_1(|x|+1)^{k_1}$ bits of $t$, and whose second component is the first $a_2(|y|+1)^{k_2}$ bits of the remaining suffix, where $y$ is that first component.

**Proof.** Unfold the composition map and its two slice operations. Decoding the pair encoding of $(x,t)$ recovers $x$ and $t$, so the first slice is the pair encoding of $x$ together with the prescribed prefix of $t$. The second slice drops that prefix, leaving the corresponding suffix. Applying the composition map’s outer slice to the encoding of the transformed first component and this suffix keeps the prefix of the suffix of length $a_2(|y|+1)^{k_2}$. These reductions give exactly the stated pair encoding.
