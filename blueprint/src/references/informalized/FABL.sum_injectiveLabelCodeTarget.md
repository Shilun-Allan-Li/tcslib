<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/MatchingMomentCombinatorics.lean :: FABL.sum_injectiveLabelCodeTarget -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Weighted Sum over Labeled Subsets

**Claim.** Summing a weight over each $k$-element subset together with every bijective labeling of that subset equals $k!$ times the sum of the weights over the subsets.

**Proof.** Group the sum over labeled subsets by its underlying $k$-element subset. For a fixed subset $S$, every bijection from the $k$-element label set to $S$ contributes the same value $w(S)$. There are $k!$ such bijections, since the elements of $S$ can be bijectively matched with the labels in exactly as many ways as there are permutations of $k$ elements. Thus the contribution of this fiber is $k!w(S)$; summing over $S$ gives the stated identity.
