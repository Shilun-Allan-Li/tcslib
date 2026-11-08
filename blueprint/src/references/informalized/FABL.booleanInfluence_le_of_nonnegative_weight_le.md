<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/LinearThresholdInfluence.lean :: FABL.booleanInfluence_le_of_nonnegative_weight_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Influence monotonicity under ordered weights

**Claim.** For a threshold function represented by an affine linear form, if two coordinate weights are nonnegative and the first is at most the second, then the first coordinate's influence is at most the second's.

**Proof.** If the coordinates coincide, the influences are equal. Otherwise, compare pivotality pointwise after swapping the two coordinates. A pivotal input for the smaller weight has its affine remainder in the interval $[-|a_i|,|a_i|)$ (`isPivotal_linearThreshold_iff`). The affine-remainder identities show that, after swapping, the remainder for coordinate $j$ differs by replacing the contribution of weight $a_i$ with that of weight $a_j$ (`affineLinearRemainder_eq_two_add` and `affineLinearRemainder_permute_swap_eq`). Because both weights are nonnegative and $a_i\le a_j$, checking the two possible signs of the original $j$th coordinate shows that this new remainder lies in $[-|a_j|,|a_j|)$. The interval criterion therefore makes the swapped input pivotal for coordinate $j$. Thus the pivotal-event indicator for $i$ is pointwise bounded by the indicator for $j$ after the swap, and taking expectations preserves the inequality. Finally, swapping coordinates is a bijection of the cube, so the latter expectation equals the unpermuted influence of $j.

**Key facts.** `FABL.isPivotal_linearThreshold_iff`, `FABL.affineLinearRemainder_permute_swap_eq`, `FABL.affineLinearRemainder_eq_two_add`.
