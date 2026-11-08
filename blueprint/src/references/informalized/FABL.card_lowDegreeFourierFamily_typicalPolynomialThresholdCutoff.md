<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/PrescribedFourierSupport.lean :: FABL.card_lowDegreeFourierFamily_typicalPolynomialThresholdCutoff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Size at the typical cutoff

**Claim.** For each natural number $n$, the number of subsets of an $n$-element set having size at most the typical cutoff $t_n$ is at least $\left(1-\frac{(1/2)^2}{6n}\right)2^n$.

**Proof.** If $n=0$, direct evaluation gives the claimed inequality. Suppose $n>0$. Consider the points of the Boolean cube whose positive-coordinate count exceeds $t_n$, and the subsets of $[n]$ whose size exceeds $t_n$. The probability of the former event under the uniform cube distribution is at most $1/(24n)$ (`measure_positiveCoordinateCount_gt_typicalCutoff_le`). Uniform measure on a finite space is the number of points in the event divided by the size of the space (`measure_uniformPMF_real_eq_ncard_div_card`), and the two events have equal cardinality (`ncard_positiveCoordinateCount_gt_typicalCutoff`). Since the cube has $2^n$ points, the number of subsets of size greater than $t_n$ is therefore at most $2^n/(24n)$. The low-degree family and this high-size family partition all subsets, so their cardinalities sum to $2^n$ (`card_lowDegreeFourierFamily_add_ncard_high`). Subtracting the high-size bound leaves at least $(1-1/(24n))2^n$. Finally, $(1/2)^2/(6n)=1/(24n)$, giving the stated bound.

**Key facts.** `FABL.measure_positiveCoordinateCount_gt_typicalCutoff_le`, `FABL.measure_uniformPMF_real_eq_ncard_div_card`, `FABL.ncard_positiveCoordinateCount_gt_typicalCutoff`, `FABL.card_lowDegreeFourierFamily_add_ncard_high`.
