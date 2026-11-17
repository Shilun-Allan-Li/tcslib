<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/RegularThresholdNoiseStability.lean :: FABL.regularThresholdPairSum_mem_lowerLeft_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Lower-Left Quadrant Characterization

**Claim.** The pair sum lies in the lower-left quadrant exactly when both threshold values are $-1$.

**Proof.** The sum's first and second coordinates are the linear forms at $x$ and $y$. Since the signs are represented by the linear-form threshold, the threshold equals $-1$ exactly when the corresponding linear form is negative (homogeneous threshold characterization, `FABL.homogeneousThreshold_eq_neg_one_iff`). Membership in the lower-left quadrant, after substituting the sign $-1$ in each coordinate, says that both linear forms are nonpositive. The hypothesis that neither is zero upgrades these two inequalities to strict negativity, giving both threshold values $-1$. Conversely, strict negativity implies nonpositivity, so the two threshold values imply quadrant membership.

**Key facts.** `FABL.homogeneousThreshold_eq_neg_one_iff`, `FABL.regularThresholdPairSum_apply_zero`, `FABL.regularThresholdPairSum_apply_one`, `FABL.signValue_neg_one`.
