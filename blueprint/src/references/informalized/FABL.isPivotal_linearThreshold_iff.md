<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/LinearThresholdInfluence.lean :: FABL.isPivotal_linearThreshold_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Affine threshold pivotality

**Claim.** For the stated affine threshold function, pivotality at $x$ in coordinate $i$ is equivalent to $-|a_i|\le R_i(x)<|a_i|$.

**Proof.** By the criterion for pivotality using the two fixed coordinate values (FABL.isPivotal_iff_setCoordinate_ne), it suffices to compare the threshold outputs after setting coordinate $i$ to $+1$ and to $-1$. The affine form at these inputs is respectively $R_i(x)+a_i$ and $R_i(x)-a_i$, by the coordinate decomposition of the affine form (FABL.affineLinearForm_setCoordinate). The threshold comparison fact (FABL.thresholdSign_add_ne_sub_iff) says these two threshold signs differ exactly when $-|a_i|\le R_i(x)<|a_i|$.

**Key facts.** `FABL.isPivotal_iff_setCoordinate_ne`, `FABL.affineLinearForm_setCoordinate`, `FABL.thresholdSign_add_ne_sub_iff`.
