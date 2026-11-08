<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/SubspacesAndDecisionTrees/DecisionTreeFourier.lean :: FABL.F₂DecisionTree.isVectorFourierGranular_intCast_mul_pathIndicator -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourier Granularity of a Path Indicator

**Claim.** If a path has length at most $k$, then multiplying its indicator by any integer $z$ gives a function whose Fourier coefficients are integer multiples of $2^{-k}$.

**Proof.** The path indicator is Fourier granular at its inverse path size, by the result that every path indicator has granularity equal to the reciprocal of $2^{\mathrm{length}(P)}$ (`FABL.F₂DecisionTree.Path.isVectorFourierGranular_indicator`). Since $\mathrm{length}(P)\leq k$, the inverse path size is $2^{k-\mathrm{length}(P)}$ times $2^{-k}$; the scaling identity for inverse powers supplies this factor (`FABL.inverse_two_pow_eq_natCast_mul_inverse_two_pow`). The factor $2^{k-\mathrm{length}(P)}$ is an integer, so refining the granularity gives granularity $2^{-k}$ (`FABL.IsVectorFourierGranular.refine`). Finally, multiplying the function by the integer $z$ preserves this granularity (`FABL.IsVectorFourierGranular.intCast_mul`).

**Key facts.** `FABL.F₂DecisionTree.Path.isVectorFourierGranular_indicator`, `FABL.inverse_two_pow_eq_natCast_mul_inverse_two_pow`, `FABL.IsVectorFourierGranular.refine`, `FABL.IsVectorFourierGranular.intCast_mul`.
