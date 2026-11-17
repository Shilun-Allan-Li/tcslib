<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/AlmostKWiseAlgorithm.lean :: FABL.AlmostKWiseInput.smallBiasScale_le_outputScale -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Small bias scale bound

**Claim.** The small-bias scale is at most the output scale.

**Proof.** By the ceiling-division criterion, it suffices to show that the product of the row count and the denominator is at most the numerator times the output scale. The reciprocal scale satisfies $N\leq (\text{numerator})R$, again by the ceiling-division criterion. The row count is at most the size scale, so multiplying first this inequality and then the reciprocal-scale inequality gives $\text{rowCount}\cdot N\leq S\cdot(\text{numerator})R$. Since the output scale is $SR$, this is the required bound.

**Key facts.** `FABL.AlmostKWiseInput.rowCount_le_sizeScale`.
