<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/KKLBribery.lean :: FABL.coalitionSuccessProbability_coordinatePolarization_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Coalition Success Under Coordinate Polarization

**Claim.** The fraction of inputs from which coalition $J$ can make the polarized function attain $b$ is at most the corresponding fraction for $f$.

**Proof.** Write each success probability as the mean of the indicator of the corresponding attainability event. Averaging over the coordinate $i$ does not change a mean (`mean_coordinateExpectation`), and the coordinate average at an input is the average of the two indicators with coordinate $i$ fixed to $1$ and $-1$ (`coordinateExpectation_apply`). It therefore suffices to compare the sums of these two indicators for each pair of inputs.

If $i\in J$, attainability for the polarized function at either fixed input implies attainability for $f$ at that same input (`coalitionCanAttain_coordinatePolarization_imp_of_mem`). The indicator sum for the polarized function is consequently no larger, by the implication comparison for indicator pairs (`indicator_pair_le_of_imp`).

If $i\notin J$, split into the two possible signs of $b$. For $b=1$, success at the polarized input with coordinate $i$ equal to $1$ implies success for $f$ at one of the two fixed inputs (`coalitionCanAttain_coordinatePolarization_one_set_one_imp`), while success at the polarized input with coordinate $i$ equal to $-1$ implies success for $f$ at both (`coalitionCanAttain_coordinatePolarization_one_set_neg_one_imp`). These implications give the required pairwise indicator comparison (`indicator_pair_le_of_union_inter`). For $b=-1$, use the corresponding implications: success at the polarized input with coordinate $i$ equal to $1$ gives success for $f$ at both fixed inputs, and success at the input with coordinate $i$ equal to $-1$ gives success at one of them (`coalitionCanAttain_coordinatePolarization_neg_one_set_one_imp`, `coalitionCanAttain_coordinatePolarization_neg_one_set_neg_one_imp`). The same indicator comparison applies. Since these pointwise comparisons hold for every input, the pointwise mean inequality (`mean_le_mean_of_pointwise`) proves the claimed bound.

**Key facts.** `FABL.mean_coordinateExpectation`, `FABL.coordinateExpectation_apply`, `FABL.coalitionCanAttain_coordinatePolarization_imp_of_mem`, `FABL.indicator_pair_le_of_imp`, `FABL.coalitionCanAttain_coordinatePolarization_one_set_one_imp`, `FABL.coalitionCanAttain_coordinatePolarization_one_set_neg_one_imp`, `FABL.indicator_pair_le_of_union_inter`, `FABL.coalitionCanAttain_coordinatePolarization_neg_one_set_one_imp`, `FABL.coalitionCanAttain_coordinatePolarization_neg_one_set_neg_one_imp`, `FABL.mean_le_mean_of_pointwise`.
