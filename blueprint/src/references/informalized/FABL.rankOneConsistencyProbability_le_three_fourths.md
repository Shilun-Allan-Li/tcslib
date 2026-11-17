<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/AlgebraicPCPP.lean :: FABL.rankOneConsistencyProbability_le_three_fourths -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Rank-one consistency bound

**Claim.** If $\Gamma$ differs from the rank-one matrix with entries $\gamma_i\gamma_j$, then the probability that the two pairings agree is at most $3/4$.

**Proof.** Let $D=\Gamma-\gamma\gamma^{\mathsf T}$. Since $\Gamma\ne\gamma\gamma^{\mathsf T}$, we have $D\ne0$. The rank-one consistency equivalence (`rankOneConsistency_iff_matrixBilinearForm_sub_eq_zero`) identifies agreement of the two pairings with the event that the bilinear form associated to $D$ vanishes. Thus the consistency probability is one minus the probability that this form is nonzero; this follows by taking expectations of the complementary indicator functions. The nonzero bilinear-form bound (`one_fourth_le_matrixBilinearNonzeroProbability`) says that the latter probability is at least $1/4$. Subtracting from one gives the upper bound $3/4$.

**Key facts.** `FABL.rankOneConsistency_iff_matrixBilinearForm_sub_eq_zero`, `FABL.one_fourth_le_matrixBilinearNonzeroProbability`.
