<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/DNFFourier.lean :: FABL.restrictedFourierWeightAtLeast_le_switchingFailureIndicator -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourier tail and switching failure

**Claim.** The Fourier weight at degrees at least $k$ of an extended restriction is at most the indicator that its restricted decision-tree depth is at least $k$.

**Proof.** Split into two cases according to whether the restricted decision-tree depth is at least $k$. If it is, the indicator is $1$. Each term in the Fourier tail is nonnegative, and the coefficients of the extended restriction agree with the ambient restriction coefficients (`fourierCoeff_extendedSignRestriction`). Parseval's identity says that the sum of squares of all its Fourier coefficients is $1$ (`sum_sq_fourierCoeff_eq_one`), so the tail is at most $1$. If the depth is less than $k$, the degree bound for an extended restriction gives Fourier degree at most that depth (`fourierDegree_extendedSignRestriction_le_restrictedDecisionTreeDepth`). Every set of size at least $k$ then has size strictly greater than the Fourier degree, so its coefficient vanishes by the characterization of Fourier degree (`fourierDegree_le_iff`). All terms in the tail are consequently zero, matching the zero indicator.

**Key facts.** `FABL.fourierCoeff_extendedSignRestriction`, `FABL.sum_sq_fourierCoeff_eq_one`, `FABL.fourierDegree_extendedSignRestriction_le_restrictedDecisionTreeDepth`, `FABL.fourierDegree_le_iff`.
