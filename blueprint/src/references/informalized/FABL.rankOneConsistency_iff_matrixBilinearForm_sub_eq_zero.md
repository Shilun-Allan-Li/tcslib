<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/AlgebraicPCPP.lean :: FABL.rankOneConsistency_iff_matrixBilinearForm_sub_eq_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Rank-one consistency equivalence

**Claim.** The rank-one pairing agrees with the pairing defined by $\Gamma$ exactly when the bilinear form of $\Gamma-\gamma\gamma^{\mathsf T}$ vanishes.

**Proof.** The pairing of the rank-one matrix with $x,y$ equals $(\gamma^{\mathsf T}x)(\gamma^{\mathsf T}y)$ (`matrixRankOnePairing_rankOneSelfMatrix`). Also, a matrix bilinear form is its corresponding matrix pairing (`matrixBilinearForm_eq_matrixRankOnePairing`), and pairing is additive in the matrix, so pairing with $\Gamma-\gamma\gamma^{\mathsf T}$ is the pairing with $\Gamma$ minus the rank-one pairing (`matrixRankOnePairing_sub`). Therefore the bilinear form vanishes exactly when the pairing with $\Gamma$ equals the rank-one pairing, as claimed.

**Key facts.** `FABL.matrixRankOnePairing_rankOneSelfMatrix`, `FABL.matrixBilinearForm_eq_matrixRankOnePairing`, `FABL.matrixRankOnePairing_sub`.
