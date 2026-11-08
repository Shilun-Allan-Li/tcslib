<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/NoiseStability/NoiseOperator.lean :: FABL.coe_normalizedCorrelatedSignSumMeasure_disagreement_eq_majority -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Majority and Gaussian Disagreement

**Claim.** For odd $n$, the probability that the normalized correlated sign sum lies in the disagreement region equals the probability that the two correlated inputs have different majority values.

**Proof.** Regard the probability of the disagreement region as the integral of its indicator. The normalized correlated sign sum measure is the pushforward of the correlated pair distribution under the normalized-sum map (\texttt{normalizedCorrelatedSignSumMeasure\_eq\_map\_correlatedPairPMF}). Since the disagreement region is open, its indicator is measurable, and the change-of-variables formula for a pushforward measure rewrites the integral as an expectation over correlated input pairs. By the finite-distribution expectation formula (\texttt{pmfExpectation\_eq\_integral}), this is the defining finite sum for the disagreement probability. For each pair, membership of its normalized sum in the disagreement region is equivalent, when $n$ is odd, to the two majority values differing (\texttt{normalizedCorrelatedPairSum\_mem\_disagreement\_iff\_majority\_ne}). Thus the two summands agree pointwise, whether the majority values differ or coincide, and so do the expectations.

**Key facts.** `FABL.isOpen_gaussianDisagreementRegion`, `FABL.normalizedCorrelatedSignSumMeasure_eq_map_correlatedPairPMF`, `FABL.pmfExpectation_eq_integral`, `FABL.normalizedCorrelatedPairSum_mem_disagreement_iff_majority_ne`.
