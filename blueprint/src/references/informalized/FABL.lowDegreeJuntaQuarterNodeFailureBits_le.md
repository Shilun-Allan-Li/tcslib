<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/LowDegreeJuntaResources.lean :: FABL.lowDegreeJuntaQuarterNodeFailureBits_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Quartered Node Failure Bits Bound

**Claim.** For all $k,b\ge0$, the failure-bit count for $\delta=1/(4T_k2^{b+1})$ is at most $\bigl(\lceil\log_2T_k\rceil+2(\lfloor3k/4\rfloor+1)+5\bigr)(b+1)$.

**Proof.** Let $T_k$ be the positive tree-call count and set $N=T_k2^{b+3}$. The node failure parameter followed by quartering has value $1/N$, by the dyadic-node and quarter-failure value formulas (`lowDegreeJuntaDyadicNodeFailure_value`, `lowDegreeJuntaQuarterFailure_value`). The failure-bit conversion lemma therefore identifies its bit count with $\lceil\log_2(2N)\rceil$ (`fourierEstimatorFailureBits_eq_clog_two_mul_denominator`). Since $2N=T_k2^{b+4}$, the binary logarithm of a product is bounded by the sum of the binary logarithms (`lowDegreeJuntaBinaryClog_mul_le`). Also $\lceil\log_2(2^{b+4})\rceil=b+4$. Thus the count is at most $\lceil\log_2T_k\rceil+b+4$. Expanding the confidence coefficient and using $b+1\ge1$ bounds this by the claimed product. Positivity of $T_k$, needed for the reciprocal parameter and the conversion, is supplied by `juntaTreeCallCount_pos`.

**Key facts.** `FABL.juntaTreeCallCount_pos`, `FABL.lowDegreeJuntaDyadicNodeFailure_value`, `FABL.lowDegreeJuntaQuarterFailure_value`, `FABL.fourierEstimatorFailureBits_eq_clog_two_mul_denominator`, `FABL.lowDegreeJuntaBinaryClog_mul_le`.
