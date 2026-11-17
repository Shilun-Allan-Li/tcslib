<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/LowDegreeJuntaResources.lean :: FABL.lowDegreeJuntaHalfNodeFailureBits_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Half-Node Failure-Bit Bound

**Claim.** For natural numbers $k$ and $b$, take the dyadic failure parameter $1/2^{b+1}$, divide it by the number of calls in the junta tree, and then halve it. The resulting number of failure bits is at most $\bigl(\lceil\log_2 T_k\rceil+2(\lfloor3k/4\rfloor+1)+5\bigr)(b+1)$, with $T_k$ the tree call count.

**Proof.** Write $T_k$ for the number of calls and set $D=T_k2^{b+2}$. The call count is positive (the positivity fact `juntaTreeCallCount_pos`), so the successive divisions defining the per-call and half-node parameters give the final parameter as $1/D$. By the reciprocal-denominator formula for failure bits (`fourierEstimatorFailureBits_eq_clog_two_mul_denominator`), its failure-bit count is therefore $\operatorname{clog}_2(2D)=\operatorname{clog}_2(T_k2^{b+3})$. Subadditivity of the binary ceiling logarithm (`lowDegreeJuntaBinaryClog_mul_le`) bounds this by $\operatorname{clog}_2(T_k)+\operatorname{clog}_2(2^{b+3})$. The second term is $b+3$, while $\operatorname{clog}_2(T_k)=\lceil\log_2 T_k\rceil$. Finally, the coefficient $\lceil\log_2 T_k\rceil+2(\lfloor3k/4\rfloor+1)+5$ is large enough that multiplying it by $b+1$ dominates their sum; this is the stated bound.

**Key facts.** `FABL.juntaTreeCallCount_pos`, `FABL.lowDegreeJuntaHalfFailure_value`, `FABL.lowDegreeJuntaDyadicNodeFailure_value`, `FABL.fourierEstimatorFailureBits_eq_clog_two_mul_denominator`, `FABL.lowDegreeJuntaBinaryClog_mul_le`.
