<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/LowDegreeJuntaResources.lean :: FABL.lowDegreeJuntaCoefficientFailureBits_le_linearConfidence -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Linear Bound on Coefficient Confidence Bits

**Claim.** With the stated failure parameter, the number of coefficient confidence failure bits is at most $L(n+1)(b+1)$, where $L=\lceil\log_2 T_k\rceil+2(\lfloor3k/4\rfloor+1)+5$ and $T_0=1$, $T_{j+1}=1+2T_j$.

**Proof.** Let $F=|\mathcal F|$ and $T=T_k$, and set $D=T F 2^{b+3}$. The Fourier family is nonempty (\(\texttt{FABL.lowDegreeJuntaFourierFamily_nonempty}\)), so $F>0$; also $T>0$ (\(\texttt{FABL.juntaTreeCallCount_pos}\)). The confidence-value formula (\(\texttt{FABL.lowDegreeJuntaCoefficientConfidence_value}\)), together with the dyadic node-failure value (\(\texttt{FABL.lowDegreeJuntaDyadicNodeFailure_value}\)), gives coefficient confidence $1/D$. The failure-bit conversion identity (\(\texttt{FABL.fourierEstimatorFailureBits_eq_clog_two_mul_denominator}\)) therefore expresses the number of bits as $\lceil\log_2(2D)\rceil$. Since $2D=(TF)2^{b+4}$, apply the product bound for the binary ceiling logarithm (\(\texttt{FABL.lowDegreeJuntaBinaryClog_mul_le}\)) twice, and use $\lceil\log_2(2^{b+4})\rceil=b+4$. This bounds the result by $\lceil\log_2 T\rceil+\lceil\log_2 F\rceil+b+4$. Finally, the family-cardinality logarithm bound (\(\texttt{FABL.clog_card_lowDegreeJuntaFourierFamily_le}\)) gives $\lceil\log_2 F\rceil\le(r+1)(n+2)\le2(r+1)(n+1)$. Each of the three resulting terms is bounded by its coefficient times $(n+1)(b+1)$: the tree term uses $n+1,b+1\ge1$, the family term uses the displayed estimate, and $b+4\le5(b+1)$. Adding them yields the claimed coefficient $\lceil\log_2 T\rceil+2(r+1)+5=L$.

**Key facts.** `FABL.lowDegreeJuntaFourierFamily_nonempty`, `FABL.juntaTreeCallCount_pos`, `FABL.lowDegreeJuntaCoefficientConfidence_value`, `FABL.lowDegreeJuntaDyadicNodeFailure_value`, `FABL.fourierEstimatorFailureBits_eq_clog_two_mul_denominator`, `FABL.lowDegreeJuntaBinaryClog_mul_le`, `FABL.clog_card_lowDegreeJuntaFourierFamily_le`.
