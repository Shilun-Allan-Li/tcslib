<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/UniformNoiseStability.lean :: FABL.map_uniformFin_fiberFlip_eq_coordinateNoisePMF -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Coordinate Flip and Noise Distribution

**Claim.** For positive $m$, a coordinate $j\in\{1,\ldots,m\}$, and $x\in\{-1,1\}$, choosing a coordinate uniformly and outputting $-x$ if it is $j$ and $x$ otherwise gives the coordinate noise distribution at $x$ with correlation parameter $1-2/m$.

**Proof.** Write $\delta=1/m$ and $\rho=1-2\delta$. The admissible range for $\delta$ implies that $\rho\in[-1,1]$, so the coordinate noise distribution is defined. Its probability of keeping $x$ is $p=(1+\rho)/2=1-\delta$, and its probability of flipping to $-x$ is consequently $1-p=\delta$. For the uniform choice of a coordinate, exactly one of the $m$ choices flips $x$, so the flip probability is $1/m=\delta$; the other $m-1$ choices keep it, with probability $(m-1)/m=1-\delta$. Thus the two distributions agree at both possible signs. The proof verifies these probabilities using the noise distribution's self and negation formulas (\texttt{coordinateNoisePMF\_apply\_self'} and \texttt{coordinateNoisePMF\_apply\_neg'}), together with the finite-coordinate count (\texttt{sum\_fin\_ite\_ne'}).

**Key facts.** `FABL.inverseDimension_mem_Icc`, `FABL.one_sub_two_mul_mem_Icc`, `FABL.correlationKeepProbability_le_one`, `FABL.sum_fin_ite_ne`, `FABL.coordinateNoisePMF_apply_self'`, `FABL.coordinateNoisePMF_apply_neg'`.
