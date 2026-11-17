<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/RegularThresholdNoiseStability.lean :: FABL.noiseStability_eq_four_mul_lowerLeftProbability_sub_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Stability and Lower-Left Probability

**Claim.** If a Boolean function has mean zero under the uniform distribution, then its noise stability is four times the probability that both correlated inputs have value $-1$, minus one.

**Proof.** Balance means that the uniform mean of the function is zero. Each marginal of the correlated pair is uniform, so the expectations of the function on the first and second inputs are both zero (\texttt{pmfExpectation_correlatedPairPMF_fst}, \texttt{pmfExpectation_correlatedPairPMF_snd}, and \texttt{pmfExpectation_uniformPMF_eq_expect}). For signs $u,v\in\{-1,1\}$, the pointwise identity $uv=4\mathbf 1_{\{u=-1,\,v=-1\}}-1+u+v$ holds by checking the four possible pairs. Take expectations of this identity. Linearity of expectation, its value on constants, and extraction of a constant factor (\texttt{pmfExpectation_add}, \texttt{pmfExpectation_const}, and \texttt{pmfExpectation_const_mul}) turn the right-hand side into four times the lower-left probability minus one, since the two marginal-mean terms vanish.

**Key facts.** `FABL.pmfExpectation_correlatedPairPMF_fst`, `FABL.pmfExpectation_uniformPMF_eq_expect`, `FABL.pmfExpectation_correlatedPairPMF_snd`, `FABL.pmfExpectation_add`, `FABL.pmfExpectation_const_mul`, `FABL.pmfExpectation_const`.
