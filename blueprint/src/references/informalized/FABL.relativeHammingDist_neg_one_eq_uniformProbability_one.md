<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter01/BasicFourierFormulas.lean :: FABL.relativeHammingDist_neg_one_eq_uniformProbability_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Distance from the Constant Negative Function

**Claim.** For a Boolean-valued function $f$ on the sign cube, its relative Hamming distance from the constant function $-1$ equals the uniform probability that $f$ takes the value $1$.

**Proof.** First express the relative Hamming distance as the uniform probability of disagreement (\(\texttt{uniformProbability\_ne\_eq\_relativeHammingDist}\)). Each value of $f$ is either $1$ or $-1$. Therefore, at each input, disagreement with the constant value $-1$ occurs exactly when $f$ equals $1$. The two indicator functions, and hence their uniform averages, agree.

**Key facts.** `FABL.uniformProbability_ne_eq_relativeHammingDist`.
