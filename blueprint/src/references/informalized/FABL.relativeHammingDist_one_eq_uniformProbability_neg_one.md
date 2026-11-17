<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter01/BasicFourierFormulas.lean :: FABL.relativeHammingDist_one_eq_uniformProbability_neg_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Distance from the Constant One Function

**Claim.** For a sign-valued Boolean function $f$, its relative Hamming distance from the constant function $1$ is the uniform probability that $f(x)=-1$.

**Proof.** The relative Hamming distance is the uniform probability of the event $f(x)\ne 1$ (\texttt{uniformProbability\_ne\_eq\_relativeHammingDist}). Since every value of $f$ is a sign, it is either $1$ or $-1$. Thus $f(x)\ne1$ holds exactly when $f(x)=-1$. The two probabilities agree pointwise in their defining averages, giving the claimed equality.

**Key facts.** `FABL.uniformProbability_ne_eq_relativeHammingDist`.
