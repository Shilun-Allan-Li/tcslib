<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/HastadThreeSat.lean :: FABL.signPMFOfMean_scaled_sign_apply_self_toReal -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Probability of Retaining a Scaled Sign

**Claim.** For $0\le\delta\le1$ and a sign $b$, the sign distribution with mean $(1-\delta)b$ assigns probability $1-\delta/2$ to $b$.

**Proof.** Since every sign is either $1$ or $-1$, consider these two cases. If $b=1$, its sign value is $1$, so the mean parameter is $1-\delta$. The probability of obtaining the input sign itself is the keep probability, namely $(1+(1-\delta))/2$ (`coordinateNoisePMF_apply_self_for_signPMF`); converting this mass to a real number and simplifying gives $1-\delta/2$. If $b=-1$, its sign value is $-1$, so the parameter is $\delta-1$. The probability of obtaining $b$ is now the probability of flipping the initial sign $1$, namely one minus the keep probability (`coordinateNoisePMF_apply_neg_for_signPMF`). The keep probability is at most one (`correlationKeepProbability_le_one`), so this subtraction converts to the corresponding real subtraction. Substituting the parameter gives $1-(1+(\delta-1))/2=1-\delta/2$. The sign-value identities for $1$ and $-1$ (`signValue_one`, `signValue_neg`) give the stated parameters in the two cases.

**Key facts.** `FABL.signValue_one`, `FABL.coordinateNoisePMF_apply_self_for_signPMF`, `FABL.signValue_neg`, `FABL.coordinateNoisePMF_apply_neg_for_signPMF`, `FABL.correlationKeepProbability_le_one`.
