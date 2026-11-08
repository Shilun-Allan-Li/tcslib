<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/HastadThreeSat.lean :: FABL.signPMFOfMean_signValue_eq_pure -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Sign Mean Gives a Point Mass

**Claim.** For every sign $b$, the sign distribution whose mean parameter is the real value of $b$ is the point mass at $b$.

**Proof.** Equality of these distributions is checked by comparing their probabilities at an arbitrary sign $c$. Both $b$ and $c$ belong to $\{1,-1\}$, so split into the four possibilities. When $b=1$, its mean parameter is $1$ (`signValue_one`): the keep probability is $1$ (`correlationKeepProbability_one_coe`), hence the mass at $1$ is one (`coordinateNoisePMF_apply_self_for_signPMF`) and at $-1$ is zero (`coordinateNoisePMF_apply_neg_for_signPMF`). When $b=-1$, the parameter is $-1$ (`signValue_neg_one`): the keep probability is zero (`correlationKeepProbability_neg_one_coe`), so the mass at $-1$ is one and at $1$ is zero, by the same self and negated-output probability formulas. These are exactly the point-mass probabilities at $c$ in every case, proving equality of the distributions.

**Key facts.** `FABL.signValue_one`, `FABL.coordinateNoisePMF_apply_self_for_signPMF`, `FABL.correlationKeepProbability_one_coe`, `FABL.coordinateNoisePMF_apply_neg_for_signPMF`, `FABL.signValue_neg_one`, `FABL.correlationKeepProbability_neg_one_coe`.
