<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/GotsmanLinialExtremizer.lean :: FABL.shiftedBinomialProbability_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Initial shifted binomial probability

**Claim.** At shift zero, the shifted binomial probability equals the odd majority influence: both are $\binom{2m}{m}/2^{2m}$.

**Proof.** Set the shift and offset parameters in the definition of the shifted binomial probability to zero. The resulting upper and lower binomial indices are $2m$ and $m$, and its denominator is $2^{2m}$. This is exactly the definition of the odd majority influence.
