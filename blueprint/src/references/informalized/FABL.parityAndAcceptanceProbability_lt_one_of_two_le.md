<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/TestingAmplification.lean :: FABL.parityAndAcceptanceProbability_lt_one_of_two_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Parity acceptance probability is below one

**Claim.** For every integer $k\ge2$, the specified parity acceptance probability $p_k$ is strictly less than $1$.

**Proof.** Since $k\ge2$, we have $2^k\ge2^2=4$, so $2^{-k}\le\frac14$. The preceding upper bound (\(\texttt{parityAndAcceptanceProbability\_le\_twoPowInv}\)) gives $p_k\le\frac12+2^{-k}\le\frac34<1$.

**Key facts.** `FABL.parityAndAcceptanceProbability_le_twoPowInv`.
