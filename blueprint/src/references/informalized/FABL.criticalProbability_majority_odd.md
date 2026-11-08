<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/BiasedAnalysis.lean :: FABL.criticalProbability_majority_odd -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Odd Majority Critical Probability

**Claim.** For every natural number $m$, the critical probability of majority on $2m+1$ signs is $1/2$.

**Proof.** Fix $m$. Odd majority is monotone and nonconstant (`FABL.majority_monotone`, `FABL.majority_odd_isNonconstant`), so its critical probability is the unique $p\in(0,1)$ for which the biased minus probability polynomial equals $1/2$ (`FABL.existsUnique_criticalProbability`). The point $p=1/2$ lies in $(0,1)$, and the polynomial equals $1/2$ there (`FABL.biasedMinusProbabilityPolynomial_majority_one_half`). By uniqueness, the critical probability is $1/2$.

**Key facts.** `FABL.majority_monotone`, `FABL.majority_odd_isNonconstant`, `FABL.existsUnique_criticalProbability`, `FABL.biasedMinusProbabilityPolynomial_majority_one_half`.
