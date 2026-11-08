<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/FourierCoefficientsOfMajority.lean :: FABL.coordinateNoisePMF_apply_neg_middleLayer -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Probability of flipping a sign

**Claim.** For $[0m\rho\in[-1,1]$, with keep probability $p=(1+\rho)/2$, coordinate noise started at any sign $x$ assigns probability $1-p$ to $-x$.

**Proof.** A sign is either $1$ or $-1$, so consider each possibility for $x$. In either case, among the two outcomes of the Boolean keep-or-flip choice, precisely the flip choice produces $-x$. Its weight is $1-p$. Summing the Boolean weights over the event that the choice is false gives exactly $1-p$ (`sum_bool_filter_false_middleLayer`).

**Key facts.** `FABL.sum_bool_filter_false_middleLayer`.
