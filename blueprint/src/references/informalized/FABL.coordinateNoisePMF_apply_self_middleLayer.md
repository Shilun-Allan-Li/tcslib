<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/FourierCoefficientsOfMajority.lean :: FABL.coordinateNoisePMF_apply_self_middleLayer -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Probability of retaining a sign

**Claim.** For $\rho\in[-1,1]$, with keep probability $p=(1+\rho)/2$, coordinate noise started at any sign $x$ assigns probability $p$ to $x$.

**Proof.** A sign is either $1$ or $-1$, so check those two cases. In either case, precisely the keep choice produces output $x$, and its weight is $p$. Summing the Boolean weights over the event that the choice is true gives $p$ (`sum_bool_filter_true_middleLayer`).

**Key facts.** `FABL.sum_bool_filter_true_middleLayer`.
