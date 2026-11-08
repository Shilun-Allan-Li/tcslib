<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Pseudorandomness/Examples.lean :: FABL.uniformProbability_correlationImmuneAndExample_eq_true -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Probability of the Example

**Claim.** For every positive integer $m$, the correlation-immune example is true on exactly one quarter of the inputs.

**Proof.** Let $f$ be this example. Its mean is $1/2$ by the established computation of the mean (\texttt{mean\_correlationImmuneAndExample}). For any sign-valued function, the mean equals the probability of the value $1$ minus the probability of the value $-1$ (\texttt{mean\_eq\_probability\_one\_sub\_probability\_neg\_one}), while these two probabilities sum to $1$ (\texttt{uniformProbability\_one\_add\_neg\_one\_eq\_one}). Thus, if $p$ is the probability that $f=-1$, then $1/2=(1-p)-p$, so $p=1/4$.

**Key facts.** `FABL.mean_correlationImmuneAndExample`, `FABL.mean_eq_probability_one_sub_probability_neg_one`, `FABL.uniformProbability_one_add_neg_one_eq_one`.
