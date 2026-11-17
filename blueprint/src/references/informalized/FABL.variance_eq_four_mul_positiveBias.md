<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/KKLBribery.lean :: FABL.variance_eq_four_mul_positiveBias -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Variance from positive bias

**Claim.** If $p$ is the uniform probability that a Boolean function takes value $+1$, then its variance is $4p(1-p)$.

**Proof.** The variance is four times the product of the probabilities that the function equals $+1$ and $-1$ (`variance_eq_four_mul_probabilities`). These two probabilities sum to one (`uniformProbability_one_add_neg_one_eq_one`), since the function takes one of these two Boolean values. Writing the second probability as $1-p$, where $p$ is the positive bias, gives $\operatorname{Var}(f)=4p(1-p)$.

**Key facts.** `FABL.variance_eq_four_mul_probabilities`, `FABL.uniformProbability_one_add_neg_one_eq_one`.
