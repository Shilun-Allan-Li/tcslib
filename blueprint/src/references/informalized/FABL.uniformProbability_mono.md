<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/KKLBribery.lean :: FABL.uniformProbability_mono -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monotonicity of Uniform Probability

**Claim.** If every element satisfying $P$ also satisfies $Q$, then the uniform probability of $P$ is at most the uniform probability of $Q$.

**Proof.** Write each probability as the sum over $\Omega$ of its indicator, divided by $|\Omega|$. At every element, the implication $P(x)\Rightarrow Q(x)$ ensures that the indicator of $P$ is at most the indicator of $Q$: if $P(x)$ holds, so does $Q(x)$, and otherwise the first indicator is zero. Summing these pointwise inequalities and dividing by the positive cardinality of the nonempty set proves the result.
