<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RandomizedDecisionTreeComplexity.lean :: FABL.RandomizedDecisionTree.queryProbability_le_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Query probability upper bound

**Claim.** For every coordinate $i$, the probability that $T$ queries $i$ under independent inputs of law $\pi$ is at most $1$.

**Proof.** For each fixed input $x$, the query probability is the seed expectation of an indicator: it is $1$ when the selected tree queries $i$ and $0$ otherwise. Each such indicator is at most the constant function $1$, so monotonicity of expectation gives a query probability on $x$ at most the expectation of $1$, which is $1$ ($\texttt{FABL.pmfExpectation\_const\_one}$). Applying the same monotonicity to the expectation over inputs bounds the overall query probability by the input expectation of the constant function $1$, also equal to $1$.

**Key facts.** `FABL.pmfExpectation_mono`, `FABL.pmfExpectation_const_one`.
