<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/BiasedThresholdPhenomena.lean :: FABL.shapleyValue_subsetPointIndicator -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Shapley value of a subset indicator

**Claim.** The Shapley value of the indicator of a subset $A$ is the sum of the probabilities of $A$ and $A\setminus\{i\}$ when $i\in A$, and is the negative of the sum of the probabilities of $A$ and $A\cup\{i\}$ when $i\notin A$.

**Proof.** Write the indicator's marginal contribution as the difference between its value at $S\cup\{i\}$ and its value at $S\setminus\{i\}$. Linearity of expectation turns the expectation of this difference into the difference of the two expectations (`pmfExpectation_sub_general`). The expectation of the indicator evaluated at $S\cup\{i\}$ is the sum of the probabilities of $A$ and $A\setminus\{i\}$ if $i\in A$, and zero otherwise (`shapleyExpectation_pointIndicator_insert`). The expectation of the indicator evaluated at $S\setminus\{i\}$ is the sum of the probabilities of $A$ and $A\cup\{i\}$ if $i\notin A$, and zero otherwise (`shapleyExpectation_pointIndicator_erase`). If $i\in A$, subtracting therefore leaves the first sum; if $i\notin A$, it leaves the negative of the second sum.

**Key facts.** `FABL.pmfExpectation_sub_general`, `FABL.shapleyExpectation_pointIndicator_insert`, `FABL.shapleyExpectation_pointIndicator_erase`.
