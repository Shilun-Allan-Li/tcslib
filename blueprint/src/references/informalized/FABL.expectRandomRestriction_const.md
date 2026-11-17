<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/DNFFourier.lean :: FABL.expectRandomRestriction_const -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Expectation of a constant under random restriction

**Claim.** For every $n$, $\delta$, and $c$, the random restriction expectation of the constant function with value $c$ is $c$.

**Proof.** For each choice of free-coordinate set, the expectation over signs of the constant $c$ is $c$. Hence the full expectation is $c$ times the sum of all subset weights. Those weights sum to one (by `sum_deltaRandomSubsetWeight`), so the result is $c$.

**Key facts.** `FABL.sum_deltaRandomSubsetWeight`.
