<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/BiasedThresholdPhenomena.lean :: FABL.shapleyValue_add -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Additivity of the Shapley Value

**Claim.** For real-valued functions $f$ and $g$ on subsets of an $n$-element set, the Shapley value of $f+g$ at $i$ is the sum of their Shapley values at $i$.

**Proof.** At each subset $S$, the marginal contribution of $f+g$ is $(f+g)(S\cup\{i\})-(f+g)(S\setminus\{i\})$. Distributing addition and subtraction shows this is the sum of the marginal contributions of $f$ and $g$. Taking expectation under the same Shapley subset distribution preserves sums, by additivity of finite probability-mass-function expectation (`pmfExpectation_add_fun`). This gives the asserted additivity.

**Key facts.** `FABL.pmfExpectation_add_fun`.
