<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/BiasedThresholdPhenomena.lean :: FABL.shapleyValue_smul -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Homogeneity of the Shapley value

**Claim.** Multiplying a game by a real scalar $c$ multiplies its Shapley value at each player by $c$.

**Proof.** In the marginal contribution at a coalition $S$, scaling the game by $c$ scales both values in the difference by $c$. Thus the resulting marginal contribution is $c$ times the original one. The expectation of a scalar multiple of a function is the scalar times its expectation (`pmfExpectation_smul_fun`), so the Shapley value scales by $c$.

**Key facts.** `FABL.pmfExpectation_smul_fun`.
