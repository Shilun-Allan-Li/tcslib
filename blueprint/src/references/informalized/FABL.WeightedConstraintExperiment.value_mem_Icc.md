<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/UniqueGamesReduction.lean :: FABL.WeightedConstraintExperiment.value_mem_Icc -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bounds on the Experiment Value

**Claim.** For every assignment, the value of the weighted constraint experiment lies in the interval $[0,1]$.

**Proof.** Each payoff lies between $0$ and $1$ (the payoff bounds theorem, `FABL.WeightedConstraintExperiment.payoff_mem_Icc`). The value is the probability-weighted expectation of these payoffs. Nonnegativity of expectation gives the lower bound, and monotonicity of expectation bounds it above by the expectation of the constant function $1$. That constant has expectation $1$ (`FABL.pmfExpectation_const`), so the value lies in $[0,1]$.

**Key facts.** `FABL.WeightedConstraintExperiment.payoff_mem_Icc`, `FABL.pmfExpectation_nonneg`, `FABL.pmfExpectation_mono`, `FABL.pmfExpectation_const`.
