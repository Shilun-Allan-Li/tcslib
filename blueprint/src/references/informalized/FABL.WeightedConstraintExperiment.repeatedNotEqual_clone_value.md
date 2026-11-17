<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/UniqueGamesReduction.lean :: FABL.WeightedConstraintExperiment.repeatedNotEqual_clone_value -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Value of the Cloned Experiment

**Claim.** In the two-clone experiment, assigning $-1$ to clone $0$ and $1$ to clone $1$ gives value $1/2$.

**Proof.** Express the cloned experiment’s value as an average first over its original outcome and then over the independent clone choices (`clone_value_eq_iterated`). The original outcome is deterministic. For any pair of clone choices, the not-equal predicate is satisfied exactly when the choices differ: the two clones receive distinct signs by injectivity of the specified assignment (`repeatedNotEqualCloneAssignment_injective`). Thus the payoff is one minus the indicator that the choices coincide. For two independent uniform choices from two clones, the probability of coincidence is $1/2$ (`uniformCloneTuple_pair_eq_probability`), so the expected payoff is $1-1/2=1/2$. The deterministic original outcome does not change this expectation (`pmfExpectation_pure`).

**Key facts.** `FABL.WeightedConstraintExperiment.clone_value_eq_iterated`, `FABL.WeightedConstraintExperiment.repeatedNotEqualCloneAssignment_injective`, `FABL.pmfExpectation_pure`, `FABL.uniformCloneTuple_pair_eq_probability`.
