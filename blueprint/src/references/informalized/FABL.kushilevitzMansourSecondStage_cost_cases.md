<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/KushilevitzMansour.lean :: FABL.kushilevitzMansourSecondStage_cost_cases -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Second-stage cost alternatives

**Claim.** Every supported output and cost pair from the second-stage program either has zero cost in all three components, or comes from a nonempty active family within the active cap and has exactly the finite-family Fourier estimator’s prescribed cost.

**Proof.** Split according to whether the active family is absent or present. If it is absent, the program returns the empty hypothesis purely, so every supported pair has zero cost. If a family is present, split on whether its cardinality is at most the active cap. When it exceeds the cap, the program again returns purely and the cost is zero. When it is within the cap, split on whether the family is nonempty: an empty family gives the pure empty hypothesis and zero cost, while a nonempty family selects the finite-family Fourier estimator at accuracy $\varepsilon$ and confidence $1/20$. In that last case, the estimator’s cost theorem identifies the cost of every supported outcome with the prescribed finite-family estimator cost. These cases give the claimed alternatives.

**Key facts.** `FABL.queriedFiniteFamilyFourierEstimatorProgramWithConfidence_cost_eq`.
