<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/DecisionTreeExercises.lean :: FABL.osssCounterexample_queryProbability_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# First-coordinate query probability

**Claim.** For the specified counterexample tree and parameter, the probability of querying coordinate $0$ under a uniform product input is $1$.

**Proof.** Apply the parameterized query-probability result (osssCounterexampleRandomizedTreeAt_queryProbability_zero) at the specified parameter $t=2+\sqrt{33}/3$. It states that coordinate $0$ is queried with probability $1$ for every parameter, hence also for this one.

**Key facts.** `FABL.osssCounterexampleRandomizedTreeAt_queryProbability_zero`.
