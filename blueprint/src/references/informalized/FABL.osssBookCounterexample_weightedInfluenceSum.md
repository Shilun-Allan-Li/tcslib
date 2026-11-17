<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/DecisionTreeExercises.lean :: FABL.osssBookCounterexample_weightedInfluenceSum -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Weighted influence sum

**Claim.** For the specified function $F$ and decision tree $T$, the sum of each coordinate's query probability times its influence is $(20+9\sqrt3)/16$.

**Proof.** Write $t=2+\sqrt3$. The tree queries coordinate $0$ with probability $1$ and each of coordinates $1$ and $2$ with probability $3/4$ (`osssCounterexampleRandomizedTreeAt_queryProbability_zero`, `osssCounterexampleRandomizedTreeAt_queryProbability_one`, and `osssCounterexampleRandomizedTreeAt_queryProbability_two`). Under the uniform sign law, product influence agrees with the stated influence (`productInfluence_uniformSign_eq_influence`). The three influences are $1/8$ for coordinate $0$ and $(t^2-t+1)/8$ for each of coordinates $1,2$ (`influence_osssCounterexampleAt_zero`, `influence_osssCounterexampleAt_one`, and `influence_osssCounterexampleAt_two`). Thus the weighted sum is $1/8+(3/4)(t^2-t+1)/4$. Substituting $t=2+\sqrt3$ and using $(\sqrt3)^2=3$ yields $(20+9\sqrt3)/16$.

**Key facts.** `FABL.osssCounterexampleRandomizedTreeAt_queryProbability_zero`, `FABL.osssCounterexampleRandomizedTreeAt_queryProbability_one`, `FABL.osssCounterexampleRandomizedTreeAt_queryProbability_two`, `FABL.productInfluence_uniformSign_eq_influence`, `FABL.influence_osssCounterexampleAt_zero`, `FABL.influence_osssCounterexampleAt_one`, `FABL.influence_osssCounterexampleAt_two`.
