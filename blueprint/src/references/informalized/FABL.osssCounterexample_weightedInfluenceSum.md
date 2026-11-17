<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/DecisionTreeExercises.lean :: FABL.osssCounterexample_weightedInfluenceSum -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Weighted influence sum

**Claim.** For the specified function and randomized decision tree, the sum over coordinates of query probability times coordinate influence equals $11/8+3\sqrt{33}/16$.

**Proof.** Expand the sum over the three coordinates. The query probabilities for coordinates $0,1,2$ are respectively $1,3/4,3/4$, and their influences are respectively $1/8, 5/6+\sqrt{33}/8, 5/6+\sqrt{33}/8$. Thus the sum is $1/8+(3/4)(5/6+\sqrt{33}/8)+(3/4)(5/6+\sqrt{33}/8)$, which simplifies to $11/8+3\sqrt{33}/16$.

**Key facts.** `FABL.osssCounterexample_queryProbability_zero`, `FABL.osssCounterexample_queryProbability_one`, `FABL.osssCounterexample_queryProbability_two`, `FABL.productInfluence_osssCounterexample_zero`, `FABL.productInfluence_osssCounterexample_one`, `FABL.productInfluence_osssCounterexample_two`.
