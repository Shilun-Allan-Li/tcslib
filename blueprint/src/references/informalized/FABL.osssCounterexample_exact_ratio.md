<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/DecisionTreeExercises.lean :: FABL.osssCounterexample_exact_ratio -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Exact variance-to-influence ratio

**Claim.** For the specified function and decision tree with $t=2+\sqrt{33}/3$, the variance divided by the query-probability-weighted sum of influences is $(42+2\sqrt{33})/51$.

**Proof.** The variance equals $11/8+5\sqrt{33}/24$ (`productVariance_osssCounterexample`), and the weighted influence sum equals $11/8+3\sqrt{33}/16$ (`osssCounterexample_weightedInfluenceSum`). Dividing these expressions and simplifying using $(\sqrt{33})^2=33$ gives $(42+2\sqrt{33})/51$. The denominator is positive, so this division is valid.

**Key facts.** `FABL.productVariance_osssCounterexample`, `FABL.osssCounterexample_weightedInfluenceSum`.
