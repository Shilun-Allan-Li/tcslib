<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/DecisionTreeExercises.lean :: FABL.osssBookCounterexample_exact_ratio -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Exact variance ratio

**Claim.** For the specified function $F$ on the three-dimensional sign cube and its randomized decision tree $T$, the ratio of its variance to the query-probability-weighted sum of its coordinate influences is $(130+20\sqrt3)/157$.

**Proof.** The variance is $(20+10\sqrt3)/16$, by the variance computation for this counterexample (`productVariance_osssBookCounterexample`), and the weighted influence sum is $(20+9\sqrt3)/16$ (`osssBookCounterexample_weightedInfluenceSum`). Their ratio is therefore $(20+10\sqrt3)/(20+9\sqrt3)$. The denominator is nonzero, and using $(\sqrt3)^2=3$ to rationalize and simplify gives $(130+20\sqrt3)/157$.

**Key facts.** `FABL.productVariance_osssBookCounterexample`, `FABL.osssBookCounterexample_weightedInfluenceSum`.
