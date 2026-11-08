<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/DecisionTreeExercises.lean :: FABL.recursiveNandTrueCost_succ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# True-Cost Recurrence

**Claim.** For every $d\in\mathbb{N}$, the true-output cost at level $d+1$ equals the false-output cost at level $d$ plus half the true-output cost at level $d$: $T_{d+1}=F_d+T_d/2$.

**Proof.** This is the successor clause in the recursive definition of the true-output cost: at level $d+1$, it is defined to be the false-output cost at level $d$ plus half the true-output cost at level $d$.
