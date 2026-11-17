<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/UniqueGamesReduction.lean :: FABL.WeightedConstraintExperiment.clonePayoff_mem_Icc -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Clone payoff bounds

**Claim.** For any assignment, outcome, and choice of clone at each query position, the clone payoff lies in $[0,1]$.

**Proof.** The payoff is $1$ if the selected predicate is satisfied and $0$ otherwise. In either case it lies between $0$ and $1$.
