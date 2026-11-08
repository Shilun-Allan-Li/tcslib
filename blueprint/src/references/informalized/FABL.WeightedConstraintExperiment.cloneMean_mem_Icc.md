<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/UniqueGamesReduction.lean :: FABL.WeightedConstraintExperiment.cloneMean_mem_Icc -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Clone mean lies in the unit interval

**Claim.** For a positive number of clones, the uniform mean of the assigned signs for any fixed variable lies in $[-1,1]$.

**Proof.** Every assigned sign has value either $-1$ or $1$ (`signValue_eq_neg_one_or_one`). Thus each term in the uniform mean is at least $-1$ and at most $1$. Taking expectations preserves these pointwise inequalities, and the expectation of a constant is that constant. Hence the mean lies between $-1$ and $1$.

**Key facts.** `FABL.signValue_eq_neg_one_or_one`.
