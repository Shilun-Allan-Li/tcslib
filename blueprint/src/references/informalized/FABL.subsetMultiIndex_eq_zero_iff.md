<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/BiasedAnalysis.lean :: FABL.subsetMultiIndex_eq_zero_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Zero Coordinates of a Subset Index

**Claim.** The subset index associated with $S$ has value zero at $i$ exactly when $i$ is not in $S$.

**Proof.** Split into the two possibilities for membership. If $i\in S$, the subset index takes value $1$ there, so it is not zero. If $i\notin S$, its defining value is $0$. These two cases establish both directions of the equivalence.
