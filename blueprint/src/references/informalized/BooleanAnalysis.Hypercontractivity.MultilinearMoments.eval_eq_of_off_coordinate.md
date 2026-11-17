<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/RandomVariables/Moments.lean :: BooleanAnalysis.Hypercontractivity.MultilinearMoments.eval_eq_of_off_coordinate -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation Ignores an Unused Coordinate

**Claim.** If every coefficient indexed by a set containing $i$ vanishes, and the two input families agree at every coordinate other than $i$, then their multilinear evaluations agree as functions on $\Omega$.

**Proof.** Fix $\omega\in\Omega$ and compare the finite sums term by term. For a set $S$ containing $i$, its coefficient is zero, so its contribution is zero for both families. For a set $S$ not containing $i$, every coordinate in its product differs from $i$; the two families therefore have equal values at each such coordinate, and the products agree. Thus every summand agrees, so the sums agree at this $\omega$. Since $\omega$ was arbitrary, the evaluations are equal as functions.
