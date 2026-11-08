<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Invariance/Coordinates.lean :: BooleanAnalysis.GaussianSpace.Invariance.indep_coordinate_parts -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Independence of coordinate-free parts

**Claim.** For an independent measurable-up-to-null coordinate family, the fixed coordinate $X_i$ is independent of the pair of multilinear evaluations formed from the coordinate-free and coordinate-derivative coefficient families.

**Proof.** The coordinate-free evaluation identity (\texttt{coordinateFree\_eval\_sum}) writes the first evaluation as a polynomial sum over subsets of the coordinates other than $i$, with coefficients $F(T)$. The coordinate-derivative evaluation identity (\texttt{coordinateDerivative\_eval\_sum}) gives the second evaluation as a sum over those same subsets, with coefficients $F(T\cup\{i\})$. The independence theorem for paired polynomial sums that omit a fixed coordinate (\texttt{MultilinearMoments.indep\_sum\_of\_notMem}) says that $X_i$ is independent of this pair whenever the other coordinates form an independent family and are measurable up to null sets. The full coordinate set with $i$ removed omits $i$, so the theorem applies; the two evaluation identities identify its polynomial pair with the one in the claim.

**Key facts.** `BooleanAnalysis.GaussianSpace.Invariance.coordinateFree_eval_sum`, `BooleanAnalysis.GaussianSpace.Invariance.coordinateDerivative_eval_sum`, `BooleanAnalysis.Hypercontractivity.MultilinearMoments.indep_sum_of_notMem`.
