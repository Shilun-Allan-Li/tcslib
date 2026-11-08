<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/SubspacesAndDecisionTrees/DecisionTreeFourier.lean :: FABL.F₂DecisionTree.vectorFourierWeightAbove_eq_fourierWeightAbove_binaryFunctionOnSignCube -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourier tail under cube encoding

**Claim.** The vector Fourier weight of $f$ above support size $k$ equals the Fourier weight of its corresponding sign-cube function above degree $k$.

**Proof.** Expand both tail weights as sums over indices satisfying the respective size threshold, and reindex the sum on binary-cube vectors by the bijection between such vectors and subsets of coordinates. Under this bijection, the associated subset is precisely the support of the vector (\texttt{f₂CubeEquivFinset\_apply}); consequently the condition that the support has size greater than $k$ becomes the condition that the subset has size greater than $k$. For each corresponding index, the vector Fourier coefficient equals the sign-cube Fourier coefficient at that support (\texttt{vectorFourierCoeff\_eq\_fourierCoeff\_binaryFunctionOnSignCube}). Squaring these equal coefficients and summing over the reindexed terms gives the equality.

**Key facts.** `FABL.f₂CubeEquivFinset_apply`, `FABL.vectorFourierCoeff_eq_fourierCoeff_binaryFunctionOnSignCube`.
