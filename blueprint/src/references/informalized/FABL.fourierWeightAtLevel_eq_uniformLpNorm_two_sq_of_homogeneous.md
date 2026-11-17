<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/MatchingMomentCombinatorics.lean :: FABL.fourierWeightAtLevel_eq_uniformLpNorm_two_sq_of_homogeneous -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Weight of a homogeneous function

**Claim.** If all nonzero Fourier coefficients of $f$ occur on sets of size $k$, then the Fourier weight at level $k$ equals the square of the uniform $L^2$ norm of $f$.

**Proof.** By the squared-norm identity and Parseval, the squared uniform $L^2$ norm equals the sum of the squared Fourier coefficients over all subsets. The homogeneity assumption says that every coefficient at a set whose size is not $k$ must be zero: otherwise its nonzero coefficient would, by the assumption, force that set to have size $k$. Thus the full sum reduces to the sum over sets of size $k$, exactly the level-$k$ Fourier weight.

**Key facts.** `FABL.uniformLpNorm_two_sq_eq_uniformInner`, `FABL.parseval`.
