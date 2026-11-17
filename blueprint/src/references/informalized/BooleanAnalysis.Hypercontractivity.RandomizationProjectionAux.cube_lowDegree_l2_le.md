<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Randomization/ProjectionBounds.lean :: BooleanAnalysis.Hypercontractivity.RandomizationProjectionAux.cube_lowDegree_l2_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Low degree projection contracts in $L^2$

**Claim.** The $L^2$ norm of the Fourier truncation to sets of size at most $k$ is at most the $L^2$ norm of the original function.

**Proof.** Both squared $L^2$ norms are expressed by Parseval's identity (`BooleanAnalysis.parseval`) as sums of squared Fourier coefficients. For each set $S$, the coefficient of the truncation is the original coefficient when $|S|\le k$ and zero otherwise (`KKL.fourierCoeff_lowDegreePart`). Its square is therefore at most the square of the original coefficient in either case. Summing these termwise inequalities bounds the squared norm of the truncation by the squared norm of the original function. Since square root is increasing on nonnegative reals, the same inequality holds for the norms.

**Key facts.** `BooleanAnalysis.parseval`, `KKL.fourierCoeff_lowDegreePart`.
