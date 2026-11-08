<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Hermite/Truncation.lean :: BooleanAnalysis.GaussianSpace.hermite_degree_truncation_tendsto -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Convergence of Hermite truncations

**Claim.** For every square-integrable function on the product Gaussian space, the stated Hermite degree truncations converge to the function in the $L^2$ norm.

**Proof.** The Hermite expansion theorem says that the net of finite partial sums of the Hermite series converges in $L^2$ to the class of $f$ (`hermite_expansion`). The finite sets of indices of total degree at most $k$ tend to exhaust all multi-indices (`hermiteDegreeIndices_tendsto`), so the corresponding partial sums also converge in $L^2$ to that class. The equivalence between convergence in $L^2$ and convergence of the associated $eLpNorm$ distances then gives convergence of the norm of the difference to zero. Finally, the finite sum in the statement is the pointwise expression for this partial sum: each $L^2$ Hermite function agrees almost everywhere with its defining function (`coeFn_sum_hermiteL2`), and rewriting the degree-indexed sum as the displayed sum over bounded coordinates gives the specified truncation (`sum_hermiteDegreeIndices`). Thus its $eLpNorm$ distance from $f$ has the same limit.

**Key facts.** `BooleanAnalysis.GaussianSpace.hermite_expansion`, `BooleanAnalysis.GaussianSpace.hermiteDegreeIndices_tendsto`, `BooleanAnalysis.GaussianSpace.coeFn_sum_hermiteL2`, `BooleanAnalysis.GaussianSpace.sum_hermiteDegreeIndices`.
