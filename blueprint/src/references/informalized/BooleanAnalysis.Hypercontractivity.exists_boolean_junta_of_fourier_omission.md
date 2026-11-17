<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Applications/KKL/Rounding.lean :: BooleanAnalysis.Hypercontractivity.exists_boolean_junta_of_fourier_omission -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# A Junta from Fourier Omission

**Claim.** For a Boolean-valued function $f$ and a coordinate set $J$, there is a Boolean-valued function depending only on $J$ whose disagreement probability with $f$ is at most half the total squared Fourier weight on sets not contained in $J$.

**Proof.** Choose a point $z$ minimizing, over the finite cube, the disagreement probability between $f$ and the restriction $x\mapsto f(x_J,z_{[n]\setminus J})$. Such a minimizer exists because the cube is finite. Its restricted function is Boolean-valued since it is obtained by evaluating $f$. It depends only on $J$: if two inputs agree on $J$, their restricted inputs agree at coordinates in $J$ by hypothesis and outside $J$ because both use the same fixed point $z$. By minimality, its disagreement probability is no greater than the average disagreement probability over all choices of the fixed point. The expectation of a constant function equals that constant (\texttt{ThresholdFunctions.expect\_const}), and expectation preserves pointwise inequalities (\texttt{ThresholdFunctions.expect\_mono}), so this average bounds the chosen minimum. The coordinate-restriction disagreement identity (\texttt{expect\_disagreement\_coordinateRestriction}) evaluates the average as half the sum of squared Fourier coefficients over sets not contained in $J$, proving the claim.

**Key facts.** `BooleanAnalysis.ThresholdFunctions.expect_const`, `BooleanAnalysis.ThresholdFunctions.expect_mono`, `BooleanAnalysis.Hypercontractivity.expect_disagreement_coordinateRestriction`.
