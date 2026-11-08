<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/SmallSetExpansion.lean :: FABL.uniformLpNorm_four_mono_abs -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monotonicity of the Fourth Norm

**Claim.** If $|f(x)|\le g(x)$ at every point of a finite set, then the uniform $L^4$ norm of $f$ is at most that of $g$.

**Proof.** The norms are nonnegative, so it suffices to compare their fourth powers. The fourth-power identity converts those powers to the averages of $f(x)^4$ and $g(x)^4` (`FABL.uniformLpNorm_four_pow_eq_expect_fourth`). For each point, $f(x)^4=|f(x)|^4$, and raising $|f(x)|\le g(x)$ to the fourth power gives $|f(x)|^4\le g(x)^4$. Averaging preserves this pointwise inequality. Taking fourth roots then gives the result.

**Key facts.** `FABL.uniformLpNorm_nonneg`, `FABL.uniformLpNorm_four_pow_eq_expect_fourth`.
