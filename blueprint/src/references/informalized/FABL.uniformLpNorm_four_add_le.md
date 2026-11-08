<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/SmallSetExpansion.lean :: FABL.uniformLpNorm_four_add_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Triangle Inequality for the Fourth Norm

**Claim.** On a finite nonempty set, the uniform $L^4$ norm of $f+g$ is at most the sum of the uniform $L^4$ norms of $f$ and $g$.

**Proof.** For counting measure on the finite set, the $L^4$ triangle inequality bounds $(\sum_x |f(x)+g(x)|^4)^{1/4}$ by $(\sum_x |f(x)|^4)^{1/4}+(\sum_x |g(x)|^4)^{1/4}$. The uniform $L^4$ norm is this counting-measure norm divided by $|\Omega|^{1/4}$, as given by the normalized-sum formula (`FABL.uniformLpNorm_four_eq_sum_rpow_div_cardRoot`). Since $\Omega$ is nonempty, the divisor is positive. Dividing the counting-measure inequality by it gives the desired inequality, with the right-hand side splitting into the two normalized norms.

**Key facts.** `FABL.uniformLpNorm_four_eq_sum_rpow_div_cardRoot`.
