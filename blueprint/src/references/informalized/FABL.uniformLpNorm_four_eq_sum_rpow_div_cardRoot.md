<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/SmallSetExpansion.lean :: FABL.uniformLpNorm_four_eq_sum_rpow_div_cardRoot -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourth Norm as a Normalized Sum

**Claim.** On a finite nonempty set, the uniform $L^4$ norm of $f$ is $\bigl(\sum_x |f(x)|^4\bigr)^{1/4}/|\Omega|^{1/4}$.

**Proof.** The uniform average of $|f|^4$ is the sum of its values divided by the cardinality of the set. Taking its $1/4$ power, as prescribed by the definition of the uniform norm, gives the displayed expression: the fourth root of a quotient of nonnegative quantities is the quotient of their fourth roots. Nonemptiness ensures the cardinality is positive.
