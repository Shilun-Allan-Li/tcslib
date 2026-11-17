<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/MatchingMomentCombinatorics.lean :: FABL.uniformLpNorm_even_pow_eq_expect_even -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Even Moments of the Uniform Norm

**Claim.** For a finite set, a positive natural number $r$, and a real-valued function $f$, the uniform $L^{2r}$ quantity raised to the power $2r$ is the uniform average of $f(x)^{2r}$.

**Proof.** Set $q=2r$, which is positive. The identity for positive exponents says that the $q$th power of the uniform norm is the average of $|f(x)|^q$ (`FABL.uniformLpNorm_rpow`). Since $q$ is the natural-number exponent $2r$, this power is an ordinary integer power, and an even power is unchanged by taking absolute values: $|f(x)|^{2r}=f(x)^{2r}$. Substituting this pointwise equality into the finite average proves the result.

**Key facts.** `FABL.uniformLpNorm_rpow`.
