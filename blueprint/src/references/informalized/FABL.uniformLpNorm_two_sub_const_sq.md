<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/HypercontractiveAnticoncentration.lean :: FABL.uniformLpNorm_two_sub_const_sq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Squared norm under a constant shift

**Claim.** For a mean-zero function on a finite nonempty set, the squared uniform $L^2$ norm of $X-\theta$ equals the squared uniform $L^2$ norm of $X$ plus $\theta^2$.

**Proof.** The identity relating the squared uniform $L^2$ norm to the uniform expectation of the square (\texttt{uniformLpNorm\_two\_sq\_eq\_expect\_sq}) reduces the claim to computing the expectation of $(X-\theta)^2$. Expand pointwise as $X^2-2\theta X+\theta^2$. Linearity of expectation separates these terms; the middle term has expectation $-2\theta\,\mathbb E X=0$ by the mean-zero hypothesis, while the expectation of the constant term is $\theta^2$. The remaining term is the expectation of $X^2$, which is the original squared norm by the same identity.

**Key facts.** `FABL.uniformLpNorm_two_sq_eq_expect_sq`.
