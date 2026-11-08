<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/HypercontractiveNecessity.lean :: FABL.zeroVariable_one_two_half_hypercontractive -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Hypercontractivity of the Zero Variable

**Claim.** For all real numbers $a$ and $b$, the uniform $L^2$ norm on a one-point space of the function with constant value $a+\tfrac12 b\cdot 0$ is at most the uniform $L^1$ norm of the function with constant value $a+b\cdot 0$.

**Proof.** Because the random variable is identically zero, both functions in the inequality are the constant function with value $a$. For any positive exponent, the uniform $L^p$ norm of a constant function on a one-point space equals the absolute value of that constant: the normalized average of its absolute value to the $p$th power is $|a|^p$, and taking the $p$th root returns $|a|$. The extended-real exponents $1$ and $2$ here reduce to the ordinary uniform norms (`uniformLpNormENNReal_coe`). Thus both sides equal $|a|$, so the desired inequality holds with equality; the scaling identity for the uniform norm (`uniformLpNorm_const_mul`) supplies the constant-function calculation.

**Key facts.** `FABL.uniformLpNormENNReal_coe`, `FABL.uniformLpNorm_const_mul`.
